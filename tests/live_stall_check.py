#!/usr/bin/env python3
"""By hand, against a running Leak IV (not in CI): can a cold file worker still
stall everyone?

    python3 tests/live_stall_check.py https://barkingtree-leak-iv.hf.space

What stalled the verifier on 2026-10-20 was the cold start of the Lean file worker,
not a script: a fresh worker needs about 200 s to load the tree, more than the 180 s a
verify may take, so the first script after any restart looked like "verify exceeded
180s", and the next request restarted the load, so with clients retrying it never
finished (25 minutes, then three hours). The check reproduces that sequence: client A
restarts the elaborator (`tengoku_sync`), client B submits a trivial script one second
later, and then the exact script that was blamed. Before the fix B's script came back
as "verify exceeded 180s". With it, B waits for the load (a few minutes) and is
answered with success, /health shows no timeouts and a warm worker, and the blamed
script (a kernel evaluation that takes about 11 s on a warm worker) also succeeds.
Plain urllib, no dependencies."""
import json
import sys
import threading
import time
import urllib.request

BASE = (sys.argv[1] if len(sys.argv) > 1 else "https://barkingtree-leak-iv.hf.space").rstrip("/")
BIG = r"""open Nat in
lemma cb_eq' (n : ℕ) : n.centralBinom = (2 * n).descFactorial n / n ! := by
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.choose_eq_descFactorial_div_factorial]

open Nat in
theorem E396_k2 : descFactorial 2480 3 ∣ centralBinom 2480 := by
  rw [cb_eq']
  decide +kernel

open Nat in
theorem E396_k3 : descFactorial 8178 4 ∣ centralBinom 8178 := by
  rw [cb_eq']
  decide +kernel

open Nat in
theorem E396_k4 : descFactorial 45153 5 ∣ centralBinom 45153 := by
  rw [cb_eq']
  decide +kernel"""
# ^ the exact script trial 7 sent at 15:08:37 UTC on 2026-10-20: the first two kernel evaluations pass in seconds, the third (a five-digit
#   numeral) does not come back, and before the fix it held the verifier for everyone for 25 minutes
SMALL = "example : (2 : ℕ) + 2 = 4 := by norm_num"


class Client:
    """One MCP-over-SSE session: GET /sse gives the message endpoint, POSTed
    JSON-RPC is answered on the stream."""

    def __init__(self, name):
        self.name = name
        self.resp = urllib.request.urlopen(f"{BASE}/sse", timeout=3600)
        self.endpoint = None
        self.answers = {}
        self.lock = threading.Condition()
        threading.Thread(target=self._pump, daemon=True).start()
        with self.lock:
            while not self.endpoint:
                self.lock.wait(30)
        self.call(0, "initialize", {"protocolVersion": "2024-11-05", "capabilities": {}, "clientInfo": {"name": name, "version": "0"}})
        self._post({"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}})

    def _pump(self):
        event = None
        for raw in self.resp:
            line = raw.decode("utf-8", "replace").rstrip("\n")
            if line.startswith("event:"):
                event = line[6:].strip()
            elif line.startswith("data:"):
                data = line[5:].strip()
                if event == "endpoint":
                    with self.lock:
                        self.endpoint = data if data.startswith("http") else BASE + data
                        self.lock.notify_all()
                else:
                    try:
                        msg = json.loads(data)
                    except ValueError:
                        continue
                    if "id" in msg:
                        with self.lock:
                            self.answers[msg["id"]] = msg
                            self.lock.notify_all()
                event = None

    def _post(self, body):
        req = urllib.request.Request(self.endpoint, data=json.dumps(body).encode(), headers={"content-type": "application/json"})
        urllib.request.urlopen(req, timeout=60).read()

    def call(self, msg_id, method, params, timeout=900):
        self._post({"jsonrpc": "2.0", "id": msg_id, "method": method, "params": params})
        with self.lock:
            while msg_id not in self.answers:
                if not self.lock.wait(timeout):
                    raise TimeoutError(f"{self.name}: no answer to {method} in {timeout}s")
            return self.answers.pop(msg_id)

    def verify(self, msg_id, script):
        t0 = time.time()
        r = self.call(msg_id, "tools/call", {"name": "verify_full_script", "arguments": {"script": script}})
        text = (r.get("result") or {}).get("content", [{}])[0].get("text", "") or json.dumps(r.get("error"))
        return time.time() - t0, text


def health():
    try:
        return json.loads(urllib.request.urlopen(f"{BASE}/health", timeout=30).read())
    except Exception as e:
        return {"error": str(e)[:80]}



def health():
    try:
        return json.loads(urllib.request.urlopen(f"{BASE}/health", timeout=30).read())
    except Exception as e:
        return {"error": str(e)[:80]}


h0 = health()
print("health before:", h0)
a, b = Client("A"), Client("B")
t_sync = {}
def restart():
    t0 = time.time()
    r = a.call(1, "tools/call", {"name": "tengoku_sync", "arguments": {}}, timeout=1200)
    t_sync["s"] = (time.time() - t0, ((r.get("result") or {}).get("content") or [{}])[0].get("text", "")[:120])
ta = threading.Thread(target=restart)
ta.start()
time.sleep(1)
t1, text1 = b.verify(1, SMALL)
ta.join()
print(f"A restart (tengoku_sync): {t_sync['s'][0]:.0f}s -> {t_sync['s'][1]!r}")
print(f"B trivial script, 1 s after the restart began: {t1:.0f}s -> {text1[:90]!r}")
t2, text2 = b.verify(2, BIG)
print(f"B the outage script, on the warmed worker: {t2:.0f}s -> {text2[:90]!r}")
h1 = health()
print("health after:", h1)
ok = (
    "Compilation Successful" in text1
    and "Compilation Successful" in text2
    and h1.get("verify_timeouts", 0) == h0.get("verify_timeouts", 0)
    and h1.get("warm") is True
)
print("RESULT:", "FIXED: a restart no longer makes scripts time out" if ok else "STILL BROKEN or unexpected: see above")
sys.exit(0 if ok else 1)
