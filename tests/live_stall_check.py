#!/usr/bin/env python3
"""By hand, against a running Leak IV (not in CI): does one script past the cap
still stall everyone else?

    python3 tests/live_stall_check.py https://barkingtree-leak-iv.hf.space

Client A submits the script that caused the 2026-10-20 outage (a kernel
evaluation on a five-digit witness). Client B, on its own connection, submits a
trivial `example` right after. Before the fix B waited for A's kernel reduction
to finish (25 minutes); with it, A gets "verify exceeded" at the cap and B is
answered within the cap plus a worker respawn. /health is read before and after.
Plain urllib, no dependencies."""
import json
import sys
import threading
import time
import urllib.request

BASE = (sys.argv[1] if len(sys.argv) > 1 else "https://barkingtree-leak-iv.hf.space").rstrip("/")
BIG = ("open Nat in\n"
       "theorem E396_k4_stall_check : (45153 : ℕ).descFactorial 5 ∣ (45153 : ℕ).centralBinom := by\n"
       "  rw [Nat.centralBinom_eq_two_mul_choose]\n  decide +kernel")
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


print("health before:", health())
a, b = Client("A"), Client("B")
out = {}
ta = threading.Thread(target=lambda: out.__setitem__("a", a.verify(1, BIG)))
ta.start()
time.sleep(5)
tb, text_b = b.verify(1, SMALL)
ta.join()
dur_a, text_a = out["a"]
print(f"A (kernel evaluation on 45153): {dur_a:.0f}s -> {text_a[:160]!r}")
print(f"B (trivial, 5 s later):         {tb:.0f}s -> {text_b[:100]!r}")
h = health()
print("health after:", h)
ok = tb < 400 and "Compilation Successful" in text_b and "exceeded" in text_a
print("RESULT:", "FIXED: the trivial script was not stuck behind the stalled one" if ok else "STILL STALLING or unexpected: see above")
sys.exit(0 if ok else 1)
