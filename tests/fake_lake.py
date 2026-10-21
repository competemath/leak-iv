#!/usr/bin/env python3
"""A stand-in for `lake serve`, for the tests: the Lean language-server protocol
over stdio, with the behaviours the daemon has to cope with, chosen by markers in
the script text it is given.

  (plain)        diagnostics: none            -> "Compilation Successful"
  FAKE_SORRY     a severity-2 warning          -> failure (a hole)
  FAKE_ERROR     a severity-1 error            -> failure
  FAKE_HINT      a severity-3 "Try this: ..."  -> success with a suggestion
  FAKE_REPUDIATED  the statement-form gate's error   -> failure
  FAKE_ROGUE     the axiom-closure gate's error   -> failure
  FAKE_STUCK     no answer, ever: a worker busy in the kernel. The fake also runs
                 a child process named `lean --worker` that ignores `exit`, so the
                 daemon's kill path is exercised; the child's pid is written to
                 $FAKE_LAKE_WORKER_PID_FILE.
  FAKE_CRASH     "Aborting." on stderr, then the watchdog's -32902 error

Cold start: with $FAKE_COLD_S=N a worker that has just been opened takes N seconds to answer its first request (loading the
tree), and, like the real worker, a new document version (didChange) while it is still loading RESTARTS that load. A request
whose version has been superseded is never answered. After the first answer the worker is warm and answers at once.

What it received is appended to $FAKE_LAKE_LOG as JSON lines (method, text),
so a test can check what was compiled (for example that `import Mathlib` became
the tree's import).
"""
import json
import os
import subprocess
import sys
import threading
import time

LOG = os.environ.get("FAKE_LAKE_LOG")
PID_FILE = os.environ.get("FAKE_LAKE_WORKER_PID_FILE")
HERE = os.path.dirname(os.path.abspath(__file__))

COLD_S = float(os.environ.get("FAKE_COLD_S", "0"))
state = {"text": "", "version": 0, "open": False, "stuck": False, "worker": None, "cold": False, "ready_at": 0.0}
out_lock = threading.Lock()


def log(method, **kw):
    if not LOG:
        return
    with open(LOG, "a") as f:
        f.write(json.dumps({"method": method, **kw}) + "\n")


def send(msg):
    body = json.dumps(msg).encode()
    with out_lock:
        sys.stdout.buffer.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
        sys.stdout.buffer.flush()


def read():
    length = 0
    while True:
        line = sys.stdin.buffer.readline()
        if not line:
            return None
        line = line.decode().strip()
        if not line and length:
            break
        if line.lower().startswith("content-length:"):
            length = int(line.split(":")[1])
    return json.loads(sys.stdin.buffer.read(length))


def start_worker():
    # a worker that does not act on `exit` (it never reads stdin): only SIGKILL ends it
    p = subprocess.Popen([sys.executable, os.path.join(HERE, "fake_worker.py"), "--worker", "sleep"], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    state["worker"] = p
    if PID_FILE:
        with open(PID_FILE, "a") as f:
            f.write(f"{p.pid}\n")


def diag(sev, msg, line=0):
    return {"range": {"start": {"line": line, "character": 0}, "end": {"line": line, "character": 1}}, "severity": sev, "message": msg}


def answer(msg_id, uri, version, text):
    if "FAKE_STUCK" in text:
        state["stuck"] = True
        log("stuck", version=version)
        return  # never answers: the worker is in the kernel
    if "FAKE_CRASH" in text:
        sys.stderr.write("INTERNAL PANIC: stack overflow\nAborting.\n")
        sys.stderr.flush()
        send({"jsonrpc": "2.0", "id": msg_id, "error": {"code": -32902, "message": "The file worker has crashed"}})
        return
    diags = []
    if "FAKE_SORRY" in text:
        diags.append(diag(2, "declaration uses 'sorry'", 1))
    if "FAKE_ERROR" in text:
        diags.append(diag(1, "unsolved goals\n⊢ False", 2))
    if "FAKE_REPUDIATED" in text:
        diags.append(diag(1, "statement form repudiated: t states an answer slot, a bare True, False or sorry as one side of an iff", 4))
    if "FAKE_ROGUE" in text:
        diags.append(diag(1, "rogue axiom(s) introduced by this script (outside the standard trust set): [cheat]", 5))
    if "FAKE_HINT" in text:
        diags.append(diag(3, "Try this: exact Nat.add_zero n", 3))
    send({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics", "params": {"uri": uri, "version": version, "diagnostics": diags}})
    send({"jsonrpc": "2.0", "id": msg_id, "result": None})


def answer_when_ready(msg_id, uri, version):
    while True:
        if state["version"] != version or not state["open"]:
            return  # superseded (a later didChange) or closed: this request is never answered
        if time.time() >= state["ready_at"] or not state["cold"]:
            break
        time.sleep(0.05)
    state["cold"] = False
    answer(msg_id, uri, version, state["text"])


def main():
    while True:
        msg = read()
        if msg is None:
            return
        method = msg.get("method")
        params = msg.get("params") or {}
        if method == "initialize":
            send({"jsonrpc": "2.0", "id": msg["id"], "result": {"capabilities": {}}})
        elif method == "textDocument/didOpen":
            state.update(text=params["textDocument"]["text"], version=params["textDocument"]["version"], open=True, stuck=False, cold=COLD_S > 0, ready_at=time.time() + COLD_S)
            start_worker()
            log(method, text=state["text"], version=state["version"])
        elif method == "textDocument/didChange":
            state.update(text=params["contentChanges"][0]["text"], version=params["textDocument"]["version"])
            if state["cold"]:
                state["ready_at"] = time.time() + COLD_S  # a new version while loading restarts the load
            log(method, text=state["text"], version=state["version"])
        elif method == "textDocument/didClose":
            # like the real watchdog: the worker is told to exit (ours ignores it) and the document is gone
            state.update(open=False, stuck=False, cold=False)
            log(method)
        elif method == "textDocument/waitForDiagnostics":
            log(method, version=params.get("version"))
            if state["stuck"] or not state["open"]:
                # a stuck worker answers nothing, for this version or any later one, until it is replaced
                continue
            threading.Thread(target=answer_when_ready, args=(msg["id"], params["uri"], params.get("version")), daemon=True).start()
        elif method == "shutdown":
            send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
        elif method == "exit":
            return


if __name__ == "__main__":
    main()
