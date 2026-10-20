#!/usr/bin/env python3
"""The fake file worker: a process whose command line says `--worker`, that never
reads stdin and so never acts on an `exit` notification. It stands for a Lean
worker busy in a kernel reduction, which only a signal ends."""
import time

while True:
    time.sleep(1)
