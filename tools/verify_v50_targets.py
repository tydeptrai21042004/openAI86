#!/usr/bin/env python3
"""Fail-closed Lean kernel verification for V50 stage-projection targets."""
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
lean = shutil.which("lean")
lake = shutil.which("lake")
if not lean or not lake:
    print("BLOCKED: Lean/Lake executable unavailable; no kernel certificate issued.")
    sys.exit(2)

# Build the exact imported library. A successful source audit is not a substitute.
cmd = [lake, "build", "OpenAI086"]
print("RUN:", " ".join(cmd))
proc = subprocess.run(cmd, cwd=root)
if proc.returncode:
    print("FAIL: Lake kernel build failed; inspect the Lean diagnostics above.")
    sys.exit(proc.returncode)
print("PASS: OpenAI086 compiled with the pinned Lean toolchain.")
print("NOTE: Review #print axioms for the V50 declarations before promotion.")
