#!/usr/bin/env python3
"""Exercise fail-closed reporting for main-theorem bridge audit."""
from pathlib import Path
import subprocess, json, sys
root=Path(__file__).resolve().parents[1]
p=subprocess.run([sys.executable,'tools/audit_theorem_bridge.py'],cwd=root,capture_output=True,text=True)
assert p.returncode == 0, p.stdout+'\n'+p.stderr
report=json.loads(p.stdout)
assert report['all_checks_pass'] is True
assert report['kernel_checked_here'] is False
assert report['main_goal_proved'] is False
assert all(report['checks'].values())
assert len(report['checks'])>=12
print(f'PASS: {len(report["checks"])} theorem-bridge statement and fail-closed status checks')
