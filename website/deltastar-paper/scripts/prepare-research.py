"""Read the canonical certificate registry without importing its search dependencies."""
import ast
import json
import math
import subprocess
from pathlib import Path

site = Path(__file__).resolve().parents[1]
root = site.parents[1]
registry = root / "scripts/probes/hdd_certificates.py"
values = {}
for stmt in ast.parse(registry.read_text()).body:
    if isinstance(stmt, ast.Assign):
        for target in stmt.targets:
            if isinstance(target, ast.Name) and target.id in {"NEXP", "RECORDS", "RECORDS_LOOSE"}:
                values[target.id] = ast.literal_eval(stmt.value)
n = 1 << values["NEXP"]
if n != 262144:
    raise SystemExit("Update the page's code-length description before publishing this registry.")
best = {}
for record in values["RECORDS"] + values["RECORDS_LOOSE"]:
    rate, d, m, smax, jcap, agreement, *_ = record
    if rate not in best or agreement < best[rate][5]:
        best[rate] = record
if set(best) != {2, 4, 8, 16}:
    raise SystemExit("Review the page for the new certificate rates.")
sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
rows = [{"rate": rate, "johnson": f"{1-math.sqrt(1/rate):.5f}",
         "radius": f"{1-record[5]/n:.5f}", "agreement": record[5],
         "derivativeOrder": record[1], "multiplicity": record[2]}
        for rate, record in sorted(best.items())]
(site / "data").mkdir(exist_ok=True)
(site / "data/research.json").write_text(json.dumps({"sourceCommit": sha, "records": rows}, indent=2) + "\n")
print(f"Prepared {len(rows)} certificate rows from {sha[:12]}")
