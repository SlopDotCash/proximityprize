# Retention mapping: G75 centered anomaly — 2026-09-06

The complete default replay of `scripts/probes/probe_466_g75_relation_anomaly.py`
passed as an executable. It reports both passing and failing numerical inequalities;
exit zero does not mean every inequality holds. The source is unchanged and retained.
This maps 36 of the original 92 unreferenced artifacts, with 56 remaining.
The adjacent JSON records the source hash, complete stdout and integer cross-checks.

The default cells are (n,p)=(32,1048609),(64,264961),(64,355009),(64,4017089).
Each samples depths 2,3,4,5,6,8,10,12,16,20,24,32,40. The first two cells pass
at every sampled depth. The third fails through depth 20 and passes at 24,32,40;
the fourth fails through 24 and passes at 32,40. These are floating FFT results,
not interval-certified bounds. The optional `--beta4` cell was not replayed.

The shadow recurrence uses exact integers. An independent depth-two calculation
counts ordered subgroup pair sums modulo p. Writing E2 for the sum of squared
pair-sum counts, character orthogonality gives S2=p*E2-n^4, and B2=3*n^2-3*n.
With A2=S2-(p-1)*B2 and K2=p*(3*n^2)-(p-1)*B2, the integer results are:

| n | p | E2 | A2 | K2 | A2 <= K2 |
| --- | --- | --- | --- | --- | --- |
| 32 | 1048609 | 2976 | -1045600 | 100669440 | yes |
| 64 | 264961 | 12096 | -16765120 | 50884608 | yes |
| 64 | 355009 | 15168 | 1073822528 | 68173824 | no |
| 64 | 4017089 | 13632 | 6153483584 | 771293184 | no |

Reproduce the integer check from the repository root with NumPy and SymPy installed:

```python
import importlib.util
from collections import Counter
spec = importlib.util.spec_from_file_location(
    "g75", "scripts/probes/probe_466_g75_relation_anomaly.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
for n, p in [(32,1048609),(64,264961),(64,355009),(64,4017089)]:
    g = m.subgroup(p, n)
    assert len(set(g)) == n and all(pow(x, n, p) == 1 for x in g)
    counts = Counter((a+b) % p for a in g for b in g)
    e = sum(c*c for c in counts.values())
    b = m.shadow_table(n, 2)[2]
    assert b == 3*n*n - 3*n
    a = p*e - n**4 - (p-1)*b
    k = p*(3*n*n) - (p-1)*b
    print(n, p, e, a, k, a <= k)
```

The check supports the depth-two finite examples without relying on FFT rounding.
It is not a Lean certificate, does not verify all hypotheses of any production
theorem, and establishes neither a general centered bound nor issue #164.
