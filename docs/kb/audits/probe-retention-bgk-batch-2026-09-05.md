# Retention claim mapping: BGK polynomial and phase probes — 2026-09-05

This separate batch covers three scripts and their three stored outputs, all
among the original 92 artifacts lacking direct filename references. Together
with the [first batch](probe-retention-semantic-batch-2026-09-05.md), fifteen of
those artifacts now have explicit semantic retention records. Nothing is deleted.

Source snapshot: `74a1641a398ca9cc7be20900f0161619d162d942`. The inspected scripts
use the Python standard library, do not access the network, and do not write files.
All ran in an isolated temporary working directory under Python 3.14.6 with a
45-second timeout. All exited zero, with empty stderr, and their complete stdout
matched the corresponding retained output byte-for-byte on this run.
[Raw outputs, fingerprints, durations, and comparisons](probe-retention-bgk-batch-2026-09-05.json)
are retained separately from the interpretation below.

## Claims and limits

- `probe_bgk_repeated_newton_absorption.py` maps to
  `docs/kb/deltastar-466-bgk-moment-tower-and-production-welds-2026-07-10.md:240–247`.
  Its symbolic dictionary calculation reproduces 15 terms in D7 with coefficient
  L1 mass 5040; the repeated-coordinate polynomial has 88 terms with mass
  25401599 and leading coefficients 42, -651, -140. The coefficient bound below
  138 has an exact Fraction certificate using `(5521/5000)^7 > 2`; the reported
  actual value and derivative use 80-digit Decimal approximations. Those Decimal
  values are numerical evidence, not an interval-certified or kernel-checked
  derivative theorem. The replay does not prove the remaining signed injective
  defect bound or revalidate the Lean theorem claims in the narrative.
- `probe_bgk_johnson_phase_grades.py` maps to the same note at lines 332–333.
  Integral group-ring arithmetic and a Fraction Vandermonde solve reproduce
  Johnson J(14,7) grade masses `[0,1/66,7/6,273/11,637/3,5005/6,3003/2,858]`.
  Lower grades 1–6 have mass 2574 versus 858 in grade 7; grade 6 contains 7/16 of
  the total. The seven initial phase power sums vanish. This is an exact finite
  phase-vector calculation, not a production subgroup estimate.
- `probe_bgk_injective_exterior_cluster.py` implements its module docstring's
  clustered-phase example. For n64 and p65537,1000003,1000000007 the normalized
  transform magnitudes reproduce approximately 0.999990067476509,
  0.999999957338892, and 0.999999999999958. The program uses complex floating
  arithmetic, checks a dynamic program against brute force on n10, and checks
  the cosine lower bound with roundoff tolerance. These values are numerical
  reproduction; the script's analytic argument for a generic-phase obstruction
  is not thereby kernel-verified. The clustered roots are not the adversarial
  multiplicative subgroup required for the prize.

## Replay

Run from the repository root:

```sh
probe_repo="$(pwd)"
probe_run="$(mktemp -d)"
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_bgk_repeated_newton_absorption.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_bgk_johnson_phase_grades.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_bgk_injective_exterior_cluster.py")
```

| Script | SHA-256 | Retained matching output |
| --- | --- | --- |
| `scripts/probes/probe_bgk_repeated_newton_absorption.py` | `e8c49ea7f2d55d122cccf41e5ed331131ecc62d0fd899d8736dced22d1128fbb` | `scripts/probes/_out_bgk_repeated_newton_absorption.txt` |
| `scripts/probes/probe_bgk_johnson_phase_grades.py` | `160845d20d9b96359f078bc5bb64fc8704b10608a8f969d085c69094364ab2f6` | `scripts/probes/_out_bgk_johnson_phase_grades.txt` |
| `scripts/probes/probe_bgk_injective_exterior_cluster.py` | `cb38ca2a4125c59ac42d0a16626f7c309d1439d6cb697f684164edc8c79ecc47` | `scripts/probes/_out_bgk_injective_exterior_cluster.txt` |
