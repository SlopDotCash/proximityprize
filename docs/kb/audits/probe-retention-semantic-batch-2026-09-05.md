# Retention claim-mapping batch — 2026-09-05

Input inventory: `python3 scripts/kb/audit_probe_retention.py` at the source head below. All six scripts and three
stored outputs were among the 92 artifacts without direct filename
references. Examined source at proximityprize cleanup head
`58cc1f0e6f3645e2e78e9e4b15c16729dcd17753`.

Each script was inspected before execution: standard-library integer/rational
arithmetic and no network access. The k=2 crosscheck writes one relative output
file, confined to the temporary directory; the other scripts do not write files. It ran via `python3 ABSOLUTE_SCRIPT`
in an isolated temporary working directory with a 45-second timeout. All exited
zero with empty stderr. Raw output, SHA-256 and durations are recorded in
[raw execution record](probe-retention-semantic-batch-2026-09-05.json). Artifacts remain retained.

| Artifact | Documented claim | Reproduced result | Limit |
| --- | --- | --- | --- |
| `_nubs_research/verify_f101_quadric.py` | `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md:8971–8982` gives the displayed Q and 196 admissible F101 points | Enumerated all 101² scalar pairs: 198 raw zeros, 196 distinct normalized/nondegenerate pairs; Q(2,33)=0 and witness present | Verifies this finite polynomial census only, not the narrative's stronger end-to-end four-codeword/no-joint-explanation claim. `_nubs_research/F101Band3BoundaryWitness.lean` was inspected but not compiled in this batch. |
| `scripts/probes/probe_bgk_primitive_depth7_counterexample.py` | `docs/kb/deltastar-466-bgk-moment-tower-and-production-welds-2026-07-10.md:335–340` and `docs/kb/deltastar-466-ten-by-ten-centered-attack-matrix-2026-07-11.md:66` report 48 nonzero primitive depth-seven disjoint pairs at n16,p337 | Exhaustive seven-subset enumeration: 0 ordered pairs for p97 and193, 48 for p337; same witness and full output as retained `_out_bgk_primitive_depth7_counterexample.txt` | Finite counterexample to proper-lower-depth recursion, not a production-scale positive bound. Script explicitly counts ordered pairs. |
| `scripts/probes/probe_bgk_h8_transition_integrality.py` | Module docstring defines normalized subset deviations and the proposed integer transition property for H8⊂F17 | Exact Fraction arithmetic and internal assertions reproduce transitions 32/21,22/7,1792/275,275/28,224/11,42; five of six nonintegral | Self-documented finite arithmetic claim; no separate narrative claim mapping found in the bounded search. No claim about production subgroup divisibility. |

For the depth-seven witness the left exponents are `[0,4,5,6,10,11,15]`, the right
exponents `[1,3,7,8,9,12,14]`. The script checks disjointness, equality of modular
sums, absence of a nonempty proper equal-cardinality/equal-sum subpair, and a
nonzero cyclotomic lift before counting a pair.

This batch establishes semantic retention reasons and verified reproduction for
these finite claims. It does not map all 92 artifacts, certify all narrative
conclusions, or justify deletion of the remaining evidence.

## Replay commands

Run from the repository root. The temporary directory keeps the k=2 output separate from the checkout.

```sh
probe_repo="$(pwd)"
probe_run="$(mktemp -d)"
mkdir -p "$probe_run/scripts/probes"
(cd "$probe_run" && python3 "$probe_repo/_nubs_research/verify_f101_quadric.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_bgk_h8_transition_integrality.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_bgk_primitive_depth7_counterexample.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_bgk_sampling_without_replacement_budget.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/probe_k2_interior_ceiling_prize_scale_crosscheck.py")
(cd "$probe_run" && python3 "$probe_repo/scripts/probes/verify_g139_phi_collision_witness.py" \
  --witness-json "$probe_repo/scripts/probes/_out_g139_phi_collision_witnesses.json")
```

## Exact source fingerprints

These fingerprints identify the code that produced the recorded results. Later
changes require a new review and replay, not reuse of the earlier outcome.

| Script | SHA-256 |
| --- | --- |
| `_nubs_research/verify_f101_quadric.py` | `4d99111b1408c028009cc2cf1ac3b2a7df1c59097561132e7959097325caa3bd` |
| `scripts/probes/probe_bgk_h8_transition_integrality.py` | `45b9dbef10042d39718d226a2255f1cda8befdd357fa57cc5a876a34a8ae5af2` |
| `scripts/probes/probe_bgk_primitive_depth7_counterexample.py` | `885043d69213916ae26a75019f2de5cc99e64948d35c9852c513c1cba6ffbd9e` |
| `scripts/probes/probe_bgk_sampling_without_replacement_budget.py` | `3af216a85741db11c5ded77a682c15c9f95aa6fd569872fbf153f77c157d24dd` |
| `scripts/probes/probe_k2_interior_ceiling_prize_scale_crosscheck.py` | `172b23d168cb88f4d04f1f23e8e94812ed0a726e8d7b6f4bc14ac5c95ec3b246` |
| `scripts/probes/verify_g139_phi_collision_witness.py` | `972464bce346d7b5902616848b5487a31b2853e3c8717bb6b51daebd928cc8a5` |

## Additional mapped claims

- `scripts/probes/probe_bgk_sampling_without_replacement_budget.py` maps to
  `docs/kb/deltastar-466-bgk-moment-tower-and-production-welds-2026-07-10.md:328–329`.
  Exact integer arithmetic at `n=2^30`, depth 7, coefficient 126871 reproduces the
  period ceiling 85047155, Paley comparison 46341, and more than 141 energy bits of
  loss. Its stdout exactly matches `_out_bgk_sampling_without_replacement_budget.txt`.
  This evaluates the consequences of a **hypothetical** pointwise bound; it does
  not establish that bound or measure actual production subgroup cancellation.
- `scripts/probes/probe_k2_interior_ceiling_prize_scale_crosscheck.py` checks its
  module-documented extension of the k=2 census to `p=21*2^128+1`. Its Proth and
  order-eight assertions pass; among the 64 monomial pencils, the ceiling example
  has 40 bad scalars and the below-ceiling maximum is 9 at `(a,b)=(4,3)`.
  `docs/kb/deltastar-sweep-A07-k2-interior-2026-06-14.md:59–75` records the same
  counts at three smaller primes. The new replay checks only this additional
  prime and monomial family. Despite the script's broad concluding sentence,
  finitely many examples do **not** prove field independence or a universal pin.
- `scripts/probes/verify_g139_phi_collision_witness.py` checks the explicit
  identities in its module docstring against the six retained input rows in
  `_out_g139_phi_collision_witnesses.json`. All six checks pass and the resulting
  JSON equals `_out_g139_phi_collision_witness_verification.json` structurally.
  Three rows use `(n,p)=(64,17318209)` and three use `(512,138027521)`; none uses
  the production subgroup order `2^30`. The verifier assumes primality. This
  batch separately confirmed both small moduli by trial division through their
  integer square roots; no primality claim is inferred from the verifier's exit.

The witness-input SHA-256 is
`a168156db3bc5815064a6d687ca4e90845e99dd98a9cfdfcd111ea7f927f89ee`.

The separate small-modulus primality check is reproducible with:

```sh
python3 - <<'PY'
from math import isqrt
for p in (17318209, 138027521):
    assert all(p % d for d in range(2, isqrt(p) + 1))
    print(p, "prime by exhaustive trial division")
PY
```
