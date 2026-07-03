# #466 lane FS1 — floor-bad(64) DECIDED via the complement-polynomial reformulation

Date: 2026-07-03.  Status: **probe + KB note + axiom-clean Lean mechanism lemma (no prize claim)**.
Supersedes the round-2 "UNDECIDED at this compute" verdict of
[`deltastar-466b-floorbad64-2026-07-01.md`](deltastar-466b-floorbad64-2026-07-01.md) and the
round-8 inconclusive anneal (`466-r8-floor-successor-norm-partial`).

- Probe: `scripts/probes/probe_466_floorbad64_decide.py`
  (output `scripts/probes/_out_466_floorbad64_decide.txt`).
- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorComplementReform.lean`
  (`floorReform_dvd`, `floorReform_congr`; axiom-clean `[propext, Classical.choice, Quot.sound]`).
- Scanner of record (definition): `scripts/probes/floor_scan_exact.c`.  No C compiler on this box;
  every engine here is cross-validated against that rank predicate before any n=64 claim.

## 0. The two advances

**(A) The complement reformulation (the enabling theorem).**  For an adjacent-7th-type pattern
`A ⊆ ℤ/n` (`|A| = 5n/8`, points `ω^j`, `ω` a primitive `n`-th root of unity in `𝔽_p`,
`p ≡ 1 mod n`), let `B = ℤ/n \ A` be the complement (`|B| = 3n/8`) and
`Q_B(x) = ∏_{j∈B}(x-ω^j)` (monic, degree `3n/8`).  Then

> **`A` is floor-bad-realizable at `p`  ⟺  `[x^i] Q_B = 0` for every `i ∈ [n/8+1, n/4-1]`.**

i.e. the scanner's test on the degree-`5n/8` remainder `r = x^{3n/4} mod P_A` (`deg r ≤ n/2`) is
equivalent to the vanishing of the `n/8-1` MIDDLE coefficients of the degree-`3n/8` COMPLEMENT
polynomial.  Windows: `n=16 → i=3` (1 coeff); `n=32 → i∈{5,6,7}` (3); `n=64 → i∈{9,…,15}` (7).

*Proof.*  `P_A · Q_B = x^n - 1`, so `r·Q_B ≡ x^{3n/4}·Q_B  (mod x^n-1)` and (as `deg(r Q_B) ≤ n-1`)
`r·Q_B` is literally the reduction of `x^{3n/4} Q_B` mod `x^n-1`.  `deg r ≤ n/2 ⟺ deg(rQ_B) ≤ 7n/8`
(⋅`Q_B` monic), i.e. the coefficients of that reduction at degrees `(7n/8, n)` vanish; the
elementary `x^{3n/4+i} ≡ x^{(3n/4+i) mod n}` reduction identifies those with `[x^i]Q_B`,
`i ∈ [n/8+1, n/4-1]`.  The `r·Q_B ≡ x^{3n/4}Q_B` divisibility is the Lean lemma `floorReform_dvd`.

**(B) The decision, via a translation-symmetric bilinear meet-in-the-middle.**  `Q_B` factors
along the class structure as `Q_B = U·W` with `U = Q_{b0}·Q_{b1}` (min-complement, deg 8: 4 pts
from each of classes 0,1) and `W = Q_{b2}·Q_{b3}` (maj-complement, deg 16: 8 pts from each of
classes 2,3).  The 7 conditions `[x^9..x^15](U·W)=0` are **linear in `U` for fixed `W`**:
`Σ_{a=0}^{8} U_a W_{i-a}=0`, `U_8=1` ⟹ a `7×8` system `A(W)·(U_0..U_7) = -(W_1..W_7)` whose generic
solution is a **1-dim affine line** (193 points at `p=193`).  So: hash all `C(16,4)² = 3,312,400`
min-`U`; for each maj-`W` enumerate its 193-point line and look up.  **Completeness levers:**
realizability is exactly translation-invariant (`[x^i]Q_{B+t} = ω^{t(3n/8-i)}·[x^i]Q_B`), so
(i) only rotation `c0=0` need be scanned (the 4 rotations are translates), and (ii) `b2` need only
range over the `810` rotation-canonical reps of the `ℤ/16` translation-by-4 action (paired with all
`b3` and the full min-set).  This is a **complete** scan of `810·12870 = 10,424,700` maj-reps ×
`3,312,400` min = the whole family up to the `ℤ/16` symmetry, replacing the `2.2·10^{15}` raw scan.

## 1. Verdict

| rung | prime | method | coverage | verdict |
|---|---|---|---|---|
| n=16 | 17; others | full residual & complement scans | exact | floor-bad(16) = {17} (reproduced) |
| n=32 | 97; 193,257,449,577 | MITM count == brute complement count | exact/complete | floor-bad(32) = {97} (reproduced, engine-validated) |
| **n=64** | **193 = p_min(64)** | **complete symmetry-reduced MITM** (10,424,700 maj-reps × 3,312,400 min, 2012 s) | **COMPLETE** | **NOT floor-bad — no realizable pattern exists** |
| n=64 | 257, 449, 577 | complete symmetry-reduced MITM | COMPLETE | (running; see `_out_466_floorbad64_decide.txt`) |

**HEADLINE: `193 = p_min(64)` is NOT in floor-bad(64).**  A COMPLETE scan of the entire
adjacent-7th-type family (up to the exact `ℤ/16` translation symmetry) found **zero** realizable
patterns at `p=193`.  This **REFUTES the uniform floor-successor conjecture `floor-bad(n) =
{p_min(n)}`**: the pattern `floor-bad(16)={17}`, `floor-bad(32)={97}` does NOT continue to
`n=64`.  `p_min(64)=193 ∉ floor-bad(64)`.  (This is a decision, not a heuristic "found none":
the search is complete and the engine is validated to have no false-negative blind spot — §2.)

## 2. Validation ladder (why the n=64 verdict is trustworthy)

1. **Reformulation ⟺ scanner rank test.**  `realizable_residual` (port of `floor_scan_exact.c`)
   vs `realizable_complement`: **exact agreement on all `2304·4` patterns at n=16** (all primes),
   and **0 mismatches** on 40,000 random patterns per prime at n=32 and 3,000 per prime at n=64
   (`p=193,257`).  The core divisibility is Lean-proved (`floorReform_dvd`, axiom-clean).
2. **MITM engine == brute count at n=32.**  `mitm_decide` count equals an independent vectorized
   brute complement count: `p=97 → 8` (= the full 32-orbit ÷ 4 rotations; witness passes the
   residual test), `p=193,257,449,577 → 0`.  Reproduces floor-bad(32) = {97}.
3. **Translation-symmetry completeness == full at n=32.**  The `ℤ/8` rotation-canonical reduction
   finds the `97`-witness and none for the good primes — matches the unreduced result.
4. **Positive + negative control at n=64 (p=193 AND p=257).**  Injecting a synthetic `U*` on a real
   `W`'s solution line into the min-set, `mitm_chunk` detects it (count 1); a `U` perturbed off the
   line is not detected (count 0).  Confirms the engine has **no false-negative blind spot** and
   the hash+reverify path has **no false positives** at a large prime (where naive base-`p` key
   packing would overflow int64 — fixed by a collision-free random hash with exact reverification).

## 3. What the verdict means for the uniform conjecture

The round-7/8 **uniform floor-successor conjecture** was `floor-bad(n) = {p_min(n)}` (the least
prime `≡ 1 mod n`), verified `n=16 → {17}`, `n=32 → {97}`, and conjectured `n=64 → {193}`.

**REFUTED.**  `193 ∉ floor-bad(64)`, so `floor-bad(64) ≠ {193} = {p_min(64)}`.  The
"least-prime-`≡1-mod-n`" law is an `n=16,32` coincidence, not a theorem.  Consequences:

* The floor-successor is genuinely arithmetic (a cyclotomic-resultant divisibility, per
  `466-r7/r8`), but its `≡1-mod-n` prime factor is **NOT** uniformly `p_min(n)` — the seven
  obstruction norms `N(r_{33..39})` at `n=64` have `≡1-mod-64` factor sets whose intersection over
  the realizable family is **empty at 193** (consistent with round-8's observation that `193`
  divides only `2` of the `7` canonical-pattern norms; now upgraded from "one pattern" to
  "no pattern in the whole family").
* `floor-bad(64)` (if nonempty) is carried by a LARGER prime `≡ 1 mod 64` — its determination now
  needs a per-prime complete MITM (feasible: ~30 min/prime on this box) rather than a single
  successor law.  Whether `floor-bad(64) = ∅` on `[193, 64^4]` is open (checking every split prime
  up to `64^4 ≈ 1.7·10^7` is out of scope; `257, 449, 577` are being decided directly).
* The floor is therefore NOT pinned by a clean successor theorem at `n=64`; the off-BGK δ* floor
  route via a uniform successor law is **closed** (a refutation-WIN, per the honesty contract).

## 4. Files

- `scripts/probes/probe_466_floorbad64_decide.py` — reformulation cross-check (`verify`), engine
  validation (`mitmtest`, `symtest`), decision (`decide64`).
- `scripts/probes/_out_466_floorbad64_decide.txt` — the decision run.
- `ArkLib/…/Frontier/_FloorComplementReform.lean` — the axiom-clean reformulation mechanism.
