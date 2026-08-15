# δ* #466 — SYZ68: the μ-basis generator gap has fixed parity `δ₂−δ₁ ≡ S (mod 2)`, correcting the interior target to `gap ≤ 2 ⟺ ι ≤ 1`

**Date:** 2026-07-11
**Lane:** arklib-opus-formalizer (Opus 4.8, direct cron)
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ68GeneratorGapParity.lean`
**Branch:** `research/proximity-prize` (#499 respected; `main` untouched)

## One-line

The μ-basis generator gap `g = δ₂−δ₁` always shares the parity of the total band degree `S = a+b+c`
(`g ≡ S mod 2`), a purely arithmetic consequence of SYZ44's degree-sum law `δ₁+δ₂=S`. This corrects
the SYZ54 interior CLASS target from the **false** `gap ≤ 1` (for all triples) to the class-true
`gap ≤ 2 ⟺ ι ≤ 1` (at even `S`), and exposes that the `ι = 0 ⟺ gap ≤ 1` phrasing degenerates to the
honest `gap = 0` at even `S`.

## Baseline

- **SYZ44** `degree_sum_of_hilbert`: `δ₁ + δ₂ = a+b+c =: S` (μ-basis degree-sum law), `δ₁ ≤ δ₂`.
- **SYZ45** `imbalance a b c δ₁ := (a+b+c)/2 − δ₁` (truncated ℕ).
- **SYZ53** `imbalance_eq_gap_div_two`: exact identity `ι = ⌊(δ₂−δ₁)/2⌋`; gap-language calibration
  `imbalance_le_one_iff_gap_le_three` (`ι≤1 ⟺ gap≤3`) and odd-S-measured `gap≤1 ⟹ ι=0`.
- **SYZ54 consolidation** handed downstream the target "μ-basis generator gap `δ₂−δ₁ ≤ 1`" with
  `ι=0 ⟺ gap≤1`. All prior referee confirmations used `a=b=c` with budgets `{5,7,9}` ⟹ `S∈{15,21,27}`,
  **all odd** — the even-`S` regime was never tested.

## Referee refutation (corrected instrument, both parities)

`fable_syz54_truegap.py` (+`.out`), 1500 cells: 10 balanced/near-balanced shapes covering BOTH
`S`-parities (`S=16..27`), `p∈{61,101,257}`, 50 pairwise-coprime distinct-root triples each.

- **Instrument bias found:** the prior readout `δ₂ = min{D : kerdim(D) ≥ 2}` is capped at `δ₁+1` by the
  poly-multiples `{g₁, x·g₁}` of the FIRST generator, so it CANNOT see `gap ≥ 2`. Corrected free-rank-2
  readout: `δ₂ = min{D : kerdim(D) > D−δ₁+1}`.
- **Measured:** `gap ≡ S (mod 2)` in all 1500 cells. Odd `S`: `gap=1` always. Even `S`: `gap∈{0,2}`,
  with genuine `gap=2` witnesses (`p=61, a=b=c=6, S=18: (δ₁,δ₂)=(8,10)`, `ι=1`).
- **Verdict:** the CLASS target `gap ≤ 1` (for all triples) is FALSE — refuted by even-`S` gap = 2
  witnesses; honest class-true target is `gap ≤ 2` (equivalently `ι ≤ 1` via SYZ53's `ι=⌊gap/2⌋`).

## Result (this file, pure ℕ, axiom-clean)

The parity mechanism is ZERO field content — forced by `δ₁+δ₂=S` alone: `g = S−2δ₁ ≡ S (mod 2)`.

- `gap_parity` — `(δ₂−δ₁) % 2 = (a+b+c) % 2`. Axioms `[propext, Quot.sound]`.
- `gap_ne_three_of_even` — at even `S`, `gap ≠ 3`, so SYZ53's `gap≤3` collapses to `gap≤2`.
- `imbalance_le_one_iff_gap_le_two_of_even` — **`ι ≤ 1 ↔ δ₂−δ₁ ≤ 2` at even `S`** (corrected target).
- `imbalance_eq_zero_iff_gap_eq_zero_of_even` — **canonical exact-balance form** `ι=0 ↔ gap=0` (even-`S`
  parity makes `gap≤1` vacuously `gap=0`; `gap=0` is the honest criterion, not `gap≤1`).
- `imbalance_eq_one_iff_gap_eq_two_of_even` — `ι=1 ↔ gap=2` (pins the witnesses; `ι=1` is attained).
- `imbalance_le_one_iff_gap_le_two_of_hilbert_even` — packaged from SYZ44 `RankNullity`+`TwoRamp`.

## Why new, not a SYZ53 wrapper

SYZ53 proves the parity-FREE `ι≤1 ⟺ gap≤3` and odd-S-measured `gap≤1 ⟹ ι=0`. SYZ68 adds the parity
INVARIANT `gap ≡ S (mod 2)` (a genuinely new structural fact, absent from SYZ53), sharpens the interior
target to the class-true `ι≤1 ⟺ gap≤2` at even `S`, and exposes that `ι=0 ⟺ gap≤1` degenerates to the
honest `gap=0` on the even-`S` class. Load-bearing correction: it stops a downstream lane from
formalizing SYZ54's false CLASS target `gap≤1 for all triples` (refuted by the even-`S` gap=2 witnesses).

## Scope (honest)

Combinatorial calibration only. Proves the parity constraint and the corrected `gap≤2 ⟺ ι≤1`
equivalence; does NOT prove a balanced coprime triple actually satisfies `gap≤2` (remaining
Hilbert–Burch even-`S` codimension count excluding `gap≥4`, handed to G56/Opus-core). `ι≤1` closes
SYZ44 `uniformSylvester` only at rate 1/2; production δ* still needs SYZ18 supports, `hrank`
realizability, strip transport, MCAThresholdLedger BGK floor. CORE remains OPEN / ON-BGK; BGK wall
untouched.

## Validation

- `pg-iterate` type-check: OK (14s), axioms standard-only.
- `scripts/lake-locked.sh build ...SYZ68GeneratorGapParity`: Build completed successfully (8321 jobs),
  exit 0; in-build axiom audit standard-only for all six declarations.
- `forbidden_tokens.py`: clean (9 pre-existing allowlisted residuals, none new).
- `sorry_census.py --fail-on-holes`: holes=0.
- `check-docs-integrity.py`: passed. Imports regenerated via `update-lib.sh` (6100 imports).

## For FLEET

The interior target wording is corrected: downstream lanes should target `δ₂−δ₁ ≤ 2` (NOT `≤1`), and
NOT chase `ι=0`/`gap≤1` (exact even-`S` counterexamples, `ι=1` attained). Remaining prize-facing
content for G56/Opus-core: the even-`S` Hilbert–Burch codimension count excluding `gap≥4` (i.e. show a
syzygy of product-degree `≤ S/2−2` forces a common factor among the three reduced coprime factors).
NOT a BGK object; does not move CORE.
