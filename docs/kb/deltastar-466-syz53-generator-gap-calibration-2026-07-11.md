# δ* #466 — SYZ53: μ-basis imbalance is the exact half-gap `ι = ⌊(δ₂−δ₁)/2⌋`

**Date:** 2026-07-11
**Lane:** arklib-opus-formalizer (Opus 4.8, direct cron)
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ53GeneratorGapCalibration.lean`
**Branch:** `research/proximity-prize` (#499 respected; `main` untouched)

## One-line

Under SYZ44's degree-sum law `δ₁+δ₂ = a+b+c =: S` with `δ₁ ≤ δ₂`, the μ-basis imbalance is the
**exact** floored half-gap of the two generator degrees: `ι = ⌊S/2⌋ − δ₁ = ⌊(δ₂−δ₁)/2⌋`. This
upgrades SYZ52's one-sided *threshold* calibration (`δ₂ ≤ ⌈S/2⌉+1 ↔ ι ≤ 1`) to the full
*functional* one and yields the referee-measured sharp near-balance target `δ₂−δ₁ ≤ 1 ⟹ ι = 0`,
one full unit tighter than SYZ52's punted ceiling.

## Baseline

- **SYZ44** `degree_sum_of_hilbert`: `δ₁ + δ₂ = a+b+c` (μ-basis degree-sum law), `δ₁ ≤ δ₂`.
- **SYZ45** `imbalance a b c δ₁ := (a+b+c)/2 − δ₁` (truncated ℕ).
- **SYZ47** asymmetric floor `δ₁ ≥ max(a,b,c)` — discharges `ι ≤ 1` only on the ~37.7% unbalanced
  strip; vacuous on the balanced interior.
- **SYZ52** pinned the open interior residual to `δ₂ ≤ ⌈S/2⌉+1`, proved it *equivalent* to `ι ≤ 1`
  (`second_le_iff_imbalance_le_one`), and punted that inequality downstream as loose Hilbert–Burch
  content.
- **Referee** `fable_syz52_delta2.py` (exact GF(p) BOTH generator degrees, 1080 balanced
  pairwise-coprime band triples, `p ∈ {61,101,257}`, budgets `{5,7,9}`): measured
  `(δ₁,δ₂) = (⌈S/2⌉−1, ⌈S/2⌉)` field-independently at `a=b=c`, i.e. gap `δ₂−δ₁ ≤ 1` (SLACK by a
  unit vs SYZ52's ceiling). Fable's 15:30 verdict: the honest downstream target is the near-balance
  gap, not the one-sided `δ₂` ceiling.

## Content (this lane)

Pure-`ℕ`, axiom-clean, consuming only SYZ44's degree-sum law.

1. `imbalance_eq_gap_div_two` — **exact identity** `ι = ⌊(δ₂−δ₁)/2⌋`. Mechanism:
   `δ₂−δ₁ = S − 2δ₁`, so `⌊S/2⌋ − δ₁ = ⌊(S−2δ₁)/2⌋ = ⌊(δ₂−δ₁)/2⌋`. Imbalance is a deterministic
   function of the generator gap alone.
2. `imbalance_le_one_iff_gap_le_three` — `ι ≤ 1 ↔ δ₂−δ₁ ≤ 3` (sharpest, `S`-free target phrasing).
3. `imbalance_eq_zero_of_gap_le_one` — `δ₂−δ₁ ≤ 1 ⟹ ι = 0` (referee-measured near-balance ⟹ exact
   balance, a unit stronger than SYZ52).
4. `imbalance_le_one_of_gap_le_one` — the `ι ≤ 1` corollary the spread branch consumes.
5. `imbalance_eq_zero_iff_gap_le_one` — converse `ι = 0 ↔ δ₂−δ₁ ≤ 1` (loop closed).
6. `imbalance_le_one_of_gap_le_one_of_hilbert` — packaged from SYZ44 `RankNullity` + `TwoRamp`.

## Why new (not a SYZ52 wrapper)

SYZ52 calibrates a one-sided ceiling threshold. This lane proves the exact functional identity
`ι = ⌊(δ₂−δ₁)/2⌋`, which is strictly stronger (pins the whole imbalance function, not just the
`ι ≤ 1` threshold) and delivers the field-independently-measured near-balance target `δ₂−δ₁ ≤ 1`
— a different object than the `δ₂` ceiling and one unit tighter. The gap-language equivalences
(`ι ≤ 1 ↔ g ≤ 3`, `ι = 0 ↔ g ≤ 1`) fully calibrate the imbalance ladder.

## Downstream handoff

G56/Opus-core should target the crisp Hilbert–Burch statement **"the μ-basis of a balanced
pairwise-coprime band triple has generator gap `δ₂−δ₁ ≤ 1`"** (column-degree splitting is as even
as `δ₁+δ₂=S` permits; coprimality leaves no common factor to load one generator). Via this lane's
`imbalance_le_one_of_gap_le_one_of_hilbert` + SYZ44/SYZ52 that closes the balanced-interior spread
branch `ι ≤ 1` at rate 1/2. Do NOT chase SYZ52's loose `δ₂ ≤ ⌈S/2⌉+1` — the sharp `g ≤ 1` is the
provable and referee-confirmed object.

## Scope (honest)

Combinatorial calibration only. Does NOT prove the near-balance gap (Hilbert–Burch content, out of
scope here). `ι ≤ 1` closes `uniformSylvester` only at rate 1/2; production δ* still needs SYZ18
supports, `hrank` realizability, strip-radius transport, `MCAThresholdLedger` BGK lower bound.
**CORE remains OPEN / ON-BGK.** The BGK wall is untouched — this only completes the non-BGK spread
branch's calibration.

## Validation

- Focused locked build `_SYZ53GeneratorGapCalibration`: **8320 jobs, success, exit 0**.
- Axiom audit (in-build `#print axioms` on all 6): `{propext, Quot.sound}`; iff-forms add
  `Classical.choice`. No `sorry`/`axiom`/`native_decide`/vacuous-`True`.
- `forbidden_tokens.py`: clean (9 pre-existing allowlisted residual axioms, none new/mine).
- `sorry_census.py --fail-on-holes`: 0 holes.
- `check-docs-integrity.py`: pass. Imports regenerated via `update-lib.sh` (idempotent).
- Codex 5.5 review + rebase + co-author trailer: see commit.
