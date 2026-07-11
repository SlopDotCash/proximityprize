# δ* / #466 — SYZ69: the parity-corrected two-class classification of the μ-basis generator gap (2026-07-11)

**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ69ParityClassification.lean`
**Branch:** `research/proximity-prize` (via `codex/syz69-parity-classification`, off fork tip `6b585d850`)
**Status:** axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`).
**Depends on:** SYZ44 (degree-sum, now unconditional via SYZ61→SYZ65), SYZ45 (imbalance),
SYZ47 (floor, hypothesis), SYZ59 (empty-middle dichotomy + census), SYZ68 (gap parity).

---

## What this consolidates

Four now-unconditional inputs about the μ-basis generator gap `g = δ₂ − δ₁` of a realizable
interior band triple `(W_AB, W_AC, W_BC)` over `μ_n`:

- **degree-sum** (SYZ44/65): `δ₁ + δ₂ = a + b + c =: S`;
- **floor** (SYZ47): `δ₁ ≥ max(a,b,c)`;
- **parity** (SYZ68): `g ≡ S (mod 2)` — zero field content, forced by the degree-sum;
- **empty-middle census** (SYZ55 cofactor / SYZ59 product convention): every *realizable* witness
  sits outside `middleBand := max(a,b,c) < δ₁ ≤ ⌊S/2⌋ − 2`.

SYZ69 assembles them into a single **two-class law** and restates the one open obligation minimally.

## The two-class law (the landable content)

**Conditional on the empty-middle census `¬ middleBand`** (the honest residual input), every
realizable interior band triple is:

- **floor-attained** — `δ₁ = max(a,b,c)`, the **constant-syzygy family**, gap `g = S − 2·max`
  (balanced `a=b=c=d ⇒ g = d`); or
- **near-balance** — `ι ≤ 1` (SYZ45 imbalance), parity-refined per class:
  - even `S`: `g ≤ 2` (SYZ54's `g ≤ 1` was FALSE — even-`S` gap = 2, `ι = 1` witnesses, e.g.
    `p=61, a=b=c=6, (δ₁,δ₂)=(8,10)`);
  - odd `S`: `g ∈ {1,3}` (`g = 3` with `ι = 1` genuinely admitted).

Lean objects:
- `two_class_law` — imbalance form (= `SYZ59.empty_middle_dichotomy`, top-level).
- `two_class_law_gap` / `two_class_law_gap_even` — gap forms (`g = S−2·max ∨ g ≤ 3`; even `S`: `≤ 2`).
- `floor_attained_gap`, `balanced_floor_attained_gap` — the constant-syzygy class gap `= S−2·max`, `= d`.
- `near_balance_gap_le_two_of_even`, `near_balance_gap_odd_admits_three` — the parity-split boundary.
- `classification_of_hilbert` — packaged end-to-end from SYZ44 `RankNullity ∧ TwoRamp`.
- `census_two_class` — finite `decide`: SYZ59 `productCensus` (`d ∈ {3,4,5}`) all floor-attained.

**The two-class law itself is a theorem** given the census input. The uniform class invariant is
`ι ≤ 1`; the crisp *gap* statement is parity-dependent (even-`S` `g ≤ 2` is the sharp correction).

## The minimal restated open exclusion

The OPEN part is the **exclusion of the middle band** (SYZ45: not an algebraic identity, needs band
realizability). SYZ69 restates it minimally, parity built in:

- `middleBand_iff_imbalance_ge_two`: `middleBand ⟺ (max < δ₁ ∧ ι ≥ 2)`.
- `middle_gap_ge_four` + `middle_gap_parity`: middle gaps are exactly
  `{ g : 4 ≤ g ≤ S − 2·max, g ≡ S (mod 2) }` — even `S`: `g ∈ {4,6,…}`; odd `S`: `g ∈ {5,7,…}`.
- `open_exclusion_gap_form`: the two-class law holds *unless* the triple carries a parity-consistent
  gap `≥ 4` strictly above the floor. **That single obligation — "no realizable interior triple has
  `ι ≥ 2` above the floor" — is the entire open geometric content of F1.**

## Consumer audit (verdict: consumers UNCHANGED)

G172 (`_G172RateHalfSyzygyGapSlack.lean`) — the sole landed consumer of the imbalance bound —
consumes **`ι ≤ 1` (imbalance), not a gap-language threshold** (`degree_gap_survives_imbalance`,
`no-go` with `himb_le : imbalance ≤ extraGap`). The identity `ι = ⌊g/2⌋ ⟹ (ι ≤ 1 ⟺ g ≤ 3)` holds in
**all** parities; SYZ68's parity is a *per-class tightening* of the gap picture (`g ≤ 2` at even `S`)
that leaves the invariant `ι ≤ 1` — and therefore every downstream consumer — unchanged. No landed
theorem asserted the refuted `g ≤ 1`; SYZ54's false wording was a target handed downstream, never a
theorem, so nothing regresses. **Verdict: SYZ68/SYZ69 change no landed consumer.**

## Scope honesty

Combinatorial classification only (pure `ℕ` / `decide`). Does NOT prove a realizable triple lands
outside the middle band (open residual). `ι ≤ 1` closes SYZ44 `uniformSylvester` only at rate `1/2`;
production δ* still needs SYZ18 supports, `hrank` realizability, strip-radius transport, and the
MCAThresholdLedger BGK lower bound. **CORE remains OPEN / ON-BGK; the BGK wall is untouched.**

*Entry point: `docs/kb/deltastar-466-one-question-map-2026-07-11.md` §1/§3 (F1, updated).*
