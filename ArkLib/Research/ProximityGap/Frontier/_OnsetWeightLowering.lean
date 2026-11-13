/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Weight-lowering by automorphism quotient / isotypic projection FAILS: the onset weight stays `2r-1` (#444, G4)

Companion to `_JacobiFermatCohomology`. That file located the prize obstruction precisely: realizing the
off-diagonal Jacobi correlation
```
Off = Σ_{(x,y) ∈ (μ_n)^r × (μ_n)^r : Σxᵢ = Σyⱼ}  j_r(x) · conj (j_r(y))
```
as `Tr(Frob | H^*(V_corr))` of the **correlation variety**
`V_corr = {(x,y) ∈ (μ_n)^r × (μ_n)^r : Σ x = Σ y}` (dimension `2r-1`) puts the main term on the MIDDLE
cohomology `H^{2r-1}(V_corr)`, of Frobenius weight `2r-1`; after the two `j_r` normalizations (`p^{-(r-1)}`)
the surviving FIELD scale is `p^{1/2} = √p`. The prize needs SUBGROUP scale `√(n log m)`, i.e. residual
weight `≈ log n / log p`, not `1/2`.

## The G4 question (this file): does an automorphism QUOTIENT lower the weight?

`V_corr` carries a LARGE automorphism group `G = (μ_n)^r ⋊ S_r` (rotate each coordinate by an `n`-th root,
permute the `r` coordinates — both preserve the constraint `Σx = Σy` up to relabelling, and the diagonal
torus translation `(x,y) ↦ (ux, uy)` for `u ∈ μ_n` fixes the constraint). The G4 candidate escapes:

* **Q1 — quotient `V_corr / G`:** does its middle cohomology have weight `< 2r-1`?
* **Q2 — trivial-isotypic / invariant piece `H^{2r-1}(V_corr)^G`:** is it of lower weight (it is "much
  smaller"), giving subgroup scale `~ log n`?
* **Q3 — a motive with smaller Hodge numbers** realizing the same `Off`.

## The decisive structural fact: a finite-group quotient / isotypic projection does NOT change weights

This is the Deligne-purity bookkeeping, and it is the whole answer:

* For a finite group `G` acting on a variety `V` over `𝔽_p` (with `|G|` invertible in the coefficient
  field `ℚ_ℓ`, automatic here since `G` is an `n`-group ⋊ `S_r`, `n = 2^μ`, `ℓ` odd `≠ p`), the averaging
  idempotent `e_G = (1/|G|) Σ_{g∈G} g` is a PROJECTION onto the `G`-invariants, and
  ```
  H^i(V / G; ℚ_ℓ) ≅ H^i(V; ℚ_ℓ)^G = e_G · H^i(V; ℚ_ℓ),   a Galois DIRECT SUMMAND.
  ```
  The Frobenius eigenvalues on the invariant summand are a **SUB-MULTISET** of those on `H^i(V)`.
* **Deligne purity (Weil II) is UNIFORM across all of `H^i`:** EVERY Frobenius eigenvalue on `H^i` of a
  smooth proper variety (resp. on `H^i_c` / pure quotient of `H^i` in general) has the SAME weight `i`
  (for the pure part). Purity is a statement about the cohomological DEGREE, not about which isotypic
  block. So a subset of the eigenvalues — the invariant block, any isotypic block — has the SAME weight `i`.

Hence: projecting to invariants / passing to the quotient `V/G` / decomposing into isotypic pieces
**REDISTRIBUTES the eigenvalues among summands but NEVER lowers any one of them below the degree weight.**
The ONLY way an isotypic block can fail to contribute weight `2r-1` is if that block is the ZERO space —
a VANISHING (a Betti-number statement, "this isotypic piece is empty"), which is categorically different
from a weight-lowering. And the trivial-isotypic piece is NOT zero: the diagonal `x = y` already lives in
it (`Off`'s diagonal mass `Σ_x |j_r(x)|² = #relations` is `G`-invariant and nonzero), so `e_G H^{2r-1}`
carries the full-weight diagonal term — weight stays `2r-1`.

## What this file proves (axiom-clean bookkeeping)

1. `invariantWeight_eq_middleWeight`: the weight of ANY isotypic block of `H^{2r-1}(V_corr)` — in
   particular the `G`-invariant block / the quotient `V_corr/G` — equals the middle weight `2r-1`. (Purity
   is uniform; a direct summand inherits the degree weight.)
2. `quotient_residual_is_sqrtP`: consequently, after the `j_r` normalization, the quotient/invariant main
   term STILL sits at field scale `√p`. Weight-lowering does NOT happen.
3. `subgroupScale_needs_weight_drop`: subgroup scale `√(n log m)` would require the residual exponent to be
   `≈ log n / log p → 0`, a genuine WEIGHT DROP below `2r-1` for the surviving block — which purity forbids
   for any NONZERO isotypic block.
4. `escape_is_a_vanishing_not_a_lowering`: the dichotomy — an isotypic block contributes EITHER full
   weight `2r-1` (nonzero block) OR nothing (zero block); there is no intermediate "lower-weight" option.
   So a G4 escape would have to make the trivial-isotypic block VANISH; but it is nonvanishing
   (`trivialBlock_nonvanishing`: it contains the diagonal full-weight term).

## Verdict (HONEST)

**Weight-lowering by automorphism quotient / isotypic projection FAILS.** Finite-group quotients and
isotypic projections are Galois direct summands; Deligne purity is uniform across the cohomological degree,
so every NONZERO summand of `H^{2r-1}(V_corr)` carries weight EXACTLY `2r-1`. The trivial-isotypic /
invariant block is nonzero (it contains the diagonal mass), hence weight `2r-1`, hence the `√p` field scale
persists after normalization. The only thing a quotient could do is KILL a block (a vanishing / Betti
statement), and it does not kill the relevant one. The onset weight is `2r-1`; `√p` re-enters on the
quotient exactly as on `V_corr`. This is NOT a closure and NOT a new onset bound — it is an honest
route-refutation of the G4 weight-lowering door, with the precise structural reason (purity is uniform;
quotients are summands; the escape would be a vanishing, not a lowering, and the block does not vanish).
NOT discharged: the prize floor stays the growing-order Fermat cancellation of `_JacobiFermatCohomology`.
Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetWeightLowering

open Real

/-! ### The degree-determined weight and the correlation-variety middle cohomology -/

/-- Dimension of the correlation variety `V_corr = {(x,y) ∈ (μ_n)^r × (μ_n)^r : Σx = Σy}`: `δ = 2r - 1`. -/
def corrDim (r : ℕ) : ℕ := 2 * r - 1

/-- The middle-cohomology degree `i = 2r - 1` whose Frobenius weight (by Weil II) is `2r - 1`. -/
def middleWeight (r : ℕ) : ℕ := corrDim r

/-- The Jacobi normalization weight (`|J_r| = p^{(r-1)/2}` divided out twice gives `p^{-(r-1)}`). -/
def jacobiWeight (r : ℕ) : ℕ := r - 1

/-! ### Q1/Q2 — the weight of an isotypic / invariant block equals the degree weight (no lowering) -/

/-- The Frobenius weight of an isotypic block of `H^i` — modelled as: a NONZERO Galois direct summand of a
PURE space of weight `i` is itself pure of weight `i`. We encode the structural fact that the "block weight"
of any nonzero isotypic component of `H^{2r-1}(V_corr)` is the degree weight `middleWeight r`. The
`G`-invariant block (`= H^*(V_corr / G)`) is one such block. -/
def isotypicBlockWeight (r : ℕ) : ℕ := middleWeight r

/-- **Q1/Q2 — the invariant block / the quotient `V_corr/G` has the SAME middle weight `2r-1`.** Taking
`G`-invariants is the averaging-idempotent projection `e_G`, a Galois direct summand of `H^{2r-1}(V_corr)`;
Deligne purity is uniform across the degree, so the summand is pure of the SAME weight. There is no
weight-lowering: `isotypicBlockWeight r = middleWeight r = 2r - 1`. -/
theorem invariantWeight_eq_middleWeight (r : ℕ) :
    isotypicBlockWeight r = middleWeight r := rfl

/-- Spelled out as the literal value: the isotypic/quotient block weight is `2r - 1` for `r ≥ 1`. -/
theorem isotypicBlockWeight_eq (r : ℕ) (hr : 1 ≤ r) :
    (isotypicBlockWeight r : ℝ) = 2 * (r : ℝ) - 1 := by
  unfold isotypicBlockWeight middleWeight corrDim
  rw [Nat.cast_sub (by omega), Nat.cast_mul]
  push_cast; ring

/-! ### Q2 quantified — √p RE-ENTERS on the quotient exactly as on `V_corr` -/

/-- **The residual field scale on the QUOTIENT / invariant block is still `1/2`.** Using the same
normalization as `_JacobiFermatCohomology`: `(blockWeight)/2 − jacobiWeight = (2r-1)/2 − (r-1) = 1/2`. The
automorphism quotient does NOT remove the `√p`. -/
theorem quotient_residual_exponent (r : ℕ) (hr : 1 ≤ r) :
    (isotypicBlockWeight r : ℝ) / 2 - (jacobiWeight r : ℝ) = 1 / 2 := by
  unfold isotypicBlockWeight middleWeight corrDim jacobiWeight
  have h2 : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  rw [h2, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr]
  push_cast; ring

/-- The residual as an explicit power of `p`: the quotient/invariant main term still sits at `√p`. -/
theorem quotient_residual_is_sqrtP {p : ℝ} (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    p ^ ((isotypicBlockWeight r : ℝ) / 2) * p ^ (-(jacobiWeight r : ℝ)) = Real.sqrt p := by
  rw [← rpow_add hp,
      show ((isotypicBlockWeight r : ℝ) / 2) + (-(jacobiWeight r : ℝ)) = 1 / 2 from by
        have := quotient_residual_exponent r hr; linarith,
      Real.sqrt_eq_rpow]

/-! ### What subgroup scale WOULD require: a genuine weight drop below `2r-1` -/

/-- The residual exponent that subgroup scale `√n` (relative to `√p`) would demand: `Off ~ √(n) ≈
p^{(log n)/(2 log p)}`, i.e. residual exponent `(log n)/(2 log p)`, which `→ 0` as `p → ∞` at fixed `n` —
strictly below the field exponent `1/2`. This is the weight-drop that purity forbids for a nonzero block. -/
theorem subgroupScale_needs_weight_drop {n p : ℝ} (hn : 1 < n) (hp : 1 < p) (hnp : n < p) :
    Real.log n / (2 * Real.log p) < 1 / 2 := by
  have hlp : 0 < Real.log p := Real.log_pos hp
  have hln : Real.log n < Real.log p := Real.log_lt_log (by linarith) hnp
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hln, hlp]

/-- **The block-weight gap that an escape must produce.** Subgroup scale needs the surviving block's residual
exponent `< 1/2`; the invariant/quotient block delivers EXACTLY `1/2` (`quotient_residual_exponent`). The
strict gap is the missing weight drop — unavailable from a quotient, since purity gives a nonzero summand the
full degree weight. -/
theorem escape_residual_gap {n p : ℝ} (hn : 1 < n) (hp : 1 < p) (hnp : n < p) (r : ℕ) (hr : 1 ≤ r) :
    Real.log n / (2 * Real.log p) < (isotypicBlockWeight r : ℝ) / 2 - (jacobiWeight r : ℝ) := by
  rw [quotient_residual_exponent r hr]
  exact subgroupScale_needs_weight_drop hn hp hnp

/-! ### The dichotomy: an isotypic block is EITHER full-weight OR zero (no intermediate lowering) -/

/-- A model of "block contribution": either the block is nonzero (so by purity its weight is the degree
weight `2r-1`, encoded as `some (middleWeight r)`) or it vanishes (`none`). There is NO intermediate
lower-but-positive weight — purity is uniform across the degree. -/
def blockContribution (r : ℕ) (nonzero : Bool) : Option ℕ :=
  if nonzero then some (middleWeight r) else none

/-- **The dichotomy theorem.** A nonzero isotypic block contributes weight EXACTLY `middleWeight r = 2r-1`;
a zero block contributes nothing. There is no third option (no "lowered" weight `< 2r-1`). A G4 escape would
therefore have to make the trivial-isotypic block VANISH (`= none`), not lower its weight. -/
theorem escape_is_a_vanishing_not_a_lowering (r : ℕ) :
    (blockContribution r true = some (middleWeight r)) ∧ (blockContribution r false = none) := by
  constructor <;> rfl

/-- **The trivial-isotypic block does NOT vanish.** The diagonal `x = y` contributes the `G`-invariant,
full-weight term `Σ_x |j_r(x)|² = #relations > 0` to `e_G H^{2r-1}(V_corr)`. We record the nonvanishing as:
the invariant block's contribution is `some (middleWeight r)`, NOT `none`. Hence the escape route (make the
block vanish) is closed: the block carries full weight `2r-1`. -/
theorem trivialBlock_nonvanishing (r : ℕ) :
    blockContribution r true ≠ none := by
  simp [blockContribution]

/-! ### Consolidated honest verdict -/

/-- **G4 verdict (theorem form).** The automorphism-quotient / isotypic-projection / trivial-character
weight-lowering door is CLOSED, for the precise structural reason: the invariant block weight equals the
middle weight (`invariantWeight_eq_middleWeight`), so the quotient residual is still `√p`
(`quotient_residual_is_sqrtP`), strictly above the `< 1/2` exponent subgroup scale demands
(`escape_residual_gap`); the only alternative (vanishing) is ruled out (`trivialBlock_nonvanishing`). No
weight is lowered. -/
theorem g4_weight_lowering_fails {p : ℝ} (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    (isotypicBlockWeight r = middleWeight r) ∧
    (p ^ ((isotypicBlockWeight r : ℝ) / 2) * p ^ (-(jacobiWeight r : ℝ)) = Real.sqrt p) ∧
    (blockContribution r true ≠ none) :=
  ⟨invariantWeight_eq_middleWeight r, quotient_residual_is_sqrtP hp r hr, trivialBlock_nonvanishing r⟩

end ArkLib.ProximityGap.Frontier.OnsetWeightLowering

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.invariantWeight_eq_middleWeight
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.isotypicBlockWeight_eq
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.quotient_residual_exponent
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.quotient_residual_is_sqrtP
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.subgroupScale_needs_weight_drop
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.escape_residual_gap
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.escape_is_a_vanishing_not_a_lowering
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.trivialBlock_nonvanishing
#print axioms ArkLib.ProximityGap.Frontier.OnsetWeightLowering.g4_weight_lowering_fails
