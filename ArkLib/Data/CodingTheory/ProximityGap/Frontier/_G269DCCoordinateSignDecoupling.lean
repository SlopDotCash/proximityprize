/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G269: the DC coordinate does not control the adjacent-rank CORE covariance sign (#466)

The current frontier object (G220, G228–G267) is the physical adjacent-rank covariance

```text
A_r(n,p) := p · Σ_x W_G(x) R_r(x) − (Σ_x W_G(x))·(Σ_x R_r(x)),
  W_G(x) := #{(y,z) ∈ G² : 2y − z = x},   R_r(x) := (dp_r ⋆ dp_{r-1})(x),
```

with `G` the order-`n` (2-power) multiplicative subgroup of `𝔽_p^*`.  The centered covariance admits
an **exact per-coordinate decomposition**.  Writing `SW := Σ_x W_G(x) = n²`, `SR := Σ_x R_r(x)`, and

```text
P(x) := (p·W_G(x) − SW)·(p·R_r(x) − SR)   (an exact integer per coordinate),
```

a one-line expansion gives the identity

```text
Σ_x P(x) = p²·Σ_x W_G(x)R_r(x) − p·SW·SR = p·A_r(n,p),
```

so `P(x)` is the exact centered contribution of coordinate `x` and `Σ_x P(x) = p·A_r`.  Split it into
the **DC-diagonal** term `P(0)` (the `x = 0`, self-collision coordinate) and the **off-DC** remainder
`Σ_{x≠0} P(x)`.

## The tempting one-sided handle this closes

A natural simplification of the binding analytic target — square-root cancellation on the off-DC arcs
— would be that the covariance sign is a *removable DC artifact*: that `sign A_r = sign P(0)`, i.e. the
`x = 0` self-collision coordinate (`W_G(0)·R_r(0)` and the mean product) controls the sign, so that
after subtracting the diagonal the object is sign-definite or trivial.  **This is false.**

An exact float-free census (`scripts/probes/g269_dc_coordinate_sign_decoupling.py`) over genuine cells
at both orders (`n = 8` at ranks `r ∈ {3,4}`, `n = 16` at ranks `r ∈ {5,6}`; `80 + 80 = 160` cells)
finds `sign A_r = sign P(0)` in only `120/160` cells, while `sign A_r = sign Σ_{x≠0}P(x)` in
`158/160`.  The DC term dominates the magnitude in only `6/160` cells.  The covariance sign lives on
the **off-DC arcs**, precisely where the open square-root-cancellation problem sits; the DC coordinate
is a frequently sign-opposed, magnitude-negligible term.

## The float-free certificate

The decisive witnesses have the DC sign **opposite** to the covariance sign, in **both** directions
(`n = 16`, `r = 5`; note `W_G(0) = 0` at these cells, so the DC term is purely `R_r`-driven):

```text
(n,p) = (16, 97):    A₅ = −6 285 008,    P(0) = +101 818 368     → A₅ < 0 < P(0)
(n,p) = (16, 433):   A₅ = +3 425 440,    P(0) = −215 519 232     → P(0) < 0 < A₅
```

`(16,97)`: the covariance is negative while the DC coordinate is positive.  `(16,433)`: the covariance
is positive while the DC coordinate is negative.  Either one alone refutes `sign A_r = sign P(0)`;
together they show the DC sign is *uninformative in both directions*.

The decomposition is also genuinely three-way (not "DC vs. rest sign-agree").  At `(16,257)`:

```text
A₅ = −1 051 408,   P(0) = −1 035 505 664,   Σ_{x≠0}P(x) = +765 293 808,
   with   P(0) + Σ_{x≠0}P(x) = p·A₅ = 257 · (−1 051 408).
```

Here DC and covariance *agree* in sign (both negative) but the off-DC block is positive: the sign is
carried by a cancellation between the DC and off-DC blocks, not by either alone.

## Scope of the formal payload (honest)

As with G214/G216/G217/G220/G266, the **computation of record** is the reproducible float-free probe;
this file does not re-derive `A_r`, `P(0)`, or `Σ_{x≠0}P(x)` from an in-Lean subset-sum definition.  It
certifies the arithmetic and the exact decomposition identity `P(0) + Poff = p·A_r` on the recorded
cells, and it certifies the sign-decoupling witnesses.  The `120/160` vs `158/160` census split is a
statistical statement whose record is the Python sweep, not dressed as a Lean theorem.

## Why this is a genuine frontier no-go

It closes the "DC-artifact" simplification of the adjacent-rank sponsor covariance: the sign is not
controlled by the `x = 0` self-collision coordinate.  Any bound must engage the off-DC arcs directly.
This is orthogonal to G266/G267 (the quadrant/thinness census of `A_r`'s value) and to the
antipodal-count floor route (G268): those study *whether* `A_r` is positive; G269 studies *which
coordinates carry the sign*, and localizes it away from the removable diagonal onto exactly the open
square-root-cancellation surface.  It does **not** bound `A₅` at production primes; CORE remains
OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G269

/-- Exact per-coordinate decomposition data for the adjacent-rank physical covariance at one
`(order, prime)` genuine BGK cell, rank `r = 5`.

`A5` is the exact integer covariance `A₅ = p · Σ_x W_G(x) R_5(x) − (Σ W_G)(Σ R_5)`.
`P0` is the exact **DC-diagonal** centered contribution `(p·W_G(0) − Σ W_G)·(p·R_5(0) − Σ R_5)`.
`Poff` is the exact **off-DC** centered contribution `Σ_{x≠0} (p·W_G(x) − Σ W_G)·(p·R_5(x) − Σ R_5)`.
All values are exact integers from the float-free probe. -/
structure DCWitness where
  n : ℕ
  p : ℕ
  A5 : ℤ
  P0 : ℤ
  Poff : ℤ

/-- The exact decomposition identity for a cell: `P(0) + Σ_{x≠0}P(x) = p · A₅`. -/
def DecompHolds (w : DCWitness) : Prop := w.P0 + w.Poff = (w.p : ℤ) * w.A5

/-- The covariance sign is strictly positive. -/
def A5Pos (w : DCWitness) : Prop := 0 < w.A5

/-- The covariance sign is strictly negative. -/
def A5Neg (w : DCWitness) : Prop := w.A5 < 0

/-- The DC-diagonal contribution is strictly positive. -/
def P0Pos (w : DCWitness) : Prop := 0 < w.P0

/-- The DC-diagonal contribution is strictly negative. -/
def P0Neg (w : DCWitness) : Prop := w.P0 < 0

/-- The off-DC contribution is strictly positive. -/
def PoffPos (w : DCWitness) : Prop := 0 < w.Poff

/-- The off-DC contribution is strictly negative. -/
def PoffNeg (w : DCWitness) : Prop := w.Poff < 0

instance (w : DCWitness) : Decidable (DecompHolds w) := by unfold DecompHolds; infer_instance
instance (w : DCWitness) : Decidable (A5Pos w) := by unfold A5Pos; infer_instance
instance (w : DCWitness) : Decidable (A5Neg w) := by unfold A5Neg; infer_instance
instance (w : DCWitness) : Decidable (P0Pos w) := by unfold P0Pos; infer_instance
instance (w : DCWitness) : Decidable (P0Neg w) := by unfold P0Neg; infer_instance
instance (w : DCWitness) : Decidable (PoffPos w) := by unfold PoffPos; infer_instance
instance (w : DCWitness) : Decidable (PoffNeg w) := by unfold PoffNeg; infer_instance

/-- The `A₅ < 0 < P(0)` decoupling cell: `n = 16`, `p = 97`.  The covariance is negative while the
DC-diagonal coordinate is positive.  `W_G(0) = 0` here, so the DC term is purely `R_5`-driven. -/
def wCovNegDCPos : DCWitness :=
  { n := 16, p := 97, A5 := -6285008, P0 := 101818368, Poff := -711464144 }

/-- The `P(0) < 0 < A₅` decoupling cell: `n = 16`, `p = 433`.  The covariance is positive while the
DC-diagonal coordinate is negative — the opposite decoupling direction from `wCovNegDCPos`. -/
def wCovPosDCNeg : DCWitness :=
  { n := 16, p := 433, A5 := 3425440, P0 := -215519232, Poff := 1698734752 }

/-- The three-way cancellation cell: `n = 16`, `p = 257`.  Here DC and covariance agree in sign (both
negative) but the off-DC block is positive: the sign arises from cancellation between the DC and
off-DC blocks, `P(0) + Poff = p·A₅`. -/
def wThreeWay : DCWitness :=
  { n := 16, p := 257, A5 := -1051408, P0 := -1035505664, Poff := 765293808 }

/-- The exact decomposition identity holds on `wCovNegDCPos`: `P(0) + Poff = p·A₅`. -/
theorem wCovNegDCPos_decomp : DecompHolds wCovNegDCPos := by decide

/-- The exact decomposition identity holds on `wCovPosDCNeg`. -/
theorem wCovPosDCNeg_decomp : DecompHolds wCovPosDCNeg := by decide

/-- The exact decomposition identity holds on `wThreeWay`. -/
theorem wThreeWay_decomp : DecompHolds wThreeWay := by decide

/-- On `wCovNegDCPos` the covariance is negative. -/
theorem wCovNegDCPos_A5_neg : A5Neg wCovNegDCPos := by decide

/-- On `wCovNegDCPos` the DC-diagonal contribution is positive — opposite the covariance sign. -/
theorem wCovNegDCPos_P0_pos : P0Pos wCovNegDCPos := by decide

/-- On `wCovPosDCNeg` the covariance is positive. -/
theorem wCovPosDCNeg_A5_pos : A5Pos wCovPosDCNeg := by decide

/-- On `wCovPosDCNeg` the DC-diagonal contribution is negative — opposite the covariance sign. -/
theorem wCovPosDCNeg_P0_neg : P0Neg wCovPosDCNeg := by decide

/-- On `wThreeWay` the covariance is negative, the DC block is negative, but the off-DC block is
positive: a genuine three-way sign configuration, not "DC vs. rest agree". -/
theorem wThreeWay_signs : A5Neg wThreeWay ∧ P0Neg wThreeWay ∧ PoffPos wThreeWay := by
  exact ⟨by decide, by decide, by decide⟩

/-- **No DC-diagonal sign lock (both directions).**  There is a genuine cell with `A₅ < 0` and
`P(0) > 0` (`wCovNegDCPos`, `(16,97)`) *and* a genuine cell with `A₅ > 0` and `P(0) < 0`
(`wCovPosDCNeg`, `(16,433)`).  Hence neither implication `P(0) > 0 ⟹ A₅ > 0` nor
`A₅ > 0 ⟹ P(0) > 0` holds: the `x = 0` self-collision coordinate does not control the covariance
sign, in either direction. -/
theorem no_dc_sign_lock :
    (∃ w : DCWitness, w.A5 < 0 ∧ 0 < w.P0) ∧ (∃ w : DCWitness, 0 < w.A5 ∧ w.P0 < 0) := by
  exact ⟨⟨wCovNegDCPos, by decide, by decide⟩, ⟨wCovPosDCNeg, by decide, by decide⟩⟩

/-- **The off-DC block, not the DC coordinate, carries the covariance sign on the decoupling
witnesses.**  On both `(16,97)` and `(16,433)` the off-DC centered contribution `Poff` matches the
covariance sign while the DC contribution `P(0)` opposes it, and the exact decomposition
`P(0) + Poff = p·A₅` holds. -/
theorem offdc_carries_sign :
    (wCovNegDCPos.A5 < 0 ∧ wCovNegDCPos.Poff < 0 ∧ 0 < wCovNegDCPos.P0 ∧ DecompHolds wCovNegDCPos) ∧
      (0 < wCovPosDCNeg.A5 ∧ 0 < wCovPosDCNeg.Poff ∧ wCovPosDCNeg.P0 < 0 ∧
        DecompHolds wCovPosDCNeg) := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide⟩⟩

/-! ## Axiom audit -/
#print axioms wCovNegDCPos_decomp
#print axioms wCovPosDCNeg_decomp
#print axioms wThreeWay_decomp
#print axioms wCovNegDCPos_A5_neg
#print axioms wCovNegDCPos_P0_pos
#print axioms wCovPosDCNeg_A5_pos
#print axioms wCovPosDCNeg_P0_neg
#print axioms wThreeWay_signs
#print axioms no_dc_sign_lock
#print axioms offdc_carries_sign

end ArkLib.ProximityGap.Frontier.G269
