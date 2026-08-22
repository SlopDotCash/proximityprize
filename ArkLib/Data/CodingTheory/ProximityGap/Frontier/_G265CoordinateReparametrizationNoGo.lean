/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G258QuotientAutomorphismPositivityNoGo

/-!
# G265: quotient coordinate reparametrization acts diagonally and preserves the CORE covariance

G258 relabels the weighted relation profile `W` by a quotient unit while holding the adjacent-rank
row `R` fixed. This is a valid countermodel to data that forget the quotient labels, but it is not a
physical change of primitive-root coordinates. Replacing a primitive root `g` by `g^a` changes
the quotient label `j` to `a*j`; therefore it relabels **both** field-derived profiles `W` and `R`
by the same unit.

This file proves the exact structural distinction. For profiles on `ZMod N`, simultaneous unit
relabeling preserves their dot product, each total mass, and hence the centered covariance

```text
C_N(W,R) = N * sum_x W(x)R(x) - (sum_x W(x))(sum_x R(x)).
```

More generally, one-sided relabeling of `W` is exactly transport of the inverse relabeling onto `R`.
Thus the unit family is coordinate gauge for the pair `(W,R)`: its physical covariance orbit is a
singleton. A sign reversal obtained by moving `W` against a fixed `R` measures relative labelled
placement, not a symmetry of the fixed sponsor pair.

The exact companion probe recomputes the characteristic-p profiles. In G258's flagship
`(n,p,m)=(16,1297,81)`, root exponent `53` produces exactly G258's moved support. The one-sided
move has covariances `(-346283,-1161769)`, while simultaneous relabeling of the two rank rows
restores the base values `(+1261081,+3691265)`. All 432 primitive-root choices preserve both
covariances. The probe also verifies that the affine stabilizer of the subgroup is `{x |-> h*x :
h in G}`, which acts trivially on the quotient.

Scope: an axiom-clean admissibility/scope correction, not a sponsor-prime estimate and not prize
closure. G258 remains a label-free marginal no-go, and G264 remains a relaxed nonnegative-cone
no-go. Neither theorem by itself realizes a new arithmetic profile at the fixed sponsor labels. The
surviving object is still the direct row-labelled sponsor covariance.
-/

open Finset ZMod

namespace ArkLib.ProximityGap.Frontier.G265CoordinateReparametrizationNoGo

open ArkLib.ProximityGap.Frontier.G258QuotientAutomorphismPositivityNoGo

variable {N : ℕ} [NeZero N]

/-- Integer centered covariance on a cyclic quotient. -/
def centeredCov (W R : ZMod N → ℤ) : ℤ :=
  (N : ℤ) * (∑ x, W x * R x) - (∑ x, W x) * (∑ x, R x)

/-- Simultaneously relabeling both profiles by a quotient unit preserves their dot product. -/
theorem unitRelabel_dot_eq (u : (ZMod N)ˣ) (W R : ZMod N → ℤ) :
    (∑ x, unitRelabel u W x * unitRelabel u R x) = ∑ x, W x * R x := by
  refine Fintype.sum_equiv u.mulLeft _ _ ?_
  intro x
  rfl

/-- **Coordinate-gauge invariance.** A physical primitive-root reparametrization relabels both
profiles, so the centered covariance is exactly unchanged. -/
theorem centeredCov_unitRelabel_both (u : (ZMod N)ˣ) (W R : ZMod N → ℤ) :
    centeredCov (unitRelabel u W) (unitRelabel u R) = centeredCov W R := by
  unfold centeredCov
  rw [unitRelabel_dot_eq, unitRelabel_sum_eq, unitRelabel_sum_eq]

/-- One-sided relabeling of `W` is transport of the inverse relabeling onto the row `R`. It changes
only the relative placement of the two profiles. -/
theorem unitRelabel_dot_transport (u : (ZMod N)ˣ) (W R : ZMod N → ℤ) :
    (∑ x, unitRelabel u W x * R x) = ∑ x, W x * unitRelabel u⁻¹ R x := by
  refine Fintype.sum_equiv u.mulLeft _ _ ?_
  intro x
  simp only [unitRelabel]
  congr 2
  simp

/-- Centered form of the one-sided transport law. -/
theorem centeredCov_unitRelabel_left (u : (ZMod N)ˣ) (W R : ZMod N → ℤ) :
    centeredCov (unitRelabel u W) R = centeredCov W (unitRelabel u⁻¹ R) := by
  unfold centeredCov
  rw [unitRelabel_dot_transport, unitRelabel_sum_eq, unitRelabel_sum_eq]

/-- Packaged route boundary: simultaneous coordinate changes preserve the target exactly, whereas a
one-sided move is only a change of relative labelled placement. -/
theorem coordinate_reparametrization_preserves_gate (u : (ZMod N)ˣ) (W R : ZMod N → ℤ) :
    centeredCov (unitRelabel u W) (unitRelabel u R) = centeredCov W R ∧
      centeredCov (unitRelabel u W) R = centeredCov W (unitRelabel u⁻¹ R) :=
  ⟨centeredCov_unitRelabel_both u W R, centeredCov_unitRelabel_left u W R⟩

/-! ## Axiom audit -/
#print axioms unitRelabel_dot_eq
#print axioms centeredCov_unitRelabel_both
#print axioms unitRelabel_dot_transport
#print axioms centeredCov_unitRelabel_left
#print axioms coordinate_reparametrization_preserves_gate

end ArkLib.ProximityGap.Frontier.G265CoordinateReparametrizationNoGo
