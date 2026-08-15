/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# G260: the quotient origin is a gauge, so no `W`-intrinsic origin anchor pins the covariance

After G258 (complete Fourier multiset + positivity + support cardinality cannot pin the
fixed-row covariance, because quotient units relabel the physical profile) and G259 (the full
bispectrum and every translation-invariant higher moment cannot pin it either, because the target
covariance is not translation invariant while those moments are), the single named open repair was:
find a *`W`-intrinsic, sponsor-uniform origin anchor* that recovers the absolute quotient origin from
`W` alone, independently of the rank rows `R_r`.

This file records the structural no-go. The choice of "zero coset" in the sponsor quotient is a
**gauge**: the cyclic shift group `ZMod m` acts on physical profiles, the total mass and every
shift-invariant statistic are preserved, and the fixed-row centered covariance

```text
centeredCov m W R = m * (∑ x, W x * R x) - (∑ x, W x) * (∑ x, R x)
```

is genuinely shift-non-invariant. Any origin marker computable from `W` is translation-covariant:
either shift-invariant (autocorrelation values, `|DFT|`, the value multiset, any degree-`k` moment),
which gives the identity and a sign-reversing shift the *same value*; or shift-equivariant (the
argmax of a unique extremum, any "distinguished residue" rule, `DFT` phases), for which "align the
marker to `0`" is a gauge fixing that maps the whole shift orbit to *one* canonical profile. Neither
class can tell the covariance which physical origin `R_r` uses.

## The exact witness (`ZMod 7`)

`W = ![2,0,1,1,1,1,0]`, row `R = ![0,0,0,1,1,1,0]`, shift by `c = 2`:

* `centeredCov 7 W R = 7*3 - 6*3 = 3 > 0`;
* `centeredCov 7 (shift 2 W) R = 7*2 - 6*3 = -4 < 0` — the same fixed row, one origin shift, a sign
  reversal;
* `W` has a unique maximum at `0`, `shift 2 W` has its unique maximum at `2 = 0 + 2`, i.e. the argmax
  marker is *equivariant*; and the two gauge-canonical forms `shift (-argmax) ·` coincide exactly:
  both equal `![2,0,1,1,1,1,0]`.

So two profiles with the *same* argmax-gauge canonical form have opposite covariance sign against the
*same* row. Any decision procedure factoring through that canonical form (any equivariant marker) is
therefore blind to the sign. The companion probe
`scripts/probes/g260_origin_anchor_gauge_nogo.py` verifies the gauge collapse over the whole shift
orbit universally and shows the simultaneous `r=5,6` sign-reversing shifts persist at `~25%` of all
shifts as the support fraction thins to `0.03` (prize scale).

This is a route no-go, not a Jacobi covariance estimate and not a prize closure. It closes the
origin-anchor repair G259 left open: the missing datum is absolute row placement itself, equivalently
the original joint sponsor-prime BGK/Paley covariance proved directly against the row label. The
weights here are the standard structural surrogate used across G245-G259; the tested property (gauge
covariance of every `W`-marker versus shift-non-invariance of the target) is structural and stable
across the surrogate.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G260OriginAnchorGaugeNoGo

variable {m : ℕ} [NeZero m]

/-- Cyclic shift of a physical profile on `ZMod m` by `c`: `(shift c W) x = W (x - c)`. -/
def shift (c : ZMod m) (W : ZMod m → ℤ) : ZMod m → ℤ := fun x => W (x - c)

/-- Shifting preserves the total mass. -/
theorem shift_sum_eq (c : ZMod m) (W : ZMod m → ℤ) :
    ∑ x, shift c W x = ∑ x, W x := by
  unfold shift
  exact Fintype.sum_equiv (Equiv.subRight c) _ _ (fun x => rfl)

/-- Composition of shifts. -/
theorem shift_shift (c d : ZMod m) (W : ZMod m → ℤ) :
    shift c (shift d W) = shift (c + d) W := by
  unfold shift
  funext x
  congr 1
  ring

/-- Shifting by `0` is the identity. -/
theorem shift_zero (W : ZMod m → ℤ) : shift (0 : ZMod m) W = W := by
  unfold shift
  funext x
  simp

/-- Integer centered covariance on a quotient of size `m`. -/
def centeredCov (m : ℕ) [NeZero m] (W R : ZMod m → ℤ) : ℤ :=
  (m : ℤ) * (∑ x, W x * R x) - (∑ x, W x) * (∑ x, R x)

/-- The correlation term of a shifted profile equals the correlation with the inversely shifted
row: `∑ x, (shift c W) x * R x = ∑ x, W x * (shift (-c) R) x`. The centered covariance depends only
on the *relative* placement of profile and row; there is no distinguished origin. -/
theorem shift_corr_eq (c : ZMod m) (W R : ZMod m → ℤ) :
    (∑ x, shift c W x * R x) = ∑ x, W x * shift (-c) R x := by
  unfold shift
  refine Fintype.sum_equiv (Equiv.subRight c) _ _ ?_
  intro x
  simp only [Equiv.subRight_apply]
  congr 2
  ring

/-! ## The exact `ZMod 7` witness -/

abbrev Q := ZMod 7

instance : NeZero 7 := ⟨by norm_num⟩

/-- The physical profile `W` on `ZMod 7`. -/
def Wprof : Q → ℤ := ![2, 0, 1, 1, 1, 1, 0]

/-- The fixed rank-row indicator `R`. -/
def Rrow : Q → ℤ := ![0, 0, 0, 1, 1, 1, 0]

/-- The shift amount witnessing the origin gauge. -/
def cWit : Q := 2

/-- The base centered covariance is strictly positive. -/
theorem base_cov_pos : 0 < centeredCov 7 Wprof Rrow := by
  simp only [centeredCov, Wprof, Rrow]
  decide

/-- The shifted centered covariance is strictly negative: the *same* fixed row, a single origin
shift, reverses the sign. -/
theorem shifted_cov_neg : centeredCov 7 (shift cWit Wprof) Rrow < 0 := by
  simp only [centeredCov, shift, cWit, Wprof, Rrow]
  decide

/-- Exact values: `+3` before the shift, `-4` after. -/
theorem cov_values :
    centeredCov 7 Wprof Rrow = 3 ∧ centeredCov 7 (shift cWit Wprof) Rrow = -4 := by
  refine ⟨?_, ?_⟩
  · simp only [centeredCov, Wprof, Rrow]; decide
  · simp only [centeredCov, shift, cWit, Wprof, Rrow]; decide

/-- One and the same fixed row is sign-reversed by an origin shift: the covariance is genuinely
shift-non-invariant. -/
theorem covariance_shift_non_invariant :
    0 < centeredCov 7 Wprof Rrow ∧ centeredCov 7 (shift cWit Wprof) Rrow < 0 :=
  ⟨base_cov_pos, shifted_cov_neg⟩

/-! ## The argmax gauge collapses the shift pair to one canonical form -/

/-- `W` attains its unique maximum at `0`. -/
theorem argmax_base : Wprof 0 = 2 ∧ ∀ x : Q, x ≠ 0 → Wprof x < 2 := by
  refine ⟨by decide, ?_⟩
  decide

/-- The shifted profile attains its unique maximum at `2 = 0 + cWit`: the argmax marker is
translation-*equivariant*. -/
theorem argmax_shifted :
    shift cWit Wprof 2 = 2 ∧ ∀ x : Q, x ≠ 2 → shift cWit Wprof x < 2 := by
  refine ⟨by decide, ?_⟩
  decide

/-- The gauge-canonical forms coincide exactly. Aligning the (equivariant) argmax marker to `0`
maps both the base profile and its sign-reversing shift to the *same* canonical profile:
`shift (-0) Wprof = shift (-(2)) (shift cWit Wprof)`. Hence any decision procedure that factors
through this canonical form is identical on the two profiles, yet their covariance signs against the
same row differ. No equivariant origin marker can pin the sign. -/
theorem gauge_canonical_forms_coincide :
    shift (-(0 : Q)) Wprof = shift (-(2 : Q)) (shift cWit Wprof) := by
  funext x
  fin_cases x <;> (simp only [shift, cWit, Wprof]; decide)

/-- The full gauge no-go, packaged: there exist a profile, a fixed row and an origin shift such that
(i) the covariance sign reverses, while (ii) the equivariant argmax gauge sends both profiles to one
canonical form. A `W`-intrinsic origin anchor built from any such gauge cannot pin the covariance
sign. -/
theorem origin_anchor_gauge_nogo :
    (0 < centeredCov 7 Wprof Rrow ∧ centeredCov 7 (shift cWit Wprof) Rrow < 0) ∧
      shift (-(0 : Q)) Wprof = shift (-(2 : Q)) (shift cWit Wprof) :=
  ⟨covariance_shift_non_invariant, gauge_canonical_forms_coincide⟩

/-! ## Axiom audit -/
#print axioms shift_sum_eq
#print axioms shift_corr_eq
#print axioms covariance_shift_non_invariant
#print axioms gauge_canonical_forms_coincide
#print axioms origin_anchor_gauge_nogo

end ArkLib.ProximityGap.Frontier.G260OriginAnchorGaugeNoGo
