/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Antipodal INVARIANT-weight kernel (#444, AvX / Bridge05 companion)

`_Bridge05_AntipodalOddVanishing.sum_eq_zero_of_antiInvariant` proves the ANTI-invariant half:
a weight `f` with `f (σ x) = - f x` sums to zero over an involution-closed set. This file proves
the **dual** half — the one driven by the *value* function rather than the weight.

## The mechanism (probe `scripts/probes/probe_antipodal_kernel.py`, k=1..6 / n=4..128, 300 random
weights each, 0 violations)

On the thin 2-power subgroup `μ_{2n}` (`n = 2^k`) the antipodal involution `σ : x ↦ −x` (`= ` mult.
by the order-2 element `ζ^{2^k} = −1`, present exactly because the subgroup has even order) negates
the **root values**: `root (σ x) = − root x`. Therefore the *weighted* character sum
`∑_{x} c x · root x` over any **`σ`-invariant** weight `c` (`c (σ x) = c x`) VANISHES: pairing each
`x` with `σ x`,
  `c x · root x + c (σ x) · root (σ x) = c x · root x + c x · (−root x) = 0`.

So the whole space of antipodally-invariant weights lies in the KERNEL of the weighted
character-sum map. Combined with the existing anti-invariant theorem (which kills the antipodal
ODD-graded part), this is the even/invariant complement: it is the `e_odd = 0` half of the antipodal
descent in pointwise-kernel form, proven directly by `Finset.sum_involution` with NO cyclotomic /
minpoly machinery (contrast `_AvX_VanishingTwoPowSumIsAntipodalP`, which proves the converse via
`minpoly.dvd` + `cyclotomic_two_pow`).

**Honest scope.** Abstract finite-involution algebra over any `AddCommGroup` / `CommRing`,
instantiated at the antipodal involution. It identifies a kernel of the weighted character-sum map;
it is char-free, thinness-AGNOSTIC structure (NOT thinness-essential) and does NOT bound `M(μ_n)`,
cross the BGK wall, or make any CORE / capacity / growth-law claim.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier

variable {ι : Type*} [DecidableEq ι]

/-- **Antipodal invariant-weight kernel (abstract core).** Let `σ` be a fixed-point-free involution
of the finite set `T`. If the value function `g` is *anti-invariant* (`g (σ x) = - g x`) and the
weight `c` is *invariant* (`c (σ x) = c x`), then the weighted sum `∑_{x ∈ T} c x • g x` vanishes:
each pair `{x, σ x}` contributes `c x • g x + c x • (- g x) = 0`. -/
theorem sum_smul_eq_zero_of_invariant_weight_antiInvariant_value
    {M : Type*} [AddCommGroup M] {R : Type*} [Monoid R] [DistribMulAction R M]
    (T : Finset ι) (σ : ι → ι)
    (hmap : ∀ x ∈ T, σ x ∈ T)
    (hinv : ∀ x ∈ T, σ (σ x) = x)
    (hnofix : ∀ x ∈ T, σ x ≠ x)
    (c : ι → R) (cinv : ∀ x ∈ T, c (σ x) = c x)
    (g : ι → M) (ganti : ∀ x ∈ T, g (σ x) = - g x) :
    ∑ x ∈ T, c x • g x = 0 := by
  refine Finset.sum_involution (fun x _ => σ x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [cinv x hx, ganti x hx, smul_neg, add_neg_cancel]
  · intro x hx _; exact hnofix x hx
  · intro x hx; exact hmap x hx
  · intro x hx; exact hinv x hx

/-- **Ring form.** Same statement over a `CommRing`, with the weight multiplied (not just smul'd)
into the value: an *invariant* weight `c` times an *anti-invariant* value `g` sums to zero.
This is the `e_odd = 0` half of the antipodal descent in pointwise-kernel form. -/
theorem sum_mul_eq_zero_of_invariant_weight_antiInvariant_value
    {R : Type*} [CommRing R]
    (T : Finset ι) (σ : ι → ι)
    (hmap : ∀ x ∈ T, σ x ∈ T)
    (hinv : ∀ x ∈ T, σ (σ x) = x)
    (hnofix : ∀ x ∈ T, σ x ≠ x)
    (c : ι → R) (cinv : ∀ x ∈ T, c (σ x) = c x)
    (g : ι → R) (ganti : ∀ x ∈ T, g (σ x) = -g x) :
    ∑ x ∈ T, c x * g x = 0 := by
  refine Finset.sum_involution (fun x _ => σ x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [cinv x hx, ganti x hx, mul_neg, add_neg_cancel]
  · intro x hx _; exact hnofix x hx
  · intro x hx; exact hmap x hx
  · intro x hx; exact hinv x hx

/-- **Sanity instance.** On `T = {0,1,2,3} ⊆ ZMod 4` with the antipodal involution `x ↦ x + 2`
(fixed-point-free since `2 ≠ 0` in `ZMod 4`), the INVARIANT weight `c x = if x = 0 ∨ x = 2 then 3
else 5` (constant on each antipodal pair `{0,2}`, `{1,3}`) times the anti-invariant signed value
`g x = if x = 0 ∨ x = 1 then (1 : ℤ) else -1` (so `g (x+2) = - g x`) sums to `0`. -/
example :
    ∑ x ∈ ({0, 1, 2, 3} : Finset (ZMod 4)),
      ((if x = 0 ∨ x = 2 then (3 : ℤ) else 5) * (if x = 0 ∨ x = 1 then 1 else -1)) = 0 := by decide

#print axioms sum_smul_eq_zero_of_invariant_weight_antiInvariant_value

end ArkLib.ProximityGap.Frontier
