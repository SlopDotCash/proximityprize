/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The dyadic halving recursion for 2-power subgroup Gaussian periods (#389)

For the subgroup Gauss sum `η_b(G) = ∑_{x∈G} ψ(b·x)` and `G = μ_{2k}` the `2k`-th roots of unity,
the antipodal split `μ_{2k} = μ_k ⊔ ζ·μ_k` (with `ζ^k = -1`) gives the EXACT halving recursion

  `eta ψ (nthRootsFinset (2k) 1) b = eta ψ (nthRootsFinset k 1) b + eta ψ (nthRootsFinset k 1) (b·ζ)`.

This is the Walsh/FFT-butterfly structure of 2-power Gaussian periods (the dyadic tower) and the exact
identity underlying the dyadic square-root-cancellation analysis; with reality (`eta` is real, since
`μ_{2k} = -μ_{2k}`) it is the structural core of the open sup-norm question for these periods.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.DyadicHalving

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- **Reality of the 2-power subgroup period.** Because `μ_{2k}` is closed under negation, the period
`η_b` equals its own complex conjugate, hence is real. -/
theorem conj_eta_nthRoots (ψ : AddChar F ℂ) (k : ℕ) (hk : 0 < k) (b : F) :
    (starRingEnd ℂ) (eta ψ (Polynomial.nthRootsFinset (2 * k) (1 : F)) b)
      = eta ψ (Polynomial.nthRootsFinset (2 * k) (1 : F)) b := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ x : F, (starRingEnd ℂ) (ψ (b * x)) = ψ (b * (-x)) := by
    intro x
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]; congr 1; ring
  rw [eta, map_sum, Finset.sum_congr rfl (fun x _ => hconj x)]
  refine Finset.sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Polynomial.mem_nthRootsFinset (by omega) (1 : F)] at hx ⊢
    rw [neg_pow, Even.neg_one_pow (even_two_mul k), one_mul, hx]
  · intro x hx
    rw [Polynomial.mem_nthRootsFinset (by omega) (1 : F)] at hx ⊢
    rw [neg_pow, Even.neg_one_pow (even_two_mul k), one_mul, hx]
  · intro x _; ring
  · intro x _; ring
  · intro x _; rfl

omit [Fintype F] in
/-- **The dyadic halving recursion.** For `ζ^k = -1` (a primitive `2k`-th root), in odd characteristic
(`(1:F) ≠ -1`), the `2k`-period splits as two `k`-periods, the second at the shifted frequency `b·ζ`. -/
theorem eta_halving (ψ : AddChar F ℂ) (k : ℕ) (hk : 0 < k) (b : F)
    (htwo : (1 : F) ≠ -1) {ζ : F} (hζ : ζ ^ k = -1) :
    eta ψ (Polynomial.nthRootsFinset (2 * k) (1 : F)) b
      = eta ψ (Polynomial.nthRootsFinset k (1 : F)) b
        + eta ψ (Polynomial.nthRootsFinset k (1 : F)) (b * ζ) := by
  have h2k : 0 < 2 * k := by omega
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, zero_pow hk.ne'] at hζ; exact (by norm_num : (0:F) ≠ -1) hζ
  -- the "negative half" {x : x^k = -1} = nthRootsFinset k (-1) is the image of μ_k under (ζ * ·)
  have himg : Polynomial.nthRootsFinset k (-1 : F)
      = (Polynomial.nthRootsFinset k (1 : F)).image (fun y => ζ * y) := by
    ext x
    simp only [Finset.mem_image, Polynomial.mem_nthRootsFinset hk]
    constructor
    · intro hxk
      refine ⟨ζ⁻¹ * x, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]⟩
      rw [mul_pow, inv_pow, hζ, hxk]; simp
    · rintro ⟨y, hy, rfl⟩
      rw [mul_pow, hζ, hy]; ring
  -- μ_{2k} splits as the disjoint union of μ_k and the negative half
  have hsplit : Polynomial.nthRootsFinset (2 * k) (1 : F)
      = Polynomial.nthRootsFinset k (1 : F) ∪ Polynomial.nthRootsFinset k (-1 : F) := by
    ext x
    simp only [Finset.mem_union, Polynomial.mem_nthRootsFinset hk,
      Polynomial.mem_nthRootsFinset h2k]
    constructor
    · intro hx
      have hsq : x ^ k * x ^ k = 1 := by rw [← pow_add, ← two_mul]; exact hx
      exact mul_self_eq_one_iff.mp hsq
    · rintro (h | h) <;> rw [two_mul, pow_add, h] <;> ring
  have hdisj : Disjoint (Polynomial.nthRootsFinset k (1 : F))
      (Polynomial.nthRootsFinset k (-1 : F)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Polynomial.mem_nthRootsFinset hk] at hx
    rw [Polynomial.mem_nthRootsFinset hk] at hx'
    exact htwo (hx.symm.trans hx')
  rw [eta, hsplit, Finset.sum_union hdisj, himg]
  congr 1
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hζ0 h), eta]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1; ring

end ArkLib.ProximityGap.DyadicHalving

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.DyadicHalving.conj_eta_nthRoots
#print axioms ArkLib.ProximityGap.DyadicHalving.eta_halving
