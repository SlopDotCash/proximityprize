/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# The multiplicative-dilation reduction of additive energy (Issue #389)

*Why is the wall about multiplicative **subgroups**, and not arbitrary sets?* Because for a
multiplicative subgroup `H` the additive energy is **dilation-invariant**: scaling a solution of
`a+b=c+d` by any `t∈H` gives another solution, and the action is free with orbits of size `|H|`.
Picking the unique representative with first coordinate `1` collapses the four-variable energy to a
single curve point-count — the object Form 6 (Szemerédi–Trotter incidences) and Form 7 (Stepanov
auxiliary polynomials) actually bound.

* `addEnergy_eq_card_mul_anchored` :  `E(H) = |H| · #{(b,c,d)∈H³ : 1+b = c+d}`.
* `addEnergy_eq_card_mul_incidence` :  `E(H) = |H| · #{(b,c)∈H² : 1+b−c ∈ H}`  (eliminate `d`).
* `card_dvd_addEnergy`              :  `|H| ∣ E(H)`  — a structural divisibility *special to
  subgroups* (absent for general sets), the cleanest fingerprint of the multiplicative symmetry.

The reduction is exact and elementary (a multiplicative reindexing of each inner sum by the unit
`y₁`), valid for any `H ⊆ F` closed under `·` and `⁻¹` with `0 ∉ H`. Composed with the
`SubgroupGaussSumFourthMoment` chain (`q·E(H) = ∑_b ‖η_b‖⁴`) and the
`EnergyCharacterTransport` brick, it routes the whole programme through the single normalized
incidence count `T(H) := #{(b,c)∈H² : 1+b−c ∈ H}` — and `T(H) = (1 + o(1))·n²/q` is the
Stepanov/Weil statement (`E(H) = (1+o(1))·n³/q` for the *full* group; the subgroup deviation from
this is exactly the sub-Johnson wall).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #389.
- [HBK00] Heath-Brown, Konyagin. *New bounds for Gauss sums derived from kth powers …*. 2000.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment (addEnergy)

namespace ArkLib.ProximityGap.EnergyDilationReduction

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The dilation reduction.** For a multiplicative subgroup `H` (closed under `·`, `⁻¹`, with
`0 ∉ H`), every inner triple sum of the additive energy is, after reindexing `(y₂,y₃,y₄) ↦
(y₁b, y₁c, y₁d)` and cancelling the unit `y₁`, the *same* `y₁`-independent count
`T = #{(b,c,d)∈H³ : 1+b=c+d}`. Hence `E(H) = |H| · T`. -/
theorem addEnergy_eq_card_mul_anchored (H : Finset F)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) (hinv : ∀ a ∈ H, a⁻¹ ∈ H) (hzero : (0 : F) ∉ H) :
    addEnergy H
      = H.card * (∑ b ∈ H, ∑ c ∈ H, ∑ d ∈ H, if (1 : F) + b = c + d then 1 else 0) := by
  classical
  have hreindex : ∀ y₁ ∈ H,
      (∑ y₂ ∈ H, ∑ y₃ ∈ H, ∑ y₄ ∈ H, if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0)
        = ∑ b ∈ H, ∑ c ∈ H, ∑ d ∈ H, if (1 : F) + b = c + d then 1 else 0 := by
    intro y₁ hy₁
    have hy₁ne : y₁ ≠ 0 := fun h => hzero (h ▸ hy₁)
    -- reindex one `H`-sum by left-multiplication by the unit `y₁`
    have hmulbij : ∀ g : F → ℕ, (∑ b ∈ H, g (y₁ * b)) = ∑ x ∈ H, g x := by
      intro g
      exact Finset.sum_nbij' (fun b => y₁ * b) (fun x => y₁⁻¹ * x)
        (fun b hb => hmul y₁ hy₁ b hb)
        (fun x hx => hmul y₁⁻¹ (hinv y₁ hy₁) x hx)
        (fun b _ => inv_mul_cancel_left₀ hy₁ne b)
        (fun x _ => mul_inv_cancel_left₀ hy₁ne x)
        (fun b _ => rfl)
    rw [← hmulbij (fun y₂ => ∑ y₃ ∈ H, ∑ y₄ ∈ H, if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← hmulbij (fun y₃ => ∑ y₄ ∈ H, if y₁ + y₁ * b = y₃ + y₄ then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← hmulbij (fun y₄ => if y₁ + y₁ * b = y₁ * c + y₄ then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have hiff : (y₁ + y₁ * b = y₁ * c + y₁ * d) ↔ ((1 : F) + b = c + d) := by
      constructor
      · intro h; exact mul_left_cancel₀ hy₁ne (by linear_combination h)
      · intro h; linear_combination y₁ * h
    simp only [hiff]
  unfold addEnergy
  rw [Finset.sum_congr rfl hreindex, Finset.sum_const, smul_eq_mul]

/-- **Eliminating `d`: the curve point-count form.** The unique `d` solving `1+b=c+d` is
`1+b−c`, counted iff it lies in `H`. So `E(H) = |H| · #{(b,c)∈H² : 1+b−c ∈ H}` — the energy is
`|H|` times an incidence count on the shifted difference set, the Stepanov/Weil object. -/
theorem addEnergy_eq_card_mul_incidence (H : Finset F)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) (hinv : ∀ a ∈ H, a⁻¹ ∈ H) (hzero : (0 : F) ∉ H) :
    addEnergy H = H.card * (∑ b ∈ H, ∑ c ∈ H, if (1 : F) + b - c ∈ H then 1 else 0) := by
  classical
  rw [addEnergy_eq_card_mul_anchored H hmul hinv hzero]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => ?_))
  have hrw : (∑ d ∈ H, if (1 : F) + b = c + d then (1 : ℕ) else 0)
      = ∑ d ∈ H, if d = 1 + b - c then (1 : ℕ) else 0 := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have hc : ((1 : F) + b = c + d) ↔ (d = 1 + b - c) := by
      constructor
      · intro h; linear_combination -h
      · intro h; linear_combination -h
    simp only [hc]
  rw [hrw, Finset.sum_ite_eq' H (1 + b - c) (fun _ => (1 : ℕ))]

/-- **`|H| ∣ E(H)`.** The additive energy of a multiplicative subgroup is always a multiple of the
subgroup order — the structural fingerprint of dilation invariance, with no analogue for a generic
set. -/
theorem card_dvd_addEnergy (H : Finset F)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) (hinv : ∀ a ∈ H, a⁻¹ ∈ H) (hzero : (0 : F) ∉ H) :
    H.card ∣ addEnergy H := by
  rw [addEnergy_eq_card_mul_anchored H hmul hinv hzero]
  exact dvd_mul_right _ _

end ArkLib.ProximityGap.EnergyDilationReduction

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.EnergyDilationReduction.addEnergy_eq_card_mul_anchored
#print axioms ArkLib.ProximityGap.EnergyDilationReduction.addEnergy_eq_card_mul_incidence
#print axioms ArkLib.ProximityGap.EnergyDilationReduction.card_dvd_addEnergy
