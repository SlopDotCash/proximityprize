/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardIdentity

/-!
# Even-tower deep-band supply: the antipodal growth lower bound, and where it is tight (#389)

`GeneralOrchardIdentity.lean` reduces the deepest-band supply of the tower word `x^{k+1}` to the
zero-sum-`(k+1)`-subset count of the domain.  `QuarticSupplyDichotomy.lean` exhibits the `k = 3`
(quartic) case at three concrete fields, including the 2-power domain `μ_8 ⊂ F₁₇` where the
supply is exactly `6 = C(n/2, 2)`.

This file lands the **general theorem** behind that observation and then **honestly bounds its
reach**:

* **`zeroSum_evenSubsets_antipodal_ge`** (proved, char-independent) — for any domain carrying a
  negation pairing `ν` on a representative set `R` (`dom (ν i) = − dom i`, `ν i ∉ R`), the
  zero-sum-`2j`-subset count is at least `C(|R|, j)`: choose `j` of the antipodal pairs and take
  their union.  Via the orchard identity this is **`evenTowerSupply_antipodal_ge`**: the
  deepest-band supply of `x^{2j}` is `≥ C(|R|, j) = Θ(n^j)` on every negation-closed domain.
  So higher even-tower words have *polynomial-but-growing* deep-band supply — nonzero, degree
  `j = (k+1)/2` in `n` — consistent with the bold pin `δ* = capacity − Θ(1/log n)`.

* **`antipodal_bound_not_tight`** (refutation, machine-checked) — the matching *upper* bound
  `C(n/2, 2)` is **false in small characteristic**: on `μ_{10} = F₁₁^×` the zero-sum-`4`-subset
  count is `20`, strictly above `C(5, 2) = 10`.  The excess comes from char-`p` coincidences
  (e.g. `1+2+3+5 ≡ 0 (mod 11)` is not a char-`0` root-of-unity relation).  Such coincidences
  exist only **below** the Sidon/resultant threshold `n² < p`; every deployed/prize field
  (`q ≈ n·2^128 ≫ n²`) is above it, where the antipodal bound becomes tight (the
  `AdditiveEnergyResultant` cone).  So `C(n/2, j)` is the *honest* deep-band growth rate on
  prize fields, a strict lower bound on small fields.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- **The antipodal growth lower bound** (char-independent).  If `ν` pairs each element of a
representative set `R` with its negation outside `R`, then the number of zero-sum `2j`-subsets
is at least `C(|R|, j)`: each `j`-subset `P ⊆ R` gives the zero-sum `2j`-set `P ∪ ν(P)`, and
distinct `P` give distinct sets (recover `P = (P ∪ ν P) ∩ R`). -/
theorem zeroSum_evenSubsets_antipodal_ge (dom : Fin n ↪ F) (ν : Fin n → Fin n)
    (R : Finset (Fin n)) (j : ℕ)
    (hν : ∀ i ∈ R, dom (ν i) = - dom i) (hνR : ∀ i ∈ R, ν i ∉ R) :
    (R.card).choose j ≤ (((Finset.univ : Finset (Fin n)).powersetCard (2 * j)).filter
        (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  -- ν is injective on R (dom is, and dom ∘ ν = -dom on R)
  have hνinj : Set.InjOn ν R := fun a ha b hb hab => dom.injective (by
    have : (- dom a) = (- dom b) := by rw [← hν a ha, ← hν b hb, hab]
    simpa using this)
  rw [show (R.card).choose j = (R.powersetCard j).card from (Finset.card_powersetCard j R).symm]
  refine Finset.card_le_card_of_injOn (fun P => P ∪ P.image ν) ?_ ?_
  · -- maps a j-subset of R to a zero-sum 2j-subset
    intro P hP
    obtain ⟨hPR, hPcard⟩ := Finset.mem_powersetCard.mp hP
    have hdisj : Disjoint P (P.image ν) := by
      rw [Finset.disjoint_left]
      rintro x hxP hxν
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxν
      exact hνR i (hPR hi) (hPR hxP)
    have himg : (P.image ν).card = j := by
      rw [Finset.card_image_of_injOn (hνinj.mono hPR), hPcard]
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_union_of_disjoint hdisj, hPcard, himg]; ring
    · rw [Finset.sum_union hdisj,
        Finset.sum_image (fun a ha b hb h => hνinj (hPR ha) (hPR hb) h)]
      have hneg : ∑ i ∈ P, dom (ν i) = ∑ i ∈ P, (- dom i) :=
        Finset.sum_congr rfl (fun i hi => hν i (hPR hi))
      rw [hneg, Finset.sum_neg_distrib, add_neg_cancel]
  · -- injective: P = (P ∪ ν P) ∩ R
    have key : ∀ S : Finset (Fin n), S ⊆ R → (S ∪ S.image ν) ∩ R = S := by
      intro S hSR
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hSR]
      have hempty : S.image ν ∩ R = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro x hx
        rw [Finset.mem_inter] at hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx.1
        exact hνR i (hSR hi) hx.2
      rw [hempty, Finset.union_empty]
    intro P hP Q hQ hfPQ
    obtain ⟨hPR, -⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hP)
    obtain ⟨hQR, -⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hQ)
    have hfPQ' : P ∪ P.image ν = Q ∪ Q.image ν := hfPQ
    rw [← key P hPR, ← key Q hQR, hfPQ']

open Classical in
/-- **The even-tower supply growth bound.**  On a negation-closed domain, the deepest-band
supply of `x^{2j}` is at least `C(|R|, j)` — polynomial of degree `j = (k+1)/2` in `n`, hence
`Θ(n^j)` when `|R| = n/2`.  (Combines the antipodal lower bound with the orchard identity at
`k = 2j − 1`.) -/
theorem evenTowerSupply_antipodal_ge (dom : Fin n ↪ F) (ν : Fin n → Fin n)
    (R : Finset (Fin n)) (j : ℕ) (hj : 1 ≤ j)
    (hν : ∀ i ∈ R, dom (ν i) = - dom i) (hνR : ∀ i ∈ R, ν i ∉ R) :
    (R.card).choose j ≤ ((Finset.univ.filter (fun c =>
        c ∈ (rsCode dom (2 * j - 1) : Submodule F (Fin n → F))
          ∧ 2 * j - 1 + 1 ≤ (agreeSet c (fun i => (dom i) ^ (2 * j - 1 + 1))).card))).card := by
  rw [general_orchard_card dom (by omega : 1 ≤ 2 * j - 1), show 2 * j - 1 + 1 = 2 * j from by omega]
  exact zeroSum_evenSubsets_antipodal_ge dom ν R j hν hνR

/-! ## The reach of the bound: tight on prize fields, strict in small characteristic -/

section SmallCharCountermodel

local instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `μ_{10} = F₁₁^×` (the full multiplicative group). -/
def dom10vals : Fin 10 → ZMod 11 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- The evaluation domain `μ_{10} ⊂ F₁₁` as an embedding (injective by `decide`). -/
def dom10 : Fin 10 ↪ ZMod 11 := ⟨dom10vals, by decide⟩

/-- The negation pairing on `μ_{10}`: `ν i = 9 − i` sends index of value `v` to index of `−v`
(`v ↦ 11 − v`); representatives `R = {0,1,2,3,4}` (values `1..5`). -/
def nu10 : Fin 10 → Fin 10 := fun i => 9 - i

set_option maxHeartbeats 8000000 in
/-- The zero-sum-`4`-subset count of `μ_{10} ⊂ F₁₁` is `20`. -/
theorem mu10_F11_zeroSum_quads_eq_twenty :
    (((Finset.univ : Finset (Fin 10)).powersetCard (2 * 2)).filter
        (fun T => ∑ i ∈ T, dom10 i = 0)).card = 20 := by
  decide

/-- The antipodal lower bound holds at `μ_{10}`: `C(|R|, 2) = C(5,2) = 10 ≤ 20`. -/
theorem mu10_antipodal_lower :
    Nat.choose 5 2 ≤ (((Finset.univ : Finset (Fin 10)).powersetCard (2 * 2)).filter
        (fun T => ∑ i ∈ T, dom10 i = 0)).card := by
  have h := zeroSum_evenSubsets_antipodal_ge dom10 nu10 ({0, 1, 2, 3, 4} : Finset (Fin 10)) 2
    (by decide) (by decide)
  rwa [show ({0, 1, 2, 3, 4} : Finset (Fin 10)).card = 5 from by decide] at h

/-- **The antipodal upper bound `C(n/2, 2)` is NOT tight in small characteristic.**  At
`μ_{10} ⊂ F₁₁` the proven lower bound `C(5,2) = 10` is *strict*: the zero-sum-`4`-subset count
is `20`.  The `10` extra quadruples are char-`11` coincidences (e.g. `1+2+3+5 ≡ 0`), not
char-`0` root-of-unity relations — they vanish above the Sidon threshold `n² < p` where every
prize field lives, so the bound becomes an equality there but is a strict lower bound here. -/
theorem antipodal_bound_not_tight :
    Nat.choose 5 2 < (((Finset.univ : Finset (Fin 10)).powersetCard (2 * 2)).filter
        (fun T => ∑ i ∈ T, dom10 i = 0)).card := by
  rw [mu10_F11_zeroSum_quads_eq_twenty]; decide

end SmallCharCountermodel

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.zeroSum_evenSubsets_antipodal_ge
#print axioms ProximityGap.PairRank.evenTowerSupply_antipodal_ge
#print axioms ProximityGap.PairRank.mu10_antipodal_lower
#print axioms ProximityGap.PairRank.antipodal_bound_not_tight
