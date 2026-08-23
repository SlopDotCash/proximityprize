/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FoldedSumThreshold

/-!
# The depth-2 engine: the folded `e₃` statistic and its two-layer threshold

Campaign #357. The depth-2 census rows (`k = a − 3`) require BOTH `e₂(A) = 0` and
`e₃(A) = 0`. The `e₂` half is the landed `WindowTwoLayerThreshold` machinery; this file
supplies the `e₃` half as an **instantiation of the generic folded-sum engine**
(`FoldedSumThreshold`) over the triple family:

* `upperTriples A` — the strictly-increasing triples of an exponent set;
* `e3FoldedSum m A` — the folded `e₃` statistic, with **faithfulness, the `ℓ¹` bound and
  the two-layer threshold all inherited from the generic engine for free**:
  `e3_vanishing_iff_char0` — above `(2^(m−1)·|A|³)^(2^(m−1))`, the triple-power sum
  `∑_{i<j<k} g^(i+j+k)` vanishes mod `p` iff the folded polynomial vanishes in
  characteristic zero;
* `coeff_prod_X_sub_C_sub_three` — the Vieta bridge: the coefficient of the vanishing
  polynomial at degree `|A| − 3` is `−e₃` (the triple-Vieta sign), connecting the engine
  to `ConstrainedBandZero` at depth 2 exactly as the pair bridge did at depth 1.

Together with the `e₂` engine this is the complete depth-2 two-layer transfer: the
depth-2 census is characteristic-zero (the intersection of the two folded conditions)
at every prime above the larger threshold — the engine the O140/O141 depth-2 death-radius
measurements call for.

## References

* Probes O139–O141 (`DISPROOF_LOG`); issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

/-! ## The triple family -/

/-- The strictly-increasing triples of an exponent set. -/
def upperTriples (A : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((A ×ˢ A) ×ˢ A).image (fun q => (q.1.1, q.1.2, q.2)) |>.filter
    (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

theorem mem_upperTriples {A : Finset ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ upperTriples A ↔
      t.1 ∈ A ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
  unfold upperTriples
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨q, ⟨⟨h1, h2⟩, h3⟩, rfl⟩, hlt1, hlt2⟩
    exact ⟨h1, h2, h3, hlt1, hlt2⟩
  · rintro ⟨h1, h2, h3, hlt1, hlt2⟩
    exact ⟨⟨((t.1, t.2.1), t.2.2), ⟨⟨h1, h2⟩, h3⟩, rfl⟩, hlt1, hlt2⟩

/-! ## The depth-2 folded statistic, by instantiation -/

/-- The folded `e₃` statistic: the generic engine over the triple family with unit
weights. Faithfulness, the `ℓ¹` bound, and the two-layer threshold are inherited. -/
noncomputable def e3FoldedSum (m : ℕ) (A : Finset ℕ) : Polynomial ℤ :=
  foldedSum m (upperTriples A) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1)

/-- **The depth-2 two-layer law** (inherited from the generic engine): above the explicit
threshold, the triple-power sum vanishes mod `p` iff the folded `e₃` polynomial vanishes
in characteristic zero. -/
theorem e3_vanishing_iff_char0 {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (A : Finset ℕ)
    (hp : (2 ^ (m - 1) * l1Weight (upperTriples A) (fun _ => 1)) ^ 2 ^ (m - 1) < p) :
    ∑ t ∈ upperTriples A, g ^ (t.1 + t.2.1 + t.2.2) = 0 ↔ e3FoldedSum m A = 0 := by
  have h := foldedSum_vanishing_iff_char0 hm hg (upperTriples A)
    (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1) hp
  simpa using h

/-- The `ℓ¹` weight of the triple family is its cardinality, at most `|A|³`. -/
theorem l1Weight_upperTriples (A : Finset ℕ) :
    l1Weight (upperTriples A) (fun _ => 1) = (upperTriples A).card := by
  unfold l1Weight
  simp

theorem upperTriples_card_le (A : Finset ℕ) :
    (upperTriples A).card ≤ A.card * A.card * A.card := by
  calc (upperTriples A).card
      ≤ (((A ×ˢ A) ×ˢ A).image (fun q => (q.1.1, q.1.2, q.2))).card :=
        Finset.card_filter_le _ _
    _ ≤ ((A ×ˢ A) ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card * A.card := by
        rw [Finset.card_product, Finset.card_product]

/-! ## The triple-Vieta bridge -/

/-- Summing a product over 3-element subsets equals summing over strictly-ordered
triples. -/
theorem sum_powersetCard_three_eq {R : Type*} [CommRing R] (A : Finset ℕ) (f : ℕ → R) :
    ∑ s ∈ A.powersetCard 3, ∏ i ∈ s, f i
      = ∑ t ∈ upperTriples A, f t.1 * f t.2.1 * f t.2.2 := by
  classical
  symm
  refine Finset.sum_nbij (fun t => ({t.1, t.2.1, t.2.2} : Finset ℕ)) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨h1, h2, h3, hlt1, hlt2⟩ := mem_upperTriples.mp ht
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          omega),
        Finset.card_singleton]
  · intro t ht t' ht' heq
    have h := mem_upperTriples.mp (Finset.mem_coe.mp ht)
    have h' := mem_upperTriples.mp (Finset.mem_coe.mp ht')
    have heq' : ({t.1, t.2.1, t.2.2} : Finset ℕ) = {t'.1, t'.2.1, t'.2.2} := heq
    have hmem : ∀ x, x ∈ ({t.1, t.2.1, t.2.2} : Finset ℕ)
        ↔ x ∈ ({t'.1, t'.2.1, t'.2.2} : Finset ℕ) := fun x => by rw [heq']
    have e1 := (hmem t.1).mp (by simp)
    have e2 := (hmem t.2.1).mp (by simp)
    have e3 := (hmem t.2.2).mp (by simp)
    have f1 := (hmem t'.1).mpr (by simp)
    have f2 := (hmem t'.2.1).mpr (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at e1 e2 e3 f1 f2
    obtain ⟨-, -, -, hlt1, hlt2⟩ := h
    obtain ⟨-, -, -, hlt1', hlt2'⟩ := h'
    have : t.1 = t'.1 ∧ t.2.1 = t'.2.1 ∧ t.2.2 = t'.2.2 := by omega
    obtain ⟨g1, g2, g3⟩ := this
    exact Prod.ext g1 (Prod.ext g2 g3)
  · intro s hs
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hs)
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
    -- order the three elements
    rcases Nat.lt_trichotomy x y with h1 | h1 | h1
    · rcases Nat.lt_trichotomy y z with h2 | h2 | h2
      · exact ⟨(x, y, z), Finset.mem_coe.mpr (mem_upperTriples.mpr
          ⟨hsub (by simp), hsub (by simp), hsub (by simp), h1, h2⟩), rfl⟩
      · omega
      · rcases Nat.lt_trichotomy x z with h3 | h3 | h3
        · exact ⟨(x, z, y), Finset.mem_coe.mpr (mem_upperTriples.mpr
            ⟨hsub (by simp), hsub (by simp), hsub (by simp), h3, h2⟩), by
            ext w
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega⟩
        · omega
        · exact ⟨(z, x, y), Finset.mem_coe.mpr (mem_upperTriples.mpr
            ⟨hsub (by simp), hsub (by simp), hsub (by simp), h3, h1⟩), by
            ext w
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega⟩
    · omega
    · rcases Nat.lt_trichotomy x z with h2 | h2 | h2
      · exact ⟨(y, x, z), Finset.mem_coe.mpr (mem_upperTriples.mpr
          ⟨hsub (by simp), hsub (by simp), hsub (by simp), h1, h2⟩), by
          ext w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega⟩
      · omega
      · rcases Nat.lt_trichotomy y z with h3 | h3 | h3
        · exact ⟨(y, z, x), Finset.mem_coe.mpr (mem_upperTriples.mpr
            ⟨hsub (by simp), hsub (by simp), hsub (by simp), h3, h2⟩), by
            ext w
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega⟩
        · omega
        · exact ⟨(z, y, x), Finset.mem_coe.mpr (mem_upperTriples.mpr
            ⟨hsub (by simp), hsub (by simp), hsub (by simp), h3, h1⟩), by
            ext w
            simp only [Finset.mem_insert, Finset.mem_singleton]
            omega⟩
  · intro t ht
    have h := mem_upperTriples.mp (Finset.mem_coe.mp ht)
    obtain ⟨-, -, -, hlt1, hlt2⟩ := h
    rw [Finset.prod_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega),
      Finset.prod_insert (by
        simp only [Finset.mem_singleton]
        omega),
      Finset.prod_singleton, mul_assoc]

/-- **The triple-Vieta bridge**: the coefficient of the vanishing polynomial at degree
`|A| − 3` is minus the triple sum (the depth-2 face of `ConstrainedBandZero`). -/
theorem coeff_prod_X_sub_C_sub_three {R : Type*} [CommRing R] (A : Finset ℕ) (f : ℕ → R)
    (ha : 3 ≤ A.card) :
    (∏ i ∈ A, (X - C (f i))).coeff (A.card - 3)
      = -∑ t ∈ upperTriples A, f t.1 * f t.2.1 * f t.2.2 := by
  have hcard : Multiset.card (A.val.map f) = A.card := by simp
  have hk : A.card - 3 ≤ Multiset.card (A.val.map f) := by rw [hcard]; omega
  have h1 : ∏ i ∈ A, (X - C (f i)) = ((A.val.map f).map (fun t => X - C t)).prod := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    rfl
  have h2 : Multiset.card (A.val.map f) - (A.card - 3) = 3 := by rw [hcard]; omega
  rw [h1, Multiset.prod_X_sub_C_coeff _ hk, h2, Finset.esymm_map_val,
    sum_powersetCard_three_eq A f]
  have : ((-1 : R) ^ 3) = -1 := by ring
  rw [this]
  ring

/-! ## Source audit -/

#print axioms mem_upperTriples
#print axioms e3_vanishing_iff_char0
#print axioms sum_powersetCard_three_eq
#print axioms coeff_prod_X_sub_C_sub_three

end ArkLib.ProximityGap.WindowTwoLayer
