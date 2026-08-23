/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CubicSupplyExact
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicSupplyBound

/-!
# The smooth cubic-supply capstone (#389): the Sylvester obstruction is sub-quadratic over μ_n

This closes the additive-face arc into one literal statement about the cubic word's
δ*-supply.  Combining `cubicSupply_eq_sumZeroCard` (`CubicSupplyExact`), the bridge
`sumZeroCard_le_zeroSumTriples_image` (here), and `zeroSumTriples_pow_le_of_gvRepBound`
(`SmoothCubicSupplyBound`) gives **`cubicSupply_pow_le_of_gvRepBound`**: over any domain
whose image is a smooth set satisfying the named Garcia–Voloch input, the cubic word's
explainable-3-core count `S` obeys `S⁶ ≤ 260·n¹¹`, i.e. `S < 2.54·n^{11/6} ≪ n²`.

The Sylvester cubic — the worst-case sub-Johnson *additive* obstruction, `Θ(n²)` on the
full field — contributes only `n^{11/6}` to the supply over a multiplicative subgroup,
conditional only on the one open subgroup sum-product input.  (`CubicSupplyZeroNTT.lean`
evaluates the count to `0` at `μ_16 ⊂ F₂₅₇`; this is the general law it instantiates.)
-/

open Finset

namespace ProximityGap.Cubic

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] in
/-- `zeroSumTriples G` as ordered pairs with the third element forced:
`#{(c, y) ∈ G² : −c−y ∈ G}` (each `c` contributes `repCount G (−c)` by definition). -/
theorem zeroSumTriples_eq_pairCard (G : Finset F) :
    zeroSumTriples G
      = ((G ×ˢ G).filter (fun p => -p.1 - p.2 ∈ G)).card := by
  classical
  rw [zeroSumTriples, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [repCount, Finset.card_filter]

/-- The canonical ordered pair extracted from a finset: `(dom of the two smallest
elements)`, with a junk fallback off the 3-subsets.  On a 3-element `T` it returns
`(dom T.min', dom (second smallest))`. -/
noncomputable def corePair (dom : Fin n ↪ F) (T : Finset (Fin n)) : F × F :=
  if h : 2 ≤ T.card then
    have h1 : T.Nonempty := Finset.card_pos.mp (by omega)
    have h2 : (T.erase (T.min' h1)).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (T.min'_mem h1)]; omega)
    (dom (T.min' h1), dom ((T.erase (T.min' h1)).min' h2))
  else (dom ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, dom ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)

omit [Fintype F] in
/-- **The bridge**: the sum-zero domain 3-subset count is at most the ordered Sylvester
count of the image.  The canonical pair `(dom a, dom b)` of the two smallest elements
`a < b` of a zero-sum triple `T = {a, b, c}` lands in the pair-set (third value
`dom c = −dom a − dom b ∈ G`), and the zero-sum condition recovers `c`, hence `T`, from
the pair — injectivity. -/
theorem sumZeroCard_le_zeroSumTriples_image (dom : Fin n ↪ F) :
    ((Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0)).card
      ≤ zeroSumTriples (Finset.image dom Finset.univ) := by
  classical
  rw [zeroSumTriples_eq_pairCard]
  set G : Finset F := Finset.image dom Finset.univ with hG
  have hmemG : ∀ i : Fin n, dom i ∈ G := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  -- decompose a 3-subset into its two smallest + the third
  have hdecomp : ∀ T ∈ (Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0),
      ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ T = {a, b, c} ∧
        corePair dom T = (dom a, dom b) ∧ dom a + dom b + dom c = 0 := by
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨-, hTcard⟩, hsum⟩ := hT
    have h1 : T.Nonempty := Finset.card_pos.mp (by omega)
    set a := T.min' h1 with ha
    have ham : a ∈ T := T.min'_mem h1
    have h2 : (T.erase a).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ham]; omega)
    set b := (T.erase a).min' h2 with hb
    have hbm : b ∈ T.erase a := (T.erase a).min'_mem h2
    have hbmT : b ∈ T := Finset.mem_of_mem_erase hbm
    have hab : a ≠ b := (Finset.ne_of_mem_erase hbm).symm
    set Tc := (T.erase a).erase b with hTc
    have h3 : Tc.Nonempty := Finset.card_pos.mp (by
      rw [hTc, Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem ham]; omega)
    set c := Tc.min' h3 with hc
    have hcm : c ∈ Tc := Tc.min'_mem h3
    have hcT : c ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcm)
    have hbc : b ≠ c := (Finset.ne_of_mem_erase hcm).symm
    have hac : a ≠ c := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcm)).symm
    have hsub : T ⊆ {a, b, c} := by
      intro x hx
      by_cases hxa : x = a
      · simp [hxa]
      · have hxe : x ∈ T.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        by_cases hxb : x = b
        · simp [hxb]
        · have hxc' : x ∈ Tc := Finset.mem_erase.mpr ⟨hxb, hxe⟩
          have hTc1 : Tc.card = 1 := by
            rw [hTc, Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem ham]; omega
          have hxc : x = c := Finset.card_le_one.mp (le_of_eq hTc1) x hxc' c hcm
          simp [hxc]
    have hcard3 : ({a, b, c} : Finset (Fin n)).card = 3 :=
      Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    have hTeq : T = {a, b, c} :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hcard3, hTcard]))
    have hcorePair : corePair dom T = (dom a, dom b) := by
      rw [corePair, dif_pos (by omega : 2 ≤ T.card)]
    have hsum3 : dom a + dom b + dom c = 0 := by
      have hs : ∑ i ∈ ({a, b, c} : Finset (Fin n)), dom i = 0 := hTeq ▸ hsum
      rw [Finset.sum_insert (by simp [hab, hac]),
        Finset.sum_insert (by simp [hbc]), Finset.sum_singleton] at hs
      linear_combination hs
    exact ⟨a, b, c, hab, hac, hbc, hTeq, hcorePair, hsum3⟩
  refine Finset.card_le_card_of_injOn (corePair dom) ?_ ?_
  · intro T hT
    obtain ⟨a, b, c, hab, hac, hbc, hTeq, hcp, hsum3⟩ := hdecomp T (Finset.mem_coe.mp hT)
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, hcp]
    refine ⟨⟨hmemG a, hmemG b⟩, ?_⟩
    have hthird : -(dom a) - dom b = dom c := by linear_combination -hsum3
    rw [hthird]; exact hmemG c
  · intro T hT T' hT' heq
    obtain ⟨a, b, c, hab, hac, hbc, hTeq, hcp, hsum3⟩ := hdecomp T (Finset.mem_coe.mp hT)
    obtain ⟨a', b', c', hab', hac', hbc', hTeq', hcp', hsum3'⟩ :=
      hdecomp T' (Finset.mem_coe.mp hT')
    rw [hcp, hcp'] at heq
    obtain ⟨haa, hbb⟩ := Prod.mk.injEq .. ▸ heq
    have ha : a = a' := dom.injective haa
    have hb : b = b' := dom.injective hbb
    have hc : c = c' := by
      apply dom.injective
      have e1 : dom c = -(dom a) - dom b := by linear_combination hsum3
      have e2 : dom c' = -(dom a') - dom b' := by linear_combination hsum3'
      rw [e1, e2, ha, hb]
    rw [hTeq, hTeq', ha, hb, hc]

open Classical in
/-- **The capstone**: over any domain whose image is a smooth set satisfying the named
Garcia–Voloch input, the cubic word's explainable-3-core count `S` obeys `S⁶ ≤ 260·n¹¹`
— `S < 2.54·n^{11/6} ≪ n²`.  The Sylvester additive obstruction is sub-quadratic over μ_n,
conditional only on the one open subgroup sum-product input. -/
theorem cubicSupply_pow_le_of_gvRepBound (dom : Fin n ↪ F) {M : ℕ}
    (h : GVRepBound (Finset.image dom Finset.univ) M) :
    (((Finset.univ.powersetCard 3).filter
        (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card) ^ 6
      ≤ 260 * n ^ 11 := by
  rw [cubicSupply_eq_sumZeroCard]
  have hcard : (Finset.image dom Finset.univ).card = n := by
    rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ, Fintype.card_fin]
  calc (((Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0)).card) ^ 6
      ≤ (zeroSumTriples (Finset.image dom Finset.univ)) ^ 6 := by
        apply Nat.pow_le_pow_left (sumZeroCard_le_zeroSumTriples_image dom)
    _ ≤ 260 * (Finset.image dom Finset.univ).card ^ 11 :=
        zeroSumTriples_pow_le_of_gvRepBound _ h
    _ = 260 * n ^ 11 := by rw [hcard]

end ProximityGap.Cubic
