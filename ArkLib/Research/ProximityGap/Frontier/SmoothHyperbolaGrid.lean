/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HyperbolaRulings
import ArkLib.Research.ProximityGap.Frontier.SixteenFiberMass
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # A six-head MCA ceiling on all multiplicative cosets of length sixteen times s -/

set_option autoImplicit false
open Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothHyperbolaGrid
open _root_.ProximityGap
open HyperbolaRulings (group owner)

private def cut (s : ℕ) (j : Fin 16) : ℕ :=
  if j.val < 9 then 0 else if j.val = 15 then s - 2 else s

private theorem cut_le (s : ℕ) (j : Fin 16) : cut s j ≤ s := by
  unfold cut
  split_ifs <;> omega

private noncomputable abbrev core (s : ℕ) := SixteenFiberMass.core s (cut s) group
private noncomputable abbrev roots (s : ℕ) := SixteenFiberMass.roots s (cut s)

private theorem roots_card (s : ℕ) (hs : 2 ≤ s) : (roots s).card = 7*s-2 := by
  rw [roots, SixteenFiberMass.card_roots s (cut s) (cut_le s)]
  simp [Fin.sum_univ_succ, cut]
  omega

private theorem core_card (s : ℕ) (hs : 2 ≤ s) (i : Fin 6) :
    (core s i).card = if i = 0 then 10*s else 10*s-2 := by
  rw [core, SixteenFiberMass.card_core s (cut s) group (cut_le s)]
  fin_cases i <;> simp [Fin.sum_univ_succ, group, cut] <;> omega

/-- At 6s+1 errors on a length-16s ordered multiplicative coset, one received pair has
36s+10 bad scalars whenever the field separates that many labels. This includes the
half-rate dimension 8s and all positive interleaving widths. -/
theorem mass {F : Type} [Field F] [Fintype F] {s k : ℕ} (hs : 2 ≤ s)
    (D : Fin (16*s) ↪ F) (u g : F) (hu : u ≠ 0) (hg : orderOf g = 16*s)
    (hd : ∀ i, D i = u*g^i.val) (hk : 8*s ≤ k) (hc : k ≤ 10*s-2)
    (hf : (36*s+10).choose 2 ≤ Nat.card F) (width : ℕ) [NeZero width] :
    ((36*s+10 : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) ((ReedSolomon.code D k : Set (Fin (16*s) → F)) ^⋈ (Fin width))
        (((6*s+1 : ℕ) : ℝ≥0) / (16*s : ℕ)) := by
  classical
  let : NeZero s := ⟨by omega⟩
  let w := g^s
  have hw : orderOf w = 16 := by
    change orderOf (g^s) = 16
    rw [orderOf_pow_of_dvd (by omega : s ≠ 0) (hg ▸ dvd_mul_left s 16), hg]
    exact Nat.mul_div_cancel _ (by omega)
  have congr (c : Bool) (i : Fin 6) (z : SixteenFiberMass.Grid s) :
      (HyperbolaRulings.poly s w u⁻¹ c i).eval (D (SixteenFiberMass.index s z)) =
        HyperbolaRulings.value w c i z.1 :=
    HyperbolaRulings.eval s hw c i z.1 (SixteenFiberMass.power s D u g hu hg hd z)
  have counts : (∑ i, (core s i)ᶜ.card) = 36*s+10 := by
    simp only [card_compl, core_card s hs, Fintype.card_fin, Fin.sum_univ_succ]
    simp
    omega
  rw [epsMCA_interleaved_eq, ← counts]
  apply SixteenFiberMass.mass s (cut s) group owner D k s _
    (HyperbolaRulings.poly s w u⁻¹ false) (HyperbolaRulings.poly s w u⁻¹ true)
    (HyperbolaRulings.value w false) (HyperbolaRulings.value w true)
    (congr false) (congr true) (HyperbolaRulings.agrees w) (HyperbolaRulings.misses hw)
    (HyperbolaRulings.separated hw)
  · change (roots s).card + s + 1 < k
    rw [roots_card s hs]
    omega
  · exact HyperbolaRulings.degree s w u⁻¹ false
  · exact HyperbolaRulings.degree s w u⁻¹ true
  · intro i
    change k ≤ (core s i).card
    rw [core_card s hs]
    split_ifs <;> omega
  · intro i
    rw [Fintype.card_fin]
    have hn : (16*s : ℕ) ≠ 0 := by omega
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by exact_mod_cast hn)]
    change _ ≤ (((core s i).card + 1 : ℕ) : ℝ≥0)
    have card : 16*s ≤ (core s i).card + 1 + (6*s+1) := by
      rw [core_card s hs]
      split_ifs <;> omega
    exact tsub_le_iff_right.mpr (by exact_mod_cast card)
  · simpa only [← counts] using hf

/-- Every smooth domain admits the construction, for any ordering of its coordinates. -/
theorem smooth_mass {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I]
    {s k : ℕ} (hs : 2 ≤ s) (D : I ↪ F) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = 16*s) (hk : 8*s ≤ k) (hc : k ≤ 10*s-2)
    (hf : (36*s+10).choose 2 ≤ Nat.card F) (width : ℕ) [NeZero width] :
    ((36*s+10 : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width))
        (((6*s+1 : ℕ) : ℝ≥0) / (16*s : ℕ)) := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  let _ : NeZero (16*s) := ⟨by omega⟩
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨sites,hsite⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let : Fintype H := Fintype.ofEquiv I sites
  have card : Nat.card H = 16*s := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr sites, hn]
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have ho : orderOf g = 16*s := hg.trans card
  have hfield : orderOf ((g.val : Fˣ) : F) = 16*s := by
    rwa [orderOf_units, Subgroup.orderOf_coe]
  let powers : Fin (16*s) ≃ H := Equiv.ofBijective (fun j => g^j.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i j hij => Fin.ext ((IsPrimitiveRoot.iff_orderOf.mpr ho).pow_inj i.isLt j.isLt hij),
        by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card]⟩)
  let e := powers.trans sites.symm
  let E := e.toEmbedding.trans D
  have he (i : Fin (16*s)) : E i = (ReedSolomon.Smooth.a D : F) * (g.val : F)^i.val := by
    change D (sites.symm (powers i)) = _
    rw [hsite, sites.apply_symm_apply]
    rfl
  have hcode (w : I → F) : w ∘ e ∈ ReedSolomon.code E k ↔ w ∈ ReedSolomon.code D k := by
    simp only [ReedSolomon.mem_code_iff_eval]
    constructor
    · rintro ⟨P,hP,heval⟩
      exact ⟨P,hP,fun i => by simpa [E,Function.comp_def] using heval (e.symm i)⟩
    · rintro ⟨P,hP,heval⟩
      exact ⟨P,hP,fun i => heval (e i)⟩
  have hm := mass hs E _ _ (ReedSolomon.Smooth.a D).ne_zero hfield he hk hc hf width
  rw [epsMCA_interleaved_eq, epsMCA_eq_mcaError] at hm ⊢
  rwa [CoreDefinitions.mcaError_comp_equiv _ _ _ e hcode] at hm

/-- Budgets below the six-head population fail by the indicated radius on every smooth
domain. The denominator Q permits any positive reciprocal-integer error tolerance. -/
theorem ceiling {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I]
    {s k Q : ℕ} (hs : 2 ≤ s) (D : I ↪ F) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = 16*s) (hk : 8*s ≤ k) (hc : k ≤ 10*s-2)
    (hf : (36*s+10).choose 2 ≤ Nat.card F) (hQ : 0 < Q)
    (hb : Fintype.card F / Q < 36*s+10) (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width))
    let radius := (((6*s+1 : ℕ) : ℝ≥0) / (16*s : ℕ))
    (1 : ℝ≥0∞)/Q < epsMCA (F := F) code radius ∧
      MCAThresholdLedger.mcaDeltaStar (F := F) code (1/Q) ≤ radius := by
  dsimp only
  have bad := (lt_of_not_ge (fun h =>
    (Nat.not_le.mpr hb) ((BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ).mp h))).trans_le
    (smooth_mass hs D hn hk hc hf width)
  exact ⟨bad, MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ bad⟩

/-- At production length this single 128-bit radius certificate covers the full
field window up to the six-head population, for prime fields and extensions. -/
theorem production_half {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I]
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 2^30)
    (hf : 2^128 ≤ Fintype.card F) (hb : Fintype.card F / 2^128 < 2415919114)
    (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code D 536870912 : Set (I → F)) ^⋈ (Fin width))
    (1 : ℝ≥0∞)/(2:ℝ≥0∞)^128 < epsMCA (F := F) code (402653185/1073741824) ∧
      MCAThresholdLedger.mcaDeltaStar (F := F) code (1/(2:ℝ≥0∞)^128) ≤ 402653185/1073741824 := by
  have h := ceiling (s := 67108864) (k := 536870912) (Q := 2^128)
    (by decide) D hn (by decide) (by decide)
    (by rw [Nat.card_eq_fintype_card]; exact le_trans (by rw [Nat.choose_two_right]; decide) hf)
    (by decide) hb width
  simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_pow, Nat.cast_ofNat] using h

#print axioms production_half
#print axioms smooth_mass
#print axioms ceiling

#print axioms mass
end ArkLib.ProximityGap.Frontier.SmoothHyperbolaGrid
