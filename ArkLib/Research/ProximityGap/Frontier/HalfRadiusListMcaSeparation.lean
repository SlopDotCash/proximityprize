/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeWordAgreement
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import ArkLib.Research.ProximityGap.Frontier.RateHalfRichHeadCensus
import ArkLib.Research.ProximityGap.Frontier._PackingBudgetFirstJump
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap

/-! # An exact worst-center list at the first prime's half-radius MCA failure

Two constant codewords fit a common ball at radius one half on any even domain.
If the dimension is below the three-word intersection bound, every list has at
most two words. On the first nominated prime this includes the first MCA
failure step for rates one eighth and one sixteenth.
-/

namespace ProximityGap.HalfRadiusListMcaSeparation

open Code Finset
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]

omit [Fintype F] in
/-- On an even-length evaluation domain, a radius-one-half ball contains both
the zero and the one codeword whenever the dimension and width are positive. -/
theorem two_le_half (D : I ↪ F) {k m h : ℕ} [NeZero k] (hm : 0 < m)
    (hn : Fintype.card I = h+h) :
    2 ≤ Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) (1/2) := by
  classical
  let C := (ReedSolomon.code D k : Set (I → F))
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (univ : Finset I)) (n := h) (by rw [card_univ, hn]; omega)
  let c (a : F) : I → F := fun _ => a
  let y (i : I) : F := if i ∈ S then 0 else 1
  have hc (a : F) : c a ∈ C := ReedSolomon.constantCode_mem_code
  have hag0 : agree (c 0) y = h := by
    change (univ.filter fun i => (0 : F) = if i ∈ S then 0 else 1).card = h
    simpa using hS
  have hag1 : agree (c 1) y = h := by
    change (univ.filter fun i => (1 : F) = if i ∈ S then 0 else 1).card = h
    have he : (univ.filter fun i => (1 : F) = if i ∈ S then 0 else 1) = Sᶜ := by
      ext i
      by_cases hi : i ∈ S <;> simp [hi]
    rw [he, card_compl, hn, hS]; omega
  have hne : c 0 ≠ c 1 := fun hh => zero_ne_one (congrFun hh (Classical.choice ‹Nonempty I›))
  have hsub : ({c 0, c 1} : Set (I → F)) ⊆ {w | w ∈ C ∧ h ≤ agree w y} := by
    rintro w (rfl | hw)
    · exact ⟨hc 0, hag0.ge⟩
    · have he : w = c 1 := hw
      exact he ▸ ⟨hc 1, hag1.ge⟩
  have hl := (Set.encard_le_encard hsub).trans (encard_setOf_le_agree_le_Lambda C y h)
  have hr : 1-(h : ℝ)/Fintype.card I = 1/2 := by
    have hn' : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have he : (Fintype.card I : ℝ) = h+h := by exact_mod_cast hn
    field_simp
    linarith
  rw [Set.encard_pair hne, hr] at hl
  exact hl.trans (Lambda_le_of_injective_comp (C := C)
    (D := interleavedCodeSet (κ := Fin m) C)
    (e := fun (a : F) (_ : Fin m) => a) (fun _ _ hh => congrFun hh ⟨0, hm⟩)
    (fun _ hw _ => hw) _)

/-- Exact worst-center list cardinality at half radius on arbitrary even
domains. The field, center, domain, and positive interleaving width are unrestricted. -/
theorem half_eq_two (D : I ↪ F) {k m h : ℕ} [NeZero k] (hm : 0 < m)
    (hn : Fintype.card I = h+h) (hdegree : 3*(k-1) < h) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) (1/2) = 2 := by
  apply le_antisymm _ (two_le_half D hm hn)
  apply ThreeWordAgreement.interleaved_list_le_two D k m h _
  · rw [hn]
    push_cast
    linarith
  · exact Or.inr (by omega)

omit [Fintype F] in
/-- Passing the integer multiplicity test for even one list of size B+1 would
be necessary for the actual interleaved worst-center list to exceed B. -/
theorem list_le_of_integer_incidences (D : I ↪ F) (k t m B a : ℕ) (δ : ℝ)
    (hδ : δ * Fintype.card I < (Fintype.card I : ℝ)-t+1)
    (hcap : (B+1)*B*(k-1)+a*(a+1)*Fintype.card I < 2*a*((B+1)*t)) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤ B := by
  classical
  apply InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound D k t m B δ hδ
  intro s S hs hp
  by_contra! hlarge
  let e (i : Fin (B+1)) := i.castLE (show B+1 ≤ s by omega)
  have he : Function.Injective e := fun i j h => Fin.ext (congrArg (fun x : Fin s => x.val) h)
  have h := RateHalfRichHeadCensus.incidence_bound (fun i => S (e i)) (fun i => (hs _).ge)
    (fun _ _ hne => hp (he.ne hne)) a
  exact (not_le_of_gt hcap) (by simpa only [Nat.add_sub_cancel] using h)

omit [Fintype F] in
/-- The two higher prize rates have small worst-center lists at the first
prime's certified MCA-failure witnesses, on every domain over any field. -/
theorem higher_rate_caps (D : Fin 1073741824 ↪ F) (m : ℕ) :
    InterleavedListJohnsonRank.AtErrors D m 536870912 313174699 118 ∧
    InterleavedListJohnsonRank.AtErrors D m 268435456 480946859 4 := by
  constructor
  · exact list_le_of_integer_incidences D 536870912 760567125 m 118 84
      ((313174699 : ℝ)/1073741824) (by rw [Fintype.card_fin]; norm_num)
      (by rw [Fintype.card_fin]; decide)
  · exact list_le_of_integer_incidences D 268435456 592794965 m 4 2
      ((480946859 : ℝ)/1073741824) (by rw [Fintype.card_fin]; norm_num)
      (by rw [Fintype.card_fin]; decide)

#print axioms higher_rate_caps

open ArkLib.ProximityGap
local instance : Fact (Nat.Prime PrizeShapePrimeP30.P) := ⟨PrizeShapePrimeP30.prime_P⟩

/-- The nominated length-2³⁰ power domain from its certified generator. -/
noncomputable abbrev productionDomain :=
  KKH26RegimeSplit.powDomain PrizeShapePrimeP30.g PrizeShapePrimeP30.orderOf_g
    (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30.orderOf_g)

/-- At both low prize rates in the first nominated prime, the worst list
contains exactly two codewords at the step which violates the MCA tolerance. -/
theorem first_prime (k m : ℕ) (hk : k = 2^27 ∨ k = 2^26) (hm : 0 < m) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code productionDomain k :
      Set (Fin (2^30) → ZMod PrizeShapePrimeP30.P))) (1/2) = 2 ∧
    ((2^128 : ℝ≥0∞)⁻¹) < epsMCA (F := ZMod PrizeShapePrimeP30.P)
      (ReedSolomon.code productionDomain k : Set (Fin (2^30) → ZMod PrizeShapePrimeP30.P)) (1/2) := by
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl <;> decide
  let _ : NeZero k := ⟨by omega⟩
  constructor
  · apply half_eq_two productionDomain hm (h := 2^29) (by simp)
    rcases hk with rfl | rfl <;> decide
  · have hl := PackingBudgetFirstJump.inv_lt_epsMCA_half_of_floor_eq_length
      (k := k) PrizeShapePrimeP30.orderOf_g (Q := 2^128) (by decide) hk2 (by decide)
      PrizeShapePrimeP30.P_div_two_pow_128 (by rcases hk with rfl | rfl <;> decide) (by decide)
    rw [KKH26RegimeSplit.evalCode_eq_reedSolomon _ PrizeShapePrimeP30.orderOf_g
      (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30.orderOf_g),
      show k-1+1 = k by omega] at hl
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hl

#print axioms half_eq_two
#print axioms first_prime

end ProximityGap.HalfRadiusListMcaSeparation
