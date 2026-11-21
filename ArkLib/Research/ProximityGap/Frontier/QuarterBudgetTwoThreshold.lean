/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Research.ProximityGap.Frontier.ReservedFiberList
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# An exact rate-half list threshold over a 130-bit prime field

For every positive interleaving width and every real radius, the closed-ball list
size passes the two-word budget precisely below the first grid radius at
268435457 errors. The chosen field size makes two words the exact integer
budget for 128 bits of security.
-/

namespace ProximityGap.QuarterBudgetTwoThreshold

open Code ReservedFiberList GrandChallenges
open scoped NNReal ENNReal
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

set_option maxRecDepth 100000

/-- The modulus of the budget-two example. -/
abbrev p : ℕ := 680564733906249808969588989158290882561

private theorem prime_factor : Nat.Prime 9162596899 := by
  let q := 9162596899
  have hpow : (2 : ZMod q) ^ (q - 1) = 1 := by rw [← binaryPow_eq_pow]; decide
  apply lucas_primality q 2 hpow
  intro v hv hdvd
  rw [show q - 1 = 2 * (3 * (3 * (7 * (13 * (19 * (37 * (73 * 109))))))) by decide] at hdvd
  simp only [hv.dvd_mul, Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 73),
    Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 109)] at hdvd
  rcases hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [← binaryPow_eq_pow] <;> decide

/-- A Lucas certificate at the concrete prime. -/
theorem prime_p : Nat.Prime p := by
  have hpow : (7 : ZMod p) ^ (p - 1) = 1 := by rw [← binaryPow_eq_pow]; decide
  apply lucas_primality p 7 hpow
  intro v hv hdvd
  rw [show p - 1 = 2^92 * (3 * (5 * 9162596899)) by decide] at hdvd
  rcases hv.dvd_mul.mp hdvd with htwo | hodd
  · have h := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow htwo)
    subst v
    rw [← binaryPow_eq_pow]
    decide
  · simp only [hv.dvd_mul, Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hv prime_factor] at hodd
    rcases hodd with rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

instance : Fact (Nat.Prime p) := ⟨prime_p⟩

private abbrev g : ZMod p := 249631592359537775319900728087975376651

/-- The generator as a unit of the field. -/
def generator : (ZMod p)ˣ := Units.mk0 g (by decide)

private theorem generator_order : orderOf generator = 268435456 * 4 := by
  have hhalf : g ^ ((2 : ℕ)^29) ≠ 1 := by rw [← binaryPow_eq_pow]; decide
  have hfull : g ^ ((2 : ℕ)^30) = 1 := by rw [← binaryPow_eq_pow]; decide
  rw [← orderOf_units]
  exact orderOf_eq_prime_pow (x := g) hhalf hfull

/-- Indexing by the four fibers of the subgroup power map. -/
abbrev Coord := Fin 4 × Fin 268435456

/-- The smooth domain has 2^30 points and the code dimension is 2^29. -/
def domain : Coord ↪ ZMod p := cyclicDomain generator generator_order

/-- The evaluation points are exactly the order-`2^30` cyclic subgroup. -/
noncomputable instance smoothDomain : ReedSolomon.Smooth domain where
  H := Subgroup.zpowers generator
  a := 1
  h_card_pow2 := ⟨30, by norm_num [Coord, Fintype.card_prod]⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
      let t := (finProdFinEquiv (ij.2, ij.1)).val
      exact ⟨generator ^ t, Subgroup.npow_mem_zpowers _ _, by change 1 * _ = _; exact one_mul _⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv)
      let T : Fin (268435456 * 4) := ⟨t, generator_order ▸ Finset.mem_range.mp ht⟩
      let ij := finProdFinEquiv.symm T
      apply Finset.mem_image.mpr
      refine ⟨(ij.2, ij.1), Finset.mem_univ _, ?_⟩
      change ↑(generator ^ (finProdFinEquiv (ij.1, ij.2)).val) =
        (1 : ZMod p) * ↑(generator ^ t)
      rw [one_mul, Prod.eta, Equiv.apply_symm_apply]

/-- The concrete scalar Reed–Solomon code. -/
noncomputable abbrev rs := ReedSolomon.code domain 536870912

/-- The last good and first bad absolute radii differ by one. -/
theorem scalar_grid_edges :
    Lambda (rs : Set (Coord → ZMod p)) ((268435456 : ℝ) / 1073741824) ≤ 1 ∧
    3 ≤ Lambda (rs : Set (Coord → ZMod p)) ((268435457 : ℝ) / 1073741824) := by
  constructor
  · have h := isUniquelyDecodable_iff_Lambda_le.mp
      (isUniquelyDecodable_relativeUniqueDecodingRadius (rs : Set (Coord → ZMod p)))
    have hr := ReedSolomon.relativeUniqueDecodingRadius_RS_eq (α := domain)
      (n := 536870912) (by norm_num [Coord, Fintype.card_prod])
    rw [show relativeUniqueDecodingRadius (rs : Set (Coord → ZMod p)) = _ from hr] at h
    norm_num [Coord, Fintype.card_prod] at h ⊢
    exact h
  · have h := cyclic_list_lower_bound (M := 4) (s := 268435456) (b := 2)
      (by decide) (by decide) (by decide) generator generator_order
    norm_num [rs, domain, Nat.choose] at h ⊢
    exact h

private theorem scalar_budget_iff (δ : ℝ) :
    Lambda (rs : Set (Coord → ZMod p)) δ ≤ 2 ↔ δ < (268435457 : ℝ) / 1073741824 := by
  constructor
  · intro h
    by_contra! hδ
    have hfail := scalar_grid_edges.2.trans (Lambda_mono hδ)
    exact (by decide : ¬ (3 : ℕ∞) ≤ 2) (hfail.trans h)
  · intro hδ
    apply Lambda_le_iff_forall_encard_le.mpr
    intro f
    let C := (rs : Set (Coord → ZMod p))
    have hsub : closeCodewordsRel C f δ ⊆
        closeCodewordsRel C f ((268435456 : ℝ) / 1073741824) := by
      intro w hw
      classical
      obtain ⟨hwC, hd⟩ := mem_closeCodewordsRel_iff.mp hw
      apply mem_closeCodewordsRel_iff.mpr
      refine ⟨hwC, ?_⟩
      rw [relHammingDist_coe] at hd ⊢
      norm_num only [Coord, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
        Nat.cast_ofNat] at hd ⊢
      have hlt : (hammingDist f w : ℝ) < 268435457 := by linarith
      have hint : hammingDist f w < 268435457 := by exact_mod_cast hlt
      have hle : (hammingDist f w : ℝ) ≤ 268435456 := by
        exact_mod_cast (show hammingDist f w ≤ 268435456 by omega)
      linarith
    exact (Set.encard_mono hsub).trans ((encard_closeCodewordsRel_le_Lambda C _ f).trans
      (scalar_grid_edges.1.trans (by decide)))

/-- The exact list-budget test at security 2^-128 for every positive arity and real radius. -/
theorem list_threshold (κ : Type*) [Fintype κ] [Nonempty κ] (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := κ) (rs : Set (Coord → ZMod p))) δ ≤
        (Nat.card (ZMod p) / 2^128 : ℕ) ↔ δ < (268435457 : ℝ) / 1073741824 := by
  rw [InterleavedListProjection.prize_list_budget_iff rs δ (by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    decide)]
  have hbudget : Nat.card (ZMod p) / 2^128 = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    decide
  rw [hbudget]
  exact scalar_budget_iff δ

/-- The same crossing in the unrounded arithmetic of the grand list challenge. -/
theorem list_threshold_unrounded (κ : Type*) [Fintype κ] [Nonempty κ] (δ : ℝ) :
    ((Lambda (interleavedCodeSet (κ := κ) (rs : Set (Coord → ZMod p))) δ : ℕ∞) : ENNReal) ≤
        ((1 / 2^128 : ℝ≥0) : ENNReal) * (Fintype.card (ZMod p) : ENNReal) ↔
      δ < (268435457 : ℝ) / 1073741824 := by
  have hlo : (2 : ℝ≥0) ≤ (1 / 2^128 : ℝ≥0) * p := by
    norm_num [p]
    rw [le_div_iff₀ (by positivity)]
    norm_num
  have hhi : (1 / 2^128 : ℝ≥0) * p < 3 := by norm_num [p]
  have hbudget : Nat.card (ZMod p) / 2^128 = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    decide
  rw [← list_threshold κ δ, hbudget, ZMod.card]
  let L := Lambda (interleavedCodeSet (κ := κ) (rs : Set (Coord → ZMod p))) δ
  change (L : ENNReal) ≤ _ ↔ L ≤ 2
  have hl : (2 : ENNReal) ≤ ((1 / 2^128 : ℝ≥0) : ENNReal) * p := by exact_mod_cast hlo
  have hu : ((1 / 2^128 : ℝ≥0) : ENNReal) * p < 3 := by exact_mod_cast hhi
  constructor
  · intro h
    have hlt : L < 3 := by exact_mod_cast (h.trans_lt hu)
    have hdiscrete (z : ℕ∞) : z < 3 → z ≤ 2 := by
      induction z using ENat.recTopCoe with
      | top => simp
      | coe n =>
        intro hn
        exact_mod_cast (show n ≤ 2 from Nat.le_of_lt_succ (by exact_mod_cast hn))
    exact hdiscrete L hlt
  · intro h
    exact (show (L : ENNReal) ≤ 2 by exact_mod_cast h).trans hl

/-- The exact boundary in the challenge's adjacent-grid resolution type. -/
noncomputable def grandListResolution (m : ℕ) (hm : 0 < m) :
    GrandListResolution (rs : Set (Coord → ZMod p)) m (prizeThreshold : ℝ≥0) := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hε : (prizeThreshold : ℝ≥0) = 1 / 2^128 := by norm_num [prizeThreshold]
  rw [hε]
  refine ⟨268435456, by norm_num [Coord, Fintype.card_prod], ?_, ?_⟩
  · apply (list_threshold_unrounded (Fin m) _).mpr
    norm_num [gridPt, Coord, Fintype.card_prod]
  · apply lt_of_not_ge
    intro h
    have hn := (list_threshold_unrounded (Fin m)
      (gridPt (ι := Coord) (268435456 + 1) : ℝ)).mp h
    norm_num [gridPt, Coord, Fintype.card_prod] at hn

private theorem half_dim {ι : Type} [Fintype ι] (h : Fintype.card ι = 1073741824) :
    prizeDimension (ι := ι) 0 = 536870912 := by
  unfold prizeDimension
  rw [h]
  decide

/-- The rate-`1/2` entry of the smooth Reed–Solomon grand list challenge. -/
theorem grandListDecodingChallengeRs_rateHalf (m : ℕ) (hm : 0 < m) :
    grandListDecodingChallengeRs domain (prizeDimension (ι := Coord) 0) m
      (prizeThreshold : ℝ≥0) := by
  have hk := half_dim (ι := Coord) (by norm_num [Coord, Fintype.card_prod])
  exact (congrArg (fun k ↦ grandListDecodingChallengeRs domain k m
    (prizeThreshold : ℝ≥0)) hk).mpr (grandListResolution m hm).to_challenge


/-- The supremum of the safe real radii in the unit interval. -/
theorem safeRadius_supremum (κ : Type*) [Fintype κ] [Nonempty κ] :
    sSup {δ : ℝ | δ ∈ Set.Icc 0 1 ∧
      ((Lambda (interleavedCodeSet (κ := κ) (rs : Set (Coord → ZMod p))) δ : ℕ∞) : ENNReal) ≤
        ((1 / 2^128 : ℝ≥0) : ENNReal) * (Fintype.card (ZMod p) : ENNReal)} =
      (268435457 : ℝ) / 1073741824 := by
  have hs : {δ : ℝ | δ ∈ Set.Icc 0 1 ∧
      ((Lambda (interleavedCodeSet (κ := κ) (rs : Set (Coord → ZMod p))) δ : ℕ∞) : ENNReal) ≤
        ((1 / 2^128 : ℝ≥0) : ENNReal) * (Fintype.card (ZMod p) : ENNReal)} =
      Set.Ico 0 ((268435457 : ℝ) / 1073741824) := by
    ext δ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ico, list_threshold_unrounded]
    constructor
    · rintro ⟨⟨h0, _⟩, hδ⟩
      exact ⟨h0, hδ⟩
    · rintro ⟨h0, hδ⟩
      exact ⟨⟨h0, by linarith⟩, hδ⟩
  rw [hs, csSup_Ico (by norm_num)]

#print axioms prime_p
#print axioms generator_order
#print axioms scalar_grid_edges
#print axioms list_threshold
#print axioms list_threshold_unrounded
#print axioms smoothDomain
#print axioms grandListDecodingChallengeRs_rateHalf
#print axioms safeRadius_supremum

end ProximityGap.QuarterBudgetTwoThreshold
