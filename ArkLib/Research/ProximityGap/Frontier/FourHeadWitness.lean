/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.KKH26RegimeSplit
import ArkLib.Research.ProximityGap.Frontier.FourHeadQuotient
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Research.ProximityGap.Frontier._SeventeenThirtyTwoDeltaStarFloor
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# Four-head scalar witness assembly

An ordinary coordinate supplies one scalar, and a special coordinate supplies four.
One affine parameter separates all the scalars simultaneously for a single received stack.
The agreement and degree hypotheses below are finite input data for a fiber construction.
-/

open Finset Polynomial Code
open scoped NNReal ENNReal Polynomial

namespace ProximityGap.FourHeadWitness

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A four-head agreement allocation on an injective Reed–Solomon evaluation domain. -/
structure CoreAllocation (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) where
  head : Fin 4 → F[X]
  background : I → F
  ordinary : Finset I
  special : Finset I
  core : Fin 4 → Finset I
  degree_head : ∀ h, (head h).degree < (k : WithBot ℕ)
  degree_first : ∀ h, (Polynomial.X * head h).degree < (k : WithBot ℕ)
  disjoint : Disjoint ordinary special
  core_disjoint : ∀ h, Disjoint (core h) special
  core_agrees : ∀ h x, x ∈ core h → (head h).eval (dom x) = background x
  core_rank : ∀ h, k ≤ (core h).card
  core_size : ∀ h, (1 - δ) * (Fintype.card I : ℝ≥0) ≤ (((core h).card + 1 : ℕ) : ℝ≥0)
  ordinary_mismatch : ∀ x ∈ ordinary, ∃ h, (head h).eval (dom x) ≠ background x

/-- The original four-head allocation with four distinct values at each special site. -/
structure Allocation (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) extends CoreAllocation dom k δ where
  special_distinct : ∀ x ∈ special, Function.Injective (fun h => (head h).eval (dom x))

variable {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}

/-- Number of scalar labels supported by the allocation. -/
def Allocation.count (A : Allocation dom k δ) : ℕ := A.ordinary.card + 4 * A.special.card

/-- A special site contributes one label for each distinct evaluated head there. -/
def CoreAllocation.count (A : CoreAllocation dom k δ) : ℕ :=
  A.ordinary.card + ∑ x : A.special, (univ.image (fun h => (A.head h).eval (dom x.val))).card

/-- The scalar construction allows evaluated heads to coincide at a special site.
One actual bad label is obtained for each distinct value at that site. -/
theorem exists_bad_scalar_set_of_values (A : CoreAllocation dom k δ) (hfour : 4 < Fintype.card F)
    (hfield : A.count * A.count < Fintype.card F) :
    ∃ (u : WordStack F (Fin 2) I) (G : Finset F), G.card = A.count ∧
      ∀ γ ∈ G, mcaEvent ((ReedSolomon.code dom k : Submodule F (I → F)) : Set (I → F))
        δ (u 0) (u 1) γ := by
  classical
  let v (x : I) (h : Fin 4) := (A.head h).eval (dom x)
  have hoff (x : I) : ∃ t : F, ∀ h, t ≠ v x h := by
    have hlt : (univ.image (v x)).card < (univ : Finset F).card := by
      exact card_image_le.trans_lt (by simpa using hfour)
    obtain ⟨t, _, ht⟩ := exists_mem_notMem_of_card_lt_card hlt
    exact ⟨t, fun h he => ht (he ▸ mem_image_of_mem (v x) (mem_univ h))⟩
  choose τ hτ using hoff
  let values (x : A.special) := univ.image (v x.val)
  let Slot := (↥A.ordinary) ⊕ (Σ x : A.special, ↥(values x))
  have hcard : Fintype.card Slot = A.count := by
    simp only [Slot, CoreAllocation.count, values, v, Fintype.card_sum, Fintype.card_sigma, Fintype.card_coe]
  let key : Slot → F × F := Sum.elim (fun x => (-dom x.val, 0))
    (fun p => (-dom p.1.val, (τ p.1.val - p.2.val)⁻¹))
  have hval (x : A.special) (r : values x) : τ x.val ≠ r.val := by
    obtain ⟨h,_,he⟩ := mem_image.mp r.property
    exact he ▸ hτ x.val h
  have hkey : Function.Injective key := by
    intro a b hab
    cases a with
    | inl x =>
      cases b with
      | inl y =>
        exact congrArg Sum.inl (Subtype.ext (dom.injective (neg_inj.mp (congrArg Prod.fst hab))))
      | inr q =>
        exact False.elim ((inv_ne_zero (sub_ne_zero.mpr (hval q.1 q.2)))
          (congrArg Prod.snd hab).symm)
    | inr p =>
      cases b with
      | inl y =>
        exact False.elim ((inv_ne_zero (sub_ne_zero.mpr (hval p.1 p.2)))
          (congrArg Prod.snd hab))
      | inr q =>
        obtain ⟨x, h⟩ := p
        obtain ⟨y, j⟩ := q
        have hxy : x = y := Subtype.ext (dom.injective (neg_inj.mp (congrArg Prod.fst hab)))
        subst y
        have hinv : (τ x.val - h.val)⁻¹ = (τ x.val - j.val)⁻¹ := congrArg Prod.snd hab
        have he : h = j := Subtype.ext (sub_right_injective (inv_inj.mp hinv))
        subst j
        rfl
  let keys := univ.image key
  have hkeys : keys.card = A.count := (card_image_of_injective _ hkey).trans (by simpa using hcard)
  obtain ⟨t, ht⟩ := FourHeadQuotient.exists_injective_affine_labels keys (by rwa [hkeys])
  let scalar (s : Slot) := (key s).1 + t * (key s).2
  have hm (s : Slot) : key s ∈ keys := mem_image_of_mem key (mem_univ s)
  have hscalar : Function.Injective scalar :=
    fun s r he => hkey (ht (hm s) (hm r) he)
  let row₀ (x : I) : F := if x ∈ A.special then dom x * τ x - t else dom x * A.background x
  let row₁ (x : I) : F := if x ∈ A.special then τ x else A.background x
  let u : WordStack F (Fin 2) I := ![row₀, row₁]
  have hdecode (x : I) (h : Fin 4) (γ : F)
      (hbad : v x h ≠ row₁ x)
      (hf : dom x * v x h + γ * v x h = row₀ x + γ * row₁ x) :
      mcaEvent ((ReedSolomon.code dom k : Submodule F (I → F)) : Set (I → F))
        δ (u 0) (u 1) γ := by
    have hcore (y : I) (hy : y ∈ A.core h) :
        (Polynomial.X * A.head h).eval (dom y) = u 0 y ∧ (A.head h).eval (dom y) = u 1 y := by
      have hns : y ∉ A.special := disjoint_left.mp (A.core_disjoint h) hy
      change (Polynomial.X * A.head h).eval (dom y) = row₀ y ∧ (A.head h).eval (dom y) = row₁ y
      simp [row₀, row₁, hns, A.core_agrees h y hy]
    apply ArkLib.ProximityGap.Frontier.HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh
      dom k δ u γ (A.core h) x (Polynomial.X * A.head h) (A.head h)
    · exact fun hx => hbad (hcore x hx).2
    · exact A.degree_first h
    · exact A.degree_head h
    · apply (Polynomial.degree_add_le _ _).trans_lt
      apply max_lt (A.degree_first h)
      by_cases hz : γ = 0
      · subst γ
        simp
      · rw [Polynomial.degree_C_mul hz]
        exact A.degree_head h
    · exact A.core_rank h
    · exact A.core_size h
    · exact hcore
    · change (Polynomial.X * A.head h + Polynomial.C γ * A.head h).eval (dom x) = row₀ x + γ * row₁ x
      simpa [v] using hf
    · exact fun he => hbad (congrArg Prod.snd he)
  refine ⟨u, univ.image scalar, (card_image_of_injective _ hscalar).trans (by simpa using hcard), ?_⟩
  intro γ hγ
  obtain ⟨s, _, rfl⟩ := mem_image.mp hγ
  cases s with
  | inl x =>
    obtain ⟨h, hh⟩ := A.ordinary_mismatch x.val x.property
    have hns : x.val ∉ A.special := disjoint_left.mp A.disjoint x.property
    apply hdecode x.val h
    · simpa [v, row₁, hns] using hh
    · simp [scalar, key, row₀, row₁, hns]
  | inr p =>
    obtain ⟨x, r⟩ := p
    obtain ⟨h,_,he⟩ := mem_image.mp r.property
    apply hdecode x.val h
    · simpa [row₁, x.property] using (hτ x.val h).symm
    · simpa [scalar, key, row₀, row₁, x.property, div_eq_mul_inv, ←he] using
        (FourHeadQuotient.off_line_agreement (dom x.val) 1 (v x.val h) (τ x.val) t (hτ x.val h)).symm

/-- The labels are distinct and all give literal MCA events for the same received stack. -/
theorem exists_bad_scalar_set (A : Allocation dom k δ) (hfour : 4 < Fintype.card F)
    (hfield : A.count * A.count < Fintype.card F) :
    ∃ (u : WordStack F (Fin 2) I) (G : Finset F), G.card = A.count ∧
      ∀ γ ∈ G, mcaEvent ((ReedSolomon.code dom k : Submodule F (I → F)) : Set (I → F))
        δ (u 0) (u 1) γ := by
  have he : A.toCoreAllocation.count = A.count := by
    unfold CoreAllocation.count Allocation.count
    have h (x : A.special) : (univ.image (fun h => (A.head h).eval (dom x.val))).card = 4 := by
      rw [card_image_of_injective _ (A.special_distinct x.val x.property)]
      simp
    simp only [h,sum_const,card_univ,Fintype.card_coe,smul_eq_mul,Nat.mul_comm]
  exact he ▸ exists_bad_scalar_set_of_values A.toCoreAllocation hfour (he.symm ▸ hfield)

/-- Literal finite-field bad-scalar probability bound from a four-head allocation. -/
theorem event_mass (A : Allocation dom k δ) (hfour : 4 < Fintype.card F)
    (hfield : A.count * A.count < Fintype.card F) :
    (A.count : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom k : Submodule F (I → F)) : Set (I → F)) δ := by
  obtain ⟨u, G, hcard, hG⟩ := exists_bad_scalar_set A hfour hfield
  rw [← hcard]
  exact MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ δ u G hG

section FirstPrime

set_option maxRecDepth 10000

open ArkLib.ProximityGap.PrizeShapePrimeP30 (prime_P orderOf_g)

private abbrev sponsorP := ArkLib.ProximityGap.PrizeShapePrimeP30.P
private abbrev generator := ArkLib.ProximityGap.PrizeShapePrimeP30.g
open ArkLib.ProximityGap.KKH26 (evalCode)

local instance : Fact (Nat.Prime sponsorP) := ⟨prime_P⟩
local instance : NeZero (2 ^ 30 : ℕ) := ⟨by decide⟩

/-- Canonical smooth evaluation domain for the first named field. -/
noncomputable abbrev firstDomain := KKH26RegimeSplit.powDomain generator orderOf_g
  (KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g)

/-- In the first prize field, an allocation of exactly one more scalar than the block
length crosses the sponsor budget on the actual half-rate evaluation code. -/
theorem firstPrime_bad (A : Allocation firstDomain (2 ^ 29) δ) (hcount : A.count = 2 ^ 30 + 1) :
    (epsStar : ℝ≥0∞) < epsMCA (F := ZMod sponsorP) (evalCode generator (2 ^ 30) (2 ^ 29 - 1)) δ := by
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon generator orderOf_g
    (KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g) (2 ^ 29 - 1)]
  rw [show (2 ^ 29 - 1 + 1 : ℕ) = 2 ^ 29 by decide]
  have hm := event_mass A (by rw [ZMod.card]; decide) (by rw [ZMod.card, hcount]; decide)
  rw [hcount, ZMod.card] at hm
  apply lt_of_lt_of_le _ hm
  rw [ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv]
  exact ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoDeltaStarFloor.inv_natCast_lt_natCast_div
    (by decide) prime_P.pos (by decide)

/-- Producing the 16-fiber allocation at 313174699 errors suffices for this upper endpoint. -/
theorem firstPrime_upper
    (A : Allocation firstDomain (2 ^ 29) ((313174699 : ℝ≥0) / 2 ^ 30))
    (hcount : A.count = 2 ^ 30 + 1) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod sponsorP) (evalCode generator (2 ^ 30) (2 ^ 29 - 1))
      (epsStar : ℝ≥0∞) ≤ (313174699 : ℝ≥0) / 2 ^ 30 :=
  MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (firstPrime_bad A hcount)

end FirstPrime

#print axioms exists_bad_scalar_set
#print axioms event_mass
#print axioms firstPrime_bad
#print axioms firstPrime_upper

end ProximityGap.FourHeadWitness
