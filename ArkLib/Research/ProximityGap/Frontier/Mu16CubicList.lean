/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.ListCountCertificates
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerOrbit
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonBridge
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # Four cubic Reed–Solomon words on the 16th roots of unity -/

set_option autoImplicit false
open Polynomial Finset Code
namespace ProximityGap.Mu16CubicList
variable {F : Type} [Field F]

private def scale (z : F) : F :=
  z ^ 2 + z ^ 4 + z ^ 6

/-- The cyclic evaluation sites indexed by exponents. -/
def site (z : F) (j : Fin 16) : F := z ^ j.val

private noncomputable def vanisher (z : F) (a b c : Fin 16) : F[X] :=
  (X - C (site z a)) * (X - C (site z b)) * (X - C (site z c))

private noncomputable def head (z : F) : Fin 4 → F[X] :=
  ![0, vanisher z 0 1 8, C (z ^ 2) * vanisher z 2 9 10,
    C (scale z) * vanisher z 1 4 12]

private def rootMask : Fin 4 → Finset (Fin 16) :=
  ![univ, {0, 1, 8}, {2, 9, 10}, {1, 4, 12}]

private def ties : List (Fin 4 × Fin 4 × Fin 16) :=
  [(0, 1, 0), (0, 1, 1), (0, 3, 1), (0, 2, 2),
   (1, 2, 3), (1, 3, 3), (0, 3, 4), (1, 2, 5),
   (1, 2, 7), (0, 1, 8), (0, 2, 9), (0, 2, 10),
   (1, 3, 11), (0, 3, 12), (2, 3, 13), (2, 3, 15)]

private def owner : Fin 16 → Fin 4 :=
  ![0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 2, 3, 2]

private def assigned : Fin 4 → Finset (Fin 16) :=
  ![{0, 1, 2, 4, 8, 9, 10, 12},
    {0, 1, 3, 5, 6, 7, 8, 11},
    {2, 3, 5, 7, 9, 10, 13, 15},
    {1, 3, 4, 11, 12, 13, 14, 15}]

private theorem minus_one {z : F} (hz : IsPrimitiveRoot z 16) : z ^ 8 = -1 := by
  apply (sq_eq_one_iff.mp (by simpa only [← pow_mul] using hz.pow_eq_one)).resolve_left
  intro he
  have := hz.pow_inj (i := 8) (j := 0) (by decide) (by decide) (by simpa using he)
  omega

private theorem ties_agree {z : F} (hz : IsPrimitiveRoot z 16)
    (p : Fin 4 × Fin 4 × Fin 16) (hp : p ∈ ties) :
    (head z p.1).eval (site z p.2.2) = (head z p.2.1).eval (site z p.2.2) := by
  have hz8 := minus_one hz
  simp only [ties, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [head, vanisher, scale, site]
    try grind (splits := 0)

private theorem site_injective {z : F} (hz : IsPrimitiveRoot z 16) : Function.Injective (site z) :=
  fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt h)

private theorem eval_nonzero {z : F} (hz : IsPrimitiveRoot z 16) (i a b c : Fin 16)
    (ha : i ≠ a) (hb : i ≠ b) (hc : i ≠ c) : (vanisher z a b c).eval (site z i) ≠ 0 := by
  simp only [vanisher, eval_mul, eval_sub, eval_X, eval_C, mul_ne_zero_iff, sub_ne_zero]
  exact ⟨⟨fun h => ha (site_injective hz h), fun h => hb (site_injective hz h)⟩,
    fun h => hc (site_injective hz h)⟩

private theorem scale_ne_zero {z : F} (hz : IsPrimitiveRoot z 16) : scale z ≠ 0 := by
  have h := ties_agree hz (1, 3, 3) (by decide)
  change (vanisher z 0 1 8).eval (site z 3) =
    (C (scale z) * vanisher z 1 4 12).eval (site z 3) at h
  intro he
  rw [he, C_0, zero_mul, eval_zero] at h
  exact eval_nonzero hz 3 0 1 8 (by decide) (by decide) (by decide) h

private theorem root_mask {z : F} (hz : IsPrimitiveRoot z 16) (i : Fin 4) (j : Fin 16) :
    (head z i).eval (site z j) = 0 ↔ j ∈ rootMask i := by
  have hinj (a b : Fin 16) : site z a = site z b ↔ a = b := (site_injective hz).eq_iff
  have hs := scale_ne_zero hz
  have hn := hz.ne_zero (by decide)
  fin_cases i <;> simp [head, rootMask, vanisher, hinj, hs, hn, sub_eq_zero, or_assoc]

private theorem head_degree (z : F) (i : Fin 4) : (head z i).natDegree < 4 := by
  have hd (a b c : Fin 16) : (vanisher z a b c).natDegree ≤ 3 := by
    unfold vanisher
    have bound (j : Fin 16) : ((X : F[X]) - C (site z j)).natDegree = 1 := natDegree_X_sub_C ..
    exact (natDegree_mul_le ..).trans ((Nat.add_le_add_right (natDegree_mul_le ..) _).trans
      (by simp only [bound]; decide))
  fin_cases i
  · simp [head]
  · exact (hd ..).trans_lt (by decide)
  · exact ((natDegree_C_mul_le ..).trans (hd ..)).trans_lt (by decide)
  · exact ((natDegree_C_mul_le ..).trans (hd ..)).trans_lt (by decide)

/-- On the 16 cyclic sites there are four distinct cubic evaluations
and a single center on which all four have eight agreements. -/
theorem four_cubics [DecidableEq F] {z : F} (hz : IsPrimitiveRoot z 16) :
    ∃ (f : Fin 4 → F[X]) (y : Fin 16 → F),
      (∀ i, (f i).natDegree < 4) ∧
      Function.Injective (fun i j => (f i).eval (site z j)) ∧
      ∀ i, 8 ≤ Code.agree (fun j => (f i).eval (site z j)) y := by
  classical
  refine ⟨head z, fun j => (head z (owner j)).eval (site z j), head_degree z, ?_, ?_⟩
  · have hsep : ∀ i j : Fin 4, i ≠ j →
        ∃ x : Fin 16, (x ∈ rootMask i) ≠ (x ∈ rootMask j) := by decide +kernel
    intro i j he
    by_contra hne
    obtain ⟨x, hx⟩ := hsep i j hne
    apply hx
    exact propext ((root_mask hz i x).symm.trans ((congrArg (· = 0) (congrFun he x)).to_iff.trans
      (root_mask hz j x)))
  · have hcom : ∀ (i : Fin 4) (j : Fin 16), j ∈ assigned i →
        owner j = i ∨ (owner j, i, j) ∈ ties := by decide +kernel
    have hsize : ∀ i, (assigned i).card = 8 := by decide +kernel
    intro i
    rw [← hsize i]
    apply card_le_card
    intro j hj
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rcases hcom i j hj with h | h
    · exact congrArg (fun a => (head z a).eval (site z j)) h.symm
    · exact (ties_agree hz _ h).symm

/-- On sixteen distinct coordinates the preceding seven-error ball is safe at every width. -/
theorem safe_predecessor [Finite F] (D : Fin 16 ↪ F) (m : ℕ) :
    Lambda (ProximityGap.ListInterpolationBoundary.words D 4 m) (7/16) ≤ 3 := by
  let : Fintype F := Fintype.ofFinite F
  have test : ProximityPrize.ListCountCertificates.test (Fintype.card (Fin 16))
      4 (Fintype.card F) m 3 9 = some true := by
    simp [ProximityPrize.ListCountCertificates.test]
  have h := (ProximityPrize.ListCountCertificates.test_correct D (by decide) test).mp rfl
  norm_num at h ⊢
  exact h


/-- On every smooth ordering and scaling the literal half-distance closed ball
has at least four cubic words. -/
theorem smooth_four_le_list [DecidableEq F] (D : Fin 16 ↪ F) [ReedSolomon.Smooth D] :
    4 ≤ Lambda (ReedSolomon.code D 4 : Set (Fin 16 → F)) (8/16) := by
  classical
  obtain ⟨z,a,e,hz,he⟩ := SmoothPowerOrbit.reindex D (Fintype.card_fin 16)
  obtain ⟨f,y,degree,distinct,hits⟩ := four_cubics hz
  let E : Fin 16 ↪ F := ⟨site z,site_injective hz⟩
  let w (i : Fin 4) := (fun j => (f i).eval (site z j)) ∘ e
  have inj : Function.Injective w := fun i j h => distinct (funext
    (fun x => by simpa [w] using congrFun h (e.symm x)))
  let W := univ.image w
  have size : W.card=4 := (card_image_of_injective _ inj).trans (by simp)
  have ball : (W : Set (Fin 16 → F)) ⊆
      closeCodewordsRel (ReedSolomon.code D 4 : Set (Fin 16 → F)) (y ∘ e) (8/16) := by
    intro c hc
    obtain ⟨i,_,rfl⟩ := mem_image.mp hc
    apply mem_closeCodewordsRel_iff.mpr
    constructor
    · apply SmoothDomainMcaEquivalence.mem_code_scale (E := E) e a he
      exact ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨f i,degree i,fun _ => rfl⟩
    · change (relHammingDist (y ∘ e) ((fun j => (f i).eval (site z j)) ∘ e) : ℝ) ≤ _
      rw [ProximityGap.relHammingDist_comp_equiv e y (fun j => (f i).eval (site z j))]
      have h := relHammingDist_le_one_sub_div_of_le_agree (hits i)
      norm_num at h ⊢
      exact h
  simpa [size] using encard_le_Lambda_of_subset_closeCodewordsRel ball

open GrandChallenges
open scoped NNReal ENNReal

/-- The sponsor's good-grid and bad-successor conditions for a sixteen-site
quarter-rate smooth code over a field with 128-bit budget three. -/
noncomputable def resolution [Fintype F] [DecidableEq F] (D : Fin 16 ↪ F)
    [ReedSolomon.Smooth D] (budget : Fintype.card F / 2 ^ 128 = 3) (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code D 4 : Set (Fin 16 → F)) m (prizeThreshold : ℝ≥0) := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  refine ⟨7,by decide,?_,?_⟩
  · apply (FourRateList128.budget_cast (Fintype.card F) _).mpr
    rw [budget]
    have safe := safe_predecessor D m
    norm_num [gridPt] at safe ⊢
    exact safe
  · apply lt_of_not_ge
    intro good
    have h := (FourRateList128.budget_cast (Fintype.card F) _).mp good
    rw [budget] at h
    norm_num [gridPt] at h
    have fieldSize : (3+1).choose 2 ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact (by decide : (3+1).choose 2 ≤ Fintype.card (Fin 16)).trans
        (Fintype.card_le_of_injective D D.injective)
    have scalar := (InterleavedListProjection.list_budget_iff (κ := Fin m)
      (ReedSolomon.code D 4) _ 3 fieldSize).mp h
    have bad := smooth_four_le_list D
    norm_num at bad
    exact (by decide : ¬ (4 : ℕ∞) ≤ 3) (bad.trans scalar)

#print axioms resolution

#print axioms four_cubics
#print axioms safe_predecessor
end ProximityGap.Mu16CubicList
