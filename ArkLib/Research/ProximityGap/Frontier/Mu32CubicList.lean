/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ArkLib.Research.ProximityGap.Frontier.PencilPairwiseBonferroni
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JohnsonBridge
import Mathlib.Tactic

/-! # Four cubic Reed–Solomon words on the 32nd roots of unity -/

set_option autoImplicit false
open Polynomial Finset Code
namespace ProximityGap.Mu32CubicList
variable {F : Type} [Field F]

private def scale (z : F) : F :=
  z + z ^ 3 + z ^ 4 - z ^ 8 - z ^ 9 - z ^ 11

/-- The cyclic evaluation sites indexed by exponents. -/
def site (z : F) (j : Fin 32) : F := z ^ j.val

private noncomputable def vanisher (z : F) (a b c : Fin 32) : F[X] :=
  (X - C (site z a)) * (X - C (site z b)) * (X - C (site z c))

private noncomputable def head (z : F) : Fin 4 → F[X] :=
  ![0, vanisher z 0 1 2, C (scale z) * vanisher z 7 9 23,
    C (scale z * z ^ 4) * vanisher z 11 25 27]

private def rootMask : Fin 4 → Finset (Fin 32) :=
  ![univ, {0, 1, 2}, {7, 9, 23}, {11, 25, 27}]

private def ties : List (Fin 4 × Fin 4 × Fin 32) :=
  [(0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 2, 7), (0, 2, 9),
   (0, 2, 23), (0, 3, 11), (0, 3, 25), (0, 3, 27), (1, 2, 6),
   (1, 2, 20), (1, 3, 14), (1, 3, 28), (2, 3, 13), (2, 3, 17),
   (2, 3, 21)]

private def owner : Fin 32 → Fin 4 :=
  ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 1,
    1, 2, 2, 2, 1, 2, 2, 0, 2, 0, 3, 0, 1, 3, 3, 3]

private def assigned : Fin 4 → Finset (Fin 32) :=
  ![{0, 1, 2, 3, 4, 5, 7, 9, 11, 23, 25, 27},
    {0, 1, 2, 6, 8, 10, 12, 14, 15, 16, 20, 28},
    {6, 7, 9, 13, 17, 18, 19, 20, 21, 22, 23, 24},
    {11, 13, 14, 17, 21, 25, 26, 27, 28, 29, 30, 31}]

private theorem minus_one {z : F} (hz : IsPrimitiveRoot z 32) : z ^ 16 = -1 := by
  apply (sq_eq_one_iff.mp (by simpa only [← pow_mul] using hz.pow_eq_one)).resolve_left
  intro he
  have := hz.pow_inj (i := 16) (j := 0) (by decide) (by decide) (by simpa using he)
  omega

private theorem ties_agree {z : F} (hz : IsPrimitiveRoot z 32)
    (p : Fin 4 × Fin 4 × Fin 32) (hp : p ∈ ties) :
    (head z p.1).eval (site z p.2.2) = (head z p.2.1).eval (site z p.2.2) := by
  have hz16 := minus_one hz
  simp only [ties, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [head, vanisher, scale, site]
    try grind (splits := 0)

private theorem site_injective {z : F} (hz : IsPrimitiveRoot z 32) : Function.Injective (site z) :=
  fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt h)

private theorem eval_nonzero {z : F} (hz : IsPrimitiveRoot z 32) (i a b c : Fin 32)
    (ha : i ≠ a) (hb : i ≠ b) (hc : i ≠ c) : (vanisher z a b c).eval (site z i) ≠ 0 := by
  simp only [vanisher, eval_mul, eval_sub, eval_X, eval_C, mul_ne_zero_iff, sub_ne_zero]
  exact ⟨⟨fun h => ha (site_injective hz h), fun h => hb (site_injective hz h)⟩,
    fun h => hc (site_injective hz h)⟩

private theorem scale_ne_zero {z : F} (hz : IsPrimitiveRoot z 32) : scale z ≠ 0 := by
  have h := ties_agree hz (1, 2, 6) (by decide)
  change (vanisher z 0 1 2).eval (site z 6) =
    (C (scale z) * vanisher z 7 9 23).eval (site z 6) at h
  intro he
  rw [he, C_0, zero_mul, eval_zero] at h
  exact eval_nonzero hz 6 0 1 2 (by decide) (by decide) (by decide) h

private theorem root_mask {z : F} (hz : IsPrimitiveRoot z 32) (i : Fin 4) (j : Fin 32) :
    (head z i).eval (site z j) = 0 ↔ j ∈ rootMask i := by
  have hinj (a b : Fin 32) : site z a = site z b ↔ a = b := (site_injective hz).eq_iff
  have hs := scale_ne_zero hz
  have hn := hz.ne_zero (by decide)
  fin_cases i <;> simp [head, rootMask, vanisher, hinj, hs, hn, sub_eq_zero, or_assoc]

private theorem head_degree (z : F) (i : Fin 4) : (head z i).natDegree < 4 := by
  have hd (a b c : Fin 32) : (vanisher z a b c).natDegree ≤ 3 := by
    unfold vanisher
    have bound (j : Fin 32) : ((X : F[X]) - C (site z j)).natDegree = 1 := natDegree_X_sub_C ..
    exact (natDegree_mul_le ..).trans ((Nat.add_le_add_right (natDegree_mul_le ..) _).trans
      (by simp only [bound]; decide))
  fin_cases i
  · simp [head]
  · exact (hd ..).trans_lt (by decide)
  · exact ((natDegree_C_mul_le ..).trans (hd ..)).trans_lt (by decide)
  · exact ((natDegree_C_mul_le ..).trans (hd ..)).trans_lt (by decide)

open Classical in
/-- On the 32 cyclic sites there are four distinct cubic evaluations
and a single center on which all four have twelve agreements. -/
theorem four_cubics {z : F} (hz : IsPrimitiveRoot z 32) :
    ∃ (f : Fin 4 → F[X]) (y : Fin 32 → F),
      (∀ i, (f i).natDegree < 4) ∧
      Function.Injective (fun i j => (f i).eval (site z j)) ∧
      ∀ i, 12 ≤ Code.agree (fun j => (f i).eval (site z j)) y := by
  classical
  refine ⟨head z, fun j => (head z (owner j)).eval (site z j), head_degree z, ?_, ?_⟩
  · have hsep : ∀ i j : Fin 4, i ≠ j →
        ∃ x : Fin 32, (x ∈ rootMask i) ≠ (x ∈ rootMask j) := by decide +kernel
    intro i j he
    by_contra hne
    obtain ⟨x, hx⟩ := hsep i j hne
    apply hx
    exact propext ((root_mask hz i x).symm.trans ((congrArg (· = 0) (congrFun he x)).to_iff.trans
      (root_mask hz j x)))
  · have hcom : ∀ (i : Fin 4) (j : Fin 32), j ∈ assigned i →
        owner j = i ∨ (owner j, i, j) ∈ ties := by decide +kernel
    have hsize : ∀ i, (assigned i).card = 12 := by decide +kernel
    intro i
    rw [← hsize i]
    apply card_le_card
    intro j hj
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rcases hcom i j hj with h | h
    · exact congrArg (fun a => (head z a).eval (site z j)) h.symm
    · exact (ties_agree hz _ h).symm

/-- Enumeration of the order-32 subgroup by powers of a generator. -/
def domain {z : F} (hz : IsPrimitiveRoot z 32) : Fin 32 ↪ F :=
  ⟨site z, site_injective hz⟩

/-- Twelve agreements suffice on every ordering and nonzero scaling of the cyclic sites. -/
theorem four_le_list_of_coordinates (D : Fin 32 ↪ F) {z : F} (hz : IsPrimitiveRoot z 32)
    (a : Fˣ) (e : Fin 32 ≃ Fin 32) (he : ∀ j, D j = (a : F) * site z (e j)) :
    4 ≤ Lambda (ReedSolomon.code D 4 : Set (Fin 32 → F)) (20 / 32) := by
  classical
  obtain ⟨f, y, hd, hi, ha⟩ := four_cubics hz
  let w (i : Fin 4) (j : Fin 32) := (f i).eval (site z (e j))
  have hinj : Function.Injective w := by
    intro i j h
    apply hi
    exact funext fun x => by simpa [w] using congrFun h (e.symm x)
  let W := univ.image w
  have hW : W.card = 4 := (card_image_of_injective _ hinj).trans (by simp)
  have hsub : (W : Set (Fin 32 → F)) ⊆
      closeCodewordsRel (ReedSolomon.code D 4 : Set (Fin 32 → F)) (y ∘ e) (20 / 32) := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    have hmem : w i ∈ ReedSolomon.code D 4 := by
      apply ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
      refine ⟨(f i).comp (C (↑a⁻¹ : F) * X), ?_, ?_⟩
      · simpa [natDegree_comp, a⁻¹.ne_zero] using hd i
      · intro j
        rw [eval_comp, eval_mul, eval_C, eval_X, he j, ← mul_assoc, Units.inv_mul, one_mul]
    refine mem_closeCodewordsRel_iff.mpr ⟨hmem, ?_⟩
    change (relHammingDist (y ∘ e) ((fun j => (f i).eval (site z j)) ∘ e) : ℝ) ≤ _
    rw [ProximityGap.relHammingDist_comp_equiv e y (fun j => (f i).eval (site z j))]
    have hh := relHammingDist_le_one_sub_div_of_le_agree (ha i)
    norm_num at hh ⊢
    exact hh
  simpa [hW] using encard_le_Lambda_of_subset_closeCodewordsRel hsub

/-- Below twenty errors on any 32 distinct sites, the scalar closed list has size at most three. -/
theorem list_le_three (D : Fin 32 ↪ F) (δ : ℝ) (hδ : δ < 20 / 32) :
    Lambda (ReedSolomon.code D 4 : Set (Fin 32 → F)) δ ≤ 3 := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro y W hclose
  by_contra! h
  obtain ⟨V, hVW, hV⟩ := exists_subset_card_eq (show 4 ≤ W.card by omega)
  let e := (Fintype.equivFinOfCardEq (by simpa using hV : Fintype.card V = 4)).symm
  let w (i : Fin 4) := (e i : Fin 32 → F)
  let S (i : Fin 4) := univ.filter (fun x => w i x = y x)
  have hmem (i : Fin 4) := mem_closeCodewordsRel_iff.mp (hclose (w i) (hVW (e i).property))
  have hsize (i : Fin 4) : 13 ≤ (S i).card := by
    have hlt := (hmem i).2.trans_lt hδ
    rw [relHammingDist_coe, Fintype.card_fin] at hlt
    have h20 : hammingDist y (w i) < 20 := by
      exact_mod_cast (show (hammingDist y (w i) : ℝ) < 20 by norm_num at hlt; linarith)
    have hd : (relHammingDist y (w i) : ℝ) ≤ 19 / 32 := by
      rw [relHammingDist_coe, Fintype.card_fin]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (show hammingDist y (w i) ≤ 19 by omega))
        (by positivity)
    have hh := (relHammingDist_le_one_sub_div_iff (ι := Fin 32) (by simp)
      (c := w i) (y := y) (x := 13)).mp (by norm_num at hd ⊢; exact hd)
    exact_mod_cast hh
  have hpair (i j : Fin 4) (hij : i < j) : (S i ∩ S j).card ≤ 3 := by
    by_contra! hbad
    have hw := ReedSolomon.eq_of_agree_of_card_le (hmem i).1 (hmem j).1 hbad (fun x hx =>
      (mem_filter.mp (mem_inter.mp hx).1).2.trans (mem_filter.mp (mem_inter.mp hx).2).2.symm)
    exact hij.ne (e.injective (Subtype.ext hw))
  let T := (univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 < p.2)
  have hT : T.card = 6 := by decide +kernel
  have ha : 52 ≤ ∑ i, (S i).card := by
    simpa using (sum_le_sum (s := univ) (fun i _ => hsize i))
  have hb : ∑ p ∈ T, (S p.1 ∩ S p.2).card ≤ 18 := by
    simpa [hT] using (sum_le_sum (s := T) fun p hp => hpair p.1 p.2 (mem_filter.mp hp).2)
  have hc : (univ.biUnion S).card ≤ 32 := card_le_univ _
  have hu := Frontier.PencilPairwiseBonferroni.biUnion_card_ge_sub_pairwise 4 S
  change (∑ i, (S i).card) ≤ (∑ p ∈ T, (S p.1 ∩ S p.2).card) + _ at hu
  omega

/-- Every smooth length-32 domain has a scalar four-word list at twenty errors. -/
theorem smooth_four_le_list [DecidableEq F] (D : Fin 32 ↪ F) [ReedSolomon.Smooth D] :
    4 ≤ Lambda (ReedSolomon.code D 4 : Set (Fin 32 → F)) (20 / 32) := by
  classical
  obtain ⟨u, hu⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let : Fintype H := Fintype.ofEquiv (Fin 32) u
  have hcard : Nat.card H = 32 := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr u, Fintype.card_fin]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have hroot : IsPrimitiveRoot g 32 := IsPrimitiveRoot.iff_orderOf.mpr (hg.trans hcard)
  let emb : H →* F := (Units.coeHom F).comp H.subtype
  have hemb : Function.Injective emb := Units.val_injective.comp Subtype.coe_injective
  let point (j : Fin 32) := g ^ j.val
  let v : Fin 32 ≃ H := Equiv.ofBijective point ((Fintype.bijective_iff_injective_and_card _).2
    ⟨fun i j he => Fin.ext (hroot.pow_inj i.isLt j.isLt he), Fintype.card_congr u⟩)
  let e := u.trans v.symm
  apply four_le_list_of_coordinates D (hroot.map_of_injective hemb) (ReedSolomon.Smooth.a D) e
  intro j
  rw [hu j]
  apply congrArg (_ * ·)
  change emb (u j) = emb g ^ (v.symm (u j)).val
  rw [← map_pow]
  exact congrArg emb (v.apply_symm_apply (u j)).symm

/-- At every real radius the budget-three boundary on a smooth 32-site domain is exactly 5/8. -/
theorem smooth_list_iff [DecidableEq F] (D : Fin 32 ↪ F) [ReedSolomon.Smooth D] (δ : ℝ) :
    Lambda (ReedSolomon.code D 4 : Set (Fin 32 → F)) δ ≤ 3 ↔ δ < 5 / 8 := by
  constructor
  · intro h
    by_contra! hn
    have hb := (smooth_four_le_list D).trans (Lambda_mono (show 20 / 32 ≤ δ by linarith))
    exact (by decide : ¬ (4 : ℕ∞) ≤ 3) (hb.trans h)
  · intro h
    exact list_le_three D δ (by linarith)

/-- The same strict real-radius boundary holds at every positive finite interleaving width. -/
theorem smooth_interleaved_iff [Finite F] [DecidableEq F] (D : Fin 32 ↪ F) [ReedSolomon.Smooth D]
    (κ : Type*) [Finite κ] [Nonempty κ] (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := κ) (ReedSolomon.code D 4 : Set (Fin 32 → F))) δ ≤ 3 ↔
      δ < 5 / 8 := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : (3 + 1).choose 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact (by decide : (3 + 1).choose 2 ≤ Fintype.card (Fin 32)).trans
      (Fintype.card_le_of_injective D D.injective)
  exact (InterleavedListProjection.list_budget_iff (κ := κ) (ReedSolomon.code D 4) δ 3 hcard).trans
    (smooth_list_iff D δ)

open GrandChallenges
open scoped NNReal ENNReal

private theorem budget_cast {q : ℕ} (hq : q / 2 ^ 128 = 3) (L : ℕ∞) :
    (L : ENNReal) ≤ ((prizeThreshold : ℝ≥0) : ENNReal) * q ↔ L ≤ 3 := by
  have hε : (prizeThreshold : ℝ≥0) = 1 / 2 ^ 128 := by norm_num [prizeThreshold]
  rw [show (3 : ℕ∞) = ((q / 2 ^ 128 : ℕ) : ℕ∞) by rw [hq]; rfl,
    hε, ← ENNReal.coe_natCast, ← ENNReal.coe_mul]
  induction L using ENat.recTopCoe with
  | top => simp only [ENat.toENNReal_top, top_le_iff, ENNReal.coe_ne_top, ENat.natCast_ne_top]
  | coe v =>
    have hreal : (v : ℝ≥0) ≤ (1 / 2 ^ 128 : ℝ≥0) * q ↔ v ≤ q / 2 ^ 128 := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
      exact_mod_cast (Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)).symm
    simpa only [ENat.toENNReal_coe, ← ENNReal.coe_natCast, ENNReal.coe_le_coe,
      ENat.natCast_le_natCast] using hreal

/-- The canonical prize resolution at length 32 and dimension 4 for every smooth domain
over an alphabet whose 128-bit integer list budget is three. -/
noncomputable def resolution [Fintype F] [DecidableEq F] (D : Fin 32 ↪ F)
    [ReedSolomon.Smooth D] (hq : Fintype.card F / 2 ^ 128 = 3) (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code D 4 : Set (Fin 32 → F)) m (prizeThreshold : ℝ≥0) := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  refine ⟨19, by decide, ?_, ?_⟩
  · apply (budget_cast hq _).mpr
    apply (smooth_interleaved_iff D (Fin m) _).mpr
    norm_num [gridPt]
  · apply lt_of_not_ge
    intro h
    have hh := (smooth_interleaved_iff D (Fin m) _).mp ((budget_cast hq _).mp h)
    norm_num [gridPt] at hh

#print axioms resolution
#print axioms smooth_four_le_list
#print axioms smooth_list_iff
#print axioms smooth_interleaved_iff
#print axioms four_cubics
#print axioms four_le_list_of_coordinates
#print axioms list_le_three
end ProximityGap.Mu32CubicList
