/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.WeightedRichLinePacking
import ArkLib.Research.ProximityGap.Frontier.RepetitionFourCenterAttack
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge
import ArkLib.Research.ProximityGap.Frontier.TerminalDimensionThreshold
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-! # The exact dimension-one threshold at the second prime -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.RepetitionSecondPrimeThreshold
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open WeightedRichLinePacking

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- At dimension one every bad scalar selects a rich affine line through two
distinct received point values, weighted by their coordinate multiplicities. -/
theorem arrangement {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 1 δ u) (t : ℕ)
    (ht : t≤⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊) (hpos : 0<t) :
    ∃ A : Arrangement (F × F) F t, A.lines=fam.G ∧ mass A.w A.points=Fintype.card I := by
  classical
  let val (i : I) := (u 0 i,u 1 i)
  let pts := univ.image val
  let w (p : F×F) := (univ.filter (fun i => val i=p)).card
  let S (g : F) := fullAgreement dom (u 0) (u 1) g (fam.q g)
  let B (g : F) := (S g).image val
  have rich (g : F) (hg : g∈fam.G) : t≤(S g).card := ht.trans (fam.threshold_le g hg)
  have wmass (T : Finset (F×F)) : mass w T=(univ.filter fun i => val i∈T).card :=
    sum_card_fiberwise_eq_card_filter univ T val
  have onLine (g : F) (hg : g∈fam.G) (p : F×F) (hp : p∈B g) :
      p.1+g*p.2=(fam.q g).coeff 0 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    have h := (mem_filter.mp hx).2
    change (fam.q g).eval (dom x)=_ at h
    have deg := fam.degree_lt g hg
    have q := eq_C_of_natDegree_le_zero (by omega : (fam.q g).natDegree≤0)
    have eq : (fam.q g).eval (dom x)=(fam.q g).coeff 0 :=
      (congrArg (fun f : F[X] => f.eval (dom x)) q).trans (eval_C ..)
    exact h.symm.trans eq
  refine ⟨{ points := pts
            lines := fam.G
            block := B
            w := w
            positive := ?_
            inside := ?_
            rich := ?_
            nontrivial := ?_
            linear := ?_ }, rfl, ?_⟩
  · intro p hp
    obtain ⟨x,_,rfl⟩ := mem_image.mp hp
    exact card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  · intro g _ p hp
    obtain ⟨x,_,rfl⟩ := mem_image.mp hp
    exact mem_image_of_mem val (mem_univ x)
  · intro g hg
    rw [wmass]
    exact (rich g hg).trans (card_le_card fun x hx =>
      mem_filter.mpr ⟨mem_univ _,mem_image_of_mem val hx⟩)
  · intro g hg
    by_contra! small
    obtain ⟨x,hx⟩ := card_pos.mp (hpos.trans_le (rich g hg))
    have fail := not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1) (S g)
      (C (u 0 x)) (C (u 1 x)) (by simp) (by simp) (fam.noJoint g hg)
    apply fail
    intro y hy
    have eq : val x=val y := card_le_one.mp (by omega : (B g).card≤1) _ (mem_image_of_mem val hx)
      _ (mem_image_of_mem val hy)
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    simpa only [eval_C] using (And.intro (congrArg Prod.fst eq) (congrArg Prod.snd eq))
  · intro a ha b hb hab
    apply card_le_one.mpr
    intro p hp q hq
    obtain ⟨hpa,hpb⟩ := mem_inter.mp hp
    obtain ⟨hqa,hqb⟩ := mem_inter.mp hq
    have h₁ := (onLine a ha p hpa).trans (onLine a ha q hqa).symm
    have h₂ := (onLine b hb p hpb).trans (onLine b hb q hqb).symm
    have hz : (a-b)*(p.2-q.2)=0 := by linear_combination h₁-h₂
    have h := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab))
    exact Prod.ext (by rw [h] at h₁; exact add_right_cancel h₁) h
  · dsimp only
    rw [wmass]
    have h : (univ.filter fun i => val i∈pts)=univ := filter_true_of_mem fun i _ =>
      mem_image_of_mem val (mem_univ i)
    rw [h,card_univ]

/-- A uniform rich-line packing bound gives the same upper bound on the number of bad
scalars for a dimension-one code on any supplied domain and at every positive width. -/
theorem probability_of_packing {N t e B : ℕ} [NeZero N] (dom : Fin N ↪ F)
    (ht : 0 < t) (he : e+t = N)
    (bound : ∀ A : Arrangement (F × F) F t, mass A.w A.points = N → A.lines.card ≤ B)
    (width : ℕ) [NeZero width] :
    epsMCA (F := F) ((ReedSolomon.code dom 1 : Set (Fin N → F)) ^⋈ (Fin width))
      ((e : ℝ≥0)/N) ≤ (B : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  classical
  rw [epsMCA_interleaved_eq]
  apply epsMCA_le_of_badCount_le
  intro u
  obtain ⟨fam, eq⟩ := exists_richPointFamily_with_badScalar_count dom ((e : ℝ≥0)/N) u
    (by decide : 1 ≤ 1)
  rw [eq]
  obtain ⟨A, lines, hm⟩ := arrangement fam t (by
    rw [Fintype.card_fin, tsub_mul, one_mul, div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne N)), ← Nat.cast_tsub]
    simpa only [show N-e=t by omega, Nat.ceil_natCast] using (le_refl t)) ht
  rw [← lines]
  exact bound A (by simpa using hm)

private abbrev n : ℕ := 1073741824
private abbrev p := PrizeShapePrimeP30Second.P
local instance : Fact p.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- The good-side probability bound for all positive widths at the last safe count. -/
theorem predecessor_of_packing (dom : Fin n ↪ ZMod p)
    (bound : ∀ A : Arrangement (ZMod p × ZMod p) (ZMod p) 134217730,
      mass A.w A.points=n → A.lines.card≤2147483648) (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width))
      (939524094/1073741824) ≤ 1/(2:ℝ≥0∞)^128 := by
  have good := probability_of_packing dom (by decide : 0 < 134217730)
    (by decide : 939524094+134217730=n) bound width
  rw [ZMod.card] at good
  apply good.trans
  have h := (BoundarySecurityBudget.count_ratio_le_iff PrizeShapePrimeP30Second.prime_P.pos
    (by decide : 0 < 2^128)).mpr (by decide : 2147483648 ≤ p/2^128)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- The dimensional-one operational threshold, using the rich-line arrangement
bound and the explicit four-center attack at its immediate successor. -/
theorem exact_of_packing (dom : Fin n ↪ ZMod p)
    (bound : ∀ A : Arrangement (ZMod p × ZMod p) (ZMod p) 134217730,
      mass A.w A.points=n → A.lines.card≤2147483648) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width))
      (1/(2:ℝ≥0∞)^128) = 939524095/1073741824 := by
  have bad := (RepetitionFourCenterAttack.second_prime dom width).2
  rw [epsMCA_interleaved_eq] at bad
  have good := predecessor_of_packing dom bound width
  rw [epsMCA_interleaved_eq] at good
  rw [mcaDeltaStar_interleaved_eq]
  apply le_antisymm (mcaDeltaStar_le_of_bad _ _ bad)
  apply PrizeShapeRateHalfBracket.latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a:=939524095)
    (by decide) (by decide : 939524095≤n)
  exact good

/-- Every production-length injective domain over the second prime is within
the sponsor tolerance at 939524094 errors at every positive width. -/
theorem predecessor (dom : Fin n ↪ ZMod p) (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width))
      (939524094/1073741824) ≤ 1/(2:ℝ≥0∞)^128 :=
  predecessor_of_packing dom Arrangement.predecessor width

/-- The exact second-prime dimension-one operational radius on every production-length domain. -/
theorem second_prime (dom : Fin n ↪ ZMod p) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width))
      (1/(2:ℝ≥0∞)^128) = 939524095/1073741824 :=
  exact_of_packing dom Arrangement.predecessor width

/-- For all positive dimensions up to rate one sixteenth, give the exact
operational supremum and the safety predicate on every real radius. -/
theorem dimension_profile (dom : Fin n ↪ ZMod p) {K : ℕ} (hK : 0 < K)
    (hmax : K ≤ 67108864) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom K : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let δ₀ : ℝ≥0 := if K = 1 then 939524095/1073741824 else 715827882/1073741824
    let ε : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128
    mcaDeltaStar (F:=ZMod p) C ε = δ₀ ∧ ∀ δ, epsMCA (F:=ZMod p) C δ ≤ ε ↔ δ < δ₀ := by
  dsimp only
  by_cases h : K = 1
  · subst K
    rw [if_pos rfl]
    have exactRadius := second_prime dom width
    refine ⟨exactRadius, fun δ => ⟨fun good => ?_, fun small => ?_⟩⟩
    · by_contra! large
      have bad := (RepetitionFourCenterAttack.second_prime dom width).2
      exact bad.not_ge ((epsMCA_mono _ large).trans good)
    · by_contra! bad
      exact small.not_ge (exactRadius ▸ mcaDeltaStar_le_of_bad _ _ bad)
  · rw [if_neg h]
    exact TerminalDimensionThreshold.twice_length_budget dom (by simp [n, TerminalDomainSecurity.n])
      (by omega) hmax (by decide) width

#print axioms dimension_profile
#print axioms second_prime
#print axioms arrangement
#print axioms exact_of_packing
end ArkLib.ProximityGap.Frontier.RepetitionSecondPrimeThreshold
