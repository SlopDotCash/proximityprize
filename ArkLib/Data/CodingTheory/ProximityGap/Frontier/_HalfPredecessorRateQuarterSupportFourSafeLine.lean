/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSparseSafeLine
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PencilSunflowerCore
import ArkLib.Data.CodingTheory.ProximityGap.LineListSupportRatioFiber

/-!
# Rate-quarter `k = 4`: zero-safe support-four lines

At `n = 16`, dimension `4`, threshold `9`, and direction support four, every codeword in the
`t = 5` zero-agreement stratum must use all four moving coordinates at one scalar. Four-point
interpolation therefore puts all such codewords on the polynomial line `A + gamma R`.

On the twelve zero coordinates, traces from distinct scalars meet in one common kernel: the
coordinates where `R` vanishes and `A` agrees with the offset. The nonzero cubic `R` gives a
kernel of size at most three. Five size-five traces with such a kernel would force
`5 * (5 - r) + r <= 12`, impossible for `r <= 3`; hence the stratum has size at most four.

The `t = 7` stratum has Plotkin cap three, while two size-eight traces cannot fit in the
twelve-point zero-coordinate universe, so the `t = 8` stratum has cap one. At `t = 6`, the
full-four-support subfamily has cap three by the same common-kernel packing, and every residual
codeword has a heavy fiber of size exactly three. The Plotkin denominator for the whole `t = 6`
stratum is exactly zero; the final theorem isolates it as `#bad <= #t6 + 14`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine

open _root_.ProximityGap _root_.ProximityGap.Ownership _root_.ProximityGap.SpikeFloor
open _root_.ProximityGap.LargeZeroWitnessSplit _root_.ProximityGap.LineListMCAWeld
open ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine
open _root_.ProximityGap.Frontier.PencilSunflowerCore

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The forced polynomial line at `t = 5` -/

/-- Degree-`<4` interpolation of a row on the four moving coordinates. -/
noncomputable def supportFourInterpolant
    (dom : Fin 16 ↪ F) (u1 w : Fin 16 → F) : F[X] :=
  Lagrange.interpolate (directionSupportSet u1) dom w

theorem supportFourInterpolant_eval_of_mem_support
    (dom : Fin 16 ↪ F) (u1 w : Fin 16 → F)
    {i : Fin 16} (hi : i ∈ directionSupportSet u1) :
    (supportFourInterpolant dom u1 w).eval (dom i) = w i := by
  exact Lagrange.eval_interpolate_at_node w dom.injective.injOn hi

theorem supportFourInterpolant_degree_lt_four
    (dom : Fin 16 ↪ F) (u1 w : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (supportFourInterpolant dom u1 w).degree < 4 := by
  have hdeg := Lagrange.degree_interpolate_lt
    (s := directionSupportSet u1) (v := dom) (r := w) dom.injective.injOn
  simpa only [hsupport] using hdeg

theorem exists_codePolynomial_of_mem_five_stratum
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    {c : Fin 16 → F} (hc : c ∈ zeroAgreementStratum dom 4 9 u0 u1 5) :
    ∃ q : F[X], q.degree < 4 ∧ c = fun i ↦ q.eval (dom i) := by
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp hc).1
  rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
  exact hcApp.2.1

/-- Canonical polynomial representative of a `t = 5` codeword. -/
noncomputable def fiveCodePolynomial
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5}) : F[X] :=
  Classical.choose (exists_codePolynomial_of_mem_five_stratum dom u0 u1 c.2)

theorem fiveCodePolynomial_degree_lt
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5}) :
    (fiveCodePolynomial dom u0 u1 c).degree < 4 :=
  (Classical.choose_spec
    (exists_codePolynomial_of_mem_five_stratum dom u0 u1 c.2)).1

theorem fiveCodePolynomial_eval
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5})
    (i : Fin 16) :
    (fiveCodePolynomial dom u0 u1 c).eval (dom i) = c.1 i := by
  have h := (Classical.choose_spec
    (exists_codePolynomial_of_mem_five_stratum dom u0 u1 c.2)).2
  exact congrFun h.symm i

/-- A canonical scalar whose support-ratio fiber witnesses appearance. -/
noncomputable def fiveScalar
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5}) : F :=
  Classical.choose
    (exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
      dom 4 9 u0 u1 c.1 (Finset.mem_filter.mp c.2).1)

/-- At `t = 5`, the heavy ratio fiber is the whole four-point moving support. -/
theorem supportRatioFiber_fiveScalar_eq_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5}) :
    supportRatioFiber c.1 u0 u1 (fiveScalar dom u0 u1 c) =
      directionSupportSet u1 := by
  have hzero : (directionZeroAgreementSet c.1 u0 u1).card = 5 :=
    (Finset.mem_filter.mp c.2).2
  have hlarge : 9 - (directionZeroAgreementSet c.1 u0 u1).card ≤
      (supportRatioFiber c.1 u0 u1 (fiveScalar dom u0 u1 c)).card := by
    simpa only [fiveScalar] using Classical.choose_spec
      (exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
        dom 4 9 u0 u1 c.1 (Finset.mem_filter.mp c.2).1)
  have hsub : supportRatioFiber c.1 u0 u1 (fiveScalar dom u0 u1 c) ⊆
      directionSupportSet u1 := by
    intro i hi
    exact (mem_supportRatioFiber c.1 u0 u1 (fiveScalar dom u0 u1 c) i).mp hi |>.1
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hsupport]
  omega

/-- Every bottom-stratum polynomial is the unique four-point interpolant `A + gamma R`. -/
theorem fiveCodePolynomial_eq_affine_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5}) :
    fiveCodePolynomial dom u0 u1 c =
      supportFourInterpolant dom u1 u0 +
        C (fiveScalar dom u0 u1 c) * supportFourInterpolant dom u1 u1 := by
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (directionSupportSet u1) dom.injective.injOn ?_ ?_ ?_
  · simpa only [hsupport] using fiveCodePolynomial_degree_lt dom u0 u1 c
  · rw [hsupport]
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact supportFourInterpolant_degree_lt_four dom u1 u0 hsupport
    · by_cases hgamma : fiveScalar dom u0 u1 c = 0
      · simp only [hgamma, C_0, zero_mul, degree_zero]
        exact WithBot.bot_lt_coe 4
      · rw [Polynomial.degree_C_mul hgamma]
        exact supportFourInterpolant_degree_lt_four dom u1 u1 hsupport
  · intro i hi
    have hfiber : i ∈ supportRatioFiber c.1 u0 u1
        (fiveScalar dom u0 u1 c) := by
      rw [supportRatioFiber_fiveScalar_eq_support dom u0 u1 hsupport c]
      exact hi
    have hratio := (mem_supportRatioFiber c.1 u0 u1
      (fiveScalar dom u0 u1 c) i).mp hfiber |>.2
    have hu1 : u1 i ≠ 0 := by
      simpa [directionSupportSet] using hi
    rw [div_eq_iff hu1] at hratio
    simp only [eval_add, eval_mul, eval_C,
      fiveCodePolynomial_eval,
      supportFourInterpolant_eval_of_mem_support dom u1 u0 hi,
      supportFourInterpolant_eval_of_mem_support dom u1 u1 hi]
    linear_combination hratio

theorem fiveCodeword_eval_eq_affine_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5})
    (i : Fin 16) :
    c.1 i =
      (supportFourInterpolant dom u1 u0 +
        C (fiveScalar dom u0 u1 c) *
          supportFourInterpolant dom u1 u1).eval (dom i) := by
  rw [← fiveCodePolynomial_eval dom u0 u1 c i,
    fiveCodePolynomial_eq_affine_support dom u0 u1 hsupport c]

/-- The interpolated moving direction is a nonzero cubic-or-lower polynomial. -/
theorem supportFourDirectionPolynomial_ne_zero
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    supportFourInterpolant dom u1 u1 ≠ 0 := by
  have hnonempty : (directionSupportSet u1).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hnonempty
  have heval := supportFourInterpolant_eval_of_mem_support dom u1 u1 hi
  have hu1 : u1 i ≠ 0 := by
    simpa [directionSupportSet] using hi
  intro hzero
  rw [hzero, eval_zero] at heval
  exact hu1 heval.symm

theorem supportFourDirectionPolynomial_natDegree_le_three
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (supportFourInterpolant dom u1 u1).natDegree ≤ 3 := by
  have hlt : (supportFourInterpolant dom u1 u1).natDegree < (4 : Nat) :=
    (Polynomial.natDegree_lt_iff_degree_lt
    (supportFourDirectionPolynomial_ne_zero dom u1 hsupport)).mpr
      (supportFourInterpolant_degree_lt_four dom u1 u1 hsupport)
  omega

/-- The fixed zero-coordinate kernel shared by all `t = 5` traces. -/
noncomputable def fiveCommonKernel
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F) :
    Finset {i : Fin 16 // i ∈ directionZeroSet u1} :=
  (Finset.univ : Finset {i : Fin 16 // i ∈ directionZeroSet u1}).filter
    (fun i =>
      (supportFourInterpolant dom u1 u1).eval (dom i.1) = 0 ∧
      (supportFourInterpolant dom u1 u0).eval (dom i.1) = u0 i.1)

theorem fiveCommonKernel_card_le_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (fiveCommonKernel dom u0 u1).card ≤ 3 := by
  let R := supportFourInterpolant dom u1 u1
  have hR0 : R ≠ 0 := by
    simpa only [R] using supportFourDirectionPolynomial_ne_zero dom u1 hsupport
  have hRdeg : R.natDegree ≤ 3 := by
    simpa only [R] using
      supportFourDirectionPolynomial_natDegree_le_three dom u1 hsupport
  calc
    (fiveCommonKernel dom u0 u1).card ≤ R.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn
        (fun i : {i : Fin 16 // i ∈ directionZeroSet u1} => dom i.1)
      · intro i hi
        change dom i.1 ∈ R.roots.toFinset
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hR0]
        exact (Finset.mem_filter.mp hi).2.1
      · intro i _ j _ hij
        exact Subtype.ext (dom.injective hij)
    _ ≤ R.roots.card := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := Polynomial.card_roots' R
    _ ≤ 3 := hRdeg

theorem fiveCommonKernel_subset_zeroAgreementTrace
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5}) :
    fiveCommonKernel dom u0 u1 ⊆ zeroAgreementTrace c.1 u0 u1 := by
  intro i hi
  have hdata := (Finset.mem_filter.mp hi).2
  rw [zeroAgreementTrace, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hc := fiveCodeword_eval_eq_affine_support dom u0 u1 hsupport c i.1
  simp only [eval_add, eval_mul, eval_C, hdata.1, mul_zero, add_zero] at hc
  exact hc.trans hdata.2

theorem fiveScalar_injective
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    Function.Injective (fiveScalar dom u0 u1) := by
  intro c d hscalar
  apply Subtype.ext
  funext i
  rw [← fiveCodePolynomial_eval dom u0 u1 c i,
    ← fiveCodePolynomial_eval dom u0 u1 d i,
    fiveCodePolynomial_eq_affine_support dom u0 u1 hsupport c,
    fiveCodePolynomial_eq_affine_support dom u0 u1 hsupport d,
    hscalar]

/-- Distinct `t = 5` traces meet in exactly the common interpolation kernel. -/
theorem zeroAgreementTrace_inter_eq_fiveCommonKernel
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c d : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5})
    (hne : c ≠ d) :
    zeroAgreementTrace c.1 u0 u1 ∩ zeroAgreementTrace d.1 u0 u1 =
      fiveCommonKernel dom u0 u1 := by
  apply Finset.Subset.antisymm
  · intro i hi
    have hic := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
    have hid := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
    have hc := fiveCodeword_eval_eq_affine_support dom u0 u1 hsupport c i.1
    have hd := fiveCodeword_eval_eq_affine_support dom u0 u1 hsupport d i.1
    simp only [eval_add, eval_mul, eval_C] at hc hd
    have hscalar : fiveScalar dom u0 u1 c ≠ fiveScalar dom u0 u1 d := by
      intro h
      exact hne (fiveScalar_injective dom u0 u1 hsupport h)
    have hmul :
        (fiveScalar dom u0 u1 c - fiveScalar dom u0 u1 d) *
          (supportFourInterpolant dom u1 u1).eval (dom i.1) = 0 := by
      linear_combination (hc.symm.trans hic) - (hd.symm.trans hid)
    have hR : (supportFourInterpolant dom u1 u1).eval (dom i.1) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hscalar)
    rw [fiveCommonKernel, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hR, ?_⟩
    rw [hR, mul_zero, add_zero] at hc
    exact hc.symm.trans hic
  · exact Finset.subset_inter
      (fiveCommonKernel_subset_zeroAgreementTrace dom u0 u1 hsupport c)
      (fiveCommonKernel_subset_zeroAgreementTrace dom u0 u1 hsupport d)

open Classical in
/-- The support-four bottom stratum has at most four codewords. -/
theorem zeroAgreementStratum_five_card_le_four_of_support_four
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (zeroAgreementStratum dom 4 9 u0 u1 5).card ≤ 4 := by
  by_contra hnot
  have hfive : 5 ≤ (zeroAgreementStratum dom 4 9 u0 u1 5).card := by omega
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hfive
  let e : Fin 5 ≃ W := (W.equivFinOfCardEq hWcard).symm
  let c : Fin 5 →
      {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 5} :=
    fun i => ⟨(e i).1, hWsub (e i).2⟩
  have hcinj : Function.Injective c := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    simpa only [c] using congrArg Subtype.val hij
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let B : Fin 5 → Finset U := fun i => zeroAgreementTrace (c i).1 u0 u1
  let T : Finset U := fiveCommonKernel dom u0 u1
  have hUcard : (Finset.univ : Finset U).card = 12 := by
    rw [Finset.card_univ]
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hTcard : T.card ≤ 3 := by
    simpa only [T] using fiveCommonKernel_card_le_three dom u0 u1 hsupport
  have hpacking := pencil_sunflower_core
    (Finset.univ : Finset U) 5 T.card (by norm_num) B T
    (fun _ => Finset.subset_univ _)
    (fun i => by
      rw [show B i = zeroAgreementTrace (c i).1 u0 u1 by rfl,
        zeroAgreementTrace_card]
      exact (Finset.mem_filter.mp (c i).2).2)
    rfl
    (fun i => by
      simpa only [B, T] using
        fiveCommonKernel_subset_zeroAgreementTrace dom u0 u1 hsupport (c i))
    (fun i j hij => by
      simpa only [B, T] using
        zeroAgreementTrace_inter_eq_fiveCommonKernel
          dom u0 u1 hsupport (c i) (c j) (hcinj.ne hij))
  rw [hUcard] at hpacking
  omega

/-! ## The full-moving-support subfamily at `t = 6` -/

/-- A generic common-kernel packing count. The punctured blocks are pairwise disjoint, so their
total size plus the kernel fits in the ambient finset. -/
theorem commonKernel_packing_bound
    {I U : Type} [Fintype I] [DecidableEq U]
    (ambient : Finset U) (w : Nat) (B : I → Finset U) (T : Finset U)
    (hsub : ∀ i, B i ⊆ ambient)
    (hsize : ∀ i, (B i).card = w)
    (hTsubAmbient : T ⊆ ambient)
    (hTsub : ∀ i, T ⊆ B i)
    (hpair : ∀ i j, i ≠ j → B i ∩ B j = T) :
    Fintype.card I * (w - T.card) + T.card ≤ ambient.card := by
  classical
  let C : I → Finset U := fun i => B i \ T
  have hCcard : ∀ i, (C i).card = w - T.card := by
    intro i
    rw [show C i = B i \ T by rfl,
      Finset.card_sdiff_of_subset (hTsub i), hsize i]
  have hCdisjT : ∀ i, Disjoint T (C i) := by
    intro i
    rw [show C i = B i \ T by rfl]
    exact Finset.sdiff_disjoint.symm
  have hCdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    change x ∈ B i \ T at hxi
    change x ∈ B j \ T at hxj
    rw [Finset.mem_sdiff] at hxi hxj
    have hmem : x ∈ B i ∩ B j := Finset.mem_inter.mpr ⟨hxi.1, hxj.1⟩
    rw [hpair i j hij] at hmem
    exact hxi.2 hmem
  let D : Finset U := Finset.univ.biUnion C
  have hDcard : D.card = Fintype.card I * (w - T.card) := by
    rw [show D = Finset.univ.biUnion C by rfl, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun i _ => hCcard i)]
      simp [Finset.sum_const, Finset.card_univ]
    · intro i _ j _ hij
      exact hCdisj i j hij
  have hTD : Disjoint T D := by
    rw [show D = Finset.univ.biUnion C by rfl,
      Finset.disjoint_biUnion_right]
    intro i _
    exact hCdisjT i
  have hDsub : D ⊆ ambient := by
    intro x hx
    rw [show D = Finset.univ.biUnion C by rfl, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact hsub i (Finset.mem_sdiff.mp hxi).1
  have hunion : T ∪ D ⊆ ambient := Finset.union_subset hTsubAmbient hDsub
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hTD, hDcard] at hcard
  omega

/-- The invariant full-moving-support part of the `t = 6` stratum. An existential predicate is
used deliberately: membership does not depend on which heavy fiber a choice function selects. -/
noncomputable def fullSupportSixStratum
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F) : Finset (Fin 16 → F) :=
  (zeroAgreementStratum dom 4 9 u0 u1 6).filter
    (fun c => ∃ gamma : F,
      supportRatioFiber c u0 u1 gamma = directionSupportSet u1)

theorem mem_fullSupportSixStratum
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F) (c : Fin 16 → F) :
    c ∈ fullSupportSixStratum dom u0 u1 ↔
      c ∈ zeroAgreementStratum dom 4 9 u0 u1 6 ∧
        ∃ gamma : F,
          supportRatioFiber c u0 u1 gamma = directionSupportSet u1 := by
  simp only [fullSupportSixStratum, Finset.mem_filter]

theorem exists_codePolynomial_of_mem_fullSupportSixStratum
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    {c : Fin 16 → F} (hc : c ∈ fullSupportSixStratum dom u0 u1) :
    ∃ q : F[X], q.degree < 4 ∧ c = fun i ↦ q.eval (dom i) := by
  have hcStratum := (mem_fullSupportSixStratum dom u0 u1 c).mp hc |>.1
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp hcStratum).1
  rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
  exact hcApp.2.1

noncomputable def sixFullCodePolynomial
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1}) : F[X] :=
  Classical.choose (exists_codePolynomial_of_mem_fullSupportSixStratum dom u0 u1 c.2)

theorem sixFullCodePolynomial_degree_lt
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1}) :
    (sixFullCodePolynomial dom u0 u1 c).degree < 4 :=
  (Classical.choose_spec
    (exists_codePolynomial_of_mem_fullSupportSixStratum dom u0 u1 c.2)).1

theorem sixFullCodePolynomial_eval
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1})
    (i : Fin 16) :
    (sixFullCodePolynomial dom u0 u1 c).eval (dom i) = c.1 i := by
  have h := (Classical.choose_spec
    (exists_codePolynomial_of_mem_fullSupportSixStratum dom u0 u1 c.2)).2
  exact congrFun h.symm i

/-- A selected scalar certifying invariant full-support membership. -/
noncomputable def sixFullScalar
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1}) : F :=
  Classical.choose ((mem_fullSupportSixStratum dom u0 u1 c.1).mp c.2).2

theorem supportRatioFiber_sixFullScalar_eq_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1}) :
    supportRatioFiber c.1 u0 u1 (sixFullScalar dom u0 u1 c) =
      directionSupportSet u1 := by
  exact Classical.choose_spec
    ((mem_fullSupportSixStratum dom u0 u1 c.1).mp c.2).2

theorem sixFullCodePolynomial_eq_affine_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1}) :
    sixFullCodePolynomial dom u0 u1 c =
      supportFourInterpolant dom u1 u0 +
        C (sixFullScalar dom u0 u1 c) * supportFourInterpolant dom u1 u1 := by
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (directionSupportSet u1) dom.injective.injOn ?_ ?_ ?_
  · simpa only [hsupport] using sixFullCodePolynomial_degree_lt dom u0 u1 c
  · rw [hsupport]
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact supportFourInterpolant_degree_lt_four dom u1 u0 hsupport
    · by_cases hgamma : sixFullScalar dom u0 u1 c = 0
      · simp only [hgamma, C_0, zero_mul, degree_zero]
        exact WithBot.bot_lt_coe 4
      · rw [Polynomial.degree_C_mul hgamma]
        exact supportFourInterpolant_degree_lt_four dom u1 u1 hsupport
  · intro i hi
    have hfiber : i ∈ supportRatioFiber c.1 u0 u1
        (sixFullScalar dom u0 u1 c) := by
      rw [supportRatioFiber_sixFullScalar_eq_support dom u0 u1 c]
      exact hi
    have hratio := (mem_supportRatioFiber c.1 u0 u1
      (sixFullScalar dom u0 u1 c) i).mp hfiber |>.2
    have hu1 : u1 i ≠ 0 := by
      simpa [directionSupportSet] using hi
    rw [div_eq_iff hu1] at hratio
    simp only [eval_add, eval_mul, eval_C,
      sixFullCodePolynomial_eval,
      supportFourInterpolant_eval_of_mem_support dom u1 u0 hi,
      supportFourInterpolant_eval_of_mem_support dom u1 u1 hi]
    linear_combination hratio

theorem sixFullCodeword_eval_eq_affine_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1})
    (i : Fin 16) :
    c.1 i =
      (supportFourInterpolant dom u1 u0 +
        C (sixFullScalar dom u0 u1 c) *
          supportFourInterpolant dom u1 u1).eval (dom i) := by
  rw [← sixFullCodePolynomial_eval dom u0 u1 c i,
    sixFullCodePolynomial_eq_affine_support dom u0 u1 hsupport c]

theorem sixFullScalar_injective
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    Function.Injective (sixFullScalar dom u0 u1) := by
  intro c d hscalar
  apply Subtype.ext
  funext i
  rw [← sixFullCodePolynomial_eval dom u0 u1 c i,
    ← sixFullCodePolynomial_eval dom u0 u1 d i,
    sixFullCodePolynomial_eq_affine_support dom u0 u1 hsupport c,
    sixFullCodePolynomial_eq_affine_support dom u0 u1 hsupport d,
    hscalar]

theorem fiveCommonKernel_subset_sixFullTrace
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1}) :
    fiveCommonKernel dom u0 u1 ⊆ zeroAgreementTrace c.1 u0 u1 := by
  intro i hi
  have hdata := (Finset.mem_filter.mp hi).2
  rw [zeroAgreementTrace, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hc := sixFullCodeword_eval_eq_affine_support dom u0 u1 hsupport c i.1
  simp only [eval_add, eval_mul, eval_C, hdata.1, mul_zero, add_zero] at hc
  exact hc.trans hdata.2

theorem sixFullTrace_inter_eq_fiveCommonKernel
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (c d : {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1})
    (hne : c ≠ d) :
    zeroAgreementTrace c.1 u0 u1 ∩ zeroAgreementTrace d.1 u0 u1 =
      fiveCommonKernel dom u0 u1 := by
  apply Finset.Subset.antisymm
  · intro i hi
    have hic := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
    have hid := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
    have hc := sixFullCodeword_eval_eq_affine_support dom u0 u1 hsupport c i.1
    have hd := sixFullCodeword_eval_eq_affine_support dom u0 u1 hsupport d i.1
    simp only [eval_add, eval_mul, eval_C] at hc hd
    have hscalar : sixFullScalar dom u0 u1 c ≠ sixFullScalar dom u0 u1 d := by
      intro h
      exact hne (sixFullScalar_injective dom u0 u1 hsupport h)
    have hmul :
        (sixFullScalar dom u0 u1 c - sixFullScalar dom u0 u1 d) *
          (supportFourInterpolant dom u1 u1).eval (dom i.1) = 0 := by
      linear_combination (hc.symm.trans hic) - (hd.symm.trans hid)
    have hR : (supportFourInterpolant dom u1 u1).eval (dom i.1) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hscalar)
    rw [fiveCommonKernel, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hR, ?_⟩
    rw [hR, mul_zero, add_zero] at hc
    exact hc.symm.trans hic
  · exact Finset.subset_inter
      (fiveCommonKernel_subset_sixFullTrace dom u0 u1 hsupport c)
      (fiveCommonKernel_subset_sixFullTrace dom u0 u1 hsupport d)

open Classical in
/-- At most three `t = 6` codewords can appear through all four moving coordinates. -/
theorem fullSupportSixStratum_card_le_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (fullSupportSixStratum dom u0 u1).card ≤ 3 := by
  by_contra hnot
  have hfour : 4 ≤ (fullSupportSixStratum dom u0 u1).card := by omega
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hfour
  let e : Fin 4 ≃ W := (W.equivFinOfCardEq hWcard).symm
  let c : Fin 4 →
      {c : Fin 16 → F // c ∈ fullSupportSixStratum dom u0 u1} :=
    fun i => ⟨(e i).1, hWsub (e i).2⟩
  have hcinj : Function.Injective c := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    simpa only [c] using congrArg Subtype.val hij
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let B : Fin 4 → Finset U := fun i => zeroAgreementTrace (c i).1 u0 u1
  let T : Finset U := fiveCommonKernel dom u0 u1
  have hUcard : (Finset.univ : Finset U).card = 12 := by
    rw [Finset.card_univ]
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hTcard : T.card ≤ 3 := by
    simpa only [T] using fiveCommonKernel_card_le_three dom u0 u1 hsupport
  have hpacking := commonKernel_packing_bound
    (Finset.univ : Finset U) 6 B T
    (fun _ => Finset.subset_univ _)
    (fun i => by
      rw [show B i = zeroAgreementTrace (c i).1 u0 u1 by rfl,
        zeroAgreementTrace_card]
      exact (Finset.mem_filter.mp
        ((mem_fullSupportSixStratum dom u0 u1 (c i).1).mp (c i).2).1).2)
    (Finset.subset_univ _)
    (fun i => by
      simpa only [B, T] using
        fiveCommonKernel_subset_sixFullTrace dom u0 u1 hsupport (c i))
    (fun i j hij => by
      simpa only [B, T] using
        sixFullTrace_inter_eq_fiveCommonKernel
          dom u0 u1 hsupport (c i) (c j) (hcinj.ne hij))
  rw [hUcard] at hpacking
  norm_num at hpacking
  omega

/-- The complementary `t = 6` residual: codewords with no scalar using all four moving
coordinates. -/
noncomputable def threeOfFourSixResidual
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F) : Finset (Fin 16 → F) :=
  zeroAgreementStratum dom 4 9 u0 u1 6 \ fullSupportSixStratum dom u0 u1

theorem mem_threeOfFourSixResidual
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F) (c : Fin 16 → F) :
    c ∈ threeOfFourSixResidual dom u0 u1 ↔
      c ∈ zeroAgreementStratum dom 4 9 u0 u1 6 ∧
        c ∉ fullSupportSixStratum dom u0 u1 := by
  simp only [threeOfFourSixResidual, Finset.mem_sdiff]

/-- In the residual, every heavy support-ratio fiber has exactly three of the four moving
coordinates. -/
theorem supportRatioFiber_card_eq_three_of_mem_threeOfFourSixResidual
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {c : Fin 16 → F} (hc : c ∈ threeOfFourSixResidual dom u0 u1)
    {gamma : F} (hheavy : 3 ≤ (supportRatioFiber c u0 u1 gamma).card) :
    (supportRatioFiber c u0 u1 gamma).card = 3 := by
  have hcData := (mem_threeOfFourSixResidual dom u0 u1 c).mp hc
  have hsub : supportRatioFiber c u0 u1 gamma ⊆ directionSupportSet u1 := by
    intro i hi
    exact (mem_supportRatioFiber c u0 u1 gamma i).mp hi |>.1
  have hle : (supportRatioFiber c u0 u1 gamma).card ≤ 4 := by
    have := Finset.card_le_card hsub
    omega
  have hcases : (supportRatioFiber c u0 u1 gamma).card = 3 ∨
      (supportRatioFiber c u0 u1 gamma).card = 4 := by omega
  rcases hcases with hthree | hfour
  · exact hthree
  · exfalso
    have heq : supportRatioFiber c u0 u1 gamma = directionSupportSet u1 := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hsupport, hfour]
    exact hcData.2 ((mem_fullSupportSixStratum dom u0 u1 c).mpr
      ⟨hcData.1, gamma, heq⟩)

/-- Every residual codeword has a heavy fiber, and that fiber has exactly three moving
coordinates. -/
theorem exists_supportRatioFiber_card_eq_three_of_mem_threeOfFourSixResidual
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {c : Fin 16 → F} (hc : c ∈ threeOfFourSixResidual dom u0 u1) :
    ∃ gamma : F, (supportRatioFiber c u0 u1 gamma).card = 3 := by
  have hcStratum := (mem_threeOfFourSixResidual dom u0 u1 c).mp hc |>.1
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp hcStratum).1
  obtain ⟨gamma, hlarge⟩ :=
    exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
      dom 4 9 u0 u1 c hcApp
  have hzero : (directionZeroAgreementSet c u0 u1).card = 6 :=
    (Finset.mem_filter.mp hcStratum).2
  refine ⟨gamma,
    supportRatioFiber_card_eq_three_of_mem_threeOfFourSixResidual
      dom u0 u1 hsupport hc ?_⟩
  omega

/-! ## Plotkin caps and the remaining `t = 6` obstruction -/

open Classical in
theorem zeroAgreementStratum_seven_card_le_three_of_support_four
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (zeroAgreementStratum dom 4 9 u0 u1 7).card ≤ 3 := by
  let I := {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 7}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let S : I → Finset U := fun c => zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hsize : ∀ c : I, (S c).card = 7 := by
    intro c
    rw [zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : ∀ c c' : I, c ≠ c' → (S c ∩ S c').card ≤ 3 := by
    intro c c' hne
    apply zeroAgreementTrace_pair_card_le_three dom u0 u1 7 c.2 c'.2
    exact fun h => hne (Subtype.ext h)
  have hplotkin := constantWeight_plotkin_div S 7 3 hsize hpair (by
    rw [hU]
    norm_num)
  norm_num [hU] at hplotkin
  simpa [I] using hplotkin

open Classical in
theorem zeroAgreementStratum_eight_card_le_two_of_support_four
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (zeroAgreementStratum dom 4 9 u0 u1 8).card ≤ 2 := by
  let I := {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 8}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let S : I → Finset U := fun c => zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hsize : ∀ c : I, (S c).card = 8 := by
    intro c
    rw [zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : ∀ c c' : I, c ≠ c' → (S c ∩ S c').card ≤ 3 := by
    intro c c' hne
    apply zeroAgreementTrace_pair_card_le_three dom u0 u1 8 c.2 c'.2
    exact fun h => hne (Subtype.ext h)
  have hplotkin := constantWeight_plotkin_div S 8 3 hsize hpair (by
    rw [hU]
    norm_num)
  norm_num [hU] at hplotkin
  simpa [I] using hplotkin

open Classical in
/-- The top support-four stratum is actually unique. Two size-eight traces in a twelve-point
zero-coordinate universe would meet in at least four points, contradicting the RS intersection
cap three. -/
theorem zeroAgreementStratum_eight_card_le_one_of_support_four
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4) :
    (zeroAgreementStratum dom 4 9 u0 u1 8).card ≤ 1 := by
  by_contra hnot
  have htwo : 1 < (zeroAgreementStratum dom 4 9 u0 u1 8).card := by omega
  obtain ⟨c, hc, d, hd, hne⟩ := Finset.one_lt_card.mp htwo
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let A : Finset U := zeroAgreementTrace c u0 u1
  let B : Finset U := zeroAgreementTrace d u0 u1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hA : A.card = 8 := by
    rw [show A = zeroAgreementTrace c u0 u1 by rfl, zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hc).2
  have hB : B.card = 8 := by
    rw [show B = zeroAgreementTrace d u0 u1 by rfl, zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hd).2
  have hinter : (A ∩ B).card ≤ 3 := by
    simpa only [A, B] using
      zeroAgreementTrace_pair_card_le_three dom u0 u1 8 hc hd hne
  have hunion : (A ∪ B).card ≤ 12 := by
    calc
      (A ∪ B).card ≤ (Finset.univ : Finset U).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 12 := by simp [hU]
  have hbook := Finset.card_union_add_card_inter A B
  omega

/-- At `t = 6`, ambient size twelve and intersection cap three make the Plotkin denominator
exactly zero. Thus the strict positivity premise used for the neighboring strata is unavailable. -/
theorem support_four_six_plotkin_denominator_eq_zero :
    (6 : ℕ) ^ 2 = 12 * 3 := by
  norm_num

open Classical in
/-- For a zero-safe support-four line, every controlled stratum contributes at most fourteen.
The only remaining term is the cardinality of the `t = 6` zero-agreement stratum. -/
theorem lineBadScalars_card_le_six_stratum_add_fourteen_of_support_four
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 4) :
    (lineBadScalars dom 4 9 u0 u1).card ≤
      (zeroAgreementStratum dom 4 9 u0 u1 6).card + 14 := by
  apply (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    dom 4 9 u0 u1 hsafe).trans
  rw [puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
    dom 4 9 u0 u1 hsafe]
  have hempty : ∀ t, t < 5 →
      zeroAgreementStratum dom 4 9 u0 u1 t = ∅ := by
    intro t ht
    apply zeroAgreementStratum_eq_empty_of_add_support_lt dom 4 9 u0 u1
    omega
  have hfive := zeroAgreementStratum_five_card_le_four_of_support_four
    dom u0 u1 hsupport
  have hseven := zeroAgreementStratum_seven_card_le_three_of_support_four
    dom u0 u1 hsupport
  have height := zeroAgreementStratum_eight_card_le_one_of_support_four
    dom u0 u1 hsupport
  have hweight :
      (∑ t ∈ Finset.range 9,
        (zeroAgreementStratum dom 4 9 u0 u1 t).card *
          ((directionSupportSet u1).card / (9 - t))) =
        (zeroAgreementStratum dom 4 9 u0 u1 5).card +
          (zeroAgreementStratum dom 4 9 u0 u1 6).card +
          (zeroAgreementStratum dom 4 9 u0 u1 7).card * 2 +
          (zeroAgreementStratum dom 4 9 u0 u1 8).card * 4 := by
    norm_num [Finset.sum_range_succ, hempty, hsupport]
  rw [hweight]
  omega

/-- Weaker compatibility form of the support-four residual budget. -/
theorem lineBadScalars_card_le_six_stratum_add_eighteen_of_support_four
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 4) :
    (lineBadScalars dom 4 9 u0 u1).card ≤
      (zeroAgreementStratum dom 4 9 u0 u1 6).card + 18 := by
  exact (lineBadScalars_card_le_six_stratum_add_fourteen_of_support_four
    dom u0 u1 hsafe hsupport).trans (by omega)

#print axioms zeroAgreementStratum_five_card_le_four_of_support_four
#print axioms fullSupportSixStratum_card_le_three
#print axioms exists_supportRatioFiber_card_eq_three_of_mem_threeOfFourSixResidual
#print axioms zeroAgreementStratum_seven_card_le_three_of_support_four
#print axioms zeroAgreementStratum_eight_card_le_one_of_support_four
#print axioms lineBadScalars_card_le_six_stratum_add_fourteen_of_support_four

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine
