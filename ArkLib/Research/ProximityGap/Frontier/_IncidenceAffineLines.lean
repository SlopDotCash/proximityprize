/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Mathlib

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace ProximityGap.IncidenceAffineLines
variable {F V I : Type} [Field F] [AddCommGroup V] [Module F V]

def OnLine (gamma : I → F) (w : I → V) (U D : V) (i : I) : Prop :=
  w i = U + gamma i • D

def CollinearTriple (gamma : I → F) (w : I → V) (i j k : I) : Prop :=
  ∃ U D : V, OnLine gamma w U D i ∧ OnLine gamma w U D j ∧ OnLine gamma w U D k

theorem params_eq_of_two {a b : F} (hab : a ≠ b) {U D U' D' : V}
    (ha : U + a • D = U' + a • D')
    (hb : U + b • D = U' + b • D') : U = U' ∧ D = D' := by
  have hz : (a - b) • (D - D') = 0 := by
    calc
      _ = (U + a • D - (U' + a • D')) -
          (U + b • D - (U' + b • D')) := by module
      _ = 0 := by
        rw [ha, hb]
        abel
  have hD : D = D' := by
    rcases smul_eq_zero.mp hz with h | h
    · exact False.elim ((sub_ne_zero.mpr hab) h)
    · exact sub_eq_zero.mp h
  rw [hD] at ha
  exact ⟨add_right_cancel ha, hD⟩

theorem distinct_lines_intersect_at_most_one
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    {U D U' D' : V} (hne : (U,D) ≠ (U',D')) {a b : I}
    (ha : OnLine gamma w U D a) (ha' : OnLine gamma w U' D' a)
    (hb : OnLine gamma w U D b) (hb' : OnLine gamma w U' D' b) : a = b := by
  by_contra hab
  have hgamma : gamma a ≠ gamma b := fun h => hab (hinj h)
  obtain ⟨hU,hD⟩ := params_eq_of_two hgamma (ha.symm.trans ha') (hb.symm.trans hb')
  exact hne (Prod.ext hU hD)

theorem collinear_triple_forces_onLine
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    {U D : V} {a b c : I} (hab : a ≠ b)
    (ha : OnLine gamma w U D a) (hb : OnLine gamma w U D b)
    (hcol : CollinearTriple gamma w a b c) : OnLine gamma w U D c := by
  obtain ⟨U',D',ha',hb',hc'⟩ := hcol
  have hgamma : gamma a ≠ gamma b := fun h => hab (hinj h)
  obtain ⟨hU,hD⟩ := params_eq_of_two hgamma (ha.symm.trans ha') (hb.symm.trans hb')
  simpa only [hU,hD] using hc'

theorem mixed_completion_unique
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    {U D : V} {a a' b c : I} (hbc : b ≠ c)
    (hbnot : ¬ OnLine gamma w U D b)
    (ha : OnLine gamma w U D a) (ha' : OnLine gamma w U D a')
    (hcol : CollinearTriple gamma w a b c)
    (hcol' : CollinearTriple gamma w a' b c) : a = a' := by
  obtain ⟨U1,D1,ha1,hb1,hc1⟩ := hcol
  obtain ⟨U2,D2,ha2,hb2,hc2⟩ := hcol'
  have ha'1 : OnLine gamma w U1 D1 a' :=
    collinear_triple_forces_onLine gamma w hinj hbc hb1 hc1
      ⟨U2,D2,hb2,hc2,ha2⟩
  by_contra haa'
  have hgamma : gamma a ≠ gamma a' := fun h => haa' (hinj h)
  obtain ⟨hU,hD⟩ := params_eq_of_two hgamma
    (ha.symm.trans ha1) (ha'.symm.trans ha'1)
  apply hbnot
  simpa only [hU,hD] using hb1

theorem mixed_triples_card_le_sq
    [DecidableEq I]
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (B R : Finset I) (U D : V)
    (hB : ∀ a ∈ B, OnLine gamma w U D a)
    (hR : ∀ b ∈ R, ¬ OnLine gamma w U D b) :
    ((B.product (R.product R)).filter (fun z =>
      z.2.1 ≠ z.2.2 ∧ CollinearTriple gamma w z.1 z.2.1 z.2.2)).card ≤ R.card ^ 2 := by
  classical
  let M := (B.product (R.product R)).filter (fun z =>
      z.2.1 ≠ z.2.2 ∧ CollinearTriple gamma w z.1 z.2.1 z.2.2)
  change M.card ≤ R.card ^ 2
  calc
    M.card ≤ (R.product R).card := by
      apply Finset.card_le_card_of_injOn (fun z : I × (I × I) => z.2)
      · intro z hz
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2
      · intro x hx y hy hxy
        obtain ⟨hxprod,hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨hyprod,hyc⟩ := Finset.mem_filter.mp hy
        have hxB := (Finset.mem_product.mp hxprod).1
        have hyB := (Finset.mem_product.mp hyprod).1
        have hxR := (Finset.mem_product.mp
          (Finset.mem_product.mp hxprod).2).1
        change x.2 = y.2 at hxy
        have hycol := hyc.2
        rw [← hxy] at hycol
        have haeq := mixed_completion_unique gamma w hinj hxc.1
          (hR _ hxR) (hB _ hxB) (hB _ hyB) hxc.2 hycol
        exact Prod.ext haeq hxy
    _ = R.card ^ 2 := by
      rw [Finset.product_eq_sprod, Finset.card_product, pow_two]

theorem params_mem_code_of_two
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (C : Submodule F V) {U D : V} {a b : I} (hab : a ≠ b)
    (ha : OnLine gamma w U D a) (hb : OnLine gamma w U D b)
    (hwa : w a ∈ C) (hwb : w b ∈ C) : U ∈ C ∧ D ∈ C := by
  have hgamma : gamma a - gamma b ≠ 0 :=
    sub_ne_zero.mpr (fun h => hab (hinj h))
  have hdiff : w a - w b = (gamma a - gamma b) • D := by
    rw [ha,hb,sub_smul]
    abel
  have hD : D = (gamma a - gamma b)⁻¹ • (w a - w b) := by
    rw [hdiff,smul_smul,inv_mul_cancel₀ hgamma,one_smul]
  have hDC : D ∈ C := by
    rw [hD]
    exact C.smul_mem _ (C.sub_mem hwa hwb)
  have hU : U = w a - gamma a • D := by
    rw [ha]
    abel
  refine ⟨?_,hDC⟩
  rw [hU]
  exact C.sub_mem hwa (C.smul_mem _ hDC)

theorem triple_line_partition
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (U D : V) {a b c : I} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcol : CollinearTriple gamma w a b c) :
    (OnLine gamma w U D a ∧ OnLine gamma w U D b ∧ OnLine gamma w U D c) ∨
    (¬ OnLine gamma w U D a ∧ ¬ OnLine gamma w U D b ∧ ¬ OnLine gamma w U D c) ∨
    (OnLine gamma w U D a ∧ ¬ OnLine gamma w U D b ∧ ¬ OnLine gamma w U D c) ∨
    (¬ OnLine gamma w U D a ∧ OnLine gamma w U D b ∧ ¬ OnLine gamma w U D c) ∨
    (¬ OnLine gamma w U D a ∧ ¬ OnLine gamma w U D b ∧ OnLine gamma w U D c) := by
  have hAB : OnLine gamma w U D a → OnLine gamma w U D b → OnLine gamma w U D c :=
    fun ha hb => collinear_triple_forces_onLine gamma w hinj hab ha hb hcol
  obtain ⟨U',D',ha',hb',hc'⟩ := hcol
  have hAC : OnLine gamma w U D a → OnLine gamma w U D c → OnLine gamma w U D b :=
    fun ha hc => collinear_triple_forces_onLine gamma w hinj hac ha hc ⟨U',D',ha',hc',hb'⟩
  have hBC : OnLine gamma w U D b → OnLine gamma w U D c → OnLine gamma w U D a :=
    fun hb hc => collinear_triple_forces_onLine gamma w hinj hbc hb hc ⟨U',D',hb',hc',ha'⟩
  by_cases ha : OnLine gamma w U D a
  all_goals by_cases hb : OnLine gamma w U D b
  all_goals by_cases hc : OnLine gamma w U D c
  all_goals aesop

theorem block_step_arithmetic (r ell s : ℕ) (hs : s ≤ ell) :
    3 * s * r ^ 2 + 3 * r ^ 3 + s ^ 2 * r ^ 2 ≤
      3 * (r + ell) ^ 3 + s ^ 2 * (r + ell) ^ 2 := by
  have hcube : r ^ 3 + s * r ^ 2 ≤ (r + ell) ^ 3 := by
    have hmul := Nat.mul_le_mul_right (r ^ 2) hs
    nlinarith [Nat.zero_le (ell ^ 3), Nat.zero_le (ell * r ^ 2),
      Nat.zero_le (ell ^ 2 * r)]
  have hsquare : r ^ 2 ≤ (r + ell) ^ 2 := by
    nlinarith [Nat.zero_le (ell ^ 2), Nat.zero_le (r * ell)]
  have hc3 := Nat.mul_le_mul_left 3 hcube
  have hs2 := Nat.mul_le_mul_left (s ^ 2) hsquare
  nlinarith

noncomputable def collinearTriples [DecidableEq I] (gamma : I -> F) (w : I -> V) (S : Finset I) : Finset (I × (I × I)) :=
  (S.product (S.product S)).filter (fun z =>
    z.1 ≠ z.2.1 ∧ z.1 ≠ z.2.2 ∧ z.2.1 ≠ z.2.2 ∧
      CollinearTriple gamma w z.1 z.2.1 z.2.2)

noncomputable def mixedTriples [DecidableEq I] (gamma : I -> F) (w : I -> V) (B R : Finset I) : Finset (I × (I × I)) :=
  (B.product (R.product R)).filter (fun z =>
    z.2.1 ≠ z.2.2 ∧ CollinearTriple gamma w z.1 z.2.1 z.2.2)

def swapAB (z : I × (I × I)) : I × (I × I) := (z.2.1,z.1,z.2.2)
def swapAC (z : I × (I × I)) : I × (I × I) := (z.2.2,z.2.1,z.1)

theorem collinearTriples_card_le_cube [DecidableEq I]
    (gamma : I -> F) (w : I -> V) (S : Finset I) :
    (collinearTriples gamma w S).card ≤ S.card ^ 3 := by
  calc
    _ ≤ (S.product (S.product S)).card := Finset.card_filter_le _ _
    _ = _ := by
      simp only [Finset.product_eq_sprod, Finset.card_product]
      ring

theorem collinearTriples_block_step [DecidableEq I]
    (gamma : I -> F) (w : I -> V) (hinj : Function.Injective gamma)
    (S : Finset I) (U D : V) :
    let B := S.filter (OnLine gamma w U D)
    let R := S \ B
    (collinearTriples gamma w S).card ≤
      B.card ^ 3 + 3 * R.card ^ 2 + (collinearTriples gamma w R).card := by
  classical
  let B := S.filter (OnLine gamma w U D)
  let R := S \ B
  let M := mixedTriples gamma w B R
  change (collinearTriples gamma w S).card ≤
      B.card ^ 3 + 3 * R.card ^ 2 + (collinearTriples gamma w R).card
  have hmemB : ∀ a ∈ S, OnLine gamma w U D a ↔ a ∈ B := by
    intro a ha
    simp [B,ha]
  have hmemR : ∀ a ∈ S, ¬ OnLine gamma w U D a ↔ a ∈ R := by
    intro a ha
    simp [R,B,ha]
  have hB : ∀ a ∈ B, OnLine gamma w U D a := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hR : ∀ a ∈ R, ¬ OnLine gamma w U D a := by
    intro a ha hline
    obtain ⟨haS,haB⟩ := Finset.mem_sdiff.mp ha
    exact haB (Finset.mem_filter.mpr ⟨haS,hline⟩)
  have hcover : collinearTriples gamma w S ⊆
      collinearTriples gamma w B ∪ (collinearTriples gamma w R ∪
        (M ∪ (M.image swapAB ∪ M.image swapAC))) := by
    rintro ⟨a,b,c⟩ hz
    obtain ⟨hp,hab,hac,hbc,hcol⟩ := Finset.mem_filter.mp hz
    have haS := (Finset.mem_product.mp hp).1
    have hbS := (Finset.mem_product.mp (Finset.mem_product.mp hp).2).1
    have hcS := (Finset.mem_product.mp (Finset.mem_product.mp hp).2).2
    simp only [Finset.mem_union]
    rcases triple_line_partition gamma w hinj U D hab hac hbc hcol with
      ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB a haS).mp ha,Finset.mem_product.mpr
          ⟨(hmemB b hbS).mp hb,(hmemB c hcS).mp hc⟩⟩,hab,hac,hbc,hcol⟩
    · right
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemR a haS).mp ha,Finset.mem_product.mpr
          ⟨(hmemR b hbS).mp hb,(hmemR c hcS).mp hc⟩⟩,hab,hac,hbc,hcol⟩
    · right
      right
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB a haS).mp ha,Finset.mem_product.mpr
          ⟨(hmemR b hbS).mp hb,(hmemR c hcS).mp hc⟩⟩,hbc,hcol⟩
    · right
      right
      right
      left
      apply Finset.mem_image.mpr
      refine ⟨(b,a,c),?_,rfl⟩
      obtain ⟨U',D',h1,h2,h3⟩ := hcol
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB b hbS).mp hb,Finset.mem_product.mpr
          ⟨(hmemR a haS).mp ha,(hmemR c hcS).mp hc⟩⟩,hac,⟨U',D',h2,h1,h3⟩⟩
    · right
      right
      right
      right
      apply Finset.mem_image.mpr
      refine ⟨(c,b,a),?_,rfl⟩
      obtain ⟨U',D',h1,h2,h3⟩ := hcol
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hmemB c hcS).mp hc,Finset.mem_product.mpr
          ⟨(hmemR b hbS).mp hb,(hmemR a haS).mp ha⟩⟩,hab.symm,⟨U',D',h3,h2,h1⟩⟩
  have h0 := Finset.card_le_card hcover
  have h1 := Finset.card_union_le (collinearTriples gamma w B)
    (collinearTriples gamma w R ∪ (M ∪ (M.image swapAB ∪ M.image swapAC)))
  have h2 := Finset.card_union_le (collinearTriples gamma w R)
    (M ∪ (M.image swapAB ∪ M.image swapAC))
  have h3 := Finset.card_union_le M (M.image swapAB ∪ M.image swapAC)
  have h4 := Finset.card_union_le (M.image swapAB) (M.image swapAC)
  have hi1 : (M.image swapAB).card ≤ M.card := Finset.card_image_le
  have hi2 : (M.image swapAC).card ≤ M.card := Finset.card_image_le
  have hm : M.card ≤ R.card ^ 2 := mixed_triples_card_le_sq gamma w hinj B R U D hB hR
  have hb := collinearTriples_card_le_cube gamma w B
  omega

theorem exists_line_through_two
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    {a b : I} (hab : a ≠ b) :
    ∃ U D : V, OnLine gamma w U D a ∧ OnLine gamma w U D b := by
  have hgamma : gamma a - gamma b ≠ 0 :=
    sub_ne_zero.mpr (fun h => hab (hinj h))
  let D := (gamma a - gamma b)⁻¹ • (w a - w b)
  let U := w a - gamma a • D
  have hmul : (gamma a - gamma b) • D = w a - w b := by
    dsimp [D]
    rw [smul_smul,mul_inv_cancel₀ hgamma,one_smul]
  refine ⟨U,D,?_,?_⟩
  · change w a = (w a - gamma a • D) + gamma a • D
    abel
  · change w b = (w a - gamma a • D) + gamma b • D
    calc
      w b = w a - (w a - w b) := by abel
      _ = w a - (gamma a - gamma b) • D := by rw [hmul]
      _ = _ := by
        rw [sub_smul]
        abel

theorem collinearTriples_card_le_of_line_cap [DecidableEq I]
    (gamma : I -> F) (w : I -> V) (hinj : Function.Injective gamma)
    (S : Finset I) (q : ℕ)
    (hcap : ∀ U D, (S.filter (OnLine gamma w U D)).card ≤ q) :
    (collinearTriples gamma w S).card ≤ S.card ^ 2 * q := by
  classical
  have hsum : (collinearTriples gamma w S).card =
      ∑ a ∈ S, ∑ b ∈ S,
        (S.filter (fun c => a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ CollinearTriple gamma w a b c)).card := by
    simp only [collinearTriples, Finset.product_eq_sprod, Finset.card_filter, Finset.sum_product]
  have hrow : ∀ a b : I,
      (S.filter (fun c => a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ CollinearTriple gamma w a b c)).card ≤ q := by
    intro a b
    by_cases hab : a = b
    · subst b
      simp
    · obtain ⟨U,D,ha,hb⟩ := exists_line_through_two gamma w hinj hab
      apply le_trans (Finset.card_le_card ?_) (hcap U D)
      intro c hc
      obtain ⟨hcS,_,_,_,hcol⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hcS,
        collinear_triple_forces_onLine gamma w hinj hab ha hb hcol⟩
  rw [hsum]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, q :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hrow a b))
    _ = _ := by
      simp only [Finset.sum_const, smul_eq_mul]
      ring

theorem collinearTriples_card_budget [DecidableEq I]
    (gamma : I -> F) (w : I -> V) (hinj : Function.Injective gamma)
    (S : Finset I) (s b : ℕ) (hs : 2 ≤ s)
    (hcap : ∀ U D, (S.filter (OnLine gamma w U D)).card ≤ b) :
    s * (collinearTriples gamma w S).card ≤
      s * S.card * b ^ 2 + 3 * S.card ^ 3 + s ^ 2 * S.card ^ 2 := by
  classical
  have hall : ∀ m : ℕ, ∀ T : Finset I, T.card = m ->
      (∀ U D, (T.filter (OnLine gamma w U D)).card ≤ b) ->
      s * (collinearTriples gamma w T).card ≤
        s * T.card * b ^ 2 + 3 * T.card ^ 3 + s ^ 2 * T.card ^ 2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hTm hcapT
      by_cases hlarge : ∃ U D, s ≤ (T.filter (OnLine gamma w U D)).card
      · obtain ⟨U,D,hline⟩ := hlarge
        let B := T.filter (OnLine gamma w U D)
        let R := T \ B
        have hBsub : B ⊆ T := Finset.filter_subset _ _
        have hpart : R.card + B.card = T.card := Finset.card_sdiff_add_card_eq_card hBsub
        have hBsize : s ≤ B.card := hline
        have hRlt : R.card < m := by omega
        have hcapR : ∀ U' D', (R.filter (OnLine gamma w U' D')).card ≤ b := by
          intro U' D'
          apply le_trans (Finset.card_le_card ?_) (hcapT U' D')
          intro a ha
          obtain ⟨haR,haL⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp haR).1,haL⟩
        have hIR := ih R.card hRlt R rfl hcapR
        have hstep := collinearTriples_block_step gamma w hinj T U D
        change (collinearTriples gamma w T).card ≤
          B.card ^ 3 + 3 * R.card ^ 2 + (collinearTriples gamma w R).card at hstep
        have hBcap : B.card ≤ b := hcapT U D
        have hcube : B.card ^ 3 ≤ B.card * b ^ 2 := by
          have hh := Nat.mul_le_mul hBcap hBcap
          have hh' := Nat.mul_le_mul_left B.card hh
          nlinarith
        have hstepS := Nat.mul_le_mul_left s hstep
        have hcubeS := Nat.mul_le_mul_left s hcube
        have hpoly := block_step_arithmetic R.card B.card s hBsize
        rw [← hpart]
        nlinarith [hstepS,hcubeS,hIR,hpoly]
      · have hsmall : ∀ U D, (T.filter (OnLine gamma w U D)).card ≤ s := by
          intro U D
          have hnot : ¬ s ≤ (T.filter (OnLine gamma w U D)).card :=
            fun h => hlarge ⟨U,D,h⟩
          omega
        have hc := collinearTriples_card_le_of_line_cap gamma w hinj T s hsmall
        calc
          _ ≤ s * (T.card ^ 2 * s) := Nat.mul_le_mul_left s hc
          _ = s ^ 2 * T.card ^ 2 := by ring
          _ ≤ _ := by omega
  exact hall S.card S rfl hcap

/- The private-coordinate argument adapts the covered-witness proof from
IncidenceAverageAnchor and UniversalStaircaseCollapse by ArkLib Contributors. -/
theorem exists_covered_witness
    {X : Type} [Fintype X] [DecidableEq X]
    (t : ℕ) (T : Fin (t + 2) -> Finset X)
    (hcompl : ∀ i, (T i)ᶜ.card ≤ t) :
    ∃ i, ∀ x ∈ T i, ∃ k, k ≠ i ∧ x ∈ T k := by
  classical
  by_contra hall
  push Not at hall
  choose xs hxsT hxsNot using hall
  have hxinj : Function.Injective xs := by
    intro a b hab
    by_contra hne
    have h1 := hxsT a
    have h2 := hxsNot b a hne
    rw [hab] at h1
    exact h2 h1
  let i0 : Fin (t + 2) := ⟨0,by omega⟩
  have hsub : ((Finset.univ.erase i0).image xs) ⊆ (T i0)ᶜ := by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_compl]
    exact hxsNot k i0 (Finset.mem_erase.mp hk).1.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hxinj,
    Finset.card_erase_of_mem (Finset.mem_univ i0),Finset.card_univ,Fintype.card_fin] at hcard
  have ht := hcompl i0
  omega

theorem affine_family_has_joint_witness
    {X A : Type} [Fintype X] [DecidableEq X] [AddCommGroup A] [Module F A]
    (t : ℕ) (gamma : Fin (t + 2) -> F) (hinj : Function.Injective gamma)
    (T : Fin (t + 2) -> Finset X) (u0 u1 U D : X -> A)
    (hcompl : ∀ i, (T i)ᶜ.card ≤ t)
    (hag : ∀ i, ∀ x ∈ T i, u0 x + gamma i • u1 x = U x + gamma i • D x) :
    ∃ i, ∀ x ∈ T i, u0 x = U x ∧ u1 x = D x := by
  classical
  have hpin : ∀ i k, i ≠ k -> ∀ x ∈ T i ∩ T k,
      u0 x = U x ∧ u1 x = D x := by
    intro i k hik x hx
    obtain ⟨hxi,hxk⟩ := Finset.mem_inter.mp hx
    have ei := hag i x hxi
    have ek := hag k x hxk
    have hn : gamma i - gamma k ≠ 0 := sub_ne_zero.mpr (fun h => hik (hinj h))
    have hz : (gamma i - gamma k) • (u1 x - D x) = 0 := by
      calc
        _ = (u0 x + gamma i • u1 x - (U x + gamma i • D x)) -
            (u0 x + gamma k • u1 x - (U x + gamma k • D x)) := by module
        _ = 0 := by
          rw [ei,ek]
          abel
    have hu1 : u1 x = D x := by
      rcases smul_eq_zero.mp hz with h | h
      · exact False.elim (hn h)
      · exact sub_eq_zero.mp h
    rw [hu1] at ei
    exact ⟨add_right_cancel ei,hu1⟩
  obtain ⟨i,hcov⟩ := exists_covered_witness t T hcompl
  refine ⟨i,?_⟩
  intro x hx
  obtain ⟨k,hki,hxk⟩ := hcov x hx
  exact hpin i k hki.symm x (Finset.mem_inter.mpr ⟨hx,hxk⟩)

theorem bad_witness_line_cap
    {X A : Type} [Fintype X] [DecidableEq X] [AddCommGroup A] [Module F A]
    [DecidableEq I]
    (t : ℕ) (gamma : I -> F) (w : I -> (X -> A))
    (hinj : Function.Injective gamma) (S : Finset I) (C : Submodule F (X -> A))
    (T : I -> Finset X) (u0 u1 : X -> A)
    (hwC : ∀ i ∈ S, w i ∈ C)
    (hcompl : ∀ i ∈ S, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i ∈ S, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ S, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (U D : X -> A) : (S.filter (OnLine gamma w U D)).card ≤ t + 1 := by
  classical
  by_contra hgt
  push Not at hgt
  obtain ⟨B,hBsub,hBcard⟩ := Finset.exists_subset_card_eq
    (s := S.filter (OnLine gamma w U D)) (n := t + 2) (by omega)
  let ind : Fin (t + 2) -> I :=
    fun j => (B.equivFin.symm (Fin.cast hBcard.symm j) : I)
  have hind : Function.Injective ind := by
    intro a b hab
    have h1 := Subtype.val_injective hab
    have h2 := B.equivFin.symm.injective h1
    exact Fin.cast_injective _ h2
  have hindB : ∀ j, ind j ∈ B := fun j =>
    (B.equivFin.symm (Fin.cast hBcard.symm j)).2
  have hindS : ∀ j, ind j ∈ S := fun j =>
    (Finset.mem_filter.mp (hBsub (hindB j))).1
  have hindLine : ∀ j, OnLine gamma w U D (ind j) := fun j =>
    (Finset.mem_filter.mp (hBsub (hindB j))).2
  let i0 : Fin (t + 2) := ⟨0,by omega⟩
  let i1 : Fin (t + 2) := ⟨1,by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hh := congrArg Fin.val h
    change 0 = 1 at hh
    omega
  have hi : ind i0 ≠ ind i1 := fun h => hi01 (hind h)
  obtain ⟨hUC,hDC⟩ := params_mem_code_of_two gamma w hinj C hi
    (hindLine i0) (hindLine i1) (hwC _ (hindS i0)) (hwC _ (hindS i1))
  have hag : ∀ j, ∀ x ∈ T (ind j),
      u0 x + gamma (ind j) • u1 x = U x + gamma (ind j) • D x := by
    intro j x hx
    have he := congrFun (hindLine j) x
    calc
      _ = w (ind j) x := (hwag _ (hindS j) x hx).symm
      _ = _ := by simpa only [Pi.add_apply,Pi.smul_apply] using he
  obtain ⟨j,hjoint⟩ := affine_family_has_joint_witness t
    (fun j => gamma (ind j)) (hinj.comp hind) (fun j => T (ind j)) u0 u1 U D
    (fun j => hcompl _ (hindS j)) hag
  apply hno (ind j) (hindS j)
  refine ⟨U,hUC,D,hDC,?_⟩
  intro x hx
  exact ⟨(hjoint x hx).1.symm,(hjoint x hx).2.symm⟩

/-- Three decoded heads are collinear when their error union is below the code distance.
The support hypothesis is the unfolded `SpikeFloor.NoWeightLE` predicate. -/
theorem collinear_of_error_union_le
    {X A : Type} [Fintype X] [DecidableEq X] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (X → A)) (hinj : Function.Injective gamma)
    (C : Submodule F (X → A)) (d : ℕ)
    (hC : ∀ z ∈ C, (∃ B : Finset X, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset X) (u0 u1 : X → A)
    {a b c : I} (hab : a ≠ b)
    (haC : w a ∈ C) (hbC : w b ∈ C) (hcC : w c ∈ C)
    (ha : ∀ x ∈ T a, w a x = u0 x + gamma a • u1 x)
    (hb : ∀ x ∈ T b, w b x = u0 x + gamma b • u1 x)
    (hc : ∀ x ∈ T c, w c x = u0 x + gamma c • u1 x)
    (hunion : (((T a)ᶜ ∪ (T b)ᶜ) ∪ (T c)ᶜ).card ≤ d) :
    CollinearTriple gamma w a b c := by
  classical
  obtain ⟨U,D,haL,hbL⟩ := exists_line_through_two gamma w hinj hab
  obtain ⟨hUC,hDC⟩ := params_mem_code_of_two gamma w hinj C hab haL hbL haC hbC
  have hz : w c - (U + gamma c • D) = 0 := by
    apply hC _ (C.sub_mem hcC (C.add_mem hUC (C.smul_mem _ hDC)))
    refine ⟨((T a)ᶜ ∪ (T b)ᶜ) ∪ (T c)ᶜ, hunion, ?_⟩
    intro x hx
    simp only [Finset.mem_union, Finset.mem_compl, not_or, not_not] at hx
    obtain ⟨⟨hxa,hxb⟩,hxc⟩ := hx
    have hea : u0 x + gamma a • u1 x = U x + gamma a • D x := by
      rw [← ha x hxa]
      exact congrFun haL x
    have heb : u0 x + gamma b • u1 x = U x + gamma b • D x := by
      rw [← hb x hxb]
      exact congrFun hbL x
    obtain ⟨hu0,hu1⟩ := params_eq_of_two (fun h => hab (hinj h)) hea heb
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    rw [hc x hxc,hu0,hu1,sub_self]
  exact ⟨U,D,haL,hbL,sub_eq_zero.mp hz⟩

/-- A noncollinear decoded triple has more errors in its union than the distance budget. -/
theorem error_union_gt_of_noncollinear
    {X A : Type} [Fintype X] [DecidableEq X] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (X → A)) (hinj : Function.Injective gamma)
    (C : Submodule F (X → A)) (d : ℕ)
    (hC : ∀ z ∈ C, (∃ B : Finset X, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset X) (u0 u1 : X → A)
    {a b c : I} (hab : a ≠ b)
    (haC : w a ∈ C) (hbC : w b ∈ C) (hcC : w c ∈ C)
    (ha : ∀ x ∈ T a, w a x = u0 x + gamma a • u1 x)
    (hb : ∀ x ∈ T b, w b x = u0 x + gamma b • u1 x)
    (hc : ∀ x ∈ T c, w c x = u0 x + gamma c • u1 x)
    (hnoncol : ¬ CollinearTriple gamma w a b c) :
    d < (((T a)ᶜ ∪ (T b)ᶜ) ∪ (T c)ᶜ).card := by
  by_contra h
  exact hnoncol (collinear_of_error_union_le gamma w hinj C d hC T u0 u1 hab
    haC hbC hcC ha hb hc (Nat.le_of_not_gt h))

/-- Repeated-index ordered triples contribute at most three square-size diagonals. -/
theorem repeated_triples_card_le [DecidableEq I] (S : Finset I) :
    ((S ×ˢ (S ×ˢ S)).filter (fun p =>
      p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2)).card ≤ 3 * S.card ^ 2 := by
  classical
  let AB := (S ×ˢ S).image (fun p => (p.1,(p.1,p.2)))
  let AC := (S ×ˢ S).image (fun p => (p.1,(p.2,p.1)))
  let BC := (S ×ˢ S).image (fun p => (p.1,(p.2,p.2)))
  have hsub : ((S ×ˢ (S ×ˢ S)).filter (fun p =>
      p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2)) ⊆ (AB ∪ AC) ∪ BC := by
    intro p hp
    obtain ⟨hpS,heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hbcS⟩ := Finset.mem_product.mp hpS
    obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbcS
    rcases heq with hab | hac | hbc
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨(p.1,p.2.2),Finset.mem_product.mpr ⟨ha,hc⟩,
        Prod.ext rfl (Prod.ext hab rfl)⟩
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨(p.1,p.2.1),Finset.mem_product.mpr ⟨ha,hb⟩,
        Prod.ext rfl (Prod.ext rfl hac)⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨(p.1,p.2.1),Finset.mem_product.mpr ⟨ha,hb⟩,
        Prod.ext rfl (Prod.ext rfl hbc)⟩
  have hAB : AB.card ≤ S.card ^ 2 := by
    exact (Finset.card_image_le).trans (by simp [Finset.card_product,pow_two])
  have hAC : AC.card ≤ S.card ^ 2 := by
    exact (Finset.card_image_le).trans (by simp [Finset.card_product,pow_two])
  have hBC : BC.card ≤ S.card ^ 2 := by
    exact (Finset.card_image_le).trans (by simp [Finset.card_product,pow_two])
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (AB ∪ AC) BC
  have h3 := Finset.card_union_le AB AC
  omega

/-- The distance lower bound on noncollinear triples controls total error-union mass. -/
theorem triple_union_mass_lower [DecidableEq I]
    {X : Type} [DecidableEq X]
    (gamma : I → F) (w : I → V) (S : Finset I) (E : I → Finset X) (d : ℕ)
    (hlow : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a ≠ b → a ≠ c → b ≠ c → ¬ CollinearTriple gamma w a b c →
      d < (E a ∪ E b ∪ E c).card) :
    (d + 1) * S.card ^ 3 ≤
      (∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (E a ∪ E b ∪ E c).card) +
        (d + 1) * ((collinearTriples gamma w S).card + 3 * S.card ^ 2) := by
  classical
  let P := S ×ˢ (S ×ˢ S)
  let R := P.filter (fun p => p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2)
  let B := R ∪ collinearTriples gamma w S
  have hR : R.card ≤ 3 * S.card ^ 2 := repeated_triples_card_le S
  have hB : B.card ≤ (collinearTriples gamma w S).card + 3 * S.card ^ 2 := by
    have h := Finset.card_union_le R (collinearTriples gamma w S)
    dsimp only [B]
    omega
  have hBsub : B ⊆ P := Finset.union_subset (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)
  have hpoint : ∀ p ∈ P, d + 1 ≤ (E p.1 ∪ E p.2.1 ∪ E p.2.2).card +
      (if p ∈ B then d + 1 else 0) := by
    intro p hp
    by_cases hpb : p ∈ B
    · simp only [if_pos hpb]
      omega
    · simp only [if_neg hpb,add_zero]
      have hpR : p ∉ R := fun h => hpb (Finset.mem_union.mpr (Or.inl h))
      have hpL : p ∉ collinearTriples gamma w S :=
        fun h => hpb (Finset.mem_union.mpr (Or.inr h))
      have hne : p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
        simpa only [R,Finset.mem_filter,hp,true_and,not_or] using hpR
      have hnc : ¬ CollinearTriple gamma w p.1 p.2.1 p.2.2 := by
        intro h
        exact hpL (Finset.mem_filter.mpr ⟨hp,hne.1,hne.2.1,hne.2.2,h⟩)
      obtain ⟨ha,hbcS⟩ := Finset.mem_product.mp hp
      obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbcS
      exact hlow _ ha _ hb _ hc hne.1 hne.2.1 hne.2.2 hnc
  have hsum := Finset.sum_le_sum hpoint
  have hind : (∑ p ∈ P, if p ∈ B then d + 1 else 0) = B.card * (d + 1) := by
    rw [← Finset.sum_filter]
    have hf : P.filter (fun p => p ∈ B) = B := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨hBsub h,h⟩⟩
    rw [hf,Finset.sum_const,smul_eq_mul]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hind] at hsum
  have hPcard : P.card = S.card ^ 3 := by
    simp only [P,Finset.card_product]
    ring
  simp only [Finset.sum_const,smul_eq_mul,hPcard] at hsum
  have hmass : (∑ p ∈ P, (E p.1 ∪ E p.2.1 ∪ E p.2.2).card) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (E a ∪ E b ∪ E c).card := by
    simp only [P,Finset.sum_product]
  rw [hmass] at hsum
  nlinarith [Nat.mul_le_mul_left (d + 1) hB]

/-- Canonical bad witnesses supply both the noncollinear distance bound and line cap. -/
theorem bad_witness_triple_mass_lower [DecidableEq I]
    {X A : Type} [Fintype X] [DecidableEq X] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (X → A)) (hinj : Function.Injective gamma)
    (S : Finset I) (C : Submodule F (X → A)) (d t s : ℕ) (hs : 2 ≤ s)
    (hC : ∀ z ∈ C, (∃ B : Finset X, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset X) (u0 u1 : X → A)
    (hwC : ∀ i ∈ S, w i ∈ C)
    (hcompl : ∀ i ∈ S, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i ∈ S, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ S, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x) :
    s * (d + 1) * S.card ^ 3 ≤
      s * (∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S,
        (((T a)ᶜ ∪ (T b)ᶜ) ∪ (T c)ᶜ).card) +
      (d + 1) * (s * S.card * (t + 1) ^ 2 + 3 * S.card ^ 3 +
        s ^ 2 * S.card ^ 2 + 3 * s * S.card ^ 2) := by
  classical
  have hcap : ∀ U D, (S.filter (OnLine gamma w U D)).card ≤ t + 1 :=
    bad_witness_line_cap t gamma w hinj S C T u0 u1 hwC hcompl hwag hno
  have hcol := collinearTriples_card_budget gamma w hinj S s (t + 1) hs hcap
  have hmass := triple_union_mass_lower gamma w S (fun i => (T i)ᶜ) d
    (fun a ha b hb c hc hab _ _ hnc =>
      error_union_gt_of_noncollinear gamma w hinj C d hC T u0 u1 hab
        (hwC a ha) (hwC b hb) (hwC c hc)
        (hwag a ha) (hwag b hb) (hwag c hc) hnc)
  have hmassS := Nat.mul_le_mul_left s hmass
  have hcolD := Nat.mul_le_mul_left (d + 1) hcol
  nlinarith [hmassS,hcolD]

end ProximityGap.IncidenceAffineLines
#print axioms ProximityGap.IncidenceAffineLines.params_eq_of_two
#print axioms ProximityGap.IncidenceAffineLines.distinct_lines_intersect_at_most_one
#print axioms ProximityGap.IncidenceAffineLines.collinear_triple_forces_onLine

#print axioms ProximityGap.IncidenceAffineLines.mixed_completion_unique
#print axioms ProximityGap.IncidenceAffineLines.mixed_triples_card_le_sq

#print axioms ProximityGap.IncidenceAffineLines.params_mem_code_of_two

#print axioms ProximityGap.IncidenceAffineLines.triple_line_partition

#print axioms ProximityGap.IncidenceAffineLines.block_step_arithmetic

#print axioms ProximityGap.IncidenceAffineLines.collinearTriples_card_le_cube

#print axioms ProximityGap.IncidenceAffineLines.collinearTriples_block_step

#print axioms ProximityGap.IncidenceAffineLines.exists_line_through_two

#print axioms ProximityGap.IncidenceAffineLines.collinearTriples_card_le_of_line_cap

#print axioms ProximityGap.IncidenceAffineLines.collinearTriples_card_budget

#print axioms ProximityGap.IncidenceAffineLines.exists_covered_witness

#print axioms ProximityGap.IncidenceAffineLines.affine_family_has_joint_witness

#print axioms ProximityGap.IncidenceAffineLines.bad_witness_line_cap

#print axioms ProximityGap.IncidenceAffineLines.collinear_of_error_union_le
#print axioms ProximityGap.IncidenceAffineLines.error_union_gt_of_noncollinear
#print axioms ProximityGap.IncidenceAffineLines.repeated_triples_card_le
#print axioms ProximityGap.IncidenceAffineLines.triple_union_mass_lower
#print axioms ProximityGap.IncidenceAffineLines.bad_witness_triple_mass_lower
