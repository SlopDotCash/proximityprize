/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceAffineLines

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ProximityGap.IncidenceWeightedTriples

open ProximityGap.IncidenceAffineLines

/-- Private coordinates on a canonical bad-witness line are contained in the
error union of every two distinct heads. This uses the same canonical assumptions
as the occupancy cap, with no additional Reed-Solomon hypothesis. -/
theorem line_card_le_pair_error_union
    {F I Coord A : Type} [Field F] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (B : Finset I) (C : Submodule F (Coord → A)) (T : I → Finset Coord)
    (u0 u1 U D : Coord → A)
    (hline : ∀ i ∈ B, OnLine gamma w U D i)
    (hwC : ∀ i ∈ B, w i ∈ C)
    (hag : ∀ i ∈ B, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ B, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    {a b : I} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    B.card ≤ ((T a)ᶜ ∪ (T b)ᶜ).card := by
  classical
  obtain ⟨hUC,hDC⟩ := params_mem_code_of_two gamma w hinj C hab
    (hline a ha) (hline b hb) (hwC a ha) (hwC b hb)
  have hpin : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∀ x ∈ T i ∩ T j,
      u0 x = U x ∧ u1 x = D x := by
    intro i hi j hj hij x hx
    obtain ⟨hxi,hxj⟩ := Finset.mem_inter.mp hx
    have ei := (hag i hi x hxi).symm.trans (congrFun (hline i hi) x)
    have ej := (hag j hj x hxj).symm.trans (congrFun (hline j hj) x)
    simp only [Pi.add_apply,Pi.smul_apply] at ei ej
    have hn : gamma i - gamma j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h))
    have hz : (gamma i - gamma j) • (u1 x - D x) = 0 := by
      calc
        _ = (u0 x + gamma i • u1 x - (U x + gamma i • D x)) -
            (u0 x + gamma j • u1 x - (U x + gamma j • D x)) := by module
        _ = 0 := by
          rw [ei,ej]
          abel
    have hu1 : u1 x = D x := by
      rcases smul_eq_zero.mp hz with h | h
      · exact False.elim (hn h)
      · exact sub_eq_zero.mp h
    rw [hu1] at ei
    exact ⟨add_right_cancel ei,hu1⟩
  have hex : ∀ i : ↥B, ∃ x ∈ T i.val, ¬ (u0 x = U x ∧ u1 x = D x) := by
    intro i
    by_contra hn
    push Not at hn
    apply hno i.val i.property
    refine ⟨U,hUC,D,hDC,?_⟩
    intro x hx
    exact ⟨(hn x hx).1.symm,(hn x hx).2.symm⟩
  choose xs hxsT hxsNot using hex
  have hxinj : Function.Injective xs := by
    intro i j he
    by_contra hn
    have hv : i.val ≠ j.val := fun h => hn (Subtype.ext h)
    have hxj : xs i ∈ T j.val := by
      rw [he]
      exact hxsT j
    exact hxsNot i (hpin i.val i.property j.val j.property hv (xs i)
      (Finset.mem_inter.mpr ⟨hxsT i,hxj⟩))
  have hsub : (Finset.univ.image xs) ⊆ (T a)ᶜ ∪ (T b)ᶜ := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    by_contra hnot
    have hh : xs i ∈ T a ∧ xs i ∈ T b := by simpa using hnot
    exact hxsNot i (hpin a ha b hb hab (xs i) (Finset.mem_inter.mpr hh))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hxinj,Finset.card_univ,Fintype.card_coe] at hc
  exact hc


variable {F V I : Type} [Field F] [AddCommGroup V] [Module F V]

private theorem sum_union_le_nat [DecidableEq I]
    (weight : I → ℕ) (A B : Finset I) :
    (∑ z ∈ A ∪ B, weight z) ≤ (∑ z ∈ A, weight z) + ∑ z ∈ B, weight z := by
  have hh := Finset.sum_union_inter (f := weight) (s₁ := A) (s₂ := B)
  omega

/-- A peeled line retains the error-union mass forced by its private coordinates. -/
theorem weighted_block_step [DecidableEq I]
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (S : Finset I) (U D : V) (weight : I × (I × I) → ℕ) (D0 : ℕ)
    (hbound : ∀ z, weight z ≤ D0)
    (hlocal : ∀ z ∈ collinearTriples gamma w (S.filter (OnLine gamma w U D)),
      weight z ≤ D0 - (S.filter (OnLine gamma w U D)).card) :
    let B := S.filter (OnLine gamma w U D)
    let R := S \ B
    (∑ z ∈ collinearTriples gamma w S, weight z) ≤
      B.card^3*(D0-B.card) + 3*D0*R.card^2 +
        ∑ z ∈ collinearTriples gamma w R, weight z := by
  classical
  let B := S.filter (OnLine gamma w U D)
  let R := S \ B
  let M := mixedTriples gamma w B R
  change (∑ z ∈ collinearTriples gamma w S, weight z) ≤
    B.card ^ 3 * (D0-B.card) + 3*D0*R.card^2 +
      ∑ z ∈ collinearTriples gamma w R, weight z
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
  have h0 := Finset.sum_le_sum_of_subset_of_nonneg hcover
    (fun z _ _ => Nat.zero_le (weight z))
  have h1 := sum_union_le_nat weight (collinearTriples gamma w B)
    (collinearTriples gamma w R ∪ (M ∪ (M.image swapAB ∪ M.image swapAC)))
  have h2 := sum_union_le_nat weight (collinearTriples gamma w R)
    (M ∪ (M.image swapAB ∪ M.image swapAC))
  have h3 := sum_union_le_nat weight M (M.image swapAB ∪ M.image swapAC)
  have h4 := sum_union_le_nat weight (M.image swapAB) (M.image swapAC)
  have hsum : ∀ Q : Finset (I × (I × I)), (∑ z ∈ Q, weight z) ≤ Q.card*D0 := by
    intro Q
    calc
      _ ≤ ∑ _z ∈ Q, D0 := Finset.sum_le_sum (fun z _ => hbound z)
      _ = _ := by simp only [Finset.sum_const,smul_eq_mul]
  have hm : M.card ≤ R.card^2 := mixed_triples_card_le_sq gamma w hinj B R U D hB hR
  have hm0 := (hsum M).trans (Nat.mul_le_mul_right D0 hm)
  have hm1 := (hsum (M.image swapAB)).trans
    (Nat.mul_le_mul_right D0 (Finset.card_image_le.trans hm))
  have hm2 := (hsum (M.image swapAC)).trans
    (Nat.mul_le_mul_right D0 (Finset.card_image_le.trans hm))
  have hinside : (∑ z ∈ collinearTriples gamma w B, weight z) ≤
      B.card^3*(D0-B.card) := by
    calc
      _ ≤ ∑ _z ∈ collinearTriples gamma w B, (D0-B.card) :=
        Finset.sum_le_sum (fun z hz => hlocal z hz)
      _ = (collinearTriples gamma w B).card*(D0-B.card) := by
        simp only [Finset.sum_const,smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (collinearTriples_card_le_cube gamma w B)
  nlinarith [h0,h1,h2,h3,h4,hm0,hm1,hm2,hinside]

theorem weighted_line_arithmetic (ell b D0 : ℕ) (hell : ell ≤ b) (hb : 3*b ≤ 2*D0) :
    ell^3*(D0-ell) ≤ ell*b^2*(D0-b) := by
  have hbD : b ≤ D0 := by omega
  have hq : b ≤ 2*(D0-b) := by omega
  have hm : ell^2 ≤ 2*ell*(D0-b) := by
    have h1 := Nat.mul_le_mul_left ell hell
    have h2 := Nat.mul_le_mul_left ell hq
    nlinarith
  have hmp := Nat.mul_le_mul_left (b-ell) hm
  have he : ell + (b-ell) = b := by omega
  have hd : D0-ell = (D0-b)+(b-ell) := by omega
  have hpoly : ell^2*(D0-ell) ≤ b^2*(D0-b) := by
    have hh : ell^2*((D0-b)+(b-ell)) ≤ (ell+(b-ell))^2*(D0-b) := by
      nlinarith [hmp,Nat.zero_le ((b-ell)^2*(D0-b))]
    simpa only [he,← hd] using hh
  have hh := Nat.mul_le_mul_left ell hpoly
  nlinarith [hh]

/-- A weighted analogue of the triple block census. -/
theorem weighted_triple_budget [DecidableEq I]
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (S : Finset I) (s b D0 : ℕ) (hs : 2 ≤ s) (hb : 3*b ≤ 2*D0)
    (weight : I × (I × I) → ℕ) (hbound : ∀ z, weight z ≤ D0)
    (hcap : ∀ U D, (S.filter (OnLine gamma w U D)).card ≤ b)
    (hlocal : ∀ Q ⊆ S, ∀ U D,
      ∀ z ∈ collinearTriples gamma w (Q.filter (OnLine gamma w U D)),
        weight z ≤ D0-(Q.filter (OnLine gamma w U D)).card) :
    s*(∑ z ∈ collinearTriples gamma w S, weight z) ≤
      s*S.card*b^2*(D0-b) + D0*(3*S.card^3+s^2*S.card^2) := by
  classical
  have hall : ∀ m : ℕ, ∀ Q : Finset I, Q.card = m → Q ⊆ S →
      s*(∑ z ∈ collinearTriples gamma w Q, weight z) ≤
        s*Q.card*b^2*(D0-b) + D0*(3*Q.card^3+s^2*Q.card^2) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro Q hQm hQS
      have hcapQ : ∀ U D, (Q.filter (OnLine gamma w U D)).card ≤ b := by
        intro U D
        apply le_trans (Finset.card_le_card ?_) (hcap U D)
        intro a ha
        obtain ⟨haQ,haL⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨hQS haQ,haL⟩
      by_cases hlarge : ∃ U D, s ≤ (Q.filter (OnLine gamma w U D)).card
      · obtain ⟨U,D,hline⟩ := hlarge
        let B := Q.filter (OnLine gamma w U D)
        let R := Q \ B
        have hBsub : B ⊆ Q := Finset.filter_subset _ _
        have hpart : R.card+B.card = Q.card := Finset.card_sdiff_add_card_eq_card hBsub
        have hBsize : s ≤ B.card := hline
        have hRlt : R.card < m := by omega
        have hRS : R ⊆ S := fun a ha => hQS (Finset.mem_sdiff.mp ha).1
        have hIR := ih R.card hRlt R rfl hRS
        have hstep := weighted_block_step gamma w hinj Q U D weight D0 hbound
          (hlocal Q hQS U D)
        change (∑ z ∈ collinearTriples gamma w Q, weight z) ≤
          B.card^3*(D0-B.card)+3*D0*R.card^2+
            ∑ z ∈ collinearTriples gamma w R, weight z at hstep
        have hpoly := weighted_line_arithmetic B.card b D0 (hcapQ U D) hb
        have hstepS := Nat.mul_le_mul_left s hstep
        have hpolyS := Nat.mul_le_mul_left s hpoly
        have hblock := Nat.mul_le_mul_left D0 (block_step_arithmetic R.card B.card s hBsize)
        rw [← hpart]
        nlinarith [hstepS,hpolyS,hIR,hblock]
      · have hsmall : ∀ U D, (Q.filter (OnLine gamma w U D)).card ≤ s := by
          intro U D
          have hn : ¬ s ≤ (Q.filter (OnLine gamma w U D)).card :=
            fun h => hlarge ⟨U,D,h⟩
          omega
        have hc := collinearTriples_card_le_of_line_cap gamma w hinj Q s hsmall
        have hsum : (∑ z ∈ collinearTriples gamma w Q, weight z) ≤
            (collinearTriples gamma w Q).card*D0 := by
          calc
            _ ≤ ∑ _z ∈ collinearTriples gamma w Q, D0 :=
              Finset.sum_le_sum (fun z _ => hbound z)
            _ = _ := by simp only [Finset.sum_const,smul_eq_mul]
        have h1 := Nat.mul_le_mul_right D0 hc
        have h2 := Nat.mul_le_mul_left s (hsum.trans h1)
        calc
          _ ≤ s*(Q.card^2*s*D0) := h2
          _ = D0*(s^2*Q.card^2) := by ring
          _ ≤ D0*(3*Q.card^3+s^2*Q.card^2) :=
            Nat.mul_le_mul_left D0 (by omega)
          _ ≤ _ := by omega
  exact hall S.card S rfl (fun _ h => h)

/-- Distance forces all deficit outside distinct collinear triples onto the
three repeated-index diagonals. -/
theorem weighted_mass_lower [DecidableEq I]
    {Coord : Type} [DecidableEq Coord]
    (gamma : I → F) (w : I → V) (S : Finset I) (E : I → Finset Coord) (d : ℕ)
    (hlow : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a ≠ b → a ≠ c → b ≠ c → ¬ CollinearTriple gamma w a b c →
        d+1 ≤ (E a ∪ E b ∪ E c).card) :
    (d+1)*S.card^3 ≤
      (∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (E a ∪ E b ∪ E c).card) +
      (∑ p ∈ collinearTriples gamma w S,
        (d+1-(E p.1 ∪ E p.2.1 ∪ E p.2.2).card)) + (d+1)*3*S.card^2 := by
  classical
  let P := S ×ˢ (S ×ˢ S)
  let R := P.filter (fun p => p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2)
  let L := collinearTriples gamma w S
  let weight := fun p : I × (I × I) => d+1-(E p.1 ∪ E p.2.1 ∪ E p.2.2).card
  have hRcard : R.card ≤ 3*S.card^2 := repeated_triples_card_le S
  have hRsub : R ⊆ P := Finset.filter_subset _ _
  have hLsub : L ⊆ P := Finset.filter_subset _ _
  have hpoint : ∀ p ∈ P, d+1 ≤ (E p.1 ∪ E p.2.1 ∪ E p.2.2).card +
      (if p ∈ L then weight p else 0) + (if p ∈ R then d+1 else 0) := by
    intro p hp
    by_cases hpl : p ∈ L
    · simp only [if_pos hpl]
      dsimp [weight]
      omega
    · simp only [if_neg hpl,add_zero]
      by_cases hpr : p ∈ R
      · simp only [if_pos hpr]
        omega
      · simp only [if_neg hpr,add_zero]
        have hne : p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
          simpa only [R,Finset.mem_filter,hp,true_and,not_or] using hpr
        have hnc : ¬ CollinearTriple gamma w p.1 p.2.1 p.2.2 := by
          intro h
          exact hpl (Finset.mem_filter.mpr ⟨hp,hne.1,hne.2.1,hne.2.2,h⟩)
        obtain ⟨ha,hbc⟩ := Finset.mem_product.mp hp
        obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
        exact hlow _ ha _ hb _ hc hne.1 hne.2.1 hne.2.2 hnc
  have hs := Finset.sum_le_sum hpoint
  have hfL : P.filter (fun p => p ∈ L) = L := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hLsub h,h⟩⟩
  have hfR : P.filter (fun p => p ∈ R) = R := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hRsub h,h⟩⟩
  have hiL : (∑ p ∈ P, if p ∈ L then weight p else 0) = ∑ p ∈ L, weight p := by
    rw [← Finset.sum_filter,hfL]
  have hiR : (∑ p ∈ P, if p ∈ R then d+1 else 0) = R.card*(d+1) := by
    rw [← Finset.sum_filter,hfR,Finset.sum_const,smul_eq_mul]
  simp only [Finset.sum_add_distrib] at hs
  rw [hiL,hiR] at hs
  have hPcard : P.card = S.card^3 := by
    simp only [P,Finset.card_product]
    ring
  simp only [Finset.sum_const,smul_eq_mul,hPcard] at hs
  have hmass : (∑ p ∈ P, (E p.1 ∪ E p.2.1 ∪ E p.2.2).card) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (E a ∪ E b ∪ E c).card := by
    simp only [P,Finset.sum_product]
  rw [hmass] at hs
  dsimp [weight,L] at hs
  nlinarith [Nat.mul_le_mul_left (d+1) hRcard]

/-- Canonical nonjointness retains line-union mass in the lower moment bound. -/
theorem bad_witness_weighted_mass_lower_of_cap [DecidableEq I]
    {Coord A : Type} [Fintype Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (S : Finset I) (C : Submodule F (Coord → A)) (d s b : ℕ) (hs : 2 ≤ s)
    (ht : 3*b ≤ 2*(d+1))
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset Coord) (u0 u1 : Coord → A)
    (hwC : ∀ i ∈ S, w i ∈ C)
    (hwag : ∀ i ∈ S, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ S, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (hcap : ∀ U D, (S.filter (OnLine gamma w U D)).card ≤ b) :
    s*(d+1)*S.card^3 ≤
      s*(∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ((T a)ᶜ ∪ (T b)ᶜ ∪ (T c)ᶜ).card) +
      s*S.card*b^2*(d+1-b) +
      (d+1)*(3*S.card^3+s^2*S.card^2+3*s*S.card^2) := by
  classical
  let weight : I × (I × I) → ℕ := fun p =>
    d+1-((T p.1)ᶜ ∪ (T p.2.1)ᶜ ∪ (T p.2.2)ᶜ).card
  have hbound : ∀ p, weight p ≤ d+1 := fun p => Nat.sub_le _ _
  have hlocal : ∀ Q ⊆ S, ∀ U D,
      ∀ p ∈ collinearTriples gamma w (Q.filter (OnLine gamma w U D)),
        weight p ≤ d+1-(Q.filter (OnLine gamma w U D)).card := by
    intro Q hQS U D p hp
    let B := Q.filter (OnLine gamma w U D)
    obtain ⟨hprod,hab,_,_,_⟩ := Finset.mem_filter.mp hp
    have haB : p.1 ∈ B := (Finset.mem_product.mp hprod).1
    have hbB : p.2.1 ∈ B :=
      (Finset.mem_product.mp (Finset.mem_product.mp hprod).2).1
    have hBS : B ⊆ S := fun i hi => hQS (Finset.mem_filter.mp hi).1
    have hpair := line_card_le_pair_error_union gamma w hinj B C T u0 u1 U D
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i hi => hwC i (hBS hi)) (fun i hi => hwag i (hBS hi))
      (fun i hi => hno i (hBS hi)) haB hbB hab
    have hunion : ((T p.1)ᶜ ∪ (T p.2.1)ᶜ).card ≤
        ((T p.1)ᶜ ∪ (T p.2.1)ᶜ ∪ (T p.2.2)ᶜ).card :=
      Finset.card_le_card Finset.subset_union_left
    dsimp [weight]
    change d+1-((T p.1)ᶜ ∪ (T p.2.1)ᶜ ∪ (T p.2.2)ᶜ).card ≤ d+1-B.card
    omega
  have hbudget := weighted_triple_budget gamma w hinj S s b (d+1) hs ht
    weight hbound hcap hlocal
  have hmass := weighted_mass_lower gamma w S (fun i => (T i)ᶜ) d
    (fun a ha b hb c hc hab _ _ hnc =>
      error_union_gt_of_noncollinear gamma w hinj C d hC T u0 u1 hab
        (hwC a ha) (hwC b hb) (hwC c hc)
        (hwag a ha) (hwag b hb) (hwag c hc) hnc)
  have hmassS := Nat.mul_le_mul_left s hmass
  dsimp [weight] at hbudget
  nlinarith [hmassS,hbudget]

/-- Canonical nonjointness retains line-union mass in the lower moment bound. -/
theorem bad_witness_weighted_mass_lower [DecidableEq I]
    {Coord A : Type} [Fintype Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (S : Finset I) (C : Submodule F (Coord → A)) (d t s : ℕ) (hs : 2 ≤ s)
    (ht : 3*(t+1) ≤ 2*(d+1))
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset Coord) (u0 u1 : Coord → A)
    (hwC : ∀ i ∈ S, w i ∈ C)
    (hcompl : ∀ i ∈ S, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i ∈ S, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ S, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x) :
    s*(d+1)*S.card^3 ≤
      s*(∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, ((T a)ᶜ ∪ (T b)ᶜ ∪ (T c)ᶜ).card) +
      s*S.card*(t+1)^2*(d+1-(t+1)) +
      (d+1)*(3*S.card^3+s^2*S.card^2+3*s*S.card^2) := by
  classical
  exact bad_witness_weighted_mass_lower_of_cap gamma w hinj S C d s (t+1) hs ht
    hC T u0 u1 hwC hwag hno
    (bad_witness_line_cap t gamma w hinj S C T u0 u1 hwC hcompl hwag hno)

end ProximityGap.IncidenceWeightedTriples

#print axioms ProximityGap.IncidenceWeightedTriples.line_card_le_pair_error_union

#print axioms ProximityGap.IncidenceWeightedTriples.weighted_block_step
#print axioms ProximityGap.IncidenceWeightedTriples.weighted_line_arithmetic
#print axioms ProximityGap.IncidenceWeightedTriples.weighted_triple_budget
#print axioms ProximityGap.IncidenceWeightedTriples.weighted_mass_lower
#print axioms ProximityGap.IncidenceWeightedTriples.bad_witness_weighted_mass_lower

#print axioms ProximityGap.IncidenceWeightedTriples.bad_witness_weighted_mass_lower_of_cap
