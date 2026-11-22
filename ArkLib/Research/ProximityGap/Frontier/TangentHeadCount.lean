/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Data.CodingTheory.Connections.GCXK25SecondMoment
import Mathlib

/-! # The counting half of the tangent-head bound

Theorem D′ of `docs/research/proximity-gap/section-incidence-hodge-index.md` has a
geometric half and a counting half. The geometric half attaches to every
polynomial section `(z, q)` of an irreducible surface a rational pair
`V = s₂ / s₁`, `R = q - z V`, with `deg s₁ ≤ c` and `deg s₂ ≤ d + c`, that takes
the received values on a set `J` of agreement sites, and bounds the sum of the
heights `c`. It is a written argument and is not formalized.

This file proves the counting half from that data: two sections whose sets `J`
share more than `d + c + c'` sites lie on one affine head, and a second-moment
count over the sites then bounds the number of sections.
-/

open Finset Polynomial

namespace ProximityGap.TangentHeadCount

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero polynomial vanishing at the images of a finite set of sites has at
least that many roots. -/
theorem card_le_natDegree_of_vanish (dom : ι ↪ F) {P : F[X]} (hP : P ≠ 0) (S : Finset ι)
    (h : ∀ x ∈ S, P.eval (dom x) = 0) : S.card ≤ P.natDegree := by
  classical
  have hsub : S.map dom ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (h x hx))
  calc S.card = (S.map dom).card := (Finset.card_map _).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P

/-- Two sections lie on one affine head `q = A + z B` with `B = s₂ / s₁` the
tangent slope of the first. -/
def CommonHead (z z' : F) (q q' s₁ s₂ : F[X]) : Prop :=
  (q - q') * s₁ = C (z - z') * s₂

/-- **Rigidity of tangent heads.** Two rational pairs of heights `c`, `c'` that take
the received values on `J` and `J'` either agree on at most `d + c + c'` common
sites or put both sections on one affine head. -/
theorem inter_card_le_or_commonHead (dom : ι ↪ F) (u₀ u₁ : ι → F) {d c c' : ℕ}
    {z z' : F} {q q' s₁ s₂ s₁' s₂' : F[X]} {J J' : Finset ι}
    (hq : q.natDegree ≤ d) (hq' : q'.natDegree ≤ d)
    (h₁ : s₁.natDegree ≤ c) (h₂ : s₂.natDegree ≤ d + c)
    (h₁' : s₁'.natDegree ≤ c') (h₂' : s₂'.natDegree ≤ d + c')
    (hV : ∀ x ∈ J, s₂.eval (dom x) = u₁ x * s₁.eval (dom x))
    (hR : ∀ x ∈ J, q.eval (dom x) * s₁.eval (dom x) - z * s₂.eval (dom x)
      = u₀ x * s₁.eval (dom x))
    (hne' : ∀ x ∈ J', s₁'.eval (dom x) ≠ 0)
    (hV' : ∀ x ∈ J', s₂'.eval (dom x) = u₁ x * s₁'.eval (dom x))
    (hR' : ∀ x ∈ J', q'.eval (dom x) * s₁'.eval (dom x) - z' * s₂'.eval (dom x)
      = u₀ x * s₁'.eval (dom x)) :
    (J ∩ J').card ≤ d + c + c' ∨ CommonHead z z' q q' s₁ s₂ := by
  classical
  by_cases hP : s₂ * s₁' - s₂' * s₁ = 0
  · by_cases hQ : (q - q') * s₁ - C (z - z') * s₂ = 0
    · exact Or.inr (sub_eq_zero.mp hQ)
    · left
      have hdeg : ((q - q') * s₁ - C (z - z') * s₂).natDegree ≤ d + c := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_mul_le.trans
            (Nat.add_le_add ((natDegree_sub_le _ _).trans (max_le hq hq')) h₁)
        · exact natDegree_mul_le.trans (by
            have := natDegree_C (z - z')
            omega)
      have hcross : s₂ * s₁' = s₂' * s₁ := sub_eq_zero.mp hP
      have hvan : ∀ x ∈ J ∩ J', ((q - q') * s₁ - C (z - z') * s₂).eval (dom x) = 0 := by
        intro x hx
        obtain ⟨hxJ, hxJ'⟩ := Finset.mem_inter.mp hx
        have e := hR x hxJ
        have e' := hR' x hxJ'
        have hc := congrArg (fun p => p.eval (dom x)) hcross
        simp only [eval_mul] at hc
        have hn := hne' x hxJ'
        simp only [eval_sub, eval_mul, eval_C]
        apply mul_right_cancel₀ hn
        linear_combination s₁'.eval (dom x) * e - s₁.eval (dom x) * e' + z' * hc
      exact (card_le_natDegree_of_vanish dom hQ _ hvan).trans (hdeg.trans (by omega))
  · left
    have hdeg : (s₂ * s₁' - s₂' * s₁).natDegree ≤ d + c + c' := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (by omega)
      · exact natDegree_mul_le.trans (by omega)
    have hvan : ∀ x ∈ J ∩ J', (s₂ * s₁' - s₂' * s₁).eval (dom x) = 0 := by
      intro x hx
      obtain ⟨hxJ, hxJ'⟩ := Finset.mem_inter.mp hx
      simp only [eval_sub, eval_mul, hV x hxJ, hV' x hxJ']
      ring
    exact (card_le_natDegree_of_vanish dom hP _ hvan).trans hdeg

/-- All sections on a common head with a fixed first section have the form
`A + z B` for one pair `A`, `B`. -/
theorem commonHead_eq {z z₁ z₂ : F} {q q₁ q₂ s₁ s₂ : F[X]} (hs : s₁ ≠ 0)
    (hz₁ : z ≠ z₁) (h₁ : CommonHead z z₁ q q₁ s₁ s₂) (h₂ : CommonHead z z₂ q q₂ s₁ s₂) :
    q₂ = (q - C z * (C (z - z₁)⁻¹ * (q - q₁))) + C z₂ * (C (z - z₁)⁻¹ * (q - q₁)) := by
  have hne : z - z₁ ≠ 0 := sub_ne_zero.mpr hz₁
  have hB : (C (z - z₁)⁻¹ * (q - q₁)) * s₁ = s₂ := by
    unfold CommonHead at h₁
    calc (C (z - z₁)⁻¹ * (q - q₁)) * s₁ = C (z - z₁)⁻¹ * ((q - q₁) * s₁) := by ring
      _ = C (z - z₁)⁻¹ * (C (z - z₁) * s₂) := by rw [h₁]
      _ = (C (z - z₁)⁻¹ * C (z - z₁)) * s₂ := by ring
      _ = s₂ := by rw [← C_mul, inv_mul_cancel₀ hne, C_1, one_mul]
  unfold CommonHead at h₂
  rw [← hB] at h₂
  have hcancel : (q - q₂) = C (z - z₂) * (C (z - z₁)⁻¹ * (q - q₁)) := by
    apply mul_right_cancel₀ hs
    rw [h₂]
    ring
  have hC : C (z - z₂) = C z - C z₂ := C_sub
  rw [hC] at hcancel
  linear_combination -hcancel

open Classical in
/-- Bound section populations with independent budgets for missed agreement sites
and the sum of tangent heights. -/
theorem tangent_head_population_of_loss {α : Type*} [DecidableEq α] (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (S : Finset α) (z : α → F) (q s₁ s₂ : α → F[X]) (c : α → ℕ) (J : α → Finset ι)
    {d m t Cs loss : ℕ} (hm : 1 ≤ m)
    (hz : ∀ σ ∈ S, ∀ τ ∈ S, σ ≠ τ → z σ ≠ z τ)
    (hq : ∀ σ ∈ S, (q σ).natDegree ≤ d)
    (hs : ∀ σ ∈ S, s₁ σ ≠ 0)
    (h₁ : ∀ σ ∈ S, (s₁ σ).natDegree ≤ c σ) (h₂ : ∀ σ ∈ S, (s₂ σ).natDegree ≤ d + c σ)
    (hne : ∀ σ ∈ S, ∀ x ∈ J σ, (s₁ σ).eval (dom x) ≠ 0)
    (hV : ∀ σ ∈ S, ∀ x ∈ J σ, (s₂ σ).eval (dom x) = u₁ x * (s₁ σ).eval (dom x))
    (hR : ∀ σ ∈ S, ∀ x ∈ J σ, (q σ).eval (dom x) * (s₁ σ).eval (dom x)
      - z σ * (s₂ σ).eval (dom x) = u₀ x * (s₁ σ).eval (dom x))
    (hhead : ∀ A B : F[X], (S.filter fun τ => q τ = A + C (z τ) * B).card ≤ m)
    (hheight : ∑ σ ∈ S, c σ ≤ Cs)
    (hlow : S.card * t ≤ ∑ σ ∈ S, (J σ).card + loss) :
    (S.card : ℝ) * ((t : ℝ) ^ 2 - Fintype.card ι * d)
      ≤ 2 * t * loss + Fintype.card ι * (m * Fintype.card ι + 2 * Cs) := by
  classical
  set n := Fintype.card ι with hn
  set N := S.card with hN
  -- pairwise intersections: generic bound plus `n` for each partner on a common head
  have hpair : ∀ σ ∈ S, ∑ τ ∈ S.erase σ, (J σ ∩ J τ).card
      ≤ ∑ τ ∈ S.erase σ, (d + c σ + c τ) + (m - 1) * n := by
    intro σ hσ
    set T := (S.erase σ).filter fun τ => CommonHead (z σ) (z τ) (q σ) (q τ) (s₁ σ) (s₂ σ)
      with hT
    have hTcard : T.card ≤ m - 1 := by
      rcases T.eq_empty_or_nonempty with hE | ⟨τ₀, hτ₀⟩
      · simp [hE]
      · obtain ⟨hτ₀S, hτ₀H⟩ := Finset.mem_filter.mp hτ₀
        have hτ₀ne : τ₀ ≠ σ := (Finset.mem_erase.mp hτ₀S).1
        have hτ₀mem : τ₀ ∈ S := (Finset.mem_erase.mp hτ₀S).2
        have hzne : z σ ≠ z τ₀ := hz σ hσ τ₀ hτ₀mem hτ₀ne.symm
        set B := C (z σ - z τ₀)⁻¹ * (q σ - q τ₀) with hB
        set A := q σ - C (z σ) * B with hA
        have hsub : insert σ T ⊆ S.filter fun τ => q τ = A + C (z τ) * B := by
          intro τ hτ
          rcases Finset.mem_insert.mp hτ with rfl | hτT
          · exact Finset.mem_filter.mpr ⟨hσ, by rw [hA]; ring⟩
          · obtain ⟨hτS, hτH⟩ := Finset.mem_filter.mp hτT
            exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hτS).2,
              commonHead_eq (hs σ hσ) hzne hτ₀H hτH⟩
        have hnot : σ ∉ T := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
        have hcard := (Finset.card_le_card hsub).trans (hhead A B)
        rw [Finset.card_insert_of_notMem hnot] at hcard
        omega
    calc ∑ τ ∈ S.erase σ, (J σ ∩ J τ).card
        ≤ ∑ τ ∈ S.erase σ, ((d + c σ + c τ) + if τ ∈ T then n else 0) := by
          refine Finset.sum_le_sum fun τ hτ => ?_
          have hτS : τ ∈ S := (Finset.mem_erase.mp hτ).2
          have hτne : τ ≠ σ := (Finset.mem_erase.mp hτ).1
          rcases inter_card_le_or_commonHead dom u₀ u₁ (hq σ hσ) (hq τ hτS) (h₁ σ hσ)
            (h₂ σ hσ) (h₁ τ hτS) (h₂ τ hτS) (hV σ hσ) (hR σ hσ) (hne τ hτS) (hV τ hτS)
            (hR τ hτS) with hle | hcommon
          · exact hle.trans (Nat.le_add_right _ _)
          · have hmem : τ ∈ T := Finset.mem_filter.mpr ⟨hτ, hcommon⟩
            simp only [hmem, ↓reduceIte]
            exact ((Finset.card_le_card Finset.inter_subset_left).trans
              (Finset.card_le_univ _)).trans (Nat.le_add_left _ _)
      _ = ∑ τ ∈ S.erase σ, (d + c σ + c τ) + ∑ τ ∈ S.erase σ, (if τ ∈ T then n else 0) :=
          Finset.sum_add_distrib
      _ ≤ ∑ τ ∈ S.erase σ, (d + c σ + c τ) + (m - 1) * n := by
          refine Nat.add_le_add_left ?_ _
          rw [← Finset.sum_filter]
          have hfilter : (S.erase σ).filter (fun τ => τ ∈ T) = T := by
            ext τ
            simp only [Finset.mem_filter, hT]
            tauto
          rw [hfilter, Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ hTcard
  -- sum the generic part
  have hgen : ∀ σ ∈ S, ∑ τ ∈ S.erase σ, (d + c σ + c τ) ≤ N * d + N * c σ + Cs := by
    intro σ hσ
    have hcardE : (S.erase σ).card ≤ N := Finset.card_erase_le
    have hsumE : ∑ τ ∈ S.erase σ, c τ ≤ Cs :=
      (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)).trans hheight
    calc ∑ τ ∈ S.erase σ, (d + c σ + c τ)
        = (S.erase σ).card * (d + c σ) + ∑ τ ∈ S.erase σ, c τ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      _ ≤ N * (d + c σ) + Cs := Nat.add_le_add (Nat.mul_le_mul_right _ hcardE) hsumE
      _ = N * d + N * c σ + Cs := by ring
  have hoff : ∑ σ ∈ S, ∑ τ ∈ S.erase σ, (J σ ∩ J τ).card
      ≤ N * N * d + 2 * N * Cs + N * ((m - 1) * n) := by
    calc ∑ σ ∈ S, ∑ τ ∈ S.erase σ, (J σ ∩ J τ).card
        ≤ ∑ σ ∈ S, (N * d + N * c σ + Cs + (m - 1) * n) :=
          Finset.sum_le_sum fun σ hσ =>
            (hpair σ hσ).trans (Nat.add_le_add_right (hgen σ hσ) _)
      _ = N * (N * d) + N * ∑ σ ∈ S, c σ + N * Cs + N * ((m - 1) * n) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hN]
      _ ≤ N * (N * d) + N * Cs + N * Cs + N * ((m - 1) * n) := by
          have := Nat.mul_le_mul_left N hheight
          omega
      _ = N * N * d + 2 * N * Cs + N * ((m - 1) * n) := by ring
  have hdiag : ∑ σ ∈ S, (J σ).card ≤ N * n := by
    calc ∑ σ ∈ S, (J σ).card ≤ ∑ _σ ∈ S, n :=
          Finset.sum_le_sum fun σ _ => Finset.card_le_univ _
      _ = N * n := by rw [Finset.sum_const, smul_eq_mul]
  have hmoment := GCXK25SecondMoment.sq_sum_card_le_card_mul_sum_sum_card_inter S J
  rw [GCXK25SecondMoment.sum_sum_card_inter_eq_diag_add_offdiag] at hmoment
  set T₀ := ∑ σ ∈ S, (J σ).card with hT₀
  have hsecond : T₀ ^ 2 ≤ n * (N * N * d + N * (m * n + 2 * Cs)) := by
    refine hmoment.trans (Nat.mul_le_mul_left _ ?_)
    have hm' : (m - 1) * n + n = m * n := by
      have : m - 1 + 1 = m := Nat.sub_add_cancel hm
      calc (m - 1) * n + n = (m - 1 + 1) * n := by ring
        _ = m * n := by rw [this]
    calc T₀ + ∑ σ ∈ S, ∑ τ ∈ S.erase σ, (J σ ∩ J τ).card
        ≤ N * n + (N * N * d + 2 * N * Cs + N * ((m - 1) * n)) := Nat.add_le_add hdiag hoff
      _ = N * N * d + N * ((m - 1) * n + n + 2 * Cs) := by ring
      _ = N * N * d + N * (m * n + 2 * Cs) := by rw [hm']
  -- pass to the reals
  have hlowR : (N : ℝ) * t - (loss : ℝ) ≤ (T₀ : ℝ) := by
    have h := hlow
    have hcast : ((N * t : ℕ) : ℝ) ≤ ((T₀ + loss : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hcast
    linarith
  have hsecondR : (T₀ : ℝ) ^ 2 ≤ (n : ℝ) * ((N : ℝ) ^ 2 * d + N * ((m : ℝ) * n + 2 * Cs)) := by
    have hcast : ((T₀ ^ 2 : ℕ) : ℝ) ≤ ((n * (N * N * d + N * (m * n + 2 * Cs)) : ℕ) : ℝ) := by
      exact_mod_cast hsecond
    push_cast at hcast
    nlinarith [hcast]
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have htnn : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hEnn : (0 : ℝ) ≤ (loss : ℝ) := by positivity
  have hnnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hFnn : (0 : ℝ) ≤ (m : ℝ) * n + 2 * Cs := by positivity
  by_cases hsmall : (N : ℝ) * t ≤ (loss : ℝ)
  · -- few sections: the bound is immediate
    have h1 : (N : ℝ) * (t : ℝ) ^ 2 ≤ t * (loss : ℝ) := by nlinarith
    have h2 : (0 : ℝ) ≤ (N : ℝ) * (n * d) := by positivity
    nlinarith [mul_nonneg htnn hEnn, mul_nonneg hnnn hFnn]
  · rw [not_le] at hsmall
    have hpos : (0 : ℝ) ≤ (N : ℝ) * t - (loss : ℝ) := by linarith
    have hsq : ((N : ℝ) * t - (loss : ℝ)) ^ 2 ≤ (T₀ : ℝ) ^ 2 := by nlinarith
    have hNpos : (0 : ℝ) < N := by
      rcases hNnn.lt_or_eq with h | h
      · exact h
      · rw [← h] at hsmall; simp at hsmall; linarith
    have key : (N : ℝ) * ((N : ℝ) * ((t : ℝ) ^ 2 - n * d))
        ≤ N * (2 * t * (loss : ℝ) + n * ((m : ℝ) * n + 2 * Cs)) := by
      nlinarith [hsq.trans hsecondR, sq_nonneg (loss : ℝ)]
    exact le_of_mul_le_mul_left key hNpos

open Classical in
/-- **Counting half of Theorem D′.** Let `S` index sections with pairwise distinct
scalars, each with tangent data of height `c σ` taking the received values on
`J σ`. Suppose at most `m` sections of `S` lie on any one affine head, the
heights sum to at most `Cs`, and the sets `J σ` have total size at least
`|S| · t - (m · n + Cs)`. Then
`|S| · (t² - n d) ≤ 2 t (m n + Cs) + n (m n + 2 Cs)`. -/
theorem tangent_head_population {α : Type*} [DecidableEq α] (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (S : Finset α) (z : α → F) (q s₁ s₂ : α → F[X]) (c : α → ℕ) (J : α → Finset ι)
    {d m t Cs : ℕ} (hm : 1 ≤ m)
    (hz : ∀ σ ∈ S, ∀ τ ∈ S, σ ≠ τ → z σ ≠ z τ)
    (hq : ∀ σ ∈ S, (q σ).natDegree ≤ d)
    (hs : ∀ σ ∈ S, s₁ σ ≠ 0)
    (h₁ : ∀ σ ∈ S, (s₁ σ).natDegree ≤ c σ) (h₂ : ∀ σ ∈ S, (s₂ σ).natDegree ≤ d + c σ)
    (hne : ∀ σ ∈ S, ∀ x ∈ J σ, (s₁ σ).eval (dom x) ≠ 0)
    (hV : ∀ σ ∈ S, ∀ x ∈ J σ, (s₂ σ).eval (dom x) = u₁ x * (s₁ σ).eval (dom x))
    (hR : ∀ σ ∈ S, ∀ x ∈ J σ, (q σ).eval (dom x) * (s₁ σ).eval (dom x)
      - z σ * (s₂ σ).eval (dom x) = u₀ x * (s₁ σ).eval (dom x))
    (hhead : ∀ A B : F[X], (S.filter fun τ => q τ = A + C (z τ) * B).card ≤ m)
    (hheight : ∑ σ ∈ S, c σ ≤ Cs)
    (hlow : S.card * t ≤ ∑ σ ∈ S, (J σ).card + (m * Fintype.card ι + Cs)) :
    (S.card : ℝ) * ((t : ℝ) ^ 2 - Fintype.card ι * d)
      ≤ 2 * t * (m * Fintype.card ι + Cs) + Fintype.card ι * (m * Fintype.card ι + 2 * Cs) := by
  simpa only [Nat.cast_add, Nat.cast_mul] using
    tangent_head_population_of_loss dom u₀ u₁ S z q s₁ s₂ c J hm hz hq hs h₁ h₂ hne hV hR
      hhead hheight hlow

open Classical in
/-- Integer form of `tangent_head_population`, as used for the price of a nonlinear
factor in `TangentHeadWindows`: below the Johnson radius the number of sections
is at most `(m n (2t + n) + 2 Cs (t + n)) / (t² - n d)`. -/
theorem tangent_head_population_nat {α : Type*} [DecidableEq α] (dom : ι ↪ F)
    (u₀ u₁ : ι → F) (S : Finset α) (z : α → F) (q s₁ s₂ : α → F[X]) (c : α → ℕ)
    (J : α → Finset ι) {d m t Cs : ℕ} (hm : 1 ≤ m)
    (hjohnson : Fintype.card ι * d < t ^ 2)
    (hz : ∀ σ ∈ S, ∀ τ ∈ S, σ ≠ τ → z σ ≠ z τ)
    (hq : ∀ σ ∈ S, (q σ).natDegree ≤ d)
    (hs : ∀ σ ∈ S, s₁ σ ≠ 0)
    (h₁ : ∀ σ ∈ S, (s₁ σ).natDegree ≤ c σ) (h₂ : ∀ σ ∈ S, (s₂ σ).natDegree ≤ d + c σ)
    (hne : ∀ σ ∈ S, ∀ x ∈ J σ, (s₁ σ).eval (dom x) ≠ 0)
    (hV : ∀ σ ∈ S, ∀ x ∈ J σ, (s₂ σ).eval (dom x) = u₁ x * (s₁ σ).eval (dom x))
    (hR : ∀ σ ∈ S, ∀ x ∈ J σ, (q σ).eval (dom x) * (s₁ σ).eval (dom x)
      - z σ * (s₂ σ).eval (dom x) = u₀ x * (s₁ σ).eval (dom x))
    (hhead : ∀ A B : F[X], (S.filter fun τ => q τ = A + C (z τ) * B).card ≤ m)
    (hheight : ∑ σ ∈ S, c σ ≤ Cs)
    (hlow : S.card * t ≤ ∑ σ ∈ S, (J σ).card + (m * Fintype.card ι + Cs)) :
    S.card ≤ (m * Fintype.card ι * (2 * t + Fintype.card ι)
        + 2 * Cs * (t + Fintype.card ι)) / (t ^ 2 - Fintype.card ι * d) := by
  have hreal := tangent_head_population dom u₀ u₁ S z q s₁ s₂ c J hm hz hq hs h₁ h₂ hne
    hV hR hhead hheight hlow
  set n := Fintype.card ι with hn
  have hden : 0 < t ^ 2 - n * d := Nat.sub_pos_of_lt hjohnson
  apply (Nat.le_div_iff_mul_le hden).mpr
  have hcast : ((t ^ 2 - n * d : ℕ) : ℝ) = (t : ℝ) ^ 2 - n * d := by
    rw [Nat.cast_sub hjohnson.le]
    push_cast
    ring
  have hgoal : ((S.card * (t ^ 2 - n * d) : ℕ) : ℝ)
      ≤ ((m * n * (2 * t + n) + 2 * Cs * (t + n) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, hcast]
    push_cast
    nlinarith [hreal]
  exact_mod_cast hgoal

#print axioms card_le_natDegree_of_vanish
#print axioms inter_card_le_or_commonHead
#print axioms commonHead_eq
#print axioms tangent_head_population_of_loss
#print axioms tangent_head_population
#print axioms tangent_head_population_nat

end ProximityGap.TangentHeadCount
