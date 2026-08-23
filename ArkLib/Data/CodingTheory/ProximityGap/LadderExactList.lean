/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.CensusClassificationCharZero

/-!
# THE LADDER EXACT LIST THEOREM (#389): the subset-sum fibre law at ladder words,
# char-0 core, m = 2

The subset-sum fibre law (issue #389) predicts that sub-Johnson single-word lists on
smooth domains are subset-sum fibres.  This file PROVES its rigidity half, exactly, for
`m = 2` ladder words over 2-power root-of-unity domains in characteristic zero — the
field-independent core layer (the per-prime halo correction is the named O134 surplus):

* `ladder_explainer_fiber` — **rigidity (the fibre law's upper half at ladder words)**:
  every codeword of `rsCode dom k` (`k ≤ 2r−2`) agreeing with the ladder word
  `w(x) = x^{2r} + λ·x^{2r−2}` on `≥ 2r` domain points differs from it by EXACTLY
  `∏_{t∈T}(x² − t)` for an `r`-subset `T` of `μ_{n/2}` with `Σ T = −λ`.
  Chain: the difference `g` is monic of degree `2r` with `2r` distinct roots in `μ_n`
  and vanishing `(2r−1)`-coefficient ⟹ `Σ(roots) = 0` ⟹ the root set is
  **antipodally closed** (the in-tree subset Lam–Leung engine
  `subset_neg_mem_of_sum_zero`) ⟹ squaring is exactly 2-to-1 on it ⟹ `g = G(X²)`
  by the matching-degree difference trick, `T := roots of G`, and the band
  coefficient pins `Σ T = −λ`.
* `exists_dom_eq_of_root` — domain surjectivity onto `μ_n` is automatic for an
  injective `n`-point domain inside `μ_n` (root counting).

Consequences: the single-word list at agreement `≥ 2r` injects into the subset-sum
fibre `{T ⊆ μ_{n/2} : |T| = r, ΣT = −λ}` — the conjectured value `N_fib` is an upper
bound, as a theorem, at every dimension `k ≤ 2r−2` (for `k < 2r−3` the formula plus
membership forces the additional census vanishing `e_j(T) = 0`, cutting the class
further, exactly as the gap-census law predicts).  Agreement is self-capped at `2r`
(the difference has degree `2r`), so this is the complete list law at these words.
The supply (lower) half in the regime `2r−3 ≤ k` is the fibre-family construction
(`w − ∏(x²−t)` has degree `≤ 2r−4 < k` when `ΣT = −λ`), registered next.
Issue #389; fibre-law conjecture comment; O134 (per-prime surplus) is the named
obstruction to a verbatim finite-field lift, as the protocol red-team note records.
-/

open Finset Polynomial

namespace ProximityGap.LadderList

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {L : Type} [Field L]
variable {ν n r k : ℕ} {ζ lam : L} {dom : Fin n ↪ L}

/-- The `m = 2` ladder word `x^{2r} + λ·x^{2r−2}` over the domain. -/
def ladderWord (dom : Fin n ↪ L) (r : ℕ) (lam : L) : Fin n → L :=
  fun i => (dom i) ^ (2 * r) + lam * (dom i) ^ (2 * r - 2)

/-- Even-coefficient extraction through `X²`-composition. -/
theorem coeff_comp_X_sq (G : L[X]) (d : ℕ) :
    (G.comp (X ^ 2)).coeff (2 * d) = G.coeff d := by
  classical
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum, Polynomial.finset_sum_coeff]
  have hterm : ∀ e ∈ G.support, (C (G.coeff e) * (X ^ 2) ^ e : L[X]).coeff (2 * d)
      = if e = d then G.coeff e else 0 := by
    intro e _
    rw [← pow_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases he : e = d
    · subst he; simp [mul_comm]
    · have h1 : ¬ (2 * d = 2 * e) := by omega
      simp [h1, he]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' G.support d]
  by_cases hd : d ∈ G.support
  · simp [hd]
  · simp [hd, Polynomial.notMem_support_iff.mp hd]

/-- Domain surjectivity onto the `n`-th roots: an injective `n`-point domain inside
`μ_n` is all of `μ_n` (root counting on `Xⁿ − 1`). -/
theorem exists_dom_eq_of_root (hn1 : 1 ≤ n) (hroot : ∀ i, (dom i) ^ n = 1)
    {y : L} (hy : y ^ n = 1) : ∃ i, dom i = y := by
  classical
  set Rt : Finset L := (X ^ n - C 1 : L[X]).roots.toFinset with hRt
  have hne : (X ^ n - C 1 : L[X]) ≠ 0 := by
    intro h
    have hdeg : (X ^ n - C 1 : L[X]).degree = n := by
      rw [degree_sub_eq_left_of_degree_lt (by
        rw [degree_X_pow]
        exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hn1)), degree_X_pow]
    rw [h, degree_zero] at hdeg
    simp at hdeg
  have hmem : ∀ z : L, z ^ n = 1 → z ∈ Rt := by
    intro z hz
    rw [hRt, Multiset.mem_toFinset, mem_roots hne]
    simp [IsRoot, hz]
  have hcard : Rt.card ≤ n := by
    calc Rt.card ≤ Multiset.card (X ^ n - C 1 : L[X]).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (X ^ n - C 1 : L[X]).natDegree := card_roots' _
      _ ≤ n := natDegree_le_iff_degree_le.mpr (by
          calc (X ^ n - C 1 : L[X]).degree
              ≤ max (X ^ n : L[X]).degree (C 1 : L[X]).degree := degree_sub_le _ _
            _ ≤ n := by
                rw [degree_X_pow]
                exact max_le le_rfl (le_trans degree_C_le (by exact_mod_cast Nat.zero_le n)))
  have himg : Finset.univ.image dom = Rt := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact hmem _ (hroot i)
    · calc Rt.card ≤ n := hcard
        _ = (Finset.univ : Finset (Fin n)).card := by
            rw [Finset.card_univ, Fintype.card_fin]
        _ = (Finset.univ.image dom).card :=
            (Finset.card_image_of_injective _ dom.injective).symm
  have hyim : y ∈ Finset.univ.image dom := himg ▸ hmem y hy
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hyim
  exact ⟨i, hi⟩

open Classical in
/-- **THE RIGIDITY HALF, general-field form**: over any field with `2 ≠ 0`, an even
domain size, and the antipodal-closure principle for `2r`-element vanishing subset
sums of `μ_n` (the Lam–Leung input, char-0-true and finite-field-true above the
resultant threshold), any codeword agreeing with the ladder word on `≥ 2r` points
differs from it by exactly `∏_{t∈T}(x² − t)` for an `r`-subset `T ⊆ μ_{n/2}` with
`Σ T = −λ`. -/
theorem ladder_explainer_fiber_of_closure (h2 : (2 : L) ≠ 0) (heven : 2 ∣ n)
    (hroot : ∀ i, (dom i) ^ n = 1)
    (hclosure : ∀ A : Finset L, A.card = 2 * r → (∀ x ∈ A, x ^ n = 1) →
      ∑ x ∈ A, x = 0 → ∀ x ∈ A, -x ∈ A)
    (hk : 1 ≤ k) (hk2 : k ≤ 2 * r - 2)
    {c : Fin n → L} (hc : c ∈ (rsCode dom k : Submodule L (Fin n → L)))
    (hagr : 2 * r ≤ (Finset.univ.filter
      (fun i => c i = ladderWord dom r lam i)).card) :
    ∃ T : Finset L, T.card = r ∧ (∀ t ∈ T, t ^ (n / 2) = 1) ∧ (∑ t ∈ T, t = -lam) ∧
      ∀ i, c i = ladderWord dom r lam i - ∏ t ∈ T, ((dom i) ^ 2 - t) := by
  classical
  obtain ⟨P, hPdeg, rfl⟩ := hc
  have hrk : 3 ≤ 2 * r := by omega
  -- the difference polynomial
  set g : L[X] := X ^ (2 * r) + C lam * X ^ (2 * r - 2) - P with hgdef
  have hPlt : P.degree < ((2 * r : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hPdeg (by exact_mod_cast (by omega : k ≤ 2 * r))
  have hheaddeg : (X ^ (2 * r) + C lam * X ^ (2 * r - 2) : L[X]).degree
      = ((2 * r : ℕ) : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt]
    · exact degree_X_pow _
    · rw [degree_X_pow]
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
        (by exact_mod_cast (by omega : 2 * r - 2 < 2 * r))
  have hgdeg : g.degree = ((2 * r : ℕ) : WithBot ℕ) := by
    rw [hgdef, degree_sub_eq_left_of_degree_lt (hheaddeg ▸ hPlt), hheaddeg]
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, degree_zero] at hgdeg
    exact WithBot.bot_ne_coe hgdeg
  have hgnat : g.natDegree = 2 * r := natDegree_eq_of_degree_eq_some hgdeg
  have hgmon : g.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hgnat, hgdef]
    have h1 : (X ^ (2 * r) : L[X]).coeff (2 * r) = 1 := by
      rw [Polynomial.coeff_X_pow]; simp
    have h2 : (C lam * X ^ (2 * r - 2) : L[X]).coeff (2 * r) = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hno : ¬ (2 * r = 2 * r - 2) := by omega
      simp [hno]
    have h3 : P.coeff (2 * r) = 0 := Polynomial.coeff_eq_zero_of_degree_lt hPlt
    simp [h1, h2, h3]
  -- agreement points give distinct roots
  set Ag : Finset (Fin n) := Finset.univ.filter
    (fun i => P.eval (dom i) = ladderWord dom r lam i) with hAg
  have hagroot : ∀ i ∈ Ag, g.IsRoot (dom i) := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    rw [ladderWord] at hi'
    simp only [IsRoot, hgdef, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    rw [hi']
    ring
  set A : Finset L := Ag.image dom with hA
  have hAcard : 2 * r ≤ A.card := by
    rw [hA, Finset.card_image_of_injective _ dom.injective]
    exact hagr
  have hAroots : ∀ x ∈ A, g.IsRoot x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hagroot i hi
  have hAle : A.card ≤ 2 * r := by
    calc A.card ≤ g.roots.toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          rw [Multiset.mem_toFinset, mem_roots hg0]
          exact hAroots x hx
      _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
      _ ≤ g.natDegree := card_roots' _
      _ = 2 * r := hgnat
  have hAcard' : A.card = 2 * r := le_antisymm hAle hAcard
  -- the difference trick: `g = ∏_{x ∈ A} (X − x)`
  have hgprod : g = ∏ x ∈ A, (X - C x) := by
    set Q : L[X] := ∏ x ∈ A, (X - C x) with hQ
    have hQmon : Q.Monic := monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x
    have hQnat : Q.natDegree = 2 * r := by
      rw [hQ, natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C x]
      simp [hAcard']
    by_contra hne
    have hD0 : g - Q ≠ 0 := sub_ne_zero.mpr hne
    have hdlt : (g - Q).degree < g.degree :=
      degree_sub_lt (by rw [hgdeg, degree_eq_natDegree hQmon.ne_zero, hQnat]) hg0
        (by rw [hgmon.leadingCoeff, hQmon.leadingCoeff])
    have hDnat : (g - Q).natDegree < 2 * r := by
      rw [hgdeg] at hdlt
      exact (natDegree_lt_iff_degree_lt hD0).mpr hdlt
    have hge : 2 * r ≤ (g - Q).natDegree := by
      calc 2 * r = A.card := hAcard'.symm
        _ ≤ (g - Q).roots.toFinset.card := by
            apply Finset.card_le_card
            intro x hx
            rw [Multiset.mem_toFinset, mem_roots hD0]
            have h1 := hAroots x hx
            have h2 : Q.IsRoot x := by
              rw [hQ, IsRoot, eval_prod]
              exact Finset.prod_eq_zero hx (by simp)
            simp only [IsRoot, eval_sub] at h1 h2 ⊢
            rw [h1, h2, sub_zero]
        _ ≤ Multiset.card (g - Q).roots := Multiset.toFinset_card_le _
        _ ≤ (g - Q).natDegree := card_roots' _
    omega
  -- `Σ A = 0` from the vanishing `(2r−1)`-coefficient
  have hsumA : ∑ x ∈ A, x = 0 := by
    have hco : g.coeff (2 * r - 1) = 0 := by
      rw [hgdef]
      have h1 : (X ^ (2 * r) : L[X]).coeff (2 * r - 1) = 0 := by
        rw [Polynomial.coeff_X_pow]
        have hno : ¬ (2 * r - 1 = 2 * r) := by omega
        simp [hno]
      have h2 : (C lam * X ^ (2 * r - 2) : L[X]).coeff (2 * r - 1) = 0 := by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have hno : ¬ (2 * r - 1 = 2 * r - 2) := by omega
        simp [hno]
      have h3 : P.coeff (2 * r - 1) = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hPdeg (by exact_mod_cast (by omega : k ≤ 2 * r - 1)))
      simp [h1, h2, h3]
    have hnext : g.nextCoeff = -∑ x ∈ A, x := by
      rw [hgprod]
      exact prod_X_sub_C_nextCoeff (fun x => x)
    have hnext' : g.nextCoeff = g.coeff (2 * r - 1) := by
      rw [nextCoeff_of_natDegree_pos (by rw [hgnat]; omega), hgnat]
    have hzero : -∑ x ∈ A, x = 0 := by rw [← hnext, hnext', hco]
    exact neg_eq_zero.mp hzero
  -- Lam–Leung: antipodal closure
  have hn0 : 0 < n := by
    have h1 : A.card ≤ n := by
      calc A.card ≤ Ag.card := by rw [hA]; exact Finset.card_image_le
        _ ≤ (Finset.univ : Finset (Fin n)).card := by
            rw [hAg]; exact Finset.card_filter_le _ _
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    omega
  have hAmu : ∀ x ∈ A, x ^ n = 1 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hroot i
  have hneg : ∀ x ∈ A, -x ∈ A := hclosure A hAcard' hAmu hsumA
  have hA0 : ∀ x ∈ A, x ≠ 0 := by
    intro x hx h0
    have h1 := hAmu x hx
    rw [h0, zero_pow hn0.ne'] at h1
    exact zero_ne_one h1
  -- squaring is exactly 2-to-1 on `A`
  set T : Finset L := A.image (fun x => x ^ 2) with hT
  have hfiber : ∀ t ∈ T, (A.filter (fun x => x ^ 2 = t)).card = 2 := by
    intro t ht
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp ht
    have hfeq : A.filter (fun x => x ^ 2 = x₀ ^ 2) = {x₀, -x₀} := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyA, hysq⟩ := Finset.mem_filter.mp hy
        have hfac : (y - x₀) * (y + x₀) = 0 := by
          have hexp : (y - x₀) * (y + x₀) = y ^ 2 - x₀ ^ 2 := by ring
          rw [hexp, hysq, sub_self]
        rcases mul_eq_zero.mp hfac with h | h
        · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp h))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
            (add_eq_zero_iff_eq_neg.mp h)))
      · intro hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Finset.mem_filter.mpr ⟨hx₀, rfl⟩
        · rw [Finset.mem_singleton] at hy
          subst hy
          exact Finset.mem_filter.mpr ⟨hneg x₀ hx₀, by ring⟩
    rw [hfeq, Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]
    intro h
    have hx2 : (2 : L) * x₀ = 0 := by linear_combination h
    rcases mul_eq_zero.mp hx2 with h2' | h2'
    · exact h2 h2'
    · exact hA0 x₀ hx₀ h2'
  have hTcard : T.card = r := by
    have hcount : A.card = ∑ t ∈ T, (A.filter (fun x => x ^ 2 = t)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem _ hx)
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hAcard'] at hcount
    omega
  -- `g = G(X²)` by the matching-degree difference trick
  set G : L[X] := ∏ t ∈ T, (X - C t) with hG
  have hGcomp : G.comp (X ^ 2) = ∏ t ∈ T, ((X : L[X]) ^ 2 - C t) := by
    rw [hG, Polynomial.prod_comp]
    exact Finset.prod_congr rfl fun t _ => by rw [sub_comp, X_comp, C_comp]
  have hgG : g = G.comp (X ^ 2) := by
    have hcmon : (G.comp (X ^ 2)).Monic := by
      rw [hGcomp]
      exact monic_prod_of_monic _ _ fun t _ => monic_X_pow_sub_C t (by norm_num)
    have hcnat : (G.comp (X ^ 2)).natDegree = 2 * r := by
      rw [hGcomp, natDegree_prod_of_monic _ _
        (fun t _ => monic_X_pow_sub_C t (by norm_num))]
      have hdd : ∀ t ∈ T, ((X : L[X]) ^ 2 - C t).natDegree = 2 := fun t _ =>
        natDegree_X_pow_sub_C
      rw [Finset.sum_congr rfl hdd, Finset.sum_const, smul_eq_mul, hTcard]
      ring
    by_contra hne
    have hD0 : g - G.comp (X ^ 2) ≠ 0 := sub_ne_zero.mpr hne
    have hdlt : (g - G.comp (X ^ 2)).degree < g.degree :=
      degree_sub_lt (by rw [hgdeg, degree_eq_natDegree hcmon.ne_zero, hcnat]) hg0
        (by rw [hgmon.leadingCoeff, hcmon.leadingCoeff])
    have hDnat : (g - G.comp (X ^ 2)).natDegree < 2 * r := by
      rw [hgdeg] at hdlt
      exact (natDegree_lt_iff_degree_lt hD0).mpr hdlt
    have hge : 2 * r ≤ (g - G.comp (X ^ 2)).natDegree := by
      calc 2 * r = A.card := hAcard'.symm
        _ ≤ (g - G.comp (X ^ 2)).roots.toFinset.card := by
            apply Finset.card_le_card
            intro x hx
            rw [Multiset.mem_toFinset, mem_roots hD0]
            have h1 := hAroots x hx
            have h2 : (G.comp (X ^ 2)).IsRoot x := by
              rw [hGcomp, IsRoot, eval_prod]
              refine Finset.prod_eq_zero
                (Finset.mem_image_of_mem (fun y => y ^ 2) hx) ?_
              simp
            simp only [IsRoot, eval_sub] at h1 h2 ⊢
            rw [h1, h2, sub_zero]
        _ ≤ Multiset.card (g - G.comp (X ^ 2)).roots := Multiset.toFinset_card_le _
        _ ≤ (g - G.comp (X ^ 2)).natDegree := card_roots' _
    omega
  -- `Σ T = −λ` from the `(2r−2)`-coefficient through the composition
  have hsumT : ∑ t ∈ T, t = -lam := by
    have hglam : g.coeff (2 * r - 2) = lam := by
      rw [hgdef]
      have h1 : (X ^ (2 * r) : L[X]).coeff (2 * r - 2) = 0 := by
        rw [Polynomial.coeff_X_pow]
        have hno : ¬ (2 * r - 2 = 2 * r) := by omega
        simp [hno]
      have h2 : (C lam * X ^ (2 * r - 2) : L[X]).coeff (2 * r - 2) = lam := by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp
      have h3 : P.coeff (2 * r - 2) = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hPdeg (by exact_mod_cast hk2))
      simp [h1, h2, h3]
    have hGnat : G.natDegree = r := by
      rw [hG, natDegree_prod_of_monic _ _ fun t _ => monic_X_sub_C t]
      simp [hTcard]
    have hco : G.coeff (r - 1) = -∑ t ∈ T, t := by
      have h1 : G.nextCoeff = -∑ t ∈ T, t := by
        rw [hG]
        exact prod_X_sub_C_nextCoeff (fun t => t)
      rw [nextCoeff_of_natDegree_pos (by rw [hGnat]; omega), hGnat] at h1
      exact h1
    have hcc : g.coeff (2 * (r - 1)) = G.coeff (r - 1) := by
      rw [hgG]
      exact coeff_comp_X_sq G (r - 1)
    have hidx : 2 * (r - 1) = 2 * r - 2 := by omega
    rw [hidx, hglam, hco] at hcc
    linear_combination hcc
  -- conclusion
  refine ⟨T, hTcard, ?_, hsumT, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    have hx1 := hAmu x hx
    have hhalf : 2 * (n / 2) = n := Nat.mul_div_cancel' heven
    calc (x ^ 2) ^ (n / 2) = x ^ (2 * (n / 2)) := by rw [← pow_mul]
      _ = x ^ n := by rw [hhalf]
      _ = 1 := hx1
  · intro i
    have heval : g.eval (dom i) = ∏ t ∈ T, ((dom i) ^ 2 - t) := by
      rw [hgG, eval_comp, hG, eval_prod]
      simp
    have hgeval : g.eval (dom i)
        = ladderWord dom r lam i - P.eval (dom i) := by
      rw [hgdef, ladderWord]
      simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    rw [← heval, hgeval]
    ring

open Classical in
/-- **THE RIGIDITY HALF (char-0 core)**: over 2-power root-of-unity domains in
characteristic zero, the closure principle is the in-tree subset Lam–Leung engine,
and the fibre law's upper bound holds unconditionally. -/
theorem ladder_explainer_fiber [CharZero L] (hν : 1 ≤ ν)
    (hζ : IsPrimitiveRoot ζ (2 ^ ν))
    (hn : n = 2 ^ ν) (hroot : ∀ i, (dom i) ^ n = 1)
    (hk : 1 ≤ k) (hk2 : k ≤ 2 * r - 2)
    {c : Fin n → L} (hc : c ∈ (rsCode dom k : Submodule L (Fin n → L)))
    (hagr : 2 * r ≤ (Finset.univ.filter
      (fun i => c i = ladderWord dom r lam i)).card) :
    ∃ T : Finset L, T.card = r ∧ (∀ t ∈ T, t ^ (n / 2) = 1) ∧ (∑ t ∈ T, t = -lam) ∧
      ∀ i, c i = ladderWord dom r lam i - ∏ t ∈ T, ((dom i) ^ 2 - t) := by
  refine ladder_explainer_fiber_of_closure two_ne_zero
    (by rw [hn]; exact dvd_pow_self 2 (by omega)) hroot ?_ hk hk2 hc hagr
  intro A _ hA hsum
  exact ArkLib.ProximityGap.KKH26.subset_neg_mem_of_sum_zero hν hζ A
    (by intro x hx; rw [← hn]; exact hA x hx) hsum

end ProximityGap.LadderList

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LadderList.coeff_comp_X_sq
#print axioms ProximityGap.LadderList.exists_dom_eq_of_root
#print axioms ProximityGap.LadderList.ladder_explainer_fiber_of_closure
#print axioms ProximityGap.LadderList.ladder_explainer_fiber
