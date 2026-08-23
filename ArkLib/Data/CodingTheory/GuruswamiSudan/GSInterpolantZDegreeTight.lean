/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSInterpolantZDegree

/-!
# The tight Z-degree budget — `D/(k-1)` per entry, not `D`

`gsMatrixZ_natDegree_le` bounds the constraint-matrix entry degrees by `D`, giving the
degenerate-set budget `n·|constraints|·D` — **quadratic in `n`**, which the Johnson
budget `johnsonBoundReal` cannot absorb (the per-stack count `(D/(k-1)+1)·n·|c|·D` exceeds
the budget by a factor growing linearly in `n`; verified numerically at
`n ∈ {2⁸, 2¹², 2¹⁶, 2²⁰}`, ratios `8×`–`3·10⁴×`).

The entry degree is really bounded by the **Y-exponent** `b ≤ D/(k-1)` (from the weighted
constraint `a + (k-1)·b ≤ D`), not by `D`.  This file re-runs the integer-interpolant
construction at the tight bound, yielding the degenerate budget
`n·|constraints|·(D/(k-1))` — linear in `n`.  With it the canonical per-stack count
`(D/(k-1)+1)·n·|c|·(D/(k-1))` sits **inside** the Johnson budget at every scale (same
numeric sweep, ratios `0.12`–`0.014`, flat in `n`) — making the arithmetic side condition
of the full discharge satisfiable.

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
-/

namespace GuruswamiSudan.OverRatFunc.ZDegree

open Polynomial Polynomial.Bivariate Finset GuruswamiSudan

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

local notation "K" => RatFunc F

/-- **The tight entry bound.**  Constraint-matrix entries have `Z`-degree at most the
`Y`-exponent budget `D/(k-1)`: the entry degree is `b - t ≤ b`, and `(k-1)·b ≤ D` from
the weighted-degree constraint. -/
theorem gsMatrixZ_natDegree_le_div {k n m : ℕ} (hk : 1 < k) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (D : ℕ) (ist : Fin n × constraintIndices m)
    (p : weigthBoundIndices k D) :
    (gsMatrixZ k n m ωs f₀ f₁ D ist p).natDegree ≤ D / (k - 1) := by
  have hb : p.1.2 ≤ D / (k - 1) := by
    have hp := p.2
    simp only [weigthBoundIndices, mem_filter] at hp
    refine Nat.le_div_iff_mul_le (by omega) |>.mpr ?_
    have := hp.2
    nlinarith [p.1.1.zero_le]
  calc (gsMatrixZ k n m ωs f₀ f₁ D ist p).natDegree
      ≤ (C ((p.1.1.choose ist.2.1.1 : F) * (ωs ist.1) ^ (p.1.1 - ist.2.1.1) *
            (p.1.2.choose ist.2.1.2 : F))).natDegree +
        ((C (f₀ ist.1) + X * C (f₁ ist.1)) ^ (p.1.2 - ist.2.1.2)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + (p.1.2 - ist.2.1.2) * 1 := by
        gcongr
        · exact le_of_eq (Polynomial.natDegree_C _)
        · refine Polynomial.natDegree_pow_le.trans ?_
          gcongr
          refine (Polynomial.natDegree_add_le _ _).trans ?_
          refine max_le (by simp) ?_
          exact (Polynomial.natDegree_mul_le).trans (by simp [Polynomial.natDegree_C])
    _ ≤ D / (k - 1) := by omega

/-- **The integer GS interpolant at the tight Z-degree budget.**  Identical to
`gs_existence_over_ratfunc_zDegree` with the per-coefficient budget improved from
`n·|c|·D` to `n·|c|·(D/(k-1))` via the tight entry bound. -/
theorem gs_existence_over_ratfunc_zDegree_div {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F)
    (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      ∀ b a : ℕ, ((Q₀.coeff b).coeff a).natDegree ≤
        (n * (constraintIndices m).card) * (gs_degree_bound k n m / (k - 1)) := by
  classical
  set D := gs_degree_bound k n m with hD
  have hcount := gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  obtain ⟨c, hc0, hck⟩ := exists_nonzero_solution_gen (F := K) k n m
    (liftedDomain ωs) (genericFold f₀ f₁) D hcount
  have hker : ((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c = 0 := by
    funext ist
    rw [← constraintMap_eq_mulVec]
    have := congr_fun (congr_fun hck ist.1) ist.2
    simpa using this
  obtain ⟨c', hc'0, hc'ker, hdeg⟩ :=
    Matrix.exists_natDegree_le_kernel_vector_of_ratFunc
      (gsMatrixZ k n m ωs f₀ f₁ D)
      (fun i j => gsMatrixZ_natDegree_le_div hk ωs f₀ f₁ D i j) c hc0 hker
  set Q₀ : (F[X])[X][Y] := ∑ p : weigthBoundIndices k D,
      Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p)) with hQ₀
  have hcoeff : ∀ a b : ℕ, ((Q₀.coeff b).coeff a) =
      if h : (a, b) ∈ weigthBoundIndices k D then c' ⟨(a, b), h⟩ else 0 := by
    intro a b
    rw [hQ₀, Polynomial.finset_sum_coeff]
    have hterm : ∀ p : weigthBoundIndices k D,
        ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b).coeff a =
          if p.1 = (a, b) then c' p else 0 := by
      intro p
      rw [Polynomial.coeff_monomial]
      by_cases h2 : p.1.2 = b
      · rw [if_pos h2, Polynomial.coeff_monomial]
        by_cases h1 : p.1.1 = a
        · rw [if_pos h1, if_pos (Prod.ext h1 h2)]
        · rw [if_neg h1, if_neg (fun h => h1 (by rw [h]))]
      · rw [if_neg h2, Polynomial.coeff_zero, if_neg (fun h => h2 (by rw [h]))]
    calc (∑ p : weigthBoundIndices k D,
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b)).coeff a
        = ∑ p : weigthBoundIndices k D,
            ((Polynomial.monomial p.1.2 (Polynomial.monomial p.1.1 (c' p))).coeff b).coeff a := by
          rw [Polynomial.finset_sum_coeff]
      _ = ∑ p : weigthBoundIndices k D, if p.1 = (a, b) then c' p else 0 := by
          exact Finset.sum_congr rfl fun p _ => hterm p
      _ = if h : (a, b) ∈ weigthBoundIndices k D then c' ⟨(a, b), h⟩ else 0 := by
          by_cases h : (a, b) ∈ weigthBoundIndices k D
          · rw [dif_pos h, Finset.sum_eq_single (⟨(a, b), h⟩ : weigthBoundIndices k D)]
            · rw [if_pos rfl]
            · intro p _ hne
              rw [if_neg (fun hp => hne (Subtype.ext hp))]
            · intro habs; exact absurd (Finset.mem_univ _) habs
          · rw [dif_neg h, Finset.sum_eq_zero]
            intro p _
            rw [if_neg (fun hp => h (by rw [← hp]; exact p.2))]
  set c'' : weigthBoundIndices k D → K := fun p => algebraMap F[X] K (c' p) with hc''
  have hmap : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K)) = coeffsToPoly k D c'' := by
    rw [coeffsToPoly_eq_sum, hQ₀, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Polynomial.map_monomial]
    simp only [Polynomial.mapRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Polynomial.map_monomial]
    rw [GuruswamiSudan.monomial, Polynomial.smul_monomial, Polynomial.smul_monomial,
      smul_eq_mul, mul_one]
  have hc''0 : c'' ≠ 0 := by
    intro habs
    apply hc'0
    funext p
    have := congr_fun habs p
    simpa [hc''] using (IsFractionRing.injective F[X] K)
      (by simpa [hc''] using congr_fun habs p)
  have hck'' : constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' = 0 := by
    funext i st
    have hrep := constraintMap_eq_mulVec (k := k) (m := m) ωs f₀ f₁ D c'' (i, st)
    rw [show constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c'' i st =
        constraintMap k n m (liftedDomain ωs) (genericFold f₀ f₁) D c''
          ((i, st) : Fin n × constraintIndices m).1 ((i, st) : Fin n × constraintIndices m).2
      from rfl, hrep]
    show (((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'') (i, st) = 0
    have : ((gsMatrixZ k n m ωs f₀ f₁ D).map (algebraMap F[X] K)).mulVec c'' (i, st) =
        algebraMap F[X] K ((gsMatrixZ k n m ωs f₀ f₁ D).mulVec c' (i, st)) := by
      simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, hc'', map_sum, map_mul]
    rw [this, hc'ker]
    simp
  have h_inj : Function.Injective (coeffsToPoly (F := K) k D) := by
    have : Function.Injective (Finsupp.linearCombination K
        (fun p : weigthBoundIndices k D ↦ GuruswamiSudan.monomial (F := K) p.1.1 p.1.2)) :=
      linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
    exact this.comp (LinearEquiv.injective _)
  refine ⟨Q₀, ?_, ?_, ?_⟩
  · obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hc'0
    intro habs
    apply hp₀
    have := hcoeff p₀.1.1 p₀.1.2
    rw [habs] at this
    simp only [Polynomial.coeff_zero] at this
    rw [dif_pos (by exact (Prod.mk.eta (p := p₀.1)) ▸ p₀.2)] at this
    rw [show (⟨(p₀.1.1, p₀.1.2), _⟩ : weigthBoundIndices k D) = p₀ from
      Subtype.ext (Prod.mk.eta)] at this
    exact this.symm
  · rw [hmap]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun h ↦ hc''0 <| h_inj <| by simpa using h
    · convert Option.some_le_some.mpr (natWeightedDegree_coeffsToPoly_le k D c'') using 1
      exact weightedDegree_eq_natWeightedDegree
    · intro i
      exact eval_eq_zero_of_constraint_zero hm fun s t hst ↦ by
        simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hck''
        have := congr_fun (congr_fun hck'' i) ⟨(s, t), Finset.mem_filter.2
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
            Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
        aesop
    · intro i
      apply rootMultiplicity_ge_of_shift_zero
      · exact fun h ↦ hc''0 <| h_inj <| by simpa using h
      · intro s t hst
        simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hck''
        have := congr_fun (congr_fun hck'' i) ⟨(s, t), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
            Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
        aesop
  · intro b a
    rw [hcoeff a b]
    by_cases h : (a, b) ∈ weigthBoundIndices k D
    · rw [dif_pos h]
      refine (hdeg ⟨(a, b), h⟩).trans ?_
      have hcard : Fintype.card (Fin n × constraintIndices m) =
          n * (constraintIndices m).card := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
      rw [hcard]
    · rw [dif_neg h]
      simp

/-- **The tight `hbadz` producer.**  The degenerate set of the tight integer interpolant
has at most `n·|c|·(D/(k-1))` elements — linear in `n`, inside the Johnson budget. -/
theorem gs_existence_over_ratfunc_zDegree_card_div [Fintype F] {n : ℕ} (k m : ℕ)
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F) (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q₀ : (F[X])[X][Y],
      Q₀ ≠ 0 ∧
      Conditions k m (gs_degree_bound k n m) (liftedDomain ωs) (genericFold f₀ f₁)
        (Q₀.map (Polynomial.mapRingHom (algebraMap F[X] K))) ∧
      (Finset.univ.filter (fun z : F =>
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0)).card ≤
        n * (constraintIndices m).card * (gs_degree_bound k n m / (k - 1)) := by
  obtain ⟨Q₀, h0, hcond, hdeg⟩ := gs_existence_over_ratfunc_zDegree_div k m ωs f₀ f₁ hk hn hm
  exact ⟨Q₀, h0, hcond, card_specialization_collapse_le h0 hdeg⟩

end GuruswamiSudan.OverRatFunc.ZDegree

/-! ## Axiom audit -/
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gsMatrixZ_natDegree_le_div
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_div
#print axioms GuruswamiSudan.OverRatFunc.ZDegree.gs_existence_over_ratfunc_zDegree_card_div
