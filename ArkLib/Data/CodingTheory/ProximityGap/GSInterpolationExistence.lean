/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
Round 14, Angle B — Guruswami–Sudan interpolation FRONT END via dimension counting.
Self-contained over Mathlib only (no ArkLib imports).

PROVED here:
* `exists_ne_zero_map_eq_zero_of_finrank_lt` : if `finrank W < finrank V` then every linear
  map `V →ₗ[F] W` sends some nonzero vector to zero (rank–nullity existence brick).
* `gsSupport_card` : the weighted-degree monomial support `{(i,j) | i + (k-1)·j < D}`,
  realized as a concrete Finset, has cardinality exactly `∑_{j<D} (D - (k-1)·j)`.
* `sudan_interpolation_exists` : multiplicity-1 (Sudan) interpolation existence — for any
  `n` points `(α s, w s)` in `F²` with `n <` the monomial count, there is a NONZERO
  bivariate `Q ∈ F[X][Y]` all of whose monomials `X^i·Y^j` satisfy `i + (k-1)·j < D`,
  vanishing at every point. No distinctness of the points is needed.
* `gs_instance_ZMod5` : a fully concrete witness over `ZMod 5` (`k = 2`, `D = 3`,
  `n = 5 < 6` monomials), so every hypothesis above is exhibited by a concrete inhabitant.

NOT proved (honest scope): multiplicity-`m ≥ 2` Hasse-derivative vanishing constraints,
the root-extraction step `(Y - f(X)) ∣ Q` for high-agreement codewords, the resulting
list-size bound, and any decoding-radius improvement past the Johnson radius. This file is
exactly the linear-algebra front end of the GS route, verified end to end.
-/

set_option maxHeartbeats 800000

open Polynomial

namespace GSInterp

/-! ### 1. Rank–nullity existence brick -/

theorem exists_ne_zero_map_eq_zero_of_finrank_lt
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (L : V →ₗ[F] W) (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    exact hcon v hne hv
  exact absurd (LinearMap.finrank_le_finrank_of_injective hinj) (not_le.mpr h)

/-! ### 2. The weighted-degree monomial support and its exact count -/

/-- Monomial support of the GS interpolation space: pairs `(i, j)` with
`i + (k-1)·j < D`, organized as rows indexed by the `Y`-degree `j`. -/
def gsSupport (D k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range D).biUnion fun j => (Finset.range (D - (k - 1) * j)).image fun i => (i, j)

lemma gsSupport_weight_lt {D k : ℕ} {p : ℕ × ℕ} (hp : p ∈ gsSupport D k) :
    p.1 + (k - 1) * p.2 < D := by
  simp only [gsSupport, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hp
  obtain ⟨j', hj', i', hi', heq⟩ := hp
  have h1 : p.1 = i' := by rw [← heq]
  have h2 : p.2 = j' := by rw [← heq]
  rw [h1, h2]
  omega

lemma mem_gsSupport {D k : ℕ} (hk : 2 ≤ k) {p : ℕ × ℕ} :
    p ∈ gsSupport D k ↔ p.1 + (k - 1) * p.2 < D := by
  refine ⟨gsSupport_weight_lt, fun h => ?_⟩
  have hj : p.2 ≤ (k - 1) * p.2 := Nat.le_mul_of_pos_left p.2 (by omega)
  simp only [gsSupport, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  exact ⟨p.2, by omega, p.1, by omega, Prod.mk.eta⟩

/-- Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`. -/
lemma gsSupport_card (D k : ℕ) :
    (gsSupport D k).card = ∑ j ∈ Finset.range D, (D - (k - 1) * j) := by
  have hdisj : ∀ j₁ ∈ Finset.range D, ∀ j₂ ∈ Finset.range D, j₁ ≠ j₂ →
      Disjoint ((Finset.range (D - (k - 1) * j₁)).image fun i => (i, j₁))
        ((Finset.range (D - (k - 1) * j₂)).image fun i => (i, j₂)) := by
    intro j₁ _ j₂ _ hne
    rw [Finset.disjoint_left]
    rintro p hp₁ hp₂
    simp only [Finset.mem_image, Finset.mem_range] at hp₁ hp₂
    obtain ⟨i₁, _, rfl⟩ := hp₁
    obtain ⟨i₂, _, heq⟩ := hp₂
    exact hne (congrArg Prod.snd heq).symm
  rw [gsSupport, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_image_of_injective _ fun a b hab => congrArg Prod.fst hab,
    Finset.card_range]

/-! ### 3. Bivariate polynomial from a coefficient vector, and its coefficients/values -/

variable {F : Type*} [Field F]

/-- The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient
`c' (i, j)` on the monomial `X^i·Y^j`, for `(i, j)` ranging over `S`. -/
noncomputable def coeffPoly (S : Finset (ℕ × ℕ)) (c' : ℕ × ℕ → F) :
    Polynomial (Polynomial F) :=
  ∑ p ∈ S, Polynomial.monomial p.2 (Polynomial.monomial p.1 (c' p))

lemma coeffPoly_coeff (S : Finset (ℕ × ℕ)) (c' : ℕ × ℕ → F) (i j : ℕ) :
    ((coeffPoly S c').coeff j).coeff i = if (i, j) ∈ S then c' (i, j) else 0 := by
  unfold coeffPoly
  rw [Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  have step : ∀ p ∈ S,
      ((Polynomial.monomial p.2 (Polynomial.monomial p.1 (c' p))).coeff j).coeff i
        = if p = (i, j) then c' p else 0 := by
    intro p _
    rcases eq_or_ne p.2 j with h2 | h2
    · rw [Polynomial.coeff_monomial, if_pos h2, Polynomial.coeff_monomial]
      rcases eq_or_ne p.1 i with h1 | h1
      · rw [if_pos h1, if_pos (by rw [← h1, ← h2])]
      · rw [if_neg h1, if_neg fun hpe => h1 (by rw [hpe])]
    · rw [Polynomial.coeff_monomial, if_neg h2, Polynomial.coeff_zero,
        if_neg fun hpe => h2 (by rw [hpe])]
  rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' S (i, j) fun p => c' p]

lemma coeffPoly_evalEval (S : Finset (ℕ × ℕ)) (c' : ℕ × ℕ → F) (a b : F) :
    ((coeffPoly S c').eval (Polynomial.C b)).eval a
      = ∑ p ∈ S, c' p * (a ^ p.1 * b ^ p.2) := by
  unfold coeffPoly
  rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Polynomial.eval_monomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C]
  ring

/-! ### 4. The evaluation linear map (coefficient vectors → values at the n points) -/

/-- The linear map sending a coefficient vector supported on `S` to the values of the
associated bivariate polynomial at the `n` points `(α s, w s)`. -/
noncomputable def evalAtPoints (S : Finset (ℕ × ℕ)) {n : ℕ} (α w : Fin n → F) :
    (↥S → F) →ₗ[F] (Fin n → F) where
  toFun c s := ∑ p ∈ S.attach, c p * (α s ^ (p : ℕ × ℕ).1 * w s ^ (p : ℕ × ℕ).2)
  map_add' c d := by
    funext s
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext s
    simp [Finset.mul_sum, mul_assoc]

lemma evalAtPoints_apply (S : Finset (ℕ × ℕ)) {n : ℕ} (α w : Fin n → F)
    (c : ↥S → F) (s : Fin n) :
    evalAtPoints S α w c s
      = ∑ p ∈ S.attach, c p * (α s ^ (p : ℕ × ℕ).1 * w s ^ (p : ℕ × ℕ).2) := rfl

/-! ### 5. The Sudan (multiplicity-1) interpolation existence theorem -/

theorem sudan_interpolation_exists (k D n : ℕ) (α w : Fin n → F)
    (hcount : n < (gsSupport D k).card) :
    ∃ Q : Polynomial (Polynomial F), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) ∧
      ∀ s : Fin n, ((Q.eval (Polynomial.C (w s))).eval (α s)) = 0 := by
  have hrank : Module.finrank F (Fin n → F)
      < Module.finrank F (↥(gsSupport D k) → F) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Fintype.card_fin]
    exact hcount
  obtain ⟨c, hc0, hLc⟩ :=
    exists_ne_zero_map_eq_zero_of_finrank_lt (evalAtPoints (gsSupport D k) α w) hrank
  set c' : ℕ × ℕ → F := fun p => if h : p ∈ gsSupport D k then c ⟨p, h⟩ else 0 with hc'
  refine ⟨coeffPoly (gsSupport D k) c', ?_, ?_, ?_⟩
  · -- nonzero
    obtain ⟨q, hq⟩ : ∃ q : ↥(gsSupport D k), c q ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc0 (funext hall)
    intro h0
    apply hq
    have h1 := coeffPoly_coeff (gsSupport D k) c' (q : ℕ × ℕ).1 (q : ℕ × ℕ).2
    rw [h0] at h1
    simp only [Polynomial.coeff_zero, Prod.mk.eta] at h1
    rw [if_pos q.2] at h1
    have h2 : c' (q : ℕ × ℕ) = c q := by
      rw [hc']
      exact dif_pos q.2
    rw [h2] at h1
    exact h1.symm
  · -- weighted-degree bound on every monomial
    intro i j hne
    rw [coeffPoly_coeff] at hne
    by_cases hmem : (i, j) ∈ gsSupport D k
    · exact gsSupport_weight_lt hmem
    · exact absurd (if_neg hmem) hne
  · -- vanishing at all n points
    intro s
    rw [coeffPoly_evalEval]
    have hL := congrFun hLc s
    rw [evalAtPoints_apply, Pi.zero_apply] at hL
    refine Eq.trans ?_ hL
    have hsum : ∑ p ∈ gsSupport D k, c' p * (α s ^ p.1 * w s ^ p.2)
        = ∑ p ∈ (gsSupport D k).attach,
            c' (p : ℕ × ℕ) * (α s ^ (p : ℕ × ℕ).1 * w s ^ (p : ℕ × ℕ).2) :=
      (Finset.sum_attach _ _).symm
    rw [hsum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h2 : c' (p : ℕ × ℕ) = c p := by
      rw [hc']
      exact dif_pos p.2
    rw [h2]

/-- Convenience form: the count hypothesis stated directly via the closed sum. -/
theorem sudan_interpolation_exists_of_sum (k D n : ℕ) (α w : Fin n → F)
    (hcount : n < ∑ j ∈ Finset.range D, (D - (k - 1) * j)) :
    ∃ Q : Polynomial (Polynomial F), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) ∧
      ∀ s : Fin n, ((Q.eval (Polynomial.C (w s))).eval (α s)) = 0 :=
  sudan_interpolation_exists k D n α w (by rw [gsSupport_card]; exact hcount)

/-! ### 6. Concrete instance: every hypothesis has a concrete inhabitant -/

lemma gsSupport_card_three_two : (gsSupport 3 2).card = 6 := by
  rw [gsSupport_card]
  decide

/-- Concrete witness over `ZMod 5` (`k = 2`, `D = 3`, `n = 5` points on the parabola
`w = α²`): since `5 < 6 = #gsSupport 3 2`, a nonzero `Q` of `(1,1)`-weighted degree `< 3`
vanishing at all five points exists. -/
theorem gs_instance_ZMod5 :
    ∃ Q : Polynomial (Polynomial (ZMod 5)), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (2 - 1) * j < 3) ∧
      ∀ s : Fin 5, ((Q.eval (Polynomial.C ((s.val : ZMod 5) ^ 2))).eval
        (s.val : ZMod 5)) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact sudan_interpolation_exists 2 3 5 (fun s => (s.val : ZMod 5))
    (fun s => (s.val : ZMod 5) ^ 2) (by rw [gsSupport_card_three_two]; norm_num)

end GSInterp

#print axioms GSInterp.exists_ne_zero_map_eq_zero_of_finrank_lt
#print axioms GSInterp.gsSupport_card
#print axioms GSInterp.sudan_interpolation_exists
#print axioms GSInterp.sudan_interpolation_exists_of_sum
#print axioms GSInterp.gs_instance_ZMod5
