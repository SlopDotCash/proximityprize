/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CubicSupplyCountermodel

/-!
# Exactness of the Sylvester-cubic characterization (#389)

`CubicSupplyCountermodel.lean` proved the ⟸ direction of the Sylvester mechanism: a
domain triple summing to zero is an explainable 3-core of the cubic word `x ↦ x³`.  For
an UPPER bound on the cubic supply (the smooth-domain suppression, conditional on the
additive-energy input — see `SmoothCubicSupplyBound.lean`) the *converse* is needed, and
it is true:

* `cubic_explainable_imp_sumZero` — three distinct domain points whose cubic graph lies on
  an affine line must sum to zero.  Elementary: from `aᵢ³ = u·aᵢ + v` (the affine explainer)
  pairwise differences give `aᵢ² + aᵢaⱼ + aⱼ² = u`, so `(a−c)(a+b+c) = 0`; distinctness
  forces `a+b+c = 0`.  No Vieta, no factorization.
* `cubic_explainable_iff_sumZero` — combining with `cubic_triple_explainable`: for distinct
  triples, **explainable ⟺ sum-zero** — the Sylvester characterization is exact.
* `cubicSupply_eq_sumZeroCard` — hence the cubic word's explainable-3-core count is EXACTLY
  the number of sum-zero domain 3-subsets.  Upper and lower bounds coincide; on smooth
  domains the sum-zero count is the additive-energy-governed quantity bounded in
  `SmoothCubicSupplyBound.lean`.
-/

open Finset Polynomial

namespace ProximityGap.Cubic

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- **The converse Sylvester direction**: three distinct domain points whose cubic graph is
collinear sum to zero.  The explainer is affine, `P.eval x = u·x + v`; the pairwise
quadratic identities `aᵢ² + aᵢaⱼ + aⱼ² = u` and distinctness give `a+b+c = 0`. -/
theorem cubic_explainable_imp_sumZero (dom : Fin n ↪ F) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hexp : ExplainableOn dom 2 (cubicWord dom) {i, j, l}) :
    dom i + dom j + dom l = 0 := by
  obtain ⟨c, ⟨P, hPdeg, hc⟩, hagree⟩ := hexp
  -- affine form of the explainer
  have hPnat : P.natDegree ≤ 1 := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · exact Nat.lt_succ_iff.mp ((Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg)
  obtain ⟨u, v, hPuv⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hPnat
  have hab : dom i ≠ dom j := fun h => hij (dom.injective h)
  have had : dom i ≠ dom l := fun h => hil (dom.injective h)
  have hbd : dom j ≠ dom l := fun h => hjl (dom.injective h)
  have heval : ∀ x : F, P.eval x = u * x + v := by
    intro x; rw [hPuv, eval_add, eval_mul, eval_C, eval_X, eval_C]
  -- the agreement equations: (dom x)³ = u·(dom x) + v on the core
  have hEval : ∀ x ∈ ({i, j, l} : Finset (Fin n)),
      (dom x) ^ 3 = u * dom x + v := by
    intro x hx
    have h := hagree x hx
    rw [hc] at h
    simp only [cubicWord] at h
    rw [← h, heval]
  have key : ∀ {p q : F}, p ≠ q → p ^ 3 = u * p + v → q ^ 3 = u * q + v →
      p ^ 2 + p * q + q ^ 2 = u := by
    intro p q hpq hp hq
    have hfac : (p - q) * (p ^ 2 + p * q + q ^ 2 - u) = 0 := by linear_combination hp - hq
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hpq
    · linear_combination h
  have hu1 : (dom i) ^ 2 + dom i * dom j + (dom j) ^ 2 = u :=
    key hab (hEval i (by simp)) (hEval j (by simp))
  have hu2 : (dom j) ^ 2 + dom j * dom l + (dom l) ^ 2 = u :=
    key hbd (hEval j (by simp)) (hEval l (by simp))
  have hfinal : (dom i - dom l) * (dom i + dom j + dom l) = 0 := by
    linear_combination hu1 - hu2
  rcases mul_eq_zero.mp hfinal with h | h
  · exact absurd (sub_eq_zero.mp h) had
  · exact h

open Classical in
omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- **The exact Sylvester characterization**: for a 3-subset of distinct domain points,
explainable by the cubic word ⟺ the three values sum to zero. -/
theorem cubic_explainable_iff_sumZero (dom : Fin n ↪ F) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ExplainableOn dom 2 (cubicWord dom) {i, j, l} ↔ dom i + dom j + dom l = 0 := by
  constructor
  · exact cubic_explainable_imp_sumZero dom hij hil hjl
  · intro h; exact cubic_triple_explainable dom h

open Classical in
omit [Fintype F] [NeZero n] in
/-- **The cubic supply is EXACTLY the sum-zero count**: the cubic word's explainable
3-core count equals the number of domain 3-subsets whose values sum to zero.  (Combining
`sumZero_subset_explainable` with the converse direction.) -/
theorem cubicSupply_eq_sumZeroCard (dom : Fin n ↪ F) :
    ((Finset.univ.powersetCard 3).filter
        (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card
      = ((Finset.univ.powersetCard 3).filter (fun T => ∑ i ∈ T, dom i = 0)).card := by
  congr 1
  apply Finset.filter_congr
  intro T hT
  obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨i, j, l, hij, hil, hjl, rfl⟩ := Finset.card_eq_three.mp hTcard
  rw [Finset.sum_insert (by simp [hij, hil]),
    Finset.sum_insert (by simp [hjl]), Finset.sum_singleton]
  rw [cubic_explainable_iff_sumZero dom hij hil hjl]
  constructor <;> intro h <;> linear_combination h

end ProximityGap.Cubic
