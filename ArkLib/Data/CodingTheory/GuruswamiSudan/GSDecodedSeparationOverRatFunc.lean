/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorDegreeOverRatFunc

/-!
# Hab25 §3 — decoded-list separation at a good point (the residual-free S5 → S6 bridge)

The Hensel step S6 of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`) tracks the decoded codewords of the
generic fold as *branches* above a good base point `x₀ ∈ D`: it is essential that **distinct
decoded polynomials stay distinct after the specialization `X ↦ x₀`** — otherwise two branches
collide at the base point and the per-factor "unique affine pair" bookkeeping breaks.

This file proves that such a separating good point exists, with **zero residual hypotheses**
(in particular no separability/characteristic assumption — unlike the per-factor discriminant
form of S5, the avoidance polynomials here are the pairwise differences `p − p'`, which are
nonzero by construction):

* `exists_eval_injOn_point` — for any finite list `Ps` of polynomials of degree `≤ D` over a
  field, once `|Ps|²·D < n` some evaluation point among `n` distinct ones is **injective on
  `Ps`**: route the `≤ |Ps|²` pairwise differences through the S5 avoidance engine
  `exists_common_eval_ne_zero`.

* `gs_decoded_eval_injective` — packaged for the GS interpolant over `K = F(Z)`: the
  cardinality side is **discharged by the S3/S4 list-size bound**
  (`Ps.card ≤ D/(k−1)`, `GSFactorExtract.gs_list_size_le`), so for any decoded list (degree
  `< k` messages whose linear factors divide `Q`) a separating point exists as soon as the
  parameters sit in the paper regime

    `(D/(k−1))² · (k−1) < n`,    `D := gs_degree_bound k n m`,

  the Lean form of Hab25's S5 numerology `ℓ²·ρn < n ≤ |F|` (with `ℓ ~ D/(k−1)·…`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

/-- **A common evaluation point separating a finite list of polynomials.** For a finite set
`Ps` of polynomials of degree `≤ D` over a field and `n > |Ps|²·D` distinct evaluation points,
some point `ωs i₀` is injective on `Ps`: the `≤ |Ps|²` nonzero pairwise differences `p − p'`
are avoidance polynomials of degree `≤ D` for the S5 engine `exists_common_eval_ne_zero`. -/
theorem exists_eval_injOn_point {K : Type*} [Field K] {n : ℕ} (ωs : Fin n ↪ K)
    (Ps : Finset K[X]) {D : ℕ}
    (hdeg : ∀ p ∈ Ps, p.natDegree ≤ D)
    (hn : Ps.card * Ps.card * D < n) :
    ∃ i₀ : Fin n, ∀ p ∈ Ps, ∀ p' ∈ Ps,
      p.eval (ωs i₀) = p'.eval (ωs i₀) → p = p' := by
  classical
  set Pairs : Finset (K[X] × K[X]) := (Ps ×ˢ Ps).filter (fun pq => pq.1 ≠ pq.2) with hPairs
  have h0 : ∀ pq ∈ Pairs, pq.1 - pq.2 ≠ 0 := by
    intro pq hpq
    rw [hPairs, Finset.mem_filter] at hpq
    exact sub_ne_zero_of_ne hpq.2
  have hdeg' : ∀ pq ∈ Pairs, (pq.1 - pq.2).natDegree ≤ D := by
    intro pq hpq
    rw [hPairs, Finset.mem_filter, Finset.mem_product] at hpq
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hdeg _ hpq.1.1) (hdeg _ hpq.1.2))
  have hcard : Pairs.card * D < n := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_right D ?_) hn
    calc Pairs.card ≤ (Ps ×ˢ Ps).card := Finset.card_filter_le _ _
      _ = Ps.card * Ps.card := Finset.card_product ..
  obtain ⟨i₀, hi₀⟩ :=
    exists_common_eval_ne_zero ωs Pairs (fun pq => pq.1 - pq.2) h0 hdeg' hcard
  refine ⟨i₀, fun p hp p' hp' heq => ?_⟩
  by_contra hne
  have hmem : (p, p') ∈ Pairs := by
    rw [hPairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp, hp'⟩, hne⟩
  have hsub := hi₀ (p, p') hmem
  rw [Polynomial.eval_sub] at hsub
  exact hsub (sub_eq_zero_of_eq heq)

variable {F : Type} [Field F]

/-- **Hab25 §3, the residual-free S5 → S6 bridge for the GS interpolant.**

There is a generic-fold GS interpolant `Q` over `K = F(Z)` (S2 `Conditions`) such that for
**any** decoded list `Ps` — degree-`≤ k−1` messages over `K` whose linear factors `Y − C p`
divide `Q` (the S1/S2 divisibility output) — once the parameters sit in the paper regime

  `(D/(k−1))² · (k−1) < n`,    `D := gs_degree_bound k n m`,

some lifted evaluation point `x₀ := liftedDomain ωs i₀` **separates the decoded list**:
`p ↦ p.eval x₀` is injective on `Ps`. The cardinality input `|Ps| ≤ D/(k−1)` is discharged
internally by the S3/S4 list-size bound (`GSFactorExtract.gs_list_size_le` composed with the
S3 `Y`-degree cap), so *no hypothesis beyond the divisibility shape and the regime remains* —
in particular no separability/characteristic residual.

This is the base-point configuration the Hensel lift (S6) starts from: distinct decoded
branches of the generic fold sit over **distinct** points of the fiber at `x₀`. -/
theorem gs_decoded_eval_injective {n : ℕ} (k m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hk1 : 1 < k) (hn0 : n ≠ 0) (hm : 1 ≤ m) (hk : 0 < k - 1)
    (hregime :
      (gs_degree_bound k n m / (k - 1)) * (gs_degree_bound k n m / (k - 1)) * (k - 1) < n) :
    ∃ Q : (RatFunc F)[X][Y],
      GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
        (liftedDomain ωs) (genericFold f₀ f₁) Q ∧
      ∀ Ps : Finset (RatFunc F)[X],
        (∀ p ∈ Ps, (X - C p) ∣ Q) →
        (∀ p ∈ Ps, p.natDegree ≤ k - 1) →
        ∃ i₀ : Fin n, ∀ p ∈ Ps, ∀ p' ∈ Ps,
          p.eval (liftedDomain ωs i₀) = p'.eval (liftedDomain ωs i₀) → p = p' := by
  obtain ⟨Q, hQ, hlist⟩ := decodedList_card_le k m ωs f₀ f₁ hk1 hn0 hm hk
  refine ⟨Q, hQ, fun Ps hdvd hdeg => ?_⟩
  refine exists_eval_injOn_point (liftedDomain ωs) Ps hdeg ?_
  have hcard := hlist Ps hdvd
  calc Ps.card * Ps.card * (k - 1)
      ≤ (gs_degree_bound k n m / (k - 1)) * (gs_degree_bound k n m / (k - 1)) * (k - 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hcard hcard)
    _ < n := hregime

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.exists_eval_injOn_point
#print axioms GuruswamiSudan.OverRatFunc.gs_decoded_eval_injective
