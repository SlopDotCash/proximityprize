/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HighMultiplicityBadCount
import ArkLib.Data.CodingTheory.ProximityGap.RatioValueMultiplicity

/-!
# Bridge: polynomial error lines are degree-collapsed (#389, face (iv) closure of the local step)

`HighMultiplicityBadCount.highMult_empty_of_lt` vanishes the per-error-line bad set once the
demanded agreement exceeds the maximum multiplicity `D` of the line's ratio.
`RatioValueMultiplicity.value_mult_le_max` bounds that multiplicity by `max(deg P, deg Q)` when the
ratio is a genuine rational function.  This file connects them: when the two error coordinates are
**low-degree polynomial evaluations** `e₀ i = P(dom i)`, `e₁ i = Q(dom i)` on an injective domain
`dom` (the Reed–Solomon / GRS case), the incidence multiplicity `mult` is itself degree-bounded,

> `mult e₀ e₁ γ ≤ max(deg P, deg Q)`   whenever `P + γ·Q ≢ 0`   (`mult_poly_le_max`),

so the degree-collapse fires unconditionally: `highMult_empty_of_lt` then gives **no bad scalar**
once `max(deg P, deg Q) < μ₀` (`badScalars_empty_of_degree`).

This is the local certificate H-EXT consumes (`DISPROOF_LOG.md` O159): for a structured error line
(both coordinates bounded-degree polynomials on the domain) the per-pair supply collapses purely by
degree.  It does NOT bypass the open core — the open core is the case where the *stack* coordinate
`u₀` is an arbitrary word (no polynomial structure), so the ratio degree is unbounded and the
collapse does not apply; the structured case is precisely the one this certifies.  Axiom-clean.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.RatioMultiplicity

open ArkLib.ProximityGap.HighMultiplicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] [Fintype F] in
/-- **A polynomial error line has degree-bounded multiplicity.**  If the error coordinates are
evaluations `e₀ i = P(dom i)`, `e₁ i = Q(dom i)` of polynomials on an injective domain `dom`, then
for every scalar `γ` with `P + γ·Q ≢ 0`, the incidence multiplicity is at most `max(deg P, deg Q)`.
The level set `{i : P(dom i) + γ·Q(dom i) = 0}` injects into the roots of the nonzero polynomial
`P + γ·Q`. -/
theorem mult_poly_le_max (dom : ι → F) (hdom : Function.Injective dom)
    (P Q : F[X]) {γ : F} (h : P + C γ * Q ≠ 0) :
    mult (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) γ
      ≤ max P.natDegree Q.natDegree := by
  classical
  -- drop the `e₁ ≠ 0` conjunct: mult ≤ #{i : P(dom i) + γ·Q(dom i) = 0}
  have hstep1 :
      mult (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) γ
        ≤ (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) = 0)).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2
  -- transport the level set along the injective domain into `image dom`
  have hstep2 :
      (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) = 0)).card
        = ((univ.image dom).filter (fun x => P.eval x = (-γ) * Q.eval x)).card := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ hdom]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> intro hi <;> linear_combination hi
  -- the level set is a value-fibre of the ratio `P/Q`; bound it by the degree
  have hc : P - C (-γ) * Q ≠ 0 := by
    rwa [map_neg, neg_mul, sub_neg_eq_add]
  exact (hstep1.trans_eq hstep2).trans
    (value_mult_le_max P Q (-γ) hc (univ.image dom))

omit [DecidableEq ι] in
/-- **Degree-collapse for polynomial error lines.**  If the error coordinates are evaluations of
`P, Q` on an injective domain, and the demanded agreement `μ₀` exceeds `max(deg P, deg Q)`, then —
provided `P + γ·Q ≢ 0` for every scalar `γ` (no value of the ratio is identically attained) — there
is **no** bad scalar: the per-error-line bad set is empty.  The structured (bounded-degree) supply
collapses purely by degree. -/
theorem badScalars_empty_of_degree (dom : ι → F) (hdom : Function.Injective dom)
    (P Q : F[X]) {μ₀ : ℕ} (hμ : max P.natDegree Q.natDegree < μ₀)
    (hnz : ∀ γ : F, P + C γ * Q ≠ 0) :
    univ.filter (fun γ : F =>
        μ₀ ≤ mult (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) γ) = ∅ :=
  highMult_empty_of_lt _ _ (fun γ => mult_poly_le_max dom hdom P Q (hnz γ)) hμ

omit [DecidableEq ι] in
/-- **Exact degree-collapse for weight-thresholded polynomial error lines.**  If the error
coordinates are polynomial evaluations and every ratio fibre has multiplicity at most
`max(deg P, deg Q)`, then the actual low-weight bad-scalar set is empty as soon as that degree is
below the exact required multiplicity

`#{Q ≠ 0 on dom} + #{Q = 0 ∧ P ≠ 0 on dom} - w`.

This composes `mult_poly_le_max` with
`HighMultiplicity.badWeight_empty_of_mult_cap_exact`, retaining the fixed zero-`Q` correction that
the older `badScalars_empty_of_degree` high-multiplicity form did not expose. -/
theorem badWeight_empty_of_degree_exact (dom : ι → F) (hdom : Function.Injective dom)
    (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hnz : ∀ γ : F, P + C γ * Q ≠ 0) :
    univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w) = ∅ :=
  badWeight_empty_of_mult_cap_exact
    (fun i => P.eval (dom i)) (fun i => Q.eval (dom i))
    (fun γ => mult_poly_le_max dom hdom P Q (hnz γ)) hdeg

omit [DecidableEq ι] in
/-- **Exact degree-collapse, degenerate-scalar containment form.**  Without assuming
`P + γ·Q` is nonzero for every scalar, the exact degree condition still forces every low-weight
bad scalar into the degenerate set where the whole line polynomial vanishes identically:

`{γ : weight(P(dom)+γQ(dom)) ≤ w} ⊆ {γ : P + γQ = 0}`.

Thus the only possible survivors of the structured polynomial-line gate are constant-ratio
degeneracies. -/
theorem badWeight_subset_degenerate_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w) :
    univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)
      ⊆ univ.filter (fun γ : F => P + C γ * Q = 0) := by
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  refine ⟨Finset.mem_univ γ, ?_⟩
  by_contra hnonzero
  have hcap : mult (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) γ
      ≤ max P.natDegree Q.natDegree :=
    mult_poly_le_max dom hdom P Q hnonzero
  have hge := weightLine_le_imp_highMult_exact
    (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) w γ hγ.2
  exact (not_lt.mpr hcap) (lt_of_lt_of_le hdeg hge)

omit [DecidableEq ι] in
/-- **Degenerate polynomials always give low-weight scalars.**  If `P + γ·Q = 0` as a polynomial,
then the evaluated line word is identically zero, hence it lies in every weight-`≤ w` ball. -/
theorem degenerateScalars_subset_badWeight (dom : ι → F) (P Q : F[X]) {w : ℕ} :
    univ.filter (fun γ : F => P + C γ * Q = 0)
      ⊆ univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w) := by
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  refine ⟨Finset.mem_univ γ, ?_⟩
  have hzero : univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _ hi
    have heval : P.eval (dom i) + γ * Q.eval (dom i) = 0 := by
      have hpoly := congrArg (fun R : F[X] => R.eval (dom i)) hγ.2
      simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using hpoly
    exact hi heval
  rw [hzero, Finset.card_empty]
  exact Nat.zero_le w

omit [DecidableEq ι] in
/-- **Exact degree-collapse equality.**  Under the exact degree condition, the low-weight scalar set
is precisely the degenerate polynomial set:

`{γ : weight(P(dom)+γQ(dom)) ≤ w} = {γ : P + γQ = 0}`.

The forward inclusion is the degree-collapse argument; the reverse inclusion is the trivial zero
line word at every degenerate scalar. -/
theorem badWeight_eq_degenerate_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w) :
    univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)
      = univ.filter (fun γ : F => P + C γ * Q = 0) :=
  Finset.Subset.antisymm
    (badWeight_subset_degenerate_of_degree_exact dom hdom P Q hdeg)
    (degenerateScalars_subset_badWeight dom P Q)

omit [DecidableEq ι] in
/-- **Exact cardinal form of degree-collapse equality.**  Under the exact degree condition, the
number of low-weight scalars equals the number of degenerate scalars. -/
theorem badWeight_card_eq_degenerate_card_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w) :
    (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)).card
      = (univ.filter (fun γ : F => P + C γ * Q = 0)).card := by
  rw [badWeight_eq_degenerate_of_degree_exact dom hdom P Q hdeg]

omit [DecidableEq ι] in
/-- **Exact degree-collapse, cardinal containment form.**  Under the exact degree condition, the
number of low-weight bad scalars is at most the number of degenerate scalars with
`P + γ·Q = 0`. -/
theorem badWeight_card_le_degenerate_card_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w) :
    (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)).card
      ≤ (univ.filter (fun γ : F => P + C γ * Q = 0)).card :=
  Finset.card_le_card (badWeight_subset_degenerate_of_degree_exact dom hdom P Q hdeg)

omit [Fintype ι] [DecidableEq ι] in
/-- **There is at most one degenerate scalar** when `Q ≠ 0`: two identities
`P + γQ = 0` and `P + δQ = 0` force `(γ-δ)Q = 0`, hence `γ = δ`. -/
theorem degenerateScalars_card_le_one (P Q : F[X]) (hQ : Q ≠ 0) :
    (univ.filter (fun γ : F => P + C γ * Q = 0)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro γ hγ δ hδ
  rw [Finset.mem_filter] at hγ hδ
  have hz : C (γ - δ) * Q = 0 := by
    calc
      C (γ - δ) * Q = C γ * Q - C δ * Q := by rw [map_sub, sub_mul]
      _ = (P + C γ * Q) - (P + C δ * Q) := by abel
      _ = 0 := by rw [hγ.2, hδ.2, sub_self]
  rcases mul_eq_zero.mp hz with hC | hQ0
  · exact sub_eq_zero.mp (Polynomial.C_eq_zero.mp hC)
  · exact absurd hQ0 hQ

omit [Fintype ι] [DecidableEq ι] in
/-- **A witnessed degenerate scalar is the unique degenerate scalar.**  If `Q ≠ 0` and
`P + γ₀·Q = 0`, then the degenerate-scalar set is exactly `{γ₀}`. -/
theorem degenerateScalars_eq_singleton_of (P Q : F[X]) {γ₀ : F}
    (hQ : Q ≠ 0) (hγ₀ : P + C γ₀ * Q = 0) :
    univ.filter (fun γ : F => P + C γ * Q = 0) = {γ₀} := by
  classical
  ext γ
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro hγ
    have hz : C (γ - γ₀) * Q = 0 := by
      calc
        C (γ - γ₀) * Q = C γ * Q - C γ₀ * Q := by rw [map_sub, sub_mul]
        _ = (P + C γ * Q) - (P + C γ₀ * Q) := by abel
        _ = 0 := by rw [hγ, hγ₀, sub_self]
    rcases mul_eq_zero.mp hz with hC | hQ0
    · exact sub_eq_zero.mp (Polynomial.C_eq_zero.mp hC)
    · exact absurd hQ0 hQ
  · intro hγ
    subst hγ
    exact hγ₀

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Degenerate scalar iff scalar multiple.**  A scalar `γ` with `P + γ·Q = 0` exists exactly
when `P` is a scalar multiple of `Q` (with scalar `-γ`). -/
theorem degenerate_exists_iff_scalarMultiple (P Q : F[X]) :
    (∃ γ : F, P + C γ * Q = 0) ↔ ∃ c : F, P = C c * Q := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨-γ, ?_⟩
    have hP : P = -(C γ * Q) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hγ
    rw [hP, map_neg, neg_mul]
  · rintro ⟨c, hP⟩
    refine ⟨-c, ?_⟩
    rw [hP, map_neg, neg_mul]
    exact add_neg_cancel _

omit [DecidableEq ι] in
/-- **Exact degree-collapse leaves at most one low-weight scalar.**  For a nonzero denominator
polynomial `Q`, the exact degree condition forces every low-weight scalar into the degenerate set,
and that degenerate set has cardinality at most one. -/
theorem badWeight_card_le_one_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hQ : Q ≠ 0) :
    (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)).card
      ≤ 1 :=
  (badWeight_card_le_degenerate_card_of_degree_exact dom hdom P Q hdeg).trans
    (degenerateScalars_card_le_one P Q hQ)

omit [DecidableEq ι] in
/-- **Exact singleton form of polynomial-line degree collapse.**  Under the exact degree
condition, if a constant-ratio scalar `γ₀` exists (`P + γ₀·Q = 0`) and `Q ≠ 0`, then the
weight-`≤ w` bad-scalar set is exactly `{γ₀}`.  The forward inclusion is the degree-collapse
containment; the reverse inclusion holds because the line word is identically zero at `γ₀`. -/
theorem badWeight_eq_singleton_of_degree_exact_of_degenerate (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ} {γ₀ : F}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hQ : Q ≠ 0) (hγ₀ : P + C γ₀ * Q = 0) :
    univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)
      = {γ₀} := by
  classical
  apply Finset.Subset.antisymm
  · intro γ hγ
    have hsub := badWeight_subset_degenerate_of_degree_exact dom hdom P Q hdeg hγ
    rw [degenerateScalars_eq_singleton_of P Q hQ hγ₀] at hsub
    exact hsub
  · intro γ hγ
    rw [Finset.mem_singleton] at hγ
    subst hγ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hzero : univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _ hi
      have heval : P.eval (dom i) + γ * Q.eval (dom i) = 0 := by
        have hpoly := congrArg (fun R : F[X] => R.eval (dom i)) hγ₀
        simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using hpoly
      exact hi heval
    rw [hzero, Finset.card_empty]
    exact Nat.zero_le w

omit [DecidableEq ι] in
/-- **Empty-or-singleton dichotomy for structured polynomial lines.**  Under the exact degree
condition and `Q ≠ 0`, the weight-`≤ w` scalar set is either empty or exactly one singleton
`{γ₀}`, where `γ₀` is the unique scalar with `P + γ₀·Q = 0`. -/
theorem badWeight_eq_empty_or_singleton_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hQ : Q ≠ 0) :
    (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w) = ∅)
      ∨ ∃ γ₀ : F, P + C γ₀ * Q = 0 ∧
        univ.filter (fun γ : F =>
          (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w) = {γ₀} := by
  classical
  by_cases hdegenerate : ∃ γ₀ : F, P + C γ₀ * Q = 0
  · rcases hdegenerate with ⟨γ₀, hγ₀⟩
    exact Or.inr ⟨γ₀, hγ₀,
      badWeight_eq_singleton_of_degree_exact_of_degenerate dom hdom P Q hdeg hQ hγ₀⟩
  · left
    rw [badWeight_eq_degenerate_of_degree_exact dom hdom P Q hdeg]
    rw [Finset.filter_eq_empty_iff]
    intro γ _ hγ
    exact hdegenerate ⟨γ, hγ⟩

omit [DecidableEq ι] in
/-- **Cardinality dichotomy for structured polynomial lines.**  Under the exact degree condition
and `Q ≠ 0`, the low-weight scalar count is exactly `0` or exactly `1`. -/
theorem badWeight_card_eq_zero_or_one_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hQ : Q ≠ 0) :
    (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)).card = 0
      ∨ (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)).card = 1 := by
  rcases badWeight_eq_empty_or_singleton_of_degree_exact dom hdom P Q hdeg hQ with h | h
  · left
    rw [h, Finset.card_empty]
  · rcases h with ⟨γ₀, _, hset⟩
    right
    rw [hset, Finset.card_singleton]

omit [DecidableEq ι] in
/-- **Cardinality-one criterion for structured polynomial lines.**  Under the exact degree
condition and `Q ≠ 0`, the low-weight scalar count is exactly one iff a degenerate scalar exists.
Combined with `badWeight_card_eq_zero_or_one_of_degree_exact`, this is the exact binary
classification of the structured polynomial-line local gate. -/
theorem badWeight_card_eq_one_iff_degenerate_exists_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hQ : Q ≠ 0) :
    (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)).card = 1
      ↔ ∃ γ₀ : F, P + C γ₀ * Q = 0 := by
  constructor
  · intro hcard
    rw [badWeight_eq_degenerate_of_degree_exact dom hdom P Q hdeg] at hcard
    rw [Finset.card_eq_one] at hcard
    rcases hcard with ⟨γ₀, hset⟩
    refine ⟨γ₀, ?_⟩
    have hmem : γ₀ ∈ univ.filter (fun γ : F => P + C γ * Q = 0) := by
      rw [hset]
      simp
    exact (Finset.mem_filter.mp hmem).2
  · rintro ⟨γ₀, hγ₀⟩
    rw [badWeight_eq_singleton_of_degree_exact_of_degenerate dom hdom P Q hdeg hQ hγ₀]
    exact Finset.card_singleton γ₀

omit [DecidableEq ι] in
/-- **Cardinality-one criterion, scalar-multiple form.**  Under the exact degree condition and
`Q ≠ 0`, the low-weight scalar count is exactly one iff `P` is a scalar multiple of `Q`. -/
theorem badWeight_card_eq_one_iff_scalarMultiple_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hQ : Q ≠ 0) :
    (univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w)).card = 1
      ↔ ∃ c : F, P = C c * Q := by
  rw [badWeight_card_eq_one_iff_degenerate_exists_of_degree_exact dom hdom P Q hdeg hQ,
    degenerate_exists_iff_scalarMultiple]

omit [DecidableEq ι] in
/-- **Empty criterion, scalar-multiple form.**  Under the exact degree condition and `Q ≠ 0`, the
low-weight scalar set is empty iff `P` is not a scalar multiple of `Q`. -/
theorem badWeight_empty_iff_not_scalarMultiple_of_degree_exact (dom : ι → F)
    (hdom : Function.Injective dom) (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hQ : Q ≠ 0) :
    univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w) = ∅
      ↔ ¬ ∃ c : F, P = C c * Q := by
  constructor
  · intro hbad hscalar
    have hone := (badWeight_card_eq_one_iff_scalarMultiple_of_degree_exact
      dom hdom P Q hdeg hQ).2 hscalar
    rw [hbad, Finset.card_empty] at hone
    omega
  · intro hnot
    rw [badWeight_eq_degenerate_of_degree_exact dom hdom P Q hdeg]
    rw [Finset.filter_eq_empty_iff]
    intro γ _ hγ
    exact hnot ((degenerate_exists_iff_scalarMultiple P Q).1 ⟨γ, hγ⟩)

end ArkLib.ProximityGap.RatioMultiplicity

open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_empty_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_subset_degenerate_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms degenerateScalars_subset_badWeight
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_eq_degenerate_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_card_eq_degenerate_card_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_card_le_degenerate_card_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms degenerateScalars_card_le_one
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_card_le_one_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms degenerateScalars_eq_singleton_of
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms degenerate_exists_iff_scalarMultiple
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_eq_singleton_of_degree_exact_of_degenerate
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_eq_empty_or_singleton_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_card_eq_zero_or_one_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_card_eq_one_iff_degenerate_exists_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_card_eq_one_iff_scalarMultiple_of_degree_exact
open ArkLib.ProximityGap.RatioMultiplicity in
#print axioms badWeight_empty_iff_not_scalarMultiple_of_degree_exact
