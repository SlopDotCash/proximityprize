/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Jo26CurveInterpolationRegime

/-!
# [Jo26] Lemma 5.4 and the Theorem 5.5 converse (issue #334, K5, brick T2b)

The hard half of the marked/original equivalence:

* `exists_far_codeword_of_curveDecodable_jo26` — **[Jo26] Lemma 5.4 (non-covering)**: a nonzero
  `F`-submodule code that is `(ℓ, δ, a, b)`-curve-decodable with `a ≤ |F|` and `b > ℓ + 1`
  cannot `δ`-cover the space: every word `y` has a codeword at distance `> δ`.  Proof: if `y`
  were `δ`-close to all of `C`, the stack `u₀ = y, u₁ = ⋯ = u_ℓ = 0` with `f α = α^{ℓ+1} • v`
  (any `0 ≠ v ∈ C`) has full close set; decodability hands a curve agreeing with `f` on
  `> ℓ + 1` seeds; applying a dual functional `φ` with `φ v = 1` turns that agreement into
  `> ℓ + 1` roots of the nonzero degree-`(ℓ+1)` scalar polynomial
  `X^{ℓ+1} − ∑ⱼ φ(cⱼ) Xʲ` — contradiction.
* `MarkedCurveDecodable.of_curveDecodable` — **the [Jo26] Theorem 5.5 converse**: for
  `b ≤ a ≤ |F|`, [GG25] curve decodability implies marked curve decodability.  For
  `b ≤ ℓ + 1` this is the interpolation regime (T2a); for `C = ⊥` the zero curve witnesses
  everything; otherwise extend the marked instance `f` off `A₀` by Lemma 5.4's far codewords,
  making the full close set *exactly* `A₀`, and apply [GG25] decodability.
* `markedCurveDecodable_iff` — the equivalence ([Jo26] Theorem 5.5), combining both
  directions.

Brick T3 (the Theorem 5.7 covering transfer) consumes the marked form produced here.
-/

open Finset Code Polynomial
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The constant stack `u₀ = y, u₁ = ⋯ = u_ℓ = 0` combines to `y` at every seed. -/
theorem curveComb_constStack (ℓ : ℕ) (y : ι → A) (α : F) (i : ι) :
    (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) •
      (fun k : Fin (ℓ + 1) => if k = 0 then y else 0) j i) = y i := by
  rw [Finset.sum_eq_single (0 : Fin (ℓ + 1))
    (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ _) h)]
  simp

/-- **[Jo26] Lemma 5.4 (curve decodability gives a non-covering condition).**  A nonzero
`F`-submodule code that is `(ℓ, δ, a, b)`-curve-decodable with `a ≤ |F|` and `ℓ + 1 < b`
cannot `δ`-cover the space. -/
theorem exists_far_codeword_of_curveDecodable_jo26 {M : Submodule F (ι → A)} (hM : M ≠ ⊥)
    {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ}
    (h : CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b)
    (ha : a ≤ Fintype.card F) (hb : ℓ + 1 < b) (y : ι → A) :
    ∃ c ∈ M, ¬ ((δᵣ(y, c) : ℝ≥0) ≤ δ) := by
  classical
  by_contra hcov
  push_neg at hcov
  -- A nonzero codeword and a separating functional with `φ v = 1`.
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : Module.Dual F (ι → A), φ v ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff F v).mp hall)
  set φ : Module.Dual F (ι → A) := (φ₀ v)⁻¹ • φ₀ with hφdef
  have hφv : φ v = 1 := by
    simp only [hφdef, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hφ₀
  -- The covering instance: stack combining to `y`, `f α = α^{ℓ+1} • v`.
  set u : Fin (ℓ + 1) → ι → A := fun k => if k = 0 then y else 0 with hu
  set f : F → ι → A := fun α => α ^ (ℓ + 1) • v with hf
  have hfM : ∀ α, f α ∈ (M : Set (ι → A)) := fun α => M.smul_mem _ hvM
  -- The close set is everything.
  have hfull : curveCloseSet δ u f = Finset.univ := by
    refine Finset.eq_univ_of_forall fun α => ?_
    simp only [curveCloseSet, mem_filter, mem_univ, true_and]
    have hcomb : (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i) = y := by
      funext i
      exact curveComb_constStack ℓ y α i
    rw [hcomb]
    exact hcov (f α) (hfM α)
  have hclose : a ≤ (curveCloseSet δ u f).card := by
    rw [hfull, Finset.card_univ]
    exact ha
  -- Decodability hands a curve agreeing on more than `ℓ + 1` seeds.
  obtain ⟨cs, _hcs, hcount⟩ := h u f hfM hclose
  set T : Finset F := (curveCloseSet δ u f).filter
    (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i) with hT
  -- The scalar polynomial with those seeds as roots.
  set p : F[X] := X ^ (ℓ + 1) - ∑ j : Fin (ℓ + 1), C (φ (cs j)) * X ^ (j : ℕ) with hp
  have hproots : ∀ α ∈ T, p.eval α = 0 := by
    intro α hα
    have heq : f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i :=
      (Finset.mem_filter.mp hα).2
    have hφeq : φ (f α) = φ (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j) := by
      congr 1
      rw [heq]
      funext i
      rw [Finset.sum_apply]
      rfl
    have hlhs : φ (f α) = α ^ (ℓ + 1) := by
      rw [hf]
      simp only [map_smul, smul_eq_mul, hφv, mul_one]
    have hrhs : φ (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j)
        = ∑ j : Fin (ℓ + 1), φ (cs j) * α ^ (j : ℕ) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    simp only [hp, eval_sub, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C]
    rw [sub_eq_zero]
    rw [hlhs] at hφeq
    rw [hrhs] at hφeq
    exact hφeq
  -- Degree bookkeeping: `p ≠ 0` and `natDegree p ≤ ℓ + 1`.
  have hsumdeg : (∑ j : Fin (ℓ + 1), C (φ (cs j)) * X ^ (j : ℕ) : F[X]).natDegree ≤ ℓ := by
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun j _ => ?_⟩
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
    omega
  have hp0 : p ≠ 0 := by
    intro h0
    have hc : p.coeff (ℓ + 1) = 0 := by rw [h0]; simp
    rw [hp] at hc
    simp only [coeff_sub, coeff_X_pow, if_pos rfl] at hc
    have hcoeff : (∑ j : Fin (ℓ + 1), C (φ (cs j)) * X ^ (j : ℕ) : F[X]).coeff (ℓ + 1)
        = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hsumdeg (by omega))
    rw [hcoeff] at hc
    norm_num at hc
  have hpdeg : p.natDegree ≤ ℓ + 1 := by
    rw [hp]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    simp only [Polynomial.natDegree_X_pow]
    omega
  -- More roots than the degree allows.
  have hsubroots : T ⊆ p.roots.toFinset := by
    intro α hα
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hproots α hα
  have : b ≤ ℓ + 1 := by
    calc b ≤ T.card := hcount
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hsubroots
      _ ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := (Polynomial.card_roots' p)
      _ ≤ ℓ + 1 := hpdeg
  omega

/-- **The [Jo26] Theorem 5.5 converse**: for `b ≤ a ≤ |F|`, [GG25] curve decodability of an
`F`-submodule code implies marked curve decodability. -/
theorem MarkedCurveDecodable.of_curveDecodable {M : Submodule F (ι → A)}
    {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ}
    (h : CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b)
    (hba : b ≤ a) (ha : a ≤ Fintype.card F) :
    MarkedCurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b := by
  classical
  -- The small-witness regime is interpolation (T2a).
  by_cases hbl : b ≤ ℓ + 1
  · exact markedCurveDecodable_interpolation M ℓ δ hbl hba
  push_neg at hbl
  -- The zero code explains everything with the zero curve.
  by_cases hM : M = ⊥
  · intro u f hf A₀ hcard _hdist
    refine ⟨fun _ => 0, fun _ => Submodule.zero_mem M, ?_⟩
    have hall : ∀ α ∈ A₀,
        f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (0 : ι → A) i := by
      intro α _
      have hf0 : f α = 0 := by
        have := hf α
        rw [hM] at this
        simpa using this
      rw [hf0]
      funext i
      simp
    rw [Finset.filter_true_of_mem hall, hcard]
    exact hba
  -- The genuine regime: extend `f` off `A₀` by far codewords.
  intro u f hf A₀ hcard hdist
  have h54 := exists_far_codeword_of_curveDecodable_jo26 hM h ha hbl
  set f' : F → ι → A := fun α =>
    if α ∈ A₀ then f α
    else Classical.choose (h54 (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i)) with hf'
  have hf'M : ∀ α, f' α ∈ (M : Set (ι → A)) := by
    intro α
    simp only [hf']
    by_cases hα : α ∈ A₀
    · rw [if_pos hα]; exact hf α
    · rw [if_neg hα]
      exact (Classical.choose_spec
        (h54 (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i))).1
  -- The full close set of `(u, f')` is exactly `A₀`.
  have hcloseSet : curveCloseSet δ u f' = A₀ := by
    ext α
    simp only [curveCloseSet, mem_filter, mem_univ, true_and]
    constructor
    · intro hle
      by_contra hα
      have hfar := (Classical.choose_spec
        (h54 (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i))).2
      simp only [hf'] at hle
      rw [if_neg hα] at hle
      exact hfar hle
    · intro hα
      rw [hf']
      simp only [if_pos hα]
      exact hdist α hα
  obtain ⟨cs, hcs, hcount⟩ := h u f' hf'M
    (by rw [hcloseSet, hcard])
  refine ⟨cs, hcs, le_trans hcount (le_of_eq ?_)⟩
  rw [hcloseSet]
  refine Finset.card_bij (fun α _ => α) ?_ (fun _ hα _ hβ h => h) (fun α hα => ⟨α, ?_, rfl⟩)
  · intro α hα
    rw [Finset.mem_filter] at hα ⊢
    refine ⟨hα.1, ?_⟩
    have := hα.2
    simp only [hf', if_pos hα.1] at this
    exact this
  · rw [Finset.mem_filter] at hα ⊢
    refine ⟨hα.1, ?_⟩
    simp only [hf', if_pos hα.1]
    exact hα.2

/-- **[Jo26] Theorem 5.5 (marked/original equivalence)** for `F`-submodule codes with
`b ≤ a ≤ |F|`. -/
theorem markedCurveDecodable_iff {M : Submodule F (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ}
    (hba : b ≤ a) (ha : a ≤ Fintype.card F) :
    MarkedCurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b
      ↔ CurveDecodable (F := F) (M : Set (ι → A)) ℓ δ a b :=
  ⟨ProximityGap.curveDecodable_of_marked,
    fun h => MarkedCurveDecodable.of_curveDecodable h hba ha⟩

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.exists_far_codeword_of_curveDecodable_jo26
#print axioms ProximityGap.MarkedCurveDecodable.of_curveDecodable
#print axioms ProximityGap.markedCurveDecodable_iff
