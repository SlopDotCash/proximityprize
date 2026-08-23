/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The ownership bound (#371): the radius-free unification

The unification of the WB-pencil lane and the dimension-ladder lane.  For a
`(k+1)`-tuple `t` of domain positions, the **interpolation residual** `e_t(y)` is
the bordered Vandermonde determinant (powers `x^0..x^{k−1}` plus the value column).
Three facts drive everything:

* `residual_eq_zero_of_extends` — if `y` agrees with a degree-`< k` polynomial on
  the tuple, the residual vanishes (the coefficient vector borders a kernel vector);
* `residual_line` — the residual is affine in the stack scalar:
  `e_t(u₀ + γu₁) = e_t(u₀) + γ·e_t(u₁)` (multilinearity in the value column);
* hence any tuple inside a bad witness with `e_t(u₁) ≠ 0` **determines** its scalar:
  `γ = −e_t(u₀)/e_t(u₁)` — tuples are owned by at most one bad scalar.

**`badScalars_card_mul_le_ownership`** — the count: if every bad scalar owns at
least `M` tuples, then `#bad · M ≤ #tuples`.  Radius-free: this is the dimension
ladder's `#bad·12 ≤ n(n−1)(n−2)` at `k = 2` (ownership `12 = 2·3!` from the
line-split) and complements the WB pencil below UDR.  The window question becomes
an ownership-degeneracy question on the Möbius-symmetric locus.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The bordered Vandermonde matrix of a `(k+1)`-tuple: `k` power columns and the
value column at the last index. -/
def borderedMatrix (dom : Fin n ↪ F) (k : ℕ) (t : Fin (k + 1) → Fin n)
    (y : Fin n → F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
  fun a b => if (b : ℕ) < k then (dom (t a)) ^ (b : ℕ) else y (t a)

/-- The interpolation residual of a tuple. -/
noncomputable def residual (dom : Fin n ↪ F) (k : ℕ) (t : Fin (k + 1) → Fin n)
    (y : Fin n → F) : F :=
  (borderedMatrix dom k t y).det

/-- The bordered matrix is the value-column update of any other bordered matrix. -/
theorem borderedMatrix_eq_updateCol (dom : Fin n ↪ F) (k : ℕ)
    (t : Fin (k + 1) → Fin n) (y z : Fin n → F) :
    borderedMatrix dom k t y
      = (borderedMatrix dom k t z).updateCol (Fin.last k) (fun a => y (t a)) := by
  funext a b
  rw [Matrix.updateCol_apply]
  by_cases hb : b = Fin.last k
  · subst hb
    rw [if_pos rfl]
    show (if ((Fin.last k : Fin (k+1)) : ℕ) < k then _ else y (t a)) = y (t a)
    rw [if_neg (by simp [Fin.last])]
  · rw [if_neg hb]
    have hbk : (b : ℕ) < k := by
      have := b.2
      rcases Nat.lt_or_ge (b : ℕ) k with h | h
      · exact h
      · exact absurd (Fin.ext (by omega : (b : ℕ) = k)) hb
    show (if (b : ℕ) < k then (dom (t a)) ^ (b : ℕ) else y (t a))
      = (if (b : ℕ) < k then (dom (t a)) ^ (b : ℕ) else z (t a))
    rw [if_pos hbk, if_pos hbk]

/-- **Affinity of the residual in the stack scalar.** -/
theorem residual_line (dom : Fin n ↪ F) (k : ℕ) (t : Fin (k + 1) → Fin n)
    (u₀ u₁ : Fin n → F) (γ : F) :
    residual dom k t (fun i => u₀ i + γ * u₁ i)
      = residual dom k t u₀ + γ * residual dom k t u₁ := by
  unfold residual
  rw [borderedMatrix_eq_updateCol dom k t _ u₀,
    show (fun a => (fun i => u₀ i + γ * u₁ i) (t a))
      = (fun a => u₀ (t a)) + γ • (fun a => u₁ (t a)) from by
        funext a
        simp [smul_eq_mul],
    Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  congr 1
  · rw [← borderedMatrix_eq_updateCol dom k t u₀ u₀]
  · congr 1
    rw [← borderedMatrix_eq_updateCol dom k t u₁ u₀]

/-- **Vanishing on extensions**: a tuple where `y` agrees with a degree-`< k`
polynomial has zero residual (the coefficients border a kernel vector). -/
theorem residual_eq_zero_of_extends (dom : Fin n ↪ F) (k : ℕ)
    (t : Fin (k + 1) → Fin n) {y : Fin n → F} {P : F[X]} (hP : P.natDegree < k)
    (hagree : ∀ a : Fin (k + 1), y (t a) = P.eval (dom (t a))) :
    residual dom k t y = 0 := by
  -- the kernel vector (coefficients, −1)
  set v : Fin (k + 1) → F := fun b => if (b : ℕ) < k then P.coeff b else -1 with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h (Fin.last k)
    rw [hv] at this
    simp only [Fin.val_last] at this
    rw [if_neg (lt_irrefl k)] at this
    simpa using this
  have hker : (borderedMatrix dom k t y).mulVec v = 0 := by
    funext a
    show ∑ b : Fin (k + 1), borderedMatrix dom k t y a b * v b = 0
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ j : Fin k, borderedMatrix dom k t y a j.castSucc * v j.castSucc
        = P.coeff (j : ℕ) * (dom (t a)) ^ (j : ℕ) := by
      intro j
      have hjk : ((j.castSucc : Fin (k+1)) : ℕ) < k := by
        rw [Fin.val_castSucc]
        exact j.2
      rw [hv]
      show (if ((j.castSucc : Fin (k+1)) : ℕ) < k
          then (dom (t a)) ^ ((j.castSucc : Fin (k+1)) : ℕ) else y (t a))
        * (if ((j.castSucc : Fin (k+1)) : ℕ) < k
          then P.coeff ((j.castSucc : Fin (k+1)) : ℕ) else -1)
        = P.coeff (j : ℕ) * (dom (t a)) ^ (j : ℕ)
      rw [if_pos hjk, if_pos hjk, Fin.val_castSucc]
      ring
    have hlast : borderedMatrix dom k t y a (Fin.last k) * v (Fin.last k)
        = -(y (t a)) := by
      rw [hv]
      show (if ((Fin.last k : Fin (k+1)) : ℕ) < k
          then (dom (t a)) ^ ((Fin.last k : Fin (k+1)) : ℕ) else y (t a))
        * (if ((Fin.last k : Fin (k+1)) : ℕ) < k then P.coeff _ else -1) = _
      rw [Fin.val_last, if_neg (lt_irrefl k), if_neg (lt_irrefl k)]
      ring
    rw [Finset.sum_congr rfl fun j _ => hcast j, hlast, hagree a,
      eval_eq_sum_range' hP, ← Fin.sum_univ_eq_sum_range
        (fun j => P.coeff j * (dom (t a)) ^ j) k]
    show (∑ j : Fin k, P.coeff (j : ℕ) * (dom (t a)) ^ (j : ℕ))
      + -(∑ j : Fin k, P.coeff (j : ℕ) * (dom (t a)) ^ (j : ℕ)) = (0 : Fin (k+1) → F) a
    rw [add_neg_cancel]
    rfl
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩

/-- **The determination lemma**: a tuple inside a bad witness with nonvanishing
direction residual determines the scalar. -/
theorem gamma_eq_of_owned (dom : Fin n ↪ F) (k : ℕ) (t : Fin (k + 1) → Fin n)
    {u₀ u₁ : Fin n → F} {γ : F}
    (h1 : residual dom k t u₁ ≠ 0)
    (h0 : residual dom k t u₀ + γ * residual dom k t u₁ = 0) :
    γ = -(residual dom k t u₀) / residual dom k t u₁ := by
  rw [eq_div_iff h1]
  linear_combination h0

open Classical in
/-- **THE OWNERSHIP BOUND** — the radius-free count unifying the WB pencil and the
dimension ladder: if every bad scalar owns at least `M` tuples (tuples inside its
witness where the direction residual does not vanish), then `#bad · M ≤ #tuples`.
The dimension ladder's `#bad·12 ≤ n(n−1)(n−2)` is the `k = 2` instance. -/
theorem badScalars_card_mul_le_ownership (dom : Fin n ↪ F) (k : ℕ)
    (u₀ u₁ : Fin n → F) (bad : Finset F) (M : ℕ)
    (𝒯 : F → Finset (Fin (k + 1) → Fin n))
    (hprop : ∀ γ ∈ bad, ∀ t ∈ 𝒯 γ, residual dom k t u₁ ≠ 0 ∧
      residual dom k t u₀ + γ * residual dom k t u₁ = 0)
    (hM : ∀ γ ∈ bad, M ≤ (𝒯 γ).card) :
    bad.card * M ≤ Fintype.card (Fin (k + 1) → Fin n) := by
  -- disjointness: a tuple owned by two scalars forces them equal
  have hdisj : ∀ γ ∈ bad, ∀ γ' ∈ bad, γ ≠ γ' → Disjoint (𝒯 γ) (𝒯 γ') := by
    intro γ hγ γ' hγ' hne
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨h1, h0⟩ := hprop γ hγ t ht
    obtain ⟨h1', h0'⟩ := hprop γ' hγ' t ht'
    apply hne
    rw [gamma_eq_of_owned dom k t h1 h0, gamma_eq_of_owned dom k t h1' h0']
  calc bad.card * M = ∑ _γ ∈ bad, M := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ bad, (𝒯 γ).card := Finset.sum_le_sum hM
    _ = (bad.biUnion 𝒯).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin (k + 1) → Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (Fin (k + 1) → Fin n) := Finset.card_univ

open Classical in
/-- **The MCA instantiation**: every bad scalar's witness supplies its owned-tuple
set — tuples inside the witness with nonvanishing direction residual.  The two
ownership properties hold automatically (vanishing on extensions + affinity). -/
theorem mcaEvent_owned_tuples (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (δ : ℝ≥0)
    {u₀ u₁ : Fin n → F} {γ : F}
    (h : mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) :
    ∃ S : Finset (Fin n), ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
      ∀ t : Fin (k + 1) → Fin n, (∀ a, t a ∈ S) →
        residual dom k t u₁ ≠ 0 →
        residual dom k t u₀ + γ * residual dom k t u₁ = 0 := by
  obtain ⟨S, hsz, ⟨c, hc, hag⟩, -⟩ := h
  obtain ⟨P, hPdeg, rfl⟩ := hc
  refine ⟨S, hsz, fun t ht _ => ?_⟩
  have hPdeg' : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0
      simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  rw [← residual_line dom k t u₀ u₁ γ]
  refine residual_eq_zero_of_extends dom k t hPdeg' fun a => ?_
  have := hag (t a) (ht a)
  simpa [smul_eq_mul] using this.symm

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.residual_line
#print axioms ProximityGap.Ownership.residual_eq_zero_of_extends
#print axioms ProximityGap.Ownership.gamma_eq_of_owned
#print axioms ProximityGap.Ownership.badScalars_card_mul_le_ownership
#print axioms ProximityGap.Ownership.mcaEvent_owned_tuples
