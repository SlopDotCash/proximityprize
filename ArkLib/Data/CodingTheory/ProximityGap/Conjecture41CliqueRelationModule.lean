/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Round 21 (Issue #232) — the clique RELATION MODULE characterized: every dependency factors
# through the nodal polynomial, with twisted coefficient conditions

The row-side companion of Round 20's kernel theorem, completing the structural solution of
Conjecture 41's universal obstruction (the `(w+1)`-clique). Round 20 proved the *column/syndrome*
kernel of the double-block matrix `[N | γN]` contains the `(w+1)`-dimensional twisted evaluation
pencil. This file characterizes the *row* dependencies — the relation module of the clique
locators with bounded-degree polynomial coefficients:

* **`relation_eval_zero`:** if `∑_α u_α·Λ_{E_α} = 0` then every coefficient polynomial vanishes at
  its own node: `u_α(α) = 0`. (Evaluate at the node — all other locators vanish there; the
  diagonal one doesn't.)

* **`relation_factor_sum` (HEADLINE, single block):** every relation factors as
  `u_α = (X−α)·v_α` with `∑_α v_α = 0` — via the **nodal identity**
  `(X−α)·Λ_{E_α} = Λ_W` (`X_sub_mul_cliqueLocator`), so the relation collapses to
  `Λ_W · ∑ v_α = 0` and `F[X]` is a domain.

* **`relation_factor_sum_twisted` (HEADLINE, double block):** a simultaneous relation of the
  `γ`-twisted double block (`∑ u_α Λ_{E_α} = 0` AND `∑ γ_α u_α Λ_{E_α} = 0`) factors with BOTH
  `∑ v_α = 0` and `∑ γ_α v_α = 0`.

**Consequences (the rank formula, recorded honestly).** With coefficients of degree `< c` the
factorization `u_α = (X−α)v_α`, `deg v_α < c−1` is a bijection onto
`{(v_α) : ∑v = 0}` (single) resp. `{(v_α) : ∑v = 0, ∑γv = 0}` (double); counting dimensions:

  `rank N_clique = (w+1)c − w(c−1) = D`,
  `rank [N|γN]_clique = (w+1)c − (w−1)(c−1) = D + c − 1`   (`D = w + c`, distinct γ's),

hence `dim ker [N|γN] = 2D − (D+c−1) = w+1` — **exactly the Round-20 twisted evaluation pencil:
the pencil is the WHOLE kernel.** (The finrank bookkeeping of this last step is routine linear
algebra over the two characterizations; the mathematical content — both inclusions — is what this
file and Round 20 prove.) Conjecture 41 for the clique is therefore reduced, completely and
verifiably, to the **degeneracy question**: for which `p` does the explicit pencil contain a
syndrome whose Vandermonde solutions are all-nonzero — with the Round-19 transfer engine confining
the exceptional `p` to divisors of one integer determinant.
-/

open Polynomial Finset

namespace Round21Relations

variable {F : Type*} [Field F] [DecidableEq F]

/-- The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`. -/
noncomputable def cliqueLocator (W : Finset F) (α : F) : F[X] :=
  ∏ β ∈ W.erase α, (X - C β)

/-- The nodal polynomial `Λ_W = ∏_{β ∈ W} (X − β)`. -/
noncomputable def nodal (W : Finset F) : F[X] :=
  ∏ β ∈ W, (X - C β)

/-- **The nodal identity:** `(X − α)·Λ_{E_α} = Λ_W` for `α ∈ W`. -/
theorem X_sub_mul_cliqueLocator {W : Finset F} {α : F} (hα : α ∈ W) :
    (X - C α) * cliqueLocator W α = nodal W := by
  unfold cliqueLocator nodal
  exact Finset.mul_prod_erase W (fun β => X - C β) hα

omit [DecidableEq F] in
/-- The nodal polynomial is nonzero. -/
theorem nodal_ne_zero (W : Finset F) : nodal W ≠ 0 := by
  unfold nodal
  apply Finset.prod_ne_zero_iff.mpr
  intro β _
  exact Polynomial.X_sub_C_ne_zero β

/-- Locator evaluation off the diagonal vanishes. -/
theorem cliqueLocator_eval_other {W : Finset F} {α β : F} (hβ : β ∈ W) (hne : β ≠ α) :
    (cliqueLocator W α).eval β = 0 := by
  unfold cliqueLocator
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hβ⟩)
  simp

/-- Locator self-evaluation is nonzero. -/
theorem cliqueLocator_eval_self_ne_zero {W : Finset F} {α : F} :
    (cliqueLocator W α).eval α ≠ 0 := by
  unfold cliqueLocator
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro β hβ
  have hne : β ≠ α := (Finset.mem_erase.mp hβ).1
  simpa using sub_ne_zero.mpr (Ne.symm hne)

/-! ## 1. Every relation vanishes at its own node -/

/-- **`relation_eval_zero`:** a vanishing combination `∑_α u_α·Λ_{E_α} = 0` forces `u_α(α) = 0`
for every `α ∈ W` (evaluate at the node; the off-diagonal locators vanish). -/
theorem relation_eval_zero {W : Finset F} (u : F → F[X])
    (hrel : (∑ α ∈ W, u α * cliqueLocator W α) = 0) :
    ∀ α ∈ W, (u α).eval α = 0 := by
  intro α₀ hα₀
  have heval := congrArg (Polynomial.eval α₀) hrel
  rw [Polynomial.eval_finset_sum, Polynomial.eval_zero] at heval
  rw [Finset.sum_eq_single α₀] at heval
  · rw [Polynomial.eval_mul] at heval
    rcases mul_eq_zero.mp heval with h | h
    · exact h
    · exact absurd h cliqueLocator_eval_self_ne_zero
  · intro β hβ hne
    rw [Polynomial.eval_mul, cliqueLocator_eval_other hα₀ (Ne.symm hne), mul_zero]
  · intro h; exact absurd hα₀ h

/-! ## 2. The factorization and the collapsed relation -/

/-- The factored coefficient: `v_α := u_α /ₘ (X − α)` — exact division when `u_α(α) = 0`. -/
noncomputable def vCoeff (u : F → F[X]) (α : F) : F[X] := u α /ₘ (X - C α)

omit [DecidableEq F] in
/-- Exactness of the factorization: `u_α = (X−α)·v_α` when `u_α(α) = 0`. -/
theorem u_eq_X_sub_mul_vCoeff {u : F → F[X]} {α : F} (h0 : (u α).eval α = 0) :
    u α = (X - C α) * vCoeff u α := by
  unfold vCoeff
  have hdvd : (X - C α) ∣ u α := Polynomial.dvd_iff_isRoot.mpr h0
  obtain ⟨q, hq⟩ := hdvd
  rw [hq]
  congr 1
  rw [Polynomial.mul_divByMonic_cancel_left q (Polynomial.monic_X_sub_C α)]

/-- **HEADLINE (single block).** Every relation `∑ u_α·Λ_{E_α} = 0` factors through the nodal
polynomial: `u_α = (X−α)·v_α` with `∑_α v_α = 0`. (Substituting the factorization and the nodal
identity collapses the relation to `Λ_W·(∑ v_α) = 0`; `F[X]` is a domain.) -/
theorem relation_factor_sum {W : Finset F} (u : F → F[X])
    (hrel : (∑ α ∈ W, u α * cliqueLocator W α) = 0) :
    (∀ α ∈ W, u α = (X - C α) * vCoeff u α) ∧ (∑ α ∈ W, vCoeff u α) = 0 := by
  have h0 := relation_eval_zero u hrel
  have hfac : ∀ α ∈ W, u α = (X - C α) * vCoeff u α :=
    fun α hα => u_eq_X_sub_mul_vCoeff (h0 α hα)
  refine ⟨hfac, ?_⟩
  -- substitute and collapse via the nodal identity
  have hcollapse : (∑ α ∈ W, u α * cliqueLocator W α) = nodal W * ∑ α ∈ W, vCoeff u α := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    calc u α * cliqueLocator W α
        = (X - C α) * vCoeff u α * cliqueLocator W α := by rw [← hfac α hα]
      _ = (X - C α) * cliqueLocator W α * vCoeff u α := by ring
      _ = nodal W * vCoeff u α := by rw [X_sub_mul_cliqueLocator hα]
  rw [hcollapse] at hrel
  rcases mul_eq_zero.mp hrel with h | h
  · exact absurd h (nodal_ne_zero W)
  · exact h

/-- **HEADLINE (double block).** A simultaneous relation of the `γ`-twisted double block —
`∑ u_α·Λ_{E_α} = 0` AND `∑ γ_α·u_α·Λ_{E_α} = 0` — factors with BOTH collapsed conditions:
`∑ v_α = 0` and `∑ γ_α·v_α = 0`. With degree bookkeeping (`deg u < c ⟹ deg v < c−1`) this
characterizes the double-block row-dependency space as
`{((X−α)v_α) : ∑v = 0, ∑γv = 0}` — dimension `(w−1)(c−1)` for distinct twists — whence
`rank [N|γN]_clique = D + c − 1` and the Round-20 pencil is the WHOLE kernel. -/
theorem relation_factor_sum_twisted {W : Finset F} (γ : F → F) (u : F → F[X])
    (hrel : (∑ α ∈ W, u α * cliqueLocator W α) = 0)
    (hrelγ : (∑ α ∈ W, C (γ α) * u α * cliqueLocator W α) = 0) :
    (∀ α ∈ W, u α = (X - C α) * vCoeff u α) ∧
      (∑ α ∈ W, vCoeff u α) = 0 ∧ (∑ α ∈ W, C (γ α) * vCoeff u α) = 0 := by
  obtain ⟨hfac, hsum⟩ := relation_factor_sum u hrel
  refine ⟨hfac, hsum, ?_⟩
  -- collapse the twisted relation the same way
  have hcollapse : (∑ α ∈ W, C (γ α) * u α * cliqueLocator W α)
      = nodal W * ∑ α ∈ W, C (γ α) * vCoeff u α := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    rw [hfac α hα]
    have : (X - C α) * cliqueLocator W α = nodal W := X_sub_mul_cliqueLocator hα
    calc C (γ α) * ((X - C α) * vCoeff u α) * cliqueLocator W α
        = C (γ α) * vCoeff u α * ((X - C α) * cliqueLocator W α) := by ring
      _ = nodal W * (C (γ α) * vCoeff u α) := by rw [this]; ring
  rw [hcollapse] at hrelγ
  rcases mul_eq_zero.mp hrelγ with h | h
  · exact absurd h (nodal_ne_zero W)
  · exact h

/-! ## 3. Degree bookkeeping: the factorization preserves the budget -/

omit [DecidableEq F] in
/-- If `deg u_α < c` then `deg v_α < c − 1` (division by a monic linear drops the degree by one);
hence the relation module with degree-`< c` coefficients is parameterized exactly by
degree-`< c−1` tuples summing to zero (and, for the double block, `γ`-twisted-summing to zero). -/
theorem vCoeff_natDegree_lt {u : F → F[X]} {α : F} {c : ℕ} (hc : 1 ≤ c)
    (h0 : (u α).eval α = 0) (hu : (u α).natDegree < c) (hune : u α ≠ 0) :
    (vCoeff u α).natDegree < c - 1 := by
  have hfac := u_eq_X_sub_mul_vCoeff h0
  have hvne : vCoeff u α ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hune hfac
  have hdeg : (u α).natDegree = 1 + (vCoeff u α).natDegree := by
    rw [hfac, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero α) hvne,
        Polynomial.natDegree_X_sub_C]
  omega

end Round21Relations

#print axioms Round21Relations.X_sub_mul_cliqueLocator
#print axioms Round21Relations.relation_eval_zero
#print axioms Round21Relations.relation_factor_sum
#print axioms Round21Relations.relation_factor_sum_twisted
#print axioms Round21Relations.vCoeff_natDegree_lt
