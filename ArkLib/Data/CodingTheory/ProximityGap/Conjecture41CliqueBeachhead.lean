/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Round 19 (Issue #232) — the Conjecture-41 BEACHHEAD: the universal (clique) obstruction is the
# Lagrange-numerator basis, and large primes kill it

ePrint 2026/858's **Conjecture 41** ("Open-Set Rank Lemma at `c ≥ 3`") is the live prize-shaped
list conjecture: for supports `E₁,…,E_m` of size `w = D−c` and distinct `γᵢ`, the constraint
matrix `A = [N_{Eᵢ} | γᵢ·N_{Eᵢ}]` has full rank for all `p` above an effective threshold —
equivalently the worst-case list obeys `M ≤ ⌊(2D−1)/c⌋`, predicting `M = O(1)` at the Johnson
radius at deployment codimension. The paper identifies **the universal obstruction at every `c`:
the `(w+1)`-clique** — supports = all `w`-subsets of a `(w+1)`-vertex set `W` — realizable only at
small primes (their triangle `c=2, p=113` and tetrahedron `c=3, p=61` counterexamples).

This file proves the two structural ingredients any resolution must combine, and the `c = 1`
instance of the mechanism, all self-contained:

* **The clique-locator structure theorem.** For the clique on `W`, the error locators are
  `Λ_{W∖{α}} = ∏_{β ∈ W∖{α}} (X − β)` — the **Lagrange numerator family**. We prove
  (`cliqueLocator_linearIndependent`) they are linearly independent over ANY field: evaluating a
  vanishing combination at the node `α` kills the `α`-coefficient (the evaluation matrix is
  diagonal: `cliqueLocator_eval_self ≠ 0`, `cliqueLocator_eval_other = 0`).

* **Kernel triviality at `c = 1`** (`clique_syndrome_kernel_trivial`): the `(w+1)` locator
  coefficient vectors span `F^{w+1}` (independent + count = dimension), so a syndrome annihilated
  by ALL clique normals is zero — **the universal obstruction carries no `c = 1` kernel over any
  field**. This is the rank statement of Conjecture 41 for the clique configuration at `c = 1`.

* **The large-`p` transfer engine** (`det_map_zmod_ne_zero`): an integer matrix with `det ≠ 0`
  stays nonsingular mod every prime `p ∤ det` — the precise "effective Schwartz–Zippel threshold"
  mechanism by which the conjecture's small-`p` clique counterexamples (their `p = 61, 113`) die
  at large `p`: the obstruction lives exactly at the primes dividing one integer determinant.

**Honest scope.** This does NOT prove Conjecture 41: the open content is the rank of the
`γ`-twisted DOUBLE blocks `[N | γN]` at `c ≥ 3` for ARBITRARY (non-clique) support families. What
is proven here: the clique family — the conjectured universal worst case — has the exact
Lagrange-numerator structure, trivial kernel at `c = 1` over every field, and its higher-`c`
exceptional primes are confined to divisors of a single integer determinant. These are the
beachhead facts for the general attack.
-/

open Polynomial Finset

namespace Round19Clique

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The clique locators -/

/-- The error locator of the clique support `E_α = W ∖ {α}`:
`Λ_{E_α}(X) = ∏_{β ∈ W.erase α} (X − β)` — the Lagrange numerator at node `α`. -/
noncomputable def cliqueLocator (W : Finset F) (α : F) : F[X] :=
  ∏ β ∈ W.erase α, (X - C β)

/-- **Diagonal evaluation, off-diagonal:** for `α' ∈ W`, `α' ≠ α`, the locator of `E_α` vanishes
at `α'` (the factor `X − α'` is present). -/
theorem cliqueLocator_eval_other {W : Finset F} {α α' : F} (hα' : α' ∈ W) (hne : α' ≠ α) :
    (cliqueLocator W α).eval α' = 0 := by
  unfold cliqueLocator
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hα'⟩)
  simp

/-- **Diagonal evaluation, diagonal:** the locator of `E_α` does NOT vanish at its own node `α`
(all nodes distinct). -/
theorem cliqueLocator_eval_self {W : Finset F} {α : F} :
    (cliqueLocator W α).eval α = ∏ β ∈ W.erase α, (α - β) := by
  unfold cliqueLocator
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro β _
  simp

theorem cliqueLocator_eval_self_ne_zero {W : Finset F} {α : F} :
    (cliqueLocator W α).eval α ≠ 0 := by
  rw [cliqueLocator_eval_self]
  apply Finset.prod_ne_zero_iff.mpr
  intro β hβ
  have hne : β ≠ α := (Finset.mem_erase.mp hβ).1
  exact sub_ne_zero.mpr (Ne.symm hne)

/-- **The clique-locator structure theorem:** the Lagrange-numerator family
`(α : W) ↦ Λ_{W∖{α}}` is linearly independent over any field. A vanishing combination, evaluated
at the node `α₀`, reduces to `g α₀ · Λ_{E_{α₀}}(α₀) = 0` with the second factor nonzero. -/
theorem cliqueLocator_linearIndependent (W : Finset F) :
    LinearIndependent F (fun α : {x // x ∈ W} => cliqueLocator W (α : F)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg α₀
  -- evaluate the vanishing polynomial combination at the node α₀
  have heval := congrArg (Polynomial.eval (α₀ : F)) hg
  rw [Polynomial.eval_finset_sum] at heval
  simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_zero] at heval
  -- all terms except α₀ vanish
  rw [Finset.sum_eq_single α₀] at heval
  · -- g α₀ * Λ(α₀) = 0 with Λ(α₀) ≠ 0
    rcases mul_eq_zero.mp heval with h | h
    · exact h
    · exact absurd h cliqueLocator_eval_self_ne_zero
  · intro β _ hβ
    have : (β : F) ≠ (α₀ : F) := by
      intro h
      exact hβ (Subtype.ext h)
    rw [cliqueLocator_eval_other α₀.2 (Ne.symm this), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ α₀) h

/-! ## 2. Kernel triviality at `c = 1`: the clique normals annihilate only the zero syndrome -/

/-- The coefficient vector of a polynomial, truncated to `Fin N`. -/
noncomputable def coeffVec (N : ℕ) (P : F[X]) : Fin N → F := fun j => P.coeff (j : ℕ)

/-- The clique locator has `natDegree = |W| − 1` (product of `|W|−1` monic linears). -/
theorem cliqueLocator_natDegree {W : Finset F} {α : F} (hα : α ∈ W) :
    (cliqueLocator W α).natDegree = W.card - 1 := by
  unfold cliqueLocator
  rw [Polynomial.natDegree_prod]
  · rw [Finset.sum_congr rfl (fun β _ => Polynomial.natDegree_X_sub_C β), Finset.sum_const,
        smul_eq_mul, mul_one, Finset.card_erase_of_mem hα]
  · intro β _
    exact Polynomial.X_sub_C_ne_zero β

/-- Coefficient vectors of the clique locators are linearly independent in `F^{|W|}`
(coefficient extraction is injective on degree `< |W|`). -/
theorem coeffVec_linearIndependent (W : Finset F) (hW : W.Nonempty) :
    LinearIndependent F (fun α : {x // x ∈ W} => coeffVec W.card (cliqueLocator W (α : F))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- transfer the vanishing coefficient-vector relation back to polynomials
  have hpoly : (∑ α : {x // x ∈ W}, g α • cliqueLocator W (α : F)) = 0 := by
    apply Polynomial.ext
    intro j
    by_cases hj : j < W.card
    · have := congrFun hg ⟨j, hj⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
      rw [Polynomial.finset_sum_coeff]
      simp only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero]
      simpa [coeffVec] using this
    · -- coefficients above the degree all vanish
      rw [Polynomial.finset_sum_coeff, Polynomial.coeff_zero]
      apply Finset.sum_eq_zero
      intro α _
      rw [Polynomial.coeff_smul]
      have hdeg : (cliqueLocator W (α : F)).natDegree < j := by
        have hcard : 1 ≤ W.card := Finset.card_pos.mpr hW
        rw [cliqueLocator_natDegree α.2]
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, smul_zero]
  have hind := cliqueLocator_linearIndependent W
  rw [Fintype.linearIndependent_iff] at hind
  exact hind g hpoly

/-- **Kernel triviality at `c = 1` (the clique rank statement).** If a syndrome
`s : Fin |W| → F` is annihilated by every clique normal — `∑ⱼ Λ_{E_α}.coeff j · s j = 0` for all
`α ∈ W` — then `s = 0`. The `|W|` independent coefficient vectors span `F^{|W|}`
(count = dimension), so the annihilator functional vanishes identically. **The universal
obstruction configuration carries no `c = 1` kernel over ANY field.** -/
theorem clique_syndrome_kernel_trivial (W : Finset F) (hW : W.Nonempty) (s : Fin W.card → F)
    (hs : ∀ α ∈ W, (∑ j : Fin W.card, (cliqueLocator W α).coeff (j : ℕ) * s j) = 0) :
    s = 0 := by
  classical
  -- the annihilator functional φ(v) = ∑ v j * s j
  let φ : (Fin W.card → F) →ₗ[F] F :=
    { toFun := fun v => ∑ j, v j * s j
      map_add' := by intro u v; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c v; simp [Finset.mul_sum, mul_assoc] }
  -- φ vanishes on the spanning family of coefficient vectors
  have hφ : ∀ α : {x // x ∈ W}, φ (coeffVec W.card (cliqueLocator W (α : F))) = 0 := by
    intro α
    exact hs (α : F) α.2
  -- the family spans F^{|W|}: independent + card = finrank
  haveI : Nonempty {x // x ∈ W} := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have hcardeq : Fintype.card {x // x ∈ W} = Module.finrank F (Fin W.card → F) := by
    rw [Fintype.card_coe, Module.finrank_pi, Fintype.card_fin]
  have hspan : Submodule.span F
      (Set.range (fun α : {x // x ∈ W} => coeffVec W.card (cliqueLocator W (α : F)))) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank
      (coeffVec_linearIndependent W hW) hcardeq
  -- hence φ = 0, so s j = φ(e_j) = 0
  have hφzero : φ = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ Submodule.span F
        (Set.range (fun α : {x // x ∈ W} => coeffVec W.card (cliqueLocator W (α : F)))) := by
      rw [hspan]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨α, rfl⟩ := hx
        exact hφ α
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [map_smul, hx]
  funext j
  have := congrArg (fun ψ : (Fin W.card → F) →ₗ[F] F => ψ (Pi.single j (1 : F))) hφzero
  simp only [LinearMap.zero_apply] at this
  have hsingle : φ (Pi.single j (1 : F)) = s j := by
    show (∑ j' : Fin W.card, (Pi.single j (1 : F) : Fin W.card → F) j' * s j') = s j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hsingle] at this
  exact this

/-! ## 3. The large-`p` transfer engine -/

/-- **The effective Schwartz–Zippel threshold mechanism.** An integer matrix with `det ≠ 0` stays
nonsingular modulo every prime not dividing its determinant: the exceptional primes of any
rank-deficiency obstruction (the conjecture's clique counterexamples at `p = 61, 113`) are
confined to the divisors of ONE integer determinant. -/
theorem det_map_zmod_ne_zero {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (hdet : ¬ (p : ℤ) ∣ M.det) :
    (M.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
  intro h
  apply hdet
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap := RingHom.map_det (Int.castRingHom (ZMod p)) M
  rw [RingHom.mapMatrix_apply] at hmap
  have hcoe : M.map (Int.cast : ℤ → ZMod p) = M.map (⇑(Int.castRingHom (ZMod p))) := rfl
  rw [hcoe, ← hmap] at h
  exact_mod_cast h

end Round19Clique

#print axioms Round19Clique.cliqueLocator_eval_other
#print axioms Round19Clique.cliqueLocator_eval_self_ne_zero
#print axioms Round19Clique.cliqueLocator_linearIndependent
#print axioms Round19Clique.coeffVec_linearIndependent
#print axioms Round19Clique.clique_syndrome_kernel_trivial
#print axioms Round19Clique.det_map_zmod_ne_zero
