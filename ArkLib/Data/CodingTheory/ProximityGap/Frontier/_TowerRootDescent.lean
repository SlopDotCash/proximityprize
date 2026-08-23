/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DyadicTowerDescent

/-!
# Root-count descent for the antipodal tower (#407 / #444)

`_AntipodalDyadicSymmetric` + `_DyadicTowerDescent` gave the *polynomial* self-similarity of the
off-BGK list route: the antipodal-tower polynomial is `Q.comp (X^{2^s})`. The **list size** of the
off-BGK route, however, is governed by *root counts* (number of close codewords / agreement points),
not coefficients. This file lands the missing concrete link — the **root-count descent** that turns
the polynomial self-similarity into c.97's list recursion `L(μ_n, k, t) = L(μ_{n/2}, ⌊k/2⌋, ⌈t/2⌉)`:

* `eval_comp_X_pow` / `isRoot_comp_X_pow_iff`: `α` is a root of `Q.comp (X^m)` **iff** `α^m` is a
  root of `Q`. So the root set of the tower polynomial is the `m`-th-power *preimage* of the root set
  of the base.
* `rootCount_comp_X_pow`: over any finite evaluation set `G`, the count of tower-polynomial roots in
  `G` equals the count of base-roots-at-`m`-th-powers in `G`.
* `rootCount_descent_of_uniform_fiber`: when the `m`-th-power map is **uniformly `k`-to-1** from `G`
  onto a target set `H` carrying the base roots (the situation for the `2^s`-power map on the
  `2`-power subgroup `μ_{2^μ}`, where `α ↦ α^{2^s}` is `2^s`-to-1 onto `μ_{2^{μ−s}}`), the tower root
  count is exactly `k ·` the base root count — the list descends by the fiber factor, **constant in
  `n` at fixed dyadic ratio** and **prime-independent**.

**Honest scope.** This is the prime-independent root-count *mechanism* of the off-BGK list recursion
(PROVEN). It is NOT a closure: that the antipodal-tower family realizes the *worst-case* list, and the
base-count bound itself (the list **upper bound** = symmetric-function constraints cutting
independently, #444 c.97), remain the open core, untouched here. Axiom-clean. Issues #407, #444.
-/

open Polynomial

namespace ProximityGap.Frontier.TowerRootDescent

open scoped Classical

variable {R : Type*} [CommSemiring R]

/-- Evaluating `Q.comp (X^m)` at `α` is evaluating `Q` at `α^m`. -/
theorem eval_comp_X_pow (Q : R[X]) (m : ℕ) (α : R) :
    (Q.comp (X ^ m)).eval α = Q.eval (α ^ m) := by
  rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]

/-- `α` is a root of the tower polynomial `Q.comp (X^m)` iff `α^m` is a root of the base `Q`. The
root set of the tower is the `m`-th-power preimage of the base root set. -/
theorem isRoot_comp_X_pow_iff (Q : R[X]) (m : ℕ) (α : R) :
    (Q.comp (X ^ m)).IsRoot α ↔ Q.IsRoot (α ^ m) := by
  simp only [Polynomial.IsRoot.def, eval_comp_X_pow]

/-- **Root-count equality.** Over any finite evaluation set `G`, the number of roots of the tower
polynomial `Q.comp (X^m)` in `G` equals the number of `α ∈ G` whose `m`-th power is a base root. -/
theorem rootCount_comp_X_pow (Q : R[X]) (m : ℕ) (G : Finset R) :
    (G.filter (fun α => (Q.comp (X ^ m)).IsRoot α)).card
      = (G.filter (fun α => Q.IsRoot (α ^ m))).card := by
  congr 1
  ext α
  simp only [Finset.mem_filter, isRoot_comp_X_pow_iff]

/-- **Root-count descent (uniform fibers).** Suppose the `m`-th-power map sends `G` into `H`
(`hmap`), every base root encountered lies in `H` via a point of `G` (so filtering by `α^m ∈ roots`
factors through `H`), and the map `α ↦ α^m` is **uniformly `k`-to-1** from `G` onto each relevant
`β ∈ H` (`hfib`). Then the tower root count in `G` is `k ·` the base root count in `H`.

This is the abstract form of the `2^s`-power map on `μ_{2^μ}` (`k = 2^s`, `H = μ_{2^{μ−s}}`): the
list descends by exactly the fiber factor, prime-independently and constant in `n` at fixed dyadic
ratio. -/
theorem rootCount_descent_of_uniform_fiber (Q : R[X]) (m : ℕ) (G H : Finset R) (k : ℕ)
    (hmap : ∀ α ∈ G, α ^ m ∈ H)
    (hfib : ∀ β ∈ H, (G.filter (fun α => α ^ m = β)).card = k) :
    (G.filter (fun α => (Q.comp (X ^ m)).IsRoot α)).card
      = k * (H.filter (fun β => Q.IsRoot β)).card := by
  rw [rootCount_comp_X_pow]
  have hmem : ∀ α ∈ G.filter (fun α => Q.IsRoot (α ^ m)),
      α ^ m ∈ H.filter (fun β => Q.IsRoot β) := by
    intro α hα
    simp only [Finset.mem_filter] at hα ⊢
    exact ⟨hmap α hα.1, hα.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  have hterm : ∀ β ∈ H.filter (fun β => Q.IsRoot β),
      ((G.filter (fun α => Q.IsRoot (α ^ m))).filter (fun α => α ^ m = β)).card = k := by
    intro β hβ
    simp only [Finset.mem_filter] at hβ
    have hsub : (G.filter (fun α => Q.IsRoot (α ^ m))).filter (fun α => α ^ m = β)
        = G.filter (fun α => α ^ m = β) := by
      ext α
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hG, _⟩, h2⟩; exact ⟨hG, h2⟩
      · rintro ⟨hG, h2⟩; exact ⟨⟨hG, by rw [h2]; exact hβ.2⟩, h2⟩
    rw [hsub, hfib β hβ.1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]

end ProximityGap.Frontier.TowerRootDescent

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.TowerRootDescent.eval_comp_X_pow
#print axioms ProximityGap.Frontier.TowerRootDescent.isRoot_comp_X_pow_iff
#print axioms ProximityGap.Frontier.TowerRootDescent.rootCount_comp_X_pow
#print axioms ProximityGap.Frontier.TowerRootDescent.rootCount_descent_of_uniform_fiber
