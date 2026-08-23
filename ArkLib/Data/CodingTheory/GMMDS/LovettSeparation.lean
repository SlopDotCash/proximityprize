/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Lovett's GM-MDS proof: the substitution-separation engine (#389)

The closing contradiction and Lemmas 2.5/2.6 of arXiv:1803.02523 all turn on one mechanism:
every member of the reduced family `P(k,V')` is divisible by `(x − aₙ)`, while the separated
polynomial `p = ∏_{j<n}(x − aⱼ)` is not.  Substituting `x = aₙ` (the ring hom `eval aₙ`, which
is `R`-linear on the module `R[X]`) kills the whole span of `P(k,V')` but not `p`.

Over a *domain* this gives genuine linear independence of the inserted family — not merely
`p ∉ span`.  (Over a non-domain, or with only `p ∉ span`, independence can fail: over `ℤ`,
`{2,3}` is dependent yet `3 ∉ span{2}`.  The `eval`-annihilation is the essential extra input.)

Stated generally over `R[X]` with `R` a commutative ring (domain where needed) and `eval c`
the substitution.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

universe u

variable {R : Type*} [CommRing R] {ι : Type u}

/-- `eval c` annihilates the entire span of polynomials it annihilates (it is `R`-linear). -/
theorem eval_eq_zero_of_mem_span {g : ι → R[X]} {c : R}
    (hg : ∀ i, eval c (g i) = 0) {p : R[X]} (hp : p ∈ Submodule.span R (Set.range g)) :
    eval c p = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hg i
  | zero => exact eval_zero
  | add x y _ _ hx hy => rw [eval_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_C_mul, eval_mul, eval_C, hx, mul_zero]

/-- **Substitution separation.**  If every member of `g` vanishes under `eval c` but `p` does
not, then `p` lies outside the span of `g`. -/
theorem not_mem_span_of_eval_ne_zero {g : ι → R[X]} {c : R}
    (hg : ∀ i, eval c (g i) = 0) {p : R[X]} (hp : eval c p ≠ 0) :
    p ∉ Submodule.span R (Set.range g) :=
  fun hmem => hp (eval_eq_zero_of_mem_span hg hmem)

/-- `(X − C c) ∣ q` gives `eval c q = 0` (root form). -/
theorem eval_eq_zero_of_dvd {c : R} {q : R[X]} (h : (X - C c) ∣ q) : eval c q = 0 :=
  (dvd_iff_isRoot).mp h

/-- **Insert separation (`Option` form), over a domain.**  A linearly independent `g` whose
every member vanishes at `c`, extended by a `p` not vanishing at `c`, stays linearly
independent.  This is the inductive payoff at every leaf of Lovett's proof. -/
theorem linearIndependent_option_of_eval [IsDomain R]
    {g : ι → R[X]} (hgi : LinearIndependent R g) {c : R} {p : R[X]}
    (hg : ∀ i, eval c (g i) = 0) (hp : eval c p ≠ 0) :
    LinearIndependent R (fun o : Option ι => o.elim p g) := by
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, eval_zero])
  have hequiv : (fun o : Option ι => o.elim p g)
      = (Sum.elim g (fun _ : PUnit.{u + 1} => p)) ∘ (Equiv.optionEquivSumPUnit.{u} ι) := by
    funext o; cases o <;> rfl
  rw [hequiv, linearIndependent_equiv, linearIndependent_sum]
  refine ⟨hgi, ?_, ?_⟩
  · rw [linearIndependent_unique_iff]; exact hp0
  · rw [Submodule.disjoint_def]
    intro y hy1 hy2
    simp only [Function.comp_def, Sum.elim_inl] at hy1
    simp only [Function.comp_def, Sum.elim_inr, Set.range_const] at hy2
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy2
    have hev : eval c (r • p) = 0 := eval_eq_zero_of_mem_span hg hy1
    rw [smul_eq_C_mul, eval_mul, eval_C] at hev
    rcases mul_eq_zero.mp hev with hr0 | hcp
    · rw [hr0]; simp
    · exact absurd hcp hp

/-- Divisibility wrapper: `(X − C c)` divides every `g i` but not `p`. -/
theorem linearIndependent_option_of_dvd [IsDomain R]
    {g : ι → R[X]} (hgi : LinearIndependent R g) {c : R} {p : R[X]}
    (hg : ∀ i, (X - C c) ∣ g i) (hp : ¬ (X - C c) ∣ p) :
    LinearIndependent R (fun o : Option ι => o.elim p g) :=
  linearIndependent_option_of_eval hgi (fun i => eval_eq_zero_of_dvd (hg i))
    (fun h => hp (dvd_iff_isRoot.mpr h))

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.not_mem_span_of_eval_ne_zero
#print axioms ArkLib.GMMDS.linearIndependent_option_of_dvd
