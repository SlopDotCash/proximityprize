/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import ArkLib.Data.CodingTheory.ProximityGap.StepanovPointCountEngine

/-!
# Frobenius reduction and the Stepanov non-vanishing wall (Issue #232, Stepanov route)

The Stepanov method bounds `#V` (the `𝔽_q`-rational points) by an auxiliary `Ψ` with
`#V · M ≤ deg Ψ`. The `√q` saving appears only when `deg Ψ` is taken as the degree of `Ψ`
**reduced modulo the Frobenius relation** `x^q = x` (so the effective degree is `< q`, not the
naive monomial degree). The genuine wall — identified by the architecture recon — is then:

> the reduced auxiliary must be **nonzero as a function on `𝔽_q`**; a nonzero *polynomial* can
> become the zero *function* after `x^q ≡ x` reduction.

This file makes that wall **concrete and checkable**: it introduces the reduction
`reduceFrob Ψ := Ψ %ₘ (X^q − X)` and proves

* `eval_reduceFrob` — `reduceFrob Ψ` agrees with `Ψ` at every point of `𝔽_q`
  (because `X^q − X` vanishes on `𝔽_q`, `FiniteField.pow_card`);
* `natDegree_reduceFrob_lt` — `reduceFrob Ψ` has degree `< q` (it is a remainder mod a degree-`q`
  monic), so it lies in the regime where "few roots ⟹ zero" applies;
* `vanishesOn_iff_reduceFrob_eq_zero` — **the wall, reformulated**: `Ψ` vanishes on *all* of `𝔽_q`
  iff `reduceFrob Ψ = 0`. Hence `Ψ` is a *nonzero function on `𝔽_q`* iff `reduceFrob Ψ ≠ 0` — a
  decidable polynomial condition replacing the analytic non-vanishing statement;
* `exists_eval_ne_zero_of_reduceFrob_ne_zero` — the usable contrapositive.

The genuinely-provable half (a nonzero polynomial of degree `< q` cannot vanish on all `q` points,
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`) is discharged here. What remains open is
purely the **construction-side residual**: proving that the *specific* Stepanov auxiliary's reduction
is nonzero (the "leading-term survives the `x^q`-reduction" argument) and that its multiplicity at
the rational points is preserved under reduction. Those depend on the (unbuilt) special-form
construction and are exactly the open core; this file does not claim them.

## Honest scope
Infrastructure + cartography for the Stepanov route to the Weil bound (`advancesOpenCore = false`).
No `√q`-strength bound is proven; #232 stays an open tracker. All `sorry`-free, axiom-clean.
-/

open Polynomial Finset

namespace ArkLib.CodingTheory.StepanovFrobenius

variable {F : Type*} [Field F] [Fintype F]

/-- The Frobenius reduction of `Ψ`: its remainder modulo `X^q − X` (`q = |F|`). It agrees with `Ψ`
on `𝔽_q` and has degree `< q`. -/
noncomputable def reduceFrob (Ψ : F[X]) : F[X] := Ψ %ₘ (X ^ Fintype.card F - X)

/-- `X^q − X` vanishes at every point of `𝔽_q` (`FiniteField.pow_card`). -/
private lemma eval_X_pow_card_sub_X (a : F) : (X ^ Fintype.card F - X : F[X]).eval a = 0 := by
  rw [eval_sub, eval_pow, eval_X, sub_eq_zero]
  exact FiniteField.pow_card a

/-- **The Frobenius reduction agrees with `Ψ` on `𝔽_q`.** -/
theorem eval_reduceFrob (Ψ : F[X]) (a : F) : (reduceFrob Ψ).eval a = Ψ.eval a := by
  have key := modByMonic_add_div Ψ (X ^ Fintype.card F - X : F[X])
  have hcongr := congrArg (Polynomial.eval a) key
  simp only [eval_add, eval_mul, eval_X_pow_card_sub_X, zero_mul, add_zero] at hcongr
  exact hcongr

/-- **The Frobenius reduction has degree `< q`** — it is a remainder modulo the degree-`q` monic
`X^q − X`. (`q = |F| ≥ 2`, so the bound also covers the zero polynomial.) -/
theorem natDegree_reduceFrob_lt (Ψ : F[X]) : (reduceFrob Ψ).natDegree < Fintype.card F := by
  have hcard : (1 : ℕ) < Fintype.card F := Fintype.one_lt_card
  have hmonic : (X ^ Fintype.card F - X : F[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hcard)
  have hne : (X ^ Fintype.card F - X : F[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero F hcard
  have hdeg_eq : (X ^ Fintype.card F - X : F[X]).degree = (Fintype.card F : WithBot ℕ) := by
    rw [degree_eq_natDegree hne, FiniteField.X_pow_card_sub_X_natDegree_eq F hcard]
  by_cases hr : reduceFrob Ψ = 0
  · rw [hr, natDegree_zero]; omega
  · have hd : (reduceFrob Ψ).degree < (Fintype.card F : WithBot ℕ) := by
      have h := degree_modByMonic_lt Ψ hmonic
      rwa [hdeg_eq] at h
    exact (Polynomial.natDegree_lt_iff_degree_lt hr).mpr hd

/-- **The wall, reformulated as a polynomial condition.** `Ψ` vanishes at *every* point of `𝔽_q`
iff its Frobenius reduction is the zero polynomial. Consequently `Ψ` is a nonzero *function* on
`𝔽_q` iff `reduceFrob Ψ ≠ 0` — replacing the analytic non-vanishing statement that is the Stepanov
wall by a decidable algebraic one. -/
theorem vanishesOn_iff_reduceFrob_eq_zero (Ψ : F[X]) :
    (∀ a : F, Ψ.eval a = 0) ↔ reduceFrob Ψ = 0 := by
  constructor
  · intro h
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (reduceFrob Ψ)
      (f := (id : F → F)) Function.injective_id (fun a => ?_) (natDegree_reduceFrob_lt Ψ)
    rw [id, eval_reduceFrob]; exact h a
  · intro h a
    rw [← eval_reduceFrob Ψ a, h, eval_zero]

/-- **Usable non-vanishing criterion.** If the Frobenius reduction of `Ψ` is nonzero, then `Ψ` does
not vanish identically on `𝔽_q`: there is a point where it is nonzero. This is the contrapositive
form fed to the Stepanov counting argument (the reduced auxiliary genuinely separates the points). -/
theorem exists_eval_ne_zero_of_reduceFrob_ne_zero {Ψ : F[X]} (h : reduceFrob Ψ ≠ 0) :
    ∃ a : F, Ψ.eval a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h ((vanishesOn_iff_reduceFrob_eq_zero Ψ).mp hcon)

/-! ## The √q-shape point bound from a reduced Stepanov auxiliary. -/

section PointBound

variable [DecidableEq F]

open ArkLib.CodingTheory.Round6Stepanov

/-- **The Stepanov √q-shape point bound, via the Frobenius-reduced auxiliary.** If the reduced
auxiliary `reduceFrob Ψ` is nonzero and vanishes to multiplicity `≥ M` at every point of a candidate
set `V ⊆ 𝔽_q`, then `|V| · M < q`. Since `deg (reduceFrob Ψ) < q`, the counting engine yields the
crucial *strict* bound by `q` (not the naive monomial degree) — this is precisely the form that
turns `M ≈ √q` into `|V| ≲ √q`.

The hypotheses are intrinsic to the (reduced) auxiliary — `reduceFrob Ψ ≠ 0` and a multiplicity
lower bound — and do **not** assume anything about `|V|`, so this is an honest reduction, not a
restatement of the conclusion. The open residual is the *construction*: producing a `Ψ` whose
reduction is nonzero with multiplicity `M ≈ √q` at *all* `𝔽_q`-rational points of the relevant
curve. That is the Stepanov wall this development isolates but does not cross. -/
theorem stepanov_point_bound_via_reduceFrob {Ψ : F[X]} (hΨ : reduceFrob Ψ ≠ 0)
    (V : Finset F) (M : ℕ)
    (hmult : ∀ a ∈ V, M ≤ (reduceFrob Ψ).rootMultiplicity a) :
    V.card * M < Fintype.card F :=
  lt_of_le_of_lt
    (stepanov_card_mul_mult_le_natDegree hΨ V M hmult)
    (natDegree_reduceFrob_lt Ψ)

end PointBound

end ArkLib.CodingTheory.StepanovFrobenius

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.CodingTheory.StepanovFrobenius
#print axioms eval_reduceFrob
#print axioms natDegree_reduceFrob_lt
#print axioms vanishesOn_iff_reduceFrob_eq_zero
#print axioms exists_eval_ne_zero_of_reduceFrob_ne_zero
#print axioms stepanov_point_bound_via_reduceFrob
end AxiomAudit
