/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Finset.Basic

/-!
# Exact scope of the antipodal-tower off-BGK route: even/odd agreement polynomials (#407 / #444)

The off-BGK list route (`_AntipodalDyadicSymmetric`, `_TowerRootDescent`, `_TwoPowerRootDescent`)
descends the list count through the squaring map `e_{2ℓ}(±z)=(−1)^ℓ e_ℓ(z²)`, which only applies when
the agreement root set is **antipodally closed** (`z ∈ S ⟺ −z ∈ S`). #444 c.11:30 made the precise
honest scope explicit: the tower captures exactly the **symmetric sub-family** (a *lower* bound on the
worst-case list), and the general non-symmetric worst case (e.g. the consecutive lacunary word
`x^a+x^{a−1}` at `ρ<¼`, whose list codewords have non-symmetric agreement sets) escapes it and remains
the BGK core. This file pins the *exact* trigger:

> the agreement set (root set of the agreement polynomial `P`) is antipodally closed **iff** `P` is
> even or odd, i.e. `P(−X) = P` or `P(−X) = −P`.

So the antipodal tower applies precisely to **even/odd** agreement polynomials. The `ρ=¼` worst word
`x^a+x^b` with `a,b` both odd is an *odd* polynomial (`u(−X)=−u`) — symmetric, tower applies fully
(c.11:30: 7/7 agreement sets symmetric). The mixed-parity consecutive word is neither even nor odd —
its root set need not be antipodally closed, so the tower gives only a lower bound there.

**Honest scope.** This is a clean char-free algebraic characterization (PROVEN) of *when* the off-BGK
descent applies; it does NOT close the prize — the non-symmetric worst case (general `P`) is exactly
the open BGK core, as #444 c.11:30 documents. Axiom-clean. Issues #407, #444.
-/

open Polynomial

namespace ProximityGap.Frontier.AntipodalAgreementScope

variable {R : Type*} [CommRing R]

/-- Evaluating `P ∘ (−X)` at `z` is evaluating `P` at `−z`. -/
theorem eval_comp_neg_X (P : R[X]) (z : R) :
    (P.comp (-X)).eval z = P.eval (-z) := by
  rw [Polynomial.eval_comp]
  congr 1
  simp

/-- **Even polynomials have negation-symmetric values.** If `P(−X) = P` then `P(−z) = P(z)`. -/
theorem eval_neg_eq_of_even {P : R[X]} (hP : P.comp (-X) = P) (z : R) :
    P.eval (-z) = P.eval z := by
  rw [← eval_comp_neg_X P z, hP]

/-- **Odd polynomials negate their values.** If `P(−X) = −P` then `P(−z) = −P(z)`. -/
theorem eval_neg_eq_neg_of_odd {P : R[X]} (hP : P.comp (-X) = -P) (z : R) :
    P.eval (-z) = -P.eval z := by
  rw [← eval_comp_neg_X P z, hP, Polynomial.eval_neg]

/-- **Even ⟹ antipodally-closed root set.** If `P` is even, `z` is a root iff `−z` is. -/
theorem isRoot_neg_iff_of_even {P : R[X]} (hP : P.comp (-X) = P) (z : R) :
    P.IsRoot (-z) ↔ P.IsRoot z := by
  unfold Polynomial.IsRoot
  rw [eval_neg_eq_of_even hP]

/-- **Odd ⟹ antipodally-closed root set.** If `P` is odd, `z` is a root iff `−z` is. -/
theorem isRoot_neg_iff_of_odd {P : R[X]} (hP : P.comp (-X) = -P) (z : R) :
    P.IsRoot (-z) ↔ P.IsRoot z := by
  unfold Polynomial.IsRoot
  rw [eval_neg_eq_neg_of_odd hP, neg_eq_zero]

/-- **The off-BGK tower's trigger (combined).** If the agreement polynomial `P` is even OR odd, then
its root set is antipodally closed (`z` root `⟺ −z` root) — exactly the condition under which the
antipodal squaring recursion `e_{2ℓ}(±z)=(−1)^ℓ e_ℓ(z²)` applies. (#444 c.11:30: this is the
symmetric sub-family the tower captures; the non-symmetric case is the open BGK core.) -/
theorem isRoot_neg_iff_of_even_or_odd {P : R[X]}
    (hP : P.comp (-X) = P ∨ P.comp (-X) = -P) (z : R) :
    P.IsRoot (-z) ↔ P.IsRoot z := by
  rcases hP with h | h
  · exact isRoot_neg_iff_of_even h z
  · exact isRoot_neg_iff_of_odd h z

/-- **Finset form.** On any negation-closed evaluation set `G` (`g ∈ G ⟹ −g ∈ G`), the root set of an
even/odd polynomial is itself negation-closed — so the antipodal-tower root-count descent
(`_TwoPowerRootDescent`) applies to it. -/
theorem rootSet_neg_closed_of_even_or_odd {P : R[X]}
    (hP : P.comp (-X) = P ∨ P.comp (-X) = -P) {G : Finset R}
    (hG : ∀ g ∈ G, -g ∈ G) {z : R} (hz : z ∈ G) (hroot : P.IsRoot z) :
    (-z) ∈ G ∧ P.IsRoot (-z) :=
  ⟨hG z hz, (isRoot_neg_iff_of_even_or_odd hP z).mpr hroot⟩

/-- **The two-monomial worst word `x^a + x^b` is odd when `a, b` are both odd** (so the `ρ=¼` worst
word is in the tower's symmetric scope, #444 c.11:30). Here `P = X^a + X^b`. -/
theorem twoMonomial_odd_of_both_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    (X ^ a + X ^ b : R[X]).comp (-X) = -(X ^ a + X ^ b) := by
  rw [Polynomial.add_comp, Polynomial.pow_comp, Polynomial.pow_comp, Polynomial.X_comp]
  rw [ha.neg_pow, hb.neg_pow]
  ring

end ProximityGap.Frontier.AntipodalAgreementScope

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AntipodalAgreementScope.isRoot_neg_iff_of_even_or_odd
#print axioms ProximityGap.Frontier.AntipodalAgreementScope.rootSet_neg_closed_of_even_or_odd
#print axioms ProximityGap.Frontier.AntipodalAgreementScope.twoMonomial_odd_of_both_odd
