/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Round 27 (Issue #232) — THE SUNFLOWER-CORE REDUCTION: shared vertices divide out, window intact

The non-disjoint half of Step 2's assembly (O50 item (ii)), reducing arbitrary equal-window
families to the DISJOINT case handled by Rounds 25–26. The key is the **degree-of-difference
formulation** of window agreement — `(P₁ − P₂).degree < d` ⟺ the top coefficients agree down
to degree `d` — under which the reduction is three lines:

* **`cofactor_window` (the engine):** in a domain, if `Q ≠ 0` and the products `Q·R₁, Q·R₂` agree
  in their top window (`(Q·R₁ − Q·R₂).degree < d`), then the cofactors agree in the
  correspondingly shifted window: `(R₁ − R₂).degree < d − deg Q`. Proof: `Q·R₁ − Q·R₂ = Q·(R₁−R₂)`
  and `degree_mul` — the common factor's degree subtracts off exactly.

* **`nodal_core_split`:** `Λ_A = Λ_{A∩B} · Λ_{A∖B}` (the shared core factors out of the nodal
  polynomial), and `A∖B`, `B∖A` are disjoint.

* **`sunflower_core_reduction` (the assembled theorem):** if `Λ_A` and `Λ_B` agree in their top
  window, then the residual nodals `Λ_{A∖B}` and `Λ_{B∖A}` — of DISJOINT sets — agree in the
  same-width window (shifted by the common core's degree). The residual sets then feed the
  verified disjoint machinery: R25 (`t=1` ⟹ antipodally closed) + R26 (window halving) ⟹ the
  `2^k`-lift structure on the residuals — the SUNFLOWER form: common core + lift-structured
  petals, generalizing R24's `w=3` classification to all sizes and all windows.

With this, Step 2's reduction chain is complete over verified components: arbitrary equal-window
pair → core division (this file) → disjoint residuals → antipodal closure (R25) → window halving
(R26, iterated) → `2^k`-lift petals (R22 floor = ceiling). Remaining assembly: the level-iteration
statement and the final Conjecture-41/δ* composition.
-/

open Polynomial Finset

namespace Round27Core

variable {F : Type*} [Field F] [DecidableEq F]

/-- The nodal polynomial of a finset. -/
noncomputable def nodal (A : Finset F) : F[X] := ∏ a ∈ A, (X - C a)

omit [DecidableEq F] in
theorem nodal_ne_zero (A : Finset F) : nodal A ≠ 0 := by
  unfold nodal
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  exact X_sub_C_ne_zero a

/-! ## 1. The cofactor-window engine -/

omit [DecidableEq F] in
/-- **The cofactor-window engine.** In a domain, top-window agreement of products with a common
nonzero factor passes to the cofactors, with the window shifted by the factor's degree:
`(Q·R₁ − Q·R₂).degree < d  ⟹  (R₁ − R₂).degree < d − deg Q`
(in `WithBot ℕ` arithmetic: `degree Q + degree (R₁ − R₂) < d`). -/
theorem cofactor_window {Q R₁ R₂ : F[X]} {d : WithBot ℕ}
    (h : (Q * R₁ - Q * R₂).degree < d) :
    Q.degree + (R₁ - R₂).degree < d := by
  have hfac : Q * R₁ - Q * R₂ = Q * (R₁ - R₂) := by ring
  rw [hfac] at h
  rwa [Polynomial.degree_mul] at h

/-! ## 2. The core splits off the nodal polynomial -/

/-- **The core split:** `Λ_A = Λ_{A∩B} · Λ_{A∖B}`. -/
theorem nodal_core_split (A B : Finset F) :
    nodal A = nodal (A ∩ B) * nodal (A \ B) := by
  unfold nodal
  exact (Finset.prod_inter_mul_prod_diff A B _).symm

omit [Field F] in
/-- The residual sets are disjoint. -/
theorem residual_disjoint (A B : Finset F) : Disjoint (A \ B) (B \ A) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1

/-! ## 3. The assembled reduction -/

/-- **THE SUNFLOWER-CORE REDUCTION.** If the nodal polynomials of `A` and `B` agree in their top
window (`(Λ_A − Λ_B).degree < d`), then the residual nodals of the DISJOINT sets `A∖B` and `B∖A`
agree in the core-shifted window:

  `degree Λ_{A∩B} + (Λ_{A∖B} − Λ_{B∖A}).degree < d`.

The residual (disjoint) pair then feeds the verified disjoint-case machinery (R25 antipodal
closure + R26 window halving), forcing the sunflower form: common core `A∩B` plus `2^k`-lift
petals. Note `B ∩ A = A ∩ B` (`inter_comm`) aligns the two core factors. -/
theorem sunflower_core_reduction (A B : Finset F) {d : WithBot ℕ}
    (h : (nodal A - nodal B).degree < d) :
    Disjoint (A \ B) (B \ A) ∧
      (nodal (A ∩ B)).degree + (nodal (A \ B) - nodal (B \ A)).degree < d := by
  refine ⟨residual_disjoint A B, ?_⟩
  have hA := nodal_core_split A B
  have hB := nodal_core_split B A
  rw [Finset.inter_comm B A] at hB
  rw [hA, hB] at h
  exact cofactor_window h

end Round27Core

#print axioms Round27Core.cofactor_window
#print axioms Round27Core.nodal_core_split
#print axioms Round27Core.sunflower_core_reduction
