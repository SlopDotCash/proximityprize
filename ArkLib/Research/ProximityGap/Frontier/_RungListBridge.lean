/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungAgreementFisher

/-!
# The list-decoding bridge (#371): attached frame classes = RS list members

The explicit attached-side bridge for the LD↔MCA deep-band equivalence.
A frame class of the MCA census is indexed by a cross-polynomial `q`
(deg `< k`) whose agreement set `A_q = {i : R₁(xᵢ) = q(xᵢ)}` is large; that
is precisely a degree-`< k` codeword **close to the direction row `R₁`** —
a member of the Reed–Solomon **list** of `R₁` at radius `n − |A_q|`.

* `attachedCrossPolys` — the set of distinct cross-polynomials whose
  agreement with `R₁` has size `≥ a` (the list at radius `n − a`);
* `attached_cross_polys_card_le` — its size obeys the universal injection
  ceiling `#list · C(a, k) ≤ C(n, k)` (the agreement-Fisher list bound),
  i.e. the class COUNT is bounded by the RS list size.

**Unification**: the attached stratum's class count is the RS list size of
`R₁`.  Where the radius is inside Johnson (`a` large, the low-degree band
`r ≤ √n`) this list is provably small and the census closes (consistent
with `kkh26_deltaStar_pin_lowdegree`).  The deep band `r ∈ (√(n log n),
n/2]` is exactly large-radius list decoding of explicit RS — the
beyond-Johnson wall — so no closure is claimed; this names the bridge.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section ListBridge

variable (dom : Fin n ↪ F) (R₁ : F[X])

open Classical in
/-- The cross-polynomials (deg `< k`) agreeing with `R₁` on `≥ a` points —
the Reed–Solomon list of `R₁` at radius `n − a`, drawn from a given finite
candidate pool `P`. -/
noncomputable def attachedCrossPolys (k a : ℕ) (P : Finset F[X]) : Finset F[X] :=
  P.filter (fun q => q.natDegree < k ∧ a ≤ (agreementSet dom R₁ q).card)

open Classical in
/-- **The list bound = the attached class-count bound**: the number of
distinct degree-`< k` codewords within agreement-radius `n − a` of `R₁`
satisfies the universal injection ceiling `#list · C(a, k) ≤ C(n, k)`. -/
theorem attached_cross_polys_card_le {k a : ℕ} (hk : 1 ≤ k) (hka : k ≤ a)
    (P : Finset F[X]) :
    (attachedCrossPolys dom R₁ k a P).card * Nat.choose a k
      ≤ Nat.choose n k := by
  classical
  refine agreement_family_fisher dom R₁ hk hka
    (Q := attachedCrossPolys dom R₁ k a P) ?_ ?_
  · intro q hq
    rw [attachedCrossPolys, Finset.mem_filter] at hq
    exact hq.2.1
  · intro q hq
    rw [attachedCrossPolys, Finset.mem_filter] at hq
    exact hq.2.2

end ListBridge

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.attached_cross_polys_card_le
