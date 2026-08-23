/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungClassFamily
import ArkLib.Data.CodingTheory.ProximityGap.RungSoloBound

/-!
# The agreement Fisher family (#371, rung): the second packing input

The complement of the factor-family confinement (`RungClassFamily`).  The
agreement set of a class is `A_q = {i : R₁(xᵢ) = q(xᵢ)}` for its cross
polynomial `q` (degree `< k`).  Distinct classes have distinct `q`, so by
`lowDegree_agreement_inter_le` their agreement sets pairwise share at most
`k − 1` points — a Fisher family.  Consequences:

* `agreementSet` / `distinct_agreement_inter_le` — the pairwise bound;
* `agreement_family_fisher` — the resulting count: agreement sets of size
  `≥ m` from distinct classes number at most `C(n, k)/C(m, k)` (`s = k−1`
  in `solo_scalars_card_le`).

Together with the 3-dim factor confinement (`RungClassFamily`), these are
the two inputs to the class-packing count `Σ(n − aⱼ) ≤ 30`: a Fisher family
of agreement sets whose vanishing factors live in one low-degree coset.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section AgreementFisher

variable (dom : Fin n ↪ F) (R₁ : F[X])

/-- The agreement set of the direction row with a cross polynomial. -/
def agreementSet (q : F[X]) : Finset (Fin n) :=
  Finset.univ.filter (fun i => R₁.eval (dom i) = q.eval (dom i))

/-- **Pairwise Fisher bound**: distinct cross polynomials of degree `< k`
have agreement sets sharing at most `k − 1` points. -/
theorem distinct_agreement_inter_le {k : ℕ} (hk : 1 ≤ k)
    {q₁ q₂ : F[X]} (hq : q₁ ≠ q₂)
    (hd₁ : q₁.natDegree < k) (hd₂ : q₂.natDegree < k) :
    (agreementSet dom R₁ q₁ ∩ agreementSet dom R₁ q₂).card ≤ k - 1 :=
  lowDegree_agreement_inter_le dom R₁ hq hd₁ hd₂ hk

/-- **The agreement Fisher count**: a family of distinct cross polynomials
whose agreement sets all have size `≥ m` numbers at most `C(n, k)/C(m, k)`
(stated in the multiplicative `· C(m, k) ≤ C(n, k)` form). -/
theorem agreement_family_fisher {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    {Q : Finset F[X]}
    (hdeg : ∀ q ∈ Q, q.natDegree < k)
    (hsize : ∀ q ∈ Q, m ≤ (agreementSet dom R₁ q).card) :
    Q.card * Nat.choose m k ≤ Nat.choose n k := by
  classical
  have hk1 : k - 1 < m := by omega
  -- the agreement-set map is injective on Q: equal sets force equal q
  -- (a deg-<k poly is pinned by ≥ k ≥ m agreement points)
  have hinj : Set.InjOn (agreementSet dom R₁) Q := by
    intro q₁ h₁ q₂ h₂ heq
    by_contra hne
    have hcap := distinct_agreement_inter_le dom R₁ hk hne (hdeg q₁ h₁) (hdeg q₂ h₂)
    rw [heq, Finset.inter_self] at hcap
    have := hsize q₂ h₂
    omega
  have himg : (Q.image (agreementSet dom R₁)).card = Q.card :=
    Finset.card_image_of_injOn hinj
  have hsub : (k - 1) + 1 = k := by omega
  rw [← himg, ← hsub]
  refine pairwise_inter_le_subsets_card_le hk1 ?_ ?_
  · intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    exact hsize q hq
  · intro T₁ hT₁ T₂ hT₂ hne
    obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hT₁
    obtain ⟨q₂, hq₂, rfl⟩ := Finset.mem_image.mp hT₂
    exact distinct_agreement_inter_le dom R₁ hk
      (fun h => hne (by rw [h])) (hdeg q₁ hq₁) (hdeg q₂ hq₂)

end AgreementFisher

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.distinct_agreement_inter_le
#print axioms ProximityGap.WBPencil.agreement_family_fisher
