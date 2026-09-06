/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The Gauss periods are REAL when the subgroup is negation-closed (#407, CRACK 7 / EVT substrate)

The crack-audit's top closure route (CRACK 7) proves the BGK floor as an extreme-value theorem for
the **exchangeable de-Finetti period family** `{η_b}`. That family is **real Gaussian** — the
real-valuedness is what makes the EVT a Gumbel max of *real* exchangeable variables and underlies the
odd-moment law. This file lands the real-valuedness, the third piece of the de-Finetti substrate
(after the first moment `Σ_{b≠0} η_b = −|G|` and the Parseval second moment `Σ‖η_b‖² = qn − n²`):

> `conj(η_b) = η_b`  whenever `G` is negation-closed (`−1 ∈ G`, i.e. `∀ y ∈ G, −y ∈ G`).

Proof: `conj(η_b) = Σ_{y∈G} ψ(−(by)) = Σ_{y∈G} ψ(b·(−y))`, and `y ↦ −y` is a bijection of `G`
(negation-closure), so reindexing gives `η_b` back. For the prize `μ_n` with `n` even, `−1 = ζ^{n/2}
∈ μ_n`, so the periods are real. Axiom-clean. Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.GaussPeriodRealValued

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The Gauss periods are real-valued** for a negation-closed subgroup: `conj(η_b) = η_b` when
`∀ y ∈ G, −y ∈ G` (true for `μ_n`, `n` even, since `−1 ∈ μ_n`). The de-Finetti period family is real
Gaussian — the substrate the EVT/Gumbel concentration (CRACK 7) is stated over. -/
theorem eta_conj_eq_of_neg_closed {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hneg : ∀ y ∈ G, -y ∈ G) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = eta ψ G b := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hGimg : G.image (fun y => -y) = G := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hneg y hy
    · intro x hx
      rw [Finset.mem_image]
      exact ⟨-x, hneg x hx, neg_neg x⟩
  have h1 : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (b * (-y)) := by
    rw [eta, map_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hconj (b * y)]; congr 1; ring
  rw [h1, eta]
  conv_rhs => rw [← hGimg]
  rw [Finset.sum_image (fun x _ y _ h => neg_injective h)]

end ProximityGap.Frontier.GaussPeriodRealValued

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.GaussPeriodRealValued.eta_conj_eq_of_neg_closed
