/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCosetAmplification

/-!
# DQR-4 stratum palindrome: tower twists halve the ledger — #466

Twelfth result of the arc, extracted from the graduated-scale discrepancy probe (which showed
`T_k = T_{14−k}` exactly in the data at every instance). The mechanism: a DYADIC TOWER twist
satisfies `a² ∈ G_j` (its square drops one level), so reindexing `b ↦ b·a` in the stratum and
collapsing `η_{b·a²} = η_b` by coset invariance gives, for every `k ≤ m`:

* `stratum_palindrome` — `∑_{b≠0} η_b^k·η_{b·a}^{m−k} = ∑_{b≠0} η_b^{m−k}·η_{b·a}^k`.

Consequences: the 13 unknown cross strata of the signed depth-14 ledger reduce to 7
(`k = 1..7`); the assembled recursion's coefficient structure symmetrizes
(`C(14,k) + C(14,14−k)` pairing); and the discrepancy question lives on half the board.
Together with the probe's finding that the actual dyadic twists are strongly ATYPICAL for the
twist mean (deviations `10³–10⁵×` at extreme strata), the palindrome is the first exact law
governing what the production twists actually do. Nothing here discharges the wall.
Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification

namespace ArkLib.ProximityGap.Frontier.DQR4StratumPalindrome

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The stratum palindrome for tower twists**: if `a ≠ 0` and `a·a ∈ G` (the dyadic tower
condition — the twist's square drops a level), then every mixed stratum is symmetric,
`∑_{b≠0} η_b^k·η_{b·a}^j = ∑_{b≠0} η_b^j·η_{b·a}^k`. -/
theorem stratum_palindrome {G : Finset F} (hG : MulClosed G)
    (ψ : AddChar F ℂ) {a : F} (ha : a ≠ 0) (ha2 : a * a ∈ G) (k j : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
      = ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ j * (eta ψ G (b * a)) ^ k := by
  -- reindex `b ↦ b·a` (permutes the nonzero frequencies), then collapse `η_{b·a²} = η_b`.
  have hstep : ∀ b : F, b ≠ 0 →
      (eta ψ G (b * a)) ^ j * (eta ψ G ((b * a) * a)) ^ k
        = (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j := by
    intro b _
    have hcoll : eta ψ G ((b * a) * a) = eta ψ G b := by
      rw [mul_assoc]
      exact eta_mul_right hG ψ b ha2
    rw [hcoll]
    ring
  calc ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ j
      = ∑ b ∈ Finset.univ.erase (0 : F),
          (eta ψ G (b * a)) ^ j * (eta ψ G ((b * a) * a)) ^ k := by
        refine Finset.sum_congr rfl (fun b hb => ?_)
        exact (hstep b (Finset.ne_of_mem_erase hb)).symm
    _ = ∑ c ∈ Finset.univ.erase (0 : F), (eta ψ G c) ^ j * (eta ψ G (c * a)) ^ k := by
        apply Finset.sum_nbij' (i := fun b => b * a) (j := fun c => c * a⁻¹)
        · intro b hb
          have hb0 : b ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast hb)
          simp [Finset.mem_coe, Finset.mem_erase, mul_ne_zero hb0 ha]
        · intro c hc
          have hc0 : c ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast hc)
          simp [Finset.mem_coe, Finset.mem_erase, mul_ne_zero hc0 (inv_ne_zero ha)]
        · intro b _
          rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
        · intro c _
          rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
        · intro b _
          rfl

end ArkLib.ProximityGap.Frontier.DQR4StratumPalindrome

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.DQR4StratumPalindrome.stratum_palindrome
