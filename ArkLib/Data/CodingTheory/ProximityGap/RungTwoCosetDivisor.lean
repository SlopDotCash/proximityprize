/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungSparseDivisor

/-!
# Two-coset divisors of `Xⁿ − 1` are `≤ n²` (#371/#389 prize, Mann lane)

Generalizes `sparse_divisors_card_le` (one coset, binomial `Xᵃ − c`, `≤ n`
values) to TWO cosets: product divisors `(Xᵃ − c)(Xᵇ − d)` of `Xⁿ − 1` number
at most `n²`.  Mechanism: any factor of a divisor of `Xⁿ − 1` is itself a
divisor of `Xⁿ − 1`, so both `Xᵃ − c ∣ Xⁿ − 1` and `Xᵇ − d ∣ Xⁿ − 1`; each
component is then constrained to `≤ n` values by the binomial bound, so the
pairs number `≤ n²`.  By induction this gives the general `t`-coset Mann count
`≤ nᵗ` (poly for fixed `t`) — the structured (coset-union) codewords that the
prize's petal/upper-bound lane must control are polynomially many.
-/

open Polynomial

namespace ProximityGap.PrizeWorkbench

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Two-coset divisors are few**: the pairs `(c,d)` for which
`(Xᵃ − C c)(Xᵇ − C d)` divides `Xⁿ − 1` number at most
`(#rootsN)²`, where `rootsN` supplies a root for each binomial divisor (≤ n
in the smooth-domain setting).  Each component divides `Xⁿ − 1`, so each is
bounded by the binomial count. -/
theorem two_coset_divisors_card_le {n a b : ℕ} (rootsN : Finset F)
    (hsplitA : ∀ c : F, (X ^ a - C c) ∣ (X ^ n - C 1) →
      ∃ r ∈ rootsN, (X ^ a - C c).IsRoot r)
    (hsplitB : ∀ d : F, (X ^ b - C d) ∣ (X ^ n - C 1) →
      ∃ r ∈ rootsN, (X ^ b - C d).IsRoot r) :
    ((Finset.univ ×ˢ Finset.univ).filter
      (fun cd : F × F =>
        (X ^ a - C cd.1) * (X ^ b - C cd.2) ∣ (X ^ n - C 1))).card
      ≤ rootsN.card * rootsN.card := by
  classical
  -- the pair set injects into (validA) ×ˢ (validB), each ≤ rootsN.card
  set validA := Finset.univ.filter (fun c : F => (X ^ a - C c) ∣ (X ^ n - C 1))
  set validB := Finset.univ.filter (fun d : F => (X ^ b - C d) ∣ (X ^ n - C 1))
  have hsub : ((Finset.univ ×ˢ Finset.univ).filter
      (fun cd : F × F =>
        (X ^ a - C cd.1) * (X ^ b - C cd.2) ∣ (X ^ n - C 1)))
      ⊆ validA ×ˢ validB := by
    intro cd hcd
    rw [Finset.mem_filter] at hcd
    obtain ⟨_, hdvd⟩ := hcd
    rw [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Dvd.dvd.trans (dvd_mul_right _ _) hdvd)⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Dvd.dvd.trans (dvd_mul_left _ _) hdvd)⟩
  calc ((Finset.univ ×ˢ Finset.univ).filter
          (fun cd : F × F =>
            (X ^ a - C cd.1) * (X ^ b - C cd.2) ∣ (X ^ n - C 1))).card
      ≤ (validA ×ˢ validB).card := Finset.card_le_card hsub
    _ = validA.card * validB.card := Finset.card_product _ _
    _ ≤ rootsN.card * rootsN.card :=
        Nat.mul_le_mul (sparse_divisors_card_le rootsN hsplitA)
          (sparse_divisors_card_le rootsN hsplitB)

end ProximityGap.PrizeWorkbench

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PrizeWorkbench.two_coset_divisors_card_le
