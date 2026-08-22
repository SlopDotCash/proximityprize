/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Bijection

/-!
# BCIKS20 Appendix A.4 — dropping the `|λ| ≤ i` filter (toward the Fubini reabsorption)

The LHS partition form of `restrictedFaaDiBrunoSum` (`restrictedFaaDiBrunoSum_eq_partitionForm`)
sums, for each Y-degree `i`, over partitions `λ ⊢ c` with **both** `|λ| ≤ i` and `(t+1) ∉ λ`.  To
Fubini-swap the `i`- and `λ`-sums (so each partition's Y-degree sum can be reabsorbed into
`hasseEvalAtRoot` via `P2Reabsorb.hasseEvalAtRoot_eq_QDegreeBinomReindex`), the `i`-dependent
`|λ| ≤ i` constraint must first be removed — the partition set then no longer depends on `i`.

`partitionSum_drop_card_filter` does exactly that: the extra terms (`|λ| > i`) carry the binomial
`C(i, |λ|) = 0`, so they vanish and the `|λ| ≤ i` filter can be dropped without changing the sum.
It is a pure, general `CommSemiring` / `Finset` fact (independent of the BCIKS20 specifics).

NO `axiom`/`admit`/`native_decide`/`sorry`. Audited in-file via `#print axioms`.
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset
open ArkLib.PowerSeriesComposition

/-- **Dropping the `|λ| ≤ i` filter (PROVEN, general).**  In the `C(i, |λ|)`-weighted partition sum,
the terms with `|λ| > i` vanish (`Nat.choose_eq_zero_of_lt`), so restricting to `|λ| ≤ i` does not
change the value.  This removes the `i`-dependence of the partition index set, enabling the Fubini
swap of the Y-degree and partition sums in the P2 reabsorption. -/
theorem partitionSum_drop_card_filter {M : Type*} [CommSemiring M] (i c T : ℕ) (b : ℕ → M) (α : M) :
    (∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter
              (fun lam => lam.parts.card ≤ i ∧ T ∉ lam.parts),
        ((i.choose lam.parts.card) * lam.parts.countPerms)
          • (α ^ (i - lam.parts.card) * (lam.parts.map b).prod))
      = ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter
                (fun lam => T ∉ lam.parts),
          ((i.choose lam.parts.card) * lam.parts.countPerms)
            • (α ^ (i - lam.parts.card) * (lam.parts.map b).prod) := by
  apply Finset.sum_subset
  · -- `{λ | |λ| ≤ i ∧ T ∉ λ} ⊆ {λ | T ∉ λ}`.
    intro lam hlam
    rw [Finset.mem_filter] at hlam ⊢
    exact ⟨hlam.1, hlam.2.2⟩
  · -- the dropped terms (`|λ| > i`) vanish: `C(i, |λ|) = 0`.
    intro lam hmem hnot
    rw [Finset.mem_filter] at hmem
    have hcard : i < lam.parts.card := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hmem.1, not_lt.mp h, hmem.2⟩)
    rw [Nat.choose_eq_zero_of_lt hcard, zero_mul, zero_smul]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.partitionSum_drop_card_filter
