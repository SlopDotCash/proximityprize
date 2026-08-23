/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.Probability.RandomSubsetInclusion

/-!
# First-moment existence for uniformly random size-`n` subsets (random-domain list decoding)

Building on the hypergeometric inclusion count `card_filter_mem_powersetCard_mul`
(`#{L ∈ s.powersetCard n : x ∈ L} · |s| = n · |s.powersetCard n|`, i.e. `Pr[x ∈ L] = n/|s|`),
this proves the **deterministic first-moment lower bound** for random domains: some size-`n` subset
`L ⊆ s` contains at least the average number of "bad" points,

  `|s| · #{ x ∈ Bad : x ∈ L }  ≥  n · |Bad|`   (i.e. count `≥ |Bad|·n/|s|`),

stated division-free over `ℕ`. This is the random-domain (random Reed–Solomon evaluation set)
analogue of `RandomLinearCode.exists_generator_count_ge_average`, feeding the random-RS
list-decoding / MCA first-moment arguments (ABF26 T3.6 / T4.15).

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `exists_subset_inclusion_count_ge_average` — a size-`n` subset attains the average bad-point count.
-/

namespace ArkLib.RandomSubset

open Finset

variable {α : Type*} [DecidableEq α]

/-- **First-moment existence (random domain).** For `Bad ⊆ s` and `n ≤ |s|`, some size-`n` subset
`L ⊆ s` contains at least the average number of bad points: `|s| · #{x ∈ Bad : x ∈ L} ≥ n · |Bad|`.
Division-free `ℕ` form of `count ≥ |Bad|·n/|s|`. -/
theorem exists_subset_inclusion_count_ge_average
    {s Bad : Finset α} (hBad : Bad ⊆ s) {n : ℕ} (hn : n ≤ s.card) :
    ∃ L ∈ s.powersetCard n,
      n * Bad.card ≤ s.card * ((Bad.filter (fun a => a ∈ L)).card) := by
  classical
  have htotal :
      s.card * (∑ L ∈ s.powersetCard n, (Bad.filter (fun a => a ∈ L)).card)
        = n * Bad.card * (s.powersetCard n).card := by
    have hswap :
        (∑ L ∈ s.powersetCard n, (Bad.filter (fun a => a ∈ L)).card)
          = ∑ x ∈ Bad, ((s.powersetCard n).filter (fun L => x ∈ L)).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap, Finset.mul_sum]
    have hper : ∀ x ∈ Bad,
        s.card * ((s.powersetCard n).filter (fun L => x ∈ L)).card
          = n * (s.powersetCard n).card := by
      intro x hx
      rw [mul_comm]
      exact card_filter_mem_powersetCard_mul (hBad hx) n
    rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
    ring
  by_contra hcon
  push Not at hcon
  have hne : (s.powersetCard n).Nonempty := Finset.powersetCard_nonempty.2 hn
  have hsumlt :
      ∑ L ∈ s.powersetCard n, s.card * (Bad.filter (fun a => a ∈ L)).card
        < ∑ _L ∈ s.powersetCard n, n * Bad.card := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro L hL; exact hcon L hL
  rw [← Finset.mul_sum, htotal, Finset.sum_const, smul_eq_mul] at hsumlt
  have heq : n * Bad.card * (s.powersetCard n).card
      = (s.powersetCard n).card * (n * Bad.card) := by ring
  rw [heq] at hsumlt
  exact (lt_irrefl _) hsumlt

end ArkLib.RandomSubset

-- Axiom audit.
#print axioms ArkLib.RandomSubset.exists_subset_inclusion_count_ge_average
