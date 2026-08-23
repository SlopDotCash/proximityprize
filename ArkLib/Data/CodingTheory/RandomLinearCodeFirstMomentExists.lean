/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RandomLinearCodeEquidistribution

/-!
# GLMRSW22 first-moment existence: a generator matrix achieving the average codeword count

Building on the equidistribution cardinality identity `card_mat_eq` (`|Matrix| = qⁿ · |fiber|`),
this proves the **deterministic first-moment lower bound** behind the GLMRSW22 random-linear-code
argument (issue #79): some generator matrix `G` has at least the *average* number of nonzero
messages whose codeword lands in a target set `S`,

`qⁿ · #{ m ≠ 0 : m ᵥ* G ∈ S }  ≥  (qᵏ − 1) · |S|`,

stated division-free over `ℕ` — the existential-witness (max ≥ mean) step feeding the list-size
lower bound.

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `qn_mul_card_filter_vecMul_mem` — `qⁿ · #{G : m ᵥ* G ∈ S} = |S| · |Matrix|` for nonzero `m`.
* `exists_generator_count_ge_average` — a generator matrix attains the average count.
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integer per-message marginal count: for a fixed nonzero message `m` and a finite target set
`S` of codewords, `qⁿ · #{G : m ᵥ* G ∈ S} = |S| · |Matrix|`. (Division-free equidistribution.) -/
theorem qn_mul_card_filter_vecMul_mem {m : Fin k → F} (hm : m ≠ 0) (S : Finset (ι → F)) :
    Fintype.card (ι → F) * (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G ∈ S)).card
      = S.card * Fintype.card (Matrix (Fin k) ι F) := by
  classical
  have hbij :
      (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G ∈ S))
        = S.biUnion (fun v => Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v)) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hGS; exact ⟨m ᵥ* G, hGS, rfl⟩
    · rintro ⟨v, hv, hGv⟩; subst hGv; exact hv
  have hdisj : ∀ v ∈ S, ∀ v' ∈ S, v ≠ v' →
      Disjoint (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v))
        (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v')) := by
    intro v _ v' _ hvv'
    rw [Finset.disjoint_left]
    intro G hG hG'
    rw [Finset.mem_filter] at hG hG'
    exact hvv' (hG.2 ▸ hG'.2)
  rw [hbij, Finset.card_biUnion hdisj, Finset.mul_sum]
  have hcell : ∀ v : ι → F,
      Fintype.card (ι → F) * (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G = v)).card
        = Fintype.card (Matrix (Fin k) ι F) := by
    intro v
    rw [← Fintype.card_subtype (fun G : Matrix (Fin k) ι F => m ᵥ* G = v)]
    exact (card_mat_eq hm v).symm
  rw [Finset.sum_congr rfl (fun v _ => hcell v), Finset.sum_const, smul_eq_mul]

/-- **First-moment existence (deterministic).** Some generator matrix `G` attains at least the
average count of nonzero messages whose codeword lies in `S`:
`qⁿ · #{m ≠ 0 : m ᵥ* G ∈ S} ≥ (qᵏ − 1) · |S|`. -/
theorem exists_generator_count_ge_average (S : Finset (ι → F)) :
    ∃ G : Matrix (Fin k) ι F,
      (Fintype.card (Fin k → F) - 1) * S.card
        ≤ Fintype.card (ι → F)
            * (Finset.univ.filter
                (fun m : Fin k → F => m ≠ 0 ∧ m ᵥ* G ∈ S)).card := by
  classical
  have hcnt_eq : ∀ G : Matrix (Fin k) ι F,
      (Finset.univ.filter (fun m : Fin k → F => m ≠ 0 ∧ m ᵥ* G ∈ S)).card
        = ((Finset.univ.filter (fun m : Fin k → F => m ≠ 0)).filter
            (fun m => m ᵥ* G ∈ S)).card := by
    intro G; rw [Finset.filter_filter]
  have htotal :
      Fintype.card (ι → F) *
          (∑ G : Matrix (Fin k) ι F,
            (Finset.univ.filter (fun m : Fin k → F => m ≠ 0 ∧ m ᵥ* G ∈ S)).card)
        = (Fintype.card (Fin k → F) - 1) * (S.card * Fintype.card (Matrix (Fin k) ι F)) := by
    have hswap :
        (∑ G : Matrix (Fin k) ι F,
            (Finset.univ.filter (fun m : Fin k → F => m ≠ 0 ∧ m ᵥ* G ∈ S)).card)
          = ∑ m ∈ Finset.univ.filter (fun m : Fin k → F => m ≠ 0),
              (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G ∈ S)).card := by
      simp_rw [hcnt_eq, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap, Finset.mul_sum]
    have hper : ∀ m ∈ Finset.univ.filter (fun m : Fin k → F => m ≠ 0),
        Fintype.card (ι → F)
            * (Finset.univ.filter (fun G : Matrix (Fin k) ι F => m ᵥ* G ∈ S)).card
          = S.card * Fintype.card (Matrix (Fin k) ι F) :=
      fun m hm => qn_mul_card_filter_vecMul_mem (Finset.mem_filter.1 hm).2 S
    rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  by_contra hcon
  push Not at hcon
  have hMatpos : 0 < Fintype.card (Matrix (Fin k) ι F) := Fintype.card_pos
  have hsumlt :
      ∑ G : Matrix (Fin k) ι F,
          Fintype.card (ι → F)
            * (Finset.univ.filter (fun m : Fin k → F => m ≠ 0 ∧ m ᵥ* G ∈ S)).card
        < ∑ _G : Matrix (Fin k) ι F, (Fintype.card (Fin k → F) - 1) * S.card := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro G _; exact hcon G
  rw [← Finset.mul_sum, htotal, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsumlt
  have heq :
      (Fintype.card (Fin k → F) - 1) * (S.card * Fintype.card (Matrix (Fin k) ι F))
        = Fintype.card (Matrix (Fin k) ι F) * ((Fintype.card (Fin k → F) - 1) * S.card) := by
    ring
  rw [heq] at hsumlt
  exact (lt_irrefl _) hsumlt

end ArkLib.RandomLinearCode

-- Axiom audit.
#print axioms ArkLib.RandomLinearCode.qn_mul_card_filter_vecMul_mem
#print axioms ArkLib.RandomLinearCode.exists_generator_count_ge_average
