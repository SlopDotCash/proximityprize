/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RSWeightEnumerator

/-!
# Reed–Solomon near-codeword count (#82 entropy-band input)

Summing the MDS weight-enumerator upper bound `card_evalWeight_le` over the low weights gives the
**near-codeword count bound**: the number of degree-`<deg` polynomials whose evaluation has Hamming
weight `≤ R` is at most `∑_{d≤R} C(n,d)·q^{d−(n−deg)}`.

This is the missing `|near| ≤ ∑_{d≤2r} A_d` ingredient of the CS25 second-moment / covered-fraction
argument (`card_close_mul_near_ge`): with `R = 2r`, it controls the near-codeword count that bounds
the variance, completing the entropy-band regime at the polynomial level.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Near-codeword count bound (polynomial level).**  The number of degree-`<deg` polynomials whose
evaluation has Hamming weight `≤ R` is at most `∑_{d≤R} C(n,d)·q^{d−(n−deg)}` — summing the per-weight
MDS upper bound `card_evalWeight_le` over `d = 0..R`.  With `R = 2r` this is the `|near|` bound used
by the CS25 covered-fraction argument. -/
theorem card_evalWeight_le_sum (α : ι ↪ F) (deg : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (R : ℕ) :
    (Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => (evalSupport α p).card ≤ R)).card
      ≤ ∑ d ∈ Finset.range (R + 1),
          (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
  classical
  have H : ∀ p ∈ (Finset.univ.filter
      (fun p : Polynomial.degreeLT F deg => (evalSupport α p).card ≤ R)),
      (evalSupport α p).card ∈ Finset.range (R + 1) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_range]; omega
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_le_sum (fun d _ => ?_)
  refine le_trans (Finset.card_le_card ?_) (card_evalWeight_le α deg d)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨Finset.mem_univ _, hp.2⟩

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.card_evalWeight_le_sum
