/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RSWeightEnumerator
import ArkLib.Data.CodingTheory.RSNearCount
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Reed–Solomon codeword weight ↔ polynomial eval-support

The Hamming weight of the Reed–Solomon codeword `evalOnPoints domain p` equals the cardinality of the
polynomial's evaluation support `evalSupport domain p` (the points where `p` does not vanish).  This is
the bridge connecting the polynomial-level weight enumerator / near-count (`card_evalWeight_le`,
`card_evalWeight_le_sum`) to the actual codewords of `ReedSolomon.code`, completing the #82
covered-fraction chain at the codeword level: the count of near codewords is controlled by the count
of low-eval-weight polynomials, which the MDS weight enumerator bounds.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **RS codeword weight = polynomial eval-support size.**  `Δ₀(evalOnPoints domain p, 0)` (the Hamming
weight of the RS codeword of `p`) equals `|evalSupport domain p|` — the number of evaluation points at
which `p` does not vanish.  Essentially definitional: `(evalOnPoints domain p) i = p.eval (domain i)`. -/
theorem hammingNorm_evalOnPoints_eq_evalSupport_card (domain : ι ↪ F) {deg : ℕ}
    (p : Polynomial.degreeLT F deg) :
    hammingNorm (ReedSolomon.evalOnPoints domain (p : F[X])) = (evalSupport domain p).card := by
  unfold hammingNorm evalSupport
  congr 1

/-- **RS near-codeword count bound.**  The number of distinct Reed–Solomon codewords of Hamming
weight `≤ R` (the images under `evalOnPoints` of the degree-`<deg` polynomials with eval-support
`≤ R` — equal by `hammingNorm_evalOnPoints_eq_evalSupport_card`) is at most
`∑_{d≤R} C(n,d)·q^{d−(n−deg)}`.  Composes `Finset.card_image_le` with the polynomial near-count
`card_evalWeight_le_sum`.  With `R = 2r` this is the `|near|` bound for the CS25 covered-fraction
argument, now at the codeword level. -/
theorem card_near_codewords_le (domain : ι ↪ F) (deg : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (R : ℕ) :
    ((Finset.univ.filter
          (fun p : Polynomial.degreeLT F deg => (evalSupport domain p).card ≤ R)).image
        (fun p : Polynomial.degreeLT F deg => ReedSolomon.evalOnPoints domain (p : F[X]))).card
      ≤ ∑ d ∈ Finset.range (R + 1),
          (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
  refine le_trans ?_ (card_evalWeight_le_sum domain deg R)
  exact Finset.card_image_le

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.hammingNorm_evalOnPoints_eq_evalSupport_card
#print axioms ArkLib.CS25.card_near_codewords_le
