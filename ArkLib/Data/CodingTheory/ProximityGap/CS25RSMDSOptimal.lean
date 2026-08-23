/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.SingletonBound
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSDimension

/-!
# Reed–Solomon is MDS: the minimum distance is exactly `n − k + 1` (#82)

`rsCodeFinset_hammingDist_ge` gives the Singleton lower bound (distinct RS codewords differ in
`≥ n−(k−1)` positions).  Here the matching upper bound: there *exist* distinct RS codewords at
distance `≤ n−(k−1)`.  If not, every distinct pair would be `≥ n−(k−1)+1` apart, and the Singleton
bound would force `|RS| ≤ q^{k−1} < q^k`, contradicting `rsCodeFinset_card = q^k`.  Together the RS
minimum distance is exactly `n−k+1` — Reed–Solomon codes are MDS.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Reed–Solomon meets the Singleton bound (MDS optimality).** There exist distinct RS codewords
at Hamming distance `≤ n−(k−1)`; with `rsCodeFinset_hammingDist_ge` this pins the RS minimum distance
to exactly `n−k+1`. -/
theorem rs_exists_pair_le_mds (domain : ι ↪ F) (k : ℕ) [NeZero k] (hnk : k ≤ Fintype.card ι)
    (hq : 2 ≤ Fintype.card F) [Fintype (Polynomial.degreeLT F k)] :
    ∃ c ∈ rsCodeFinset domain k, ∃ c' ∈ rsCodeFinset domain k,
      c ≠ c' ∧ hammingDist c c' ≤ Fintype.card ι - (k - 1) := by
  by_contra hcon
  push_neg at hcon
  have hmin : ∀ c ∈ rsCodeFinset domain k, ∀ c' ∈ rsCodeFinset domain k, c ≠ c' →
      (Fintype.card ι - (k - 1) + 1) ≤ hammingDist c c' := by
    intro c hc c' hc' hne
    have := hcon c hc c' hc' hne
    omega
  have hsing := singleton_bound (rsCodeFinset domain k) (Fintype.card ι - (k - 1) + 1)
    (by omega) hmin
  rw [rsCodeFinset_card domain k hnk] at hsing
  have hexp : Fintype.card ι - ((Fintype.card ι - (k - 1) + 1) - 1) = k - 1 := by omega
  rw [hexp] at hsing
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have : Fintype.card F ^ (k - 1) < Fintype.card F ^ k :=
    Nat.pow_lt_pow_right hq (by omega)
  omega

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.rs_exists_pair_le_mds
