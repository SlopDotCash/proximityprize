/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeListSize
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Refuting the up-to-capacity list-decoding bound (the negative side of ABF26 #232)

The Grand List Decoding Challenge (`GrandChallenges.grandListDecodingChallenge`) asks for the
largest `δ*` with `|Λ(C, δ*)| ≤ ε*·|F|`. The *up-to-capacity* hope — that `δ*` can reach the
Singleton/min-distance radius `1 - ρ` — is **false** ([CS25], [KK25], the prime-field
counterexample arXiv 2604.09724). This file gives the machine-checked negative result, built on
the already-proven, axiom-clean entropy-volume list lower bound
`CodingTheory.rs_lambda_ge_capacity_exponent`:

  `|Λ(RS[α,k], δ)| ≥ q^{capExp} / (n+1)`,  `capExp = n·H_q(⌊δn⌋/n) − (n − k)`.

When `capExp` is large enough that this lower bound exceeds `ε*·|F|`, the list-decoding bound is
*violated* at `δ` — so any valid threshold `δ*` lies strictly below `δ`.

## Main results

* `capExp` — the capacity exponent `n·H_q(⌊δn⌋/n) − (n − k)`.
* `rs_lambda_gt_threshold_of_capExp` — if the capacity-exponent lower bound exceeds `ε*·|F|`, then
  `|Λ(RS, δ)| > ε*·|F|`: the list bound fails at `δ`.
* `ListDecodingUpperWitness` — a certified radius where `|Λ| > ε*·|F|` (the list-decoding analogue
  of `GrandChallenges.MCAUpperWitness`).
* `rs_listDecodingUpperWitness_of_capExp` — constructs such a witness for Reed–Solomon.
* `lambda_gt_threshold_of_ge` — monotone propagation: once the bound fails at `δ`, it fails at
  every larger radius.
* `threshold_lt_of_upperWitness` — **the refutation:** any radius `δ*` at which the list bound
  *holds* lies strictly below the witness radius. So an upper witness caps the Grand List Decoding
  threshold; if it sits below capacity `1 - ρ`, the up-to-capacity bound is provably impossible.

## Honest scope

This is a *conditional* refutation: the hypothesis is that the (axiom-clean) capacity-exponent
lower bound overflows the threshold (`capExp` large). That hypothesis is exactly the literature's
near-capacity regime; discharging it *unconditionally below `1 - ρ`* requires the entropy-inversion
fact `H_q⁻¹(1 − ρ) < 1 − ρ` (the list-decoding-capacity-vs-Singleton gap), which is the genuine
open analytic input — not formalized here. What is proven, axiom-clean, is that whenever the list
overflow occurs, the list-decoding bound demonstrably fails and the challenge threshold is capped.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; §1 Grand List Decoding Challenge, §3 list-decoding bounds.
- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. ePrint 2025/2046.
-/

open scoped NNReal ENNReal
open CodingTheory ListDecodable

namespace ProximityGap.ListDecodingConjectureRefutation

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The **capacity exponent** `n·H_q(⌊δn⌋/n) − (n − k)` (`q`, `n` are the field / domain
cardinalities). The RS list size `|Λ(RS[α,k], δ)| ≥ q^{capExp}/(n+1)` is super-polynomial exactly
when this is positive (`H_q(⌊δn⌋/n) > 1 − ρ`, `ρ = k/n`). -/
noncomputable def capExp (q n k : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * qEntropy q ((⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) - ((n : ℝ) - (k : ℝ))

/-- **List-decoding bound violated (RS, capacity-exponent form).** If the (proven) capacity-exponent
list lower bound already exceeds the prize threshold `ε*·|F|`, then the RS list size strictly
exceeds `ε*·|F|` at radius `δ` — i.e. the up-to-capacity list-decoding bound fails at `δ`. Direct
transitivity through the axiom-clean `CodingTheory.rs_lambda_ge_capacity_exponent`. -/
theorem rs_lambda_gt_threshold_of_capExp
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card F) (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (ε_star : ℝ≥0)
    (hbig : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < ENNReal.ofReal ((Fintype.card F : ℝ) ^ capExp (Fintype.card F) (Fintype.card ι) k δ
            / ((Fintype.card ι : ℝ) + 1))) :
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda (ReedSolomon.code α k : Set (ι → F)) δ : ENNReal) :=
  lt_of_lt_of_le hbig (rs_lambda_ge_capacity_exponent α k δ hδ_pos hδ_lt hq hkcard hk0 hkn)

/-- **A certified list-decoding overflow radius.** A radius at which the list size provably exceeds
`ε*·|F|` — the list-decoding analogue of `GrandChallenges.MCAUpperWitness`. It caps the Grand List
Decoding threshold strictly below `δ` (see `threshold_lt_of_upperWitness`). -/
structure ListDecodingUpperWitness (C : Set (ι → F)) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `|Λ(C, δ)| > ε*·|F|`. -/
  exceeds : (ε_star : ENNReal) * (Fintype.card F : ENNReal) < (Lambda C (δ : ℝ) : ENNReal)

/-- **The negative result, as a witness.** A capacity-exponent overflow yields a
`ListDecodingUpperWitness` for the Reed–Solomon code: a radius where the list size exceeds the
prize threshold. -/
noncomputable def rs_listDecodingUpperWitness_of_capExp
    (α : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hq : 2 ≤ Fintype.card F) (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (ε_star : ℝ≥0)
    (hbig : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < ENNReal.ofReal ((Fintype.card F : ℝ)
            ^ capExp (Fintype.card F) (Fintype.card ι) k (δ : ℝ) / ((Fintype.card ι : ℝ) + 1))) :
    ListDecodingUpperWitness (ReedSolomon.code α k : Set (ι → F)) ε_star where
  δ := δ
  exceeds := rs_lambda_gt_threshold_of_capExp α k (δ : ℝ) hδ_pos hδ_lt hq hkcard hk0 hkn ε_star hbig

/-- **Monotone propagation.** Once the list-decoding bound fails at the witness radius, it fails at
every larger radius (`Lambda` is monotone in `δ`). -/
theorem lambda_gt_threshold_of_ge
    (C : Set (ι → F)) (ε_star : ℝ≥0) (W : ListDecodingUpperWitness C ε_star)
    {δ' : ℝ} (hδ' : (W.δ : ℝ) ≤ δ') :
    (ε_star : ENNReal) * (Fintype.card F : ENNReal) < (Lambda C δ' : ENNReal) := by
  refine lt_of_lt_of_le W.exceeds ?_
  exact_mod_cast (Lambda_mono (C := C) hδ')

/-- **The refutation.** Any radius `δ*` at which the list bound `|Λ| ≤ ε*·|F|` *holds* lies strictly
below an upper-witness radius. Hence an upper witness caps the Grand List Decoding threshold: if it
sits below capacity `1 − ρ`, no valid `δ*` can reach capacity, so the up-to-capacity list-decoding
bound is impossible. -/
theorem threshold_lt_of_upperWitness
    {D : Set (ι → F)} {ε_star : ℝ≥0} (W : ListDecodingUpperWitness D ε_star)
    {δ_star : ℝ≥0}
    (hb : (Lambda D (δ_star : ℝ) : ENNReal) ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    δ_star < W.δ := by
  by_contra hle
  rw [not_lt] at hle
  have hgt := lambda_gt_threshold_of_ge D ε_star W (by exact_mod_cast hle)
  exact absurd hb (not_le.mpr hgt)

#print axioms rs_lambda_gt_threshold_of_capExp
#print axioms rs_listDecodingUpperWitness_of_capExp
#print axioms lambda_gt_threshold_of_ge
#print axioms threshold_lt_of_upperWitness

end ProximityGap.ListDecodingConjectureRefutation
