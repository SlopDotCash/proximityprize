/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.HammingBallVolume

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability

/-!
# Hamming ball volume

ABF26 Definition 2.4: the volume of a Hamming ball.

  `Vol_q(δ, n) := ∑_{i=0}^{⌊δ · n⌋} (n choose i) · (q-1)^i`

Counts the number of words in `Σ^n` (with `|Σ| = q`) within absolute Hamming
distance `⌊δ · n⌋` of any fixed center. Independent of the choice of center.

Used in:

- ABF26 Lemma 3.7 (Elias lower bound for `|Λ(C, δ)|`).
- ABF26 Corollary 3.8 (volume-based lower bound).

This file also provides the bridge between the volume function and the existing
`hammingBall` set in `ListDecodability.lean`.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace CodingTheory

/-- **Top-term lower bound on the Hamming-ball volume.** The volume is at least
its single largest-index summand `C(n, ⌊δn⌋)·(q−1)^⌊δn⌋`. This is the first
(combinatorial) half of the entropy-volume estimate `q^{nH_q(δ)}/√(…) ≤ Vol`
(ABF26 C3.8): keep only the boundary term, then the remaining work is the
Stirling lower bound on the single binomial coefficient. -/
theorem hammingBallVolume_ge_top_term (q : ℕ) (δ : ℝ) (n : ℕ) :
    Nat.choose n (⌊δ * n⌋₊) * (q - 1) ^ (⌊δ * n⌋₊) ≤ hammingBallVolume q δ n := by
  classical
  rw [hammingBallVolume]
  refine Finset.single_le_sum (f := fun i => Nat.choose n i * (q - 1) ^ i)
    (fun i _ => Nat.zero_le _) ?_
  exact Finset.self_mem_range_succ _

/-- **Single-term lower bound on the Hamming-ball volume.**

Every summand whose radius index lies inside the ball gives a lower bound on
`Vol_q(δ,n)`.  This is the flexible form used by entropy-volume arguments that
choose an index near `δn` and then apply a binomial/Stirling estimate to that
single summand. -/
theorem hammingBallVolume_ge_term_of_le_floor
    (q : ℕ) (δ : ℝ) (n i : ℕ) (hi : i ≤ ⌊δ * n⌋₊) :
    Nat.choose n i * (q - 1) ^ i ≤ hammingBallVolume q δ n := by
  classical
  rw [hammingBallVolume]
  refine Finset.single_le_sum (f := fun j => Nat.choose n j * (q - 1) ^ j)
    (fun j _ => Nat.zero_le _) ?_
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi)

/-- Real-valued form of `hammingBallVolume_ge_term_of_le_floor`. -/
theorem hammingBallVolume_real_ge_term_of_le_floor
    (q : ℕ) (δ : ℝ) (n i : ℕ) (hi : i ≤ ⌊δ * n⌋₊) :
    ((Nat.choose n i * (q - 1) ^ i : ℕ) : ℝ) ≤ (hammingBallVolume q δ n : ℝ) := by
  exact_mod_cast hammingBallVolume_ge_term_of_le_floor q δ n i hi

/-- Real-valued form of the top-term lower bound. -/
theorem hammingBallVolume_real_ge_top_term (q : ℕ) (δ : ℝ) (n : ℕ) :
    ((Nat.choose n (⌊δ * n⌋₊) * (q - 1) ^ (⌊δ * n⌋₊) : ℕ) : ℝ)
      ≤ (hammingBallVolume q δ n : ℝ) := by
  exact hammingBallVolume_real_ge_term_of_le_floor q δ n (⌊δ * n⌋₊) le_rfl

end CodingTheory
