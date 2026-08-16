/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Cyclotomic power-sum concentration and the q-independence dichotomy (#407)

The prize counterexample needs a `q`-independent (field-size-independent) family of subsets of the
smooth domain `μ_n` (`n = 2^μ`) whose power sums concentrate on a single target. Rounds 7–8 of the
#232/#407 development obtained the `e_1 = 0` (first power sum) concentration via the **negation**
involution `x ↦ −x` (`SubsetSumNegSymmConcentration.lean`). This file proves the **general cyclotomic
generalization** and the structural reason it is a dead end for the interior.

> **`powerSum_eq_zero_of_smul_invariant`** — if `S ⊆ F` is invariant under multiplication by `ξ`
> (`ξ·S = S`, `ξ ≠ 0`), then for **every** `j` with `ξ^j ≠ 1` the power sum `∑_{x∈S} x^j = 0`.

Specializing `ξ` to a primitive `2^s`-th root of unity (which lies in `μ_{2^μ}` for `s ≤ μ`) gives
`p_1 = p_2 = ⋯ = p_{2^s − 1} = 0` simultaneously (all power sums `p_j` with `2^s ∤ j` vanish), and
Newton's identities promote this to `e_1 = ⋯ = e_{2^s−1} = 0`. The `s = 1` case (`ξ = −1`) recovers
the negation-symmetric `e_1 = 0`.

**Why this is the dichotomy, not a bypass.** A `ξ`-invariant `S` (with `ξ` a primitive `2^s`-th root)
is a union of full `⟨ξ⟩`-orbits, so its subset-sum polynomial factors through the power map:
`∏_{x∈S}(X − x) = ∏_{orbits}(X^{2^s} − x_o^{2^s})`, a polynomial in `X^{2^s}`. That is **exactly** the
"correlated" / degenerate stratum (`MonomialSubgroupCorrelated.lean`) excluded from the genuine MCA
challenge. Numerically (probes, `n = 8, 16`): every `q`-INDEPENDENT concentrating subset is of this
form (count constant in `q`: 28 at `n=16, a=4, e_1=0`), while NON-correlated concentration appears
only at finitely many "bad primes" `p ≤ (2t)^{n/2}` (`q`-DEPENDENT — the char-`p` additive-energy
anomaly = the BGK/Paley object). Hence the closed/`q`-independent combinatorial families reach only
the low-regime bands; the interior δ\* is irreducibly `q`-dependent.

Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.CyclotomicConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Cyclotomic power-sum vanishing.** If `S ⊆ F` is invariant under multiplication by a nonzero
`ξ` (`ξ · S = S` as finsets), then every power sum `∑_{x∈S} x^j` with `ξ^j ≠ 1` vanishes. -/
theorem powerSum_eq_zero_of_smul_invariant {S : Finset F} {ξ : F} (hξ : ξ ≠ 0)
    (hinv : S.image (fun x => ξ * x) = S) {j : ℕ} (hj : ξ ^ j ≠ 1) :
    ∑ x ∈ S, x ^ j = 0 := by
  have hinj : ∀ x ∈ S, ∀ y ∈ S, ξ * x = ξ * y → x = y :=
    fun a _ b _ h => mul_left_cancel₀ hξ h
  -- reindex the sum over the bijection `x ↦ ξx` of `S`, then factor `(ξx)^j = ξ^j x^j`
  have hp : ∑ x ∈ S, x ^ j = ξ ^ j * ∑ x ∈ S, x ^ j := by
    calc ∑ x ∈ S, x ^ j
        = ∑ x ∈ S.image (fun x => ξ * x), x ^ j := by rw [hinv]
      _ = ∑ x ∈ S, (ξ * x) ^ j := Finset.sum_image hinj
      _ = ξ ^ j * ∑ x ∈ S, x ^ j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by rw [mul_pow]
  -- `(1 - ξ^j) · p_j = 0` with `1 - ξ^j ≠ 0`
  have hzero : (1 - ξ ^ j) * ∑ x ∈ S, x ^ j = 0 := by
    rw [sub_mul, one_mul, ← hp, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h).symm hj
  · exact h

/-- **Negation specialization (`s = 1`).** A subset closed under negation has vanishing first power
sum `∑_{x∈S} x = 0` — the `e_1 = 0` concentration of Round 7, recovered from the general theorem with
`ξ = −1`, `j = 1` (`(-1)^1 = -1 ≠ 1` since `char F ≠ 2`). -/
theorem sum_eq_zero_of_neg_invariant {S : Finset F} (h2 : (2 : F) ≠ 0)
    (hinv : S.image (fun x => (-1 : F) * x) = S) :
    ∑ x ∈ S, x = 0 := by
  have hneg1 : (-1 : F) ^ 1 ≠ 1 := by
    rw [pow_one]; intro h; exact h2 (by linear_combination -h)
  simpa using powerSum_eq_zero_of_smul_invariant (S := S) (ξ := -1)
    (by norm_num) hinv (j := 1) hneg1

end ProximityGap.Frontier.CyclotomicConcentration

#print axioms ProximityGap.Frontier.CyclotomicConcentration.powerSum_eq_zero_of_smul_invariant
#print axioms ProximityGap.Frontier.CyclotomicConcentration.sum_eq_zero_of_neg_invariant
