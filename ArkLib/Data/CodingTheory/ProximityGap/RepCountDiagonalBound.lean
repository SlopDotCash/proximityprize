/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountDiagonalSymmetry
import ArkLib.Data.CodingTheory.ProximityGap.RepCountStepanovOrderTwo
import ArkLib.Data.CodingTheory.ProximityGap.StepanovContradictionEngine

/-!
# The order-2 Stepanov bound on the diagonal — completing `2·r(c) ≤ n+1` for ALL `c ≠ 0` (#389)

`RepCountStepanovOrderTwo.repCount_two_mul_le_of_pow_ne_one` gives `2·r(c) ≤ n+1` for the
off-diagonal cosets (`c^n ≠ 1`).  Its auxiliary `(c−X)^{n+1}+X^{n+1}−c` superficially degenerates
at `c = 1` (`Q(0) = c(c^n−1) = 0`), but the *same* polynomial still works there: at `c = 1`,

> `Q₁(X) = (1−X)^{n+1} + X^{n+1} − 1`

still vanishes to order 2 at every diagonal rep point (`y^n = 1 ∧ (1−y)^n = 1`), and it is nonzero
because `Q₁(2) = (−1)^{n+1} + 2^{n+1} − 1 = 2^{n+1} − 2 = 2·(2^n − 1) ≠ 0` for even `n` (the
leading `X^{n+1}` cancels, but the polynomial does not vanish).  So:

> **`repCount_one_two_mul_le`** — for `G = μ_n` with `n` even, `2 ≠ 0`, `2^n ≠ 1`:
> `2·r(1) ≤ n+1`.

Combined with the diagonal symmetry `repCount_eq_of_pow_eq_one` (`r(c) = r(1)` for `c^n = 1`),
this yields the **complete, uniform** explicit order-2 Stepanov bound:

> **`repCount_two_mul_le`** — for `G = μ_n` (`n = 2^μ` even), `2 ≠ 0`, `2^n ≠ 1`, every `c ≠ 0`
> (diagonal *and* off-diagonal) satisfies `2·r(c) ≤ n+1`.

Unconditional over any field meeting the parity/characteristic side conditions (`2^n ≠ 1` holds
automatically in the deployed regime `p > 2^n`); axiom-clean.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The order-2 Stepanov bound at the diagonal value `c = 1`.**  For `G = μ_n` with `n` even,
`2 ≠ 0` and `2^n ≠ 1`, the representation count at `1` satisfies `2·r(1) ≤ n+1`. -/
theorem repCount_one_two_mul_le {G : Finset F} {n : ℕ} (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (h2 : (2 : F) ≠ 0) (h2n : (2 : F) ^ n ≠ 1) :
    repCount G 1 * 2 ≤ n + 1 := by
  classical
  set Q : F[X] := (C 1 - X) ^ (n + 1) + X ^ (n + 1) - C 1 with hQ
  -- `Q ≠ 0`, since `Q(2) = (-1)^{n+1} + 2^{n+1} - 1 = 2^{n+1} - 2 = 2(2^n - 1) ≠ 0`.
  have hQ0 : Q ≠ 0 := by
    intro h
    have hev : Q.eval 2 = 0 := by rw [h, eval_zero]
    rw [hQ] at hev
    simp only [eval_sub, eval_add, eval_pow, eval_C, eval_X] at hev
    -- hev : (1 - 2)^(n+1) + 2^(n+1) - 1 = 0
    have hodd : Odd (n + 1) := Even.add_one hEven
    rw [show (1 : F) - 2 = -1 by ring, hodd.neg_one_pow] at hev
    -- hev : -1 + 2^(n+1) - 1 = 0
    apply h2n
    have : (2 : F) * ((2 : F) ^ n - 1) = 0 := by rw [pow_succ] at hev; linear_combination hev
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h2
    · linear_combination h'
  -- `deg Q ≤ n + 1`.
  have hdeg : Q.natDegree ≤ n + 1 := by rw [hQ]; compute_degree!
  -- Each diagonal rep point is a double root of `Q`.
  have hmult : ∀ y ∈ G.filter (fun y => 1 - y ∈ G), 2 ≤ rootMultiplicity y Q := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyG, hyyG⟩ := hy
    have hyn : y ^ n = 1 := (hGmem y).mp hyG
    have hyyn : (1 - y) ^ n = 1 := (hGmem (1 - y)).mp hyyG
    have hev : Q.eval y = 0 := by
      rw [hQ]
      simp only [eval_sub, eval_add, eval_pow, eval_C, eval_X]
      rw [pow_succ (1 - y) n, pow_succ y n, hyyn, hyn]; ring
    have hd : Q.derivative.eval y = 0 := by
      rw [hQ]
      simp only [derivative_sub, derivative_add, derivative_pow, derivative_C, derivative_X,
        Nat.add_sub_cancel, mul_one, sub_zero, zero_sub, mul_neg,
        eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_X]
      rw [hyyn, hyn]; ring
    have hr1 : (X - C y) ∣ Q := dvd_iff_isRoot.mpr hev
    obtain ⟨g, hg⟩ := hr1
    have hgy : g.eval y = 0 := by
      have hQd : Q.derivative = g + (X - C y) * g.derivative := by
        rw [hg, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
      rw [hQd] at hd
      simpa [sub_self] using hd
    obtain ⟨g2, hg2⟩ := dvd_iff_isRoot.mpr hgy
    have hdvd : (X - C y) ^ 2 ∣ Q := ⟨g2, by rw [hg, hg2]; ring⟩
    exact (le_rootMultiplicity_iff hQ0).mpr hdvd
  calc repCount G 1 * 2
      = (G.filter (fun y => 1 - y ∈ G)).card * 2 := rfl
    _ ≤ Q.natDegree :=
        StepanovContradictionEngine.stepanov_card_mul_M_le_natDegree Q hQ0 _ 2 hmult
    _ ≤ n + 1 := hdeg

/-- **The complete order-2 Stepanov bound.**  For `G = μ_n` (`n` even), `2 ≠ 0`, `2^n ≠ 1`, every
nonzero `c` — diagonal or off-diagonal — satisfies `2·r(c) ≤ n+1`. -/
theorem repCount_two_mul_le {G : Finset F} {n : ℕ} (hn : 1 ≤ n) (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (h2 : (2 : F) ≠ 0) (h2n : (2 : F) ^ n ≠ 1)
    {c : F} (hc0 : c ≠ 0) :
    repCount G c * 2 ≤ n + 1 := by
  by_cases hcn : c ^ n = 1
  · rw [repCount_eq_of_pow_eq_one hn hGmem hcn]
    exact repCount_one_two_mul_le hEven hGmem h2 h2n
  · exact repCount_two_mul_le_of_pow_ne_one hn hGmem hc0 hcn

end ArkLib.ProximityGap.AdditiveEnergyRepBound
