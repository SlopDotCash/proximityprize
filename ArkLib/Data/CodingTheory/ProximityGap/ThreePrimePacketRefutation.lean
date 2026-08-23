/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #232 — de Bruijn's packet conjecture FAILS at three primes (O105)

O104 pinned the witness numerically; this file lands the formal refutation.  At
`n = 30 = 2·3·5`, the exponent set `S = {5, 6, 12, 18, 24, 25}`:

* **vanishes**: `Σ_{e∈S} ζ₃₀^e = 0` — it is `(μ₅-relation) − (μ₃-relation)` with
  the signs absorbed through `ζ₃₀^15 = −1`
  (`three_prime_witness_vanishes`, by `linear_combination` over the three
  cyclotomic relations);
* **is not an ℕ-combination of full prime packets**: no functions
  `A B C : ℕ → ℕ` satisfy `𝟙_S e = A (e%15) + B (e%10) + C (e%6)` on `[0, 30)` —
  four instances (`e = 5, 20, 15, 11`) force `A 5 = B 5 = C 5 = 0` against
  `A 5 + B 5 + C 5 = 1` (`three_prime_witness_not_packet_combination`).

So the packet-combination classification proved at two-prime moduli
(O94 indicator, O103 weighted) is SHARP: it genuinely fails at the first
three-prime modulus, exactly as the literature records (de Bruijn 1953's
conjecture refuted; Lam–Leung J. Algebra 224 (2000) §5).  The honest positive
target past two primes is the ℕ-span theorem `|w| ∈ ℕp₁ + … + ℕp_k`
(Lam–Leung's main theorem — genuinely different tools, open here).

Witness verified first (exact ℤ[x]/Φ₃₀ arithmetic, this session's probe run):
vanishing TRUE; contains no full μ₂-, μ₃-, or μ₅-packet.
-/

namespace ThreePrimePacketRefutation

open Finset

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- The three cyclotomic relations at `n = 30`, extracted once. -/
private lemma relations {ζ : L} (hζ : IsPrimitiveRoot ζ 30) :
    (1 + ζ ^ 6 + ζ ^ 12 + ζ ^ 18 + ζ ^ 24 = 0)
    ∧ (1 + ζ ^ 10 + ζ ^ 20 = 0) ∧ ζ ^ 15 = -1 := by
  have h30 : (0 : ℕ) < 30 := by norm_num
  have hη : IsPrimitiveRoot (ζ ^ 6) 5 := hζ.pow h30 (by norm_num)
  have hω2 : IsPrimitiveRoot (ζ ^ 10) 3 := hζ.pow h30 (by norm_num)
  have hω : IsPrimitiveRoot (ζ ^ 5) 6 := hζ.pow h30 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have h := hη.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ← pow_mul] at h
    norm_num at h
    linear_combination h
  · have h := hω2.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ← pow_mul] at h
    norm_num at h
    linear_combination h
  · have hsq : ζ ^ 15 * ζ ^ 15 = 1 := by
      rw [← pow_add]
      norm_num
      exact hζ.pow_eq_one
    have hne : ζ ^ 15 ≠ 1 :=
      hζ.pow_ne_one_of_pos_of_lt (by norm_num : (15:ℕ) ≠ 0)
        (by norm_num : (15:ℕ) < 30)
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h hne
    · exact h

omit [CharZero L] in
/-- **The witness vanishes**: `ζ₃₀⁵ + ζ₃₀⁶ + ζ₃₀¹² + ζ₃₀¹⁸ + ζ₃₀²⁴ + ζ₃₀²⁵ = 0`
— the μ₅-relation minus the μ₃-relation with signs absorbed via `ζ^15 = −1`. -/
theorem three_prime_witness_vanishes {ζ : L} (hζ : IsPrimitiveRoot ζ 30) :
    ζ ^ 5 + ζ ^ 6 + ζ ^ 12 + ζ ^ 18 + ζ ^ 24 + ζ ^ 25 = 0 := by
  obtain ⟨h5, h3, h15⟩ := relations hζ
  linear_combination h5 - h3 + (ζ ^ 5 + ζ ^ 10) * h15

/-- **The witness is not an ℕ-packet-combination**: no `A B C : ℕ → ℕ` realize the
indicator of `{5, 6, 12, 18, 24, 25}` as `A (e%15) + B (e%10) + C (e%6)` on
`[0, 30)` — the support contains no full prime packet, so the four instances
`e = 5, 20, 15, 11` are contradictory. -/
theorem three_prime_witness_not_packet_combination :
    ¬ ∃ A B C : ℕ → ℕ, ∀ e < 30,
      (if e ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ) then 1 else 0)
        = A (e % 15) + B (e % 10) + C (e % 6) := by
  rintro ⟨A, B, C, h⟩
  have h5 := h 5 (by norm_num)
  have h20 := h 20 (by norm_num)
  have h15 := h 15 (by norm_num)
  have h11 := h 11 (by norm_num)
  norm_num at h5 h20 h15 h11
  omega

omit [CharZero L] in
/-- **DE BRUIJN'S PACKET CONJECTURE FAILS AT THREE PRIMES** (the combined
refutation, `n = 30 = 2·3·5`): a vanishing `{0,1}`-sum of 30-th roots of unity
exists whose weight function is NOT an ℕ-combination of full prime packets — the
two-prime classification (O94/O103) is sharp. -/
theorem debruijn_packet_conjecture_fails_three_primes {ζ : L}
    (hζ : IsPrimitiveRoot ζ 30) :
    (∑ e ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ), ζ ^ e = 0)
    ∧ ¬ ∃ A B C : ℕ → ℕ, ∀ e < 30,
        (if e ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ) then 1 else 0)
          = A (e % 15) + B (e % 10) + C (e % 6) := by
  constructor
  · have hsum : ∑ e ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ), ζ ^ e
        = ζ ^ 5 + ζ ^ 6 + ζ ^ 12 + ζ ^ 18 + ζ ^ 24 + ζ ^ 25 := by
      simp [Finset.sum_insert, Finset.mem_insert]
      ring
    rw [hsum]
    exact three_prime_witness_vanishes hζ
  · exact three_prime_witness_not_packet_combination

end ThreePrimePacketRefutation

#print axioms ThreePrimePacketRefutation.three_prime_witness_vanishes
#print axioms ThreePrimePacketRefutation.three_prime_witness_not_packet_combination
#print axioms ThreePrimePacketRefutation.debruijn_packet_conjecture_fails_three_primes
