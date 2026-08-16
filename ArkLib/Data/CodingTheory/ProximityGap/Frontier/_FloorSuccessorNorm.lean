/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-!
# The floor-successor obstruction norm forces the least prime `≡ 1 mod n` (#466, lane F1)

**The round-7 S3 arithmetic mechanism, formalized at the two decided levels `n = 16, 32`.**

## The mechanism (verified computationally, char-0, in `scripts/probes/probe_466_successor_norm.py`)

For `n = 2^k` the floor-bad realizability predicate of a structured "adjacent-7th-type"
pattern `A ⊆ ℤ/n` is: with `V_A(t) = ∏_{j ∈ A} (t − ζ^j)` (monic, `ζ` a primitive `n`-th root
of unity, `Φ_n = x^{n/2}+1`) and `r(t) = t^{3n/4} mod V_A(t)`, the obstruction coefficients
`r_k` for `k ∈ [n/2+1, |A|−1]` are algebraic integers of `ℤ[ζ_n]`.  A pattern `A` is
realizable over `𝔽_p` (`p ≡ 1 mod n`) — i.e. `p` is floor-bad witnessed by `A` — only if every
`r_k(A)` lies in the split prime `P = (p, ζ − g₀)`, hence

  **necessary condition**:  `p ∣ Norm_{ℚ(ζ_n)/ℚ}(r_k(A))`  for every obstruction index `k`.

Define the *obstruction norm* `R_n(A) := gcd_k Norm(r_k(A)) ∈ ℤ` (`p`-independent, char-0).
Then `p` floor-bad ⟹ `p ∣ R_n(A)` for the witnessing pattern.  The exact char-0 computation
(EXACT `ℤ[ζ_n]` arithmetic + `sympy` resultant, `probe_466_successor_norm.py`) gives, for
**every** realizable witness:

* `n = 16`: single obstruction `r_9`, `R_16 = Norm(r_9) = 2^3 · 17^2 = 2312`
  (identical across all `160` realizable patterns — one distinct norm tuple).
* `n = 32`: three obstructions, `Norm(r_17)=2^9·97^4`, `Norm(r_18)=2^6·31^2·97^2`,
  `Norm(r_19)=2^9·97^2`, so `R_32 = gcd = 2^6 · 97^2 = 602176`
  (`31 ≡ −1 mod 32` is off-regime; `97 ≡ 1 mod 32`).

The decisive arithmetic fact, in both cases, is that the **only** prime factor of `R_n` that is
`≡ 1 mod n` is the least such prime `p_min(n)` — `p_min(16)=17`, `p_min(32)=97`.  Combined with
the necessary condition this pins the floor-bad set to `{p_min(n)}`.

## What is proved here (axiom-clean)

This file formalizes the **arithmetic reduction step** of the mechanism — the pure integer
divisibility fact — for the two levels the exhaustive scan decided (`n = 16, 32`):

  `floorObstructionNorm_forces_pmin_16` :
    `p.Prime → p % 16 = 1 → p ∣ 2312 → p = 17`
  `floorObstructionNorm_forces_pmin_32` :
    `p.Prime → p % 32 = 1 → p ∣ 602176 → p = 97`

Together with the (computationally verified, *not* here formalized) facts that
`R_16 = 2312`, `R_32 = 602176` are the char-0 obstruction norms and that floor-bad ⟹ `p ∣ R_n`,
these give `floor-bad(16) ⊆ {17}` and `floor-bad(32) ⊆ {97}` purely arithmetically.

**Honesty.**  Nothing here claims to *prove* `floor-bad(n) = {p_min(n)}` in Lean: the
resultant identities `R_16 = 2312`, `R_32 = 602176` and the "floor-bad ⟹ `p ∣ R_n`" necessary
condition are verified *computationally* (exact `ℤ[ζ]` arithmetic), not in Lean.  What is
axiom-clean here is only the final divisibility ⇒ identification step, and the recorded
constants.  The naive hope of *resolving* the compute-undecidable `floor-bad(64)` by evaluating
one canonical resultant is **REFUTED** in the probe: the obstruction norm is genuinely
pattern-dependent (an arbitrary structured pattern's per-`k` norm factor sets have *empty*
`≡1 mod n` intersection), so no single char-0 resultant replaces the `2.2·10^{15}`-pattern
search — see the module docstring tail and `_out_466_successor_norm.txt`.
-/

namespace ArkLib.ProximityGap.Frontier.FloorSuccessorNorm

/-- `R_16`, the char-0 floor obstruction norm at `n = 16` (`= 2^3 · 17^2`). -/
def R16 : ℕ := 2312

/-- `R_32`, the gcd of the three char-0 floor obstruction norms at `n = 32` (`= 2^6 · 97^2`). -/
def R32 : ℕ := 602176

theorem R16_factorization : R16 = 2 ^ 3 * 17 ^ 2 := by norm_num [R16]

theorem R32_factorization : R32 = 2 ^ 6 * 97 ^ 2 := by norm_num [R32]

/-- **`n = 16` floor-successor reduction.**  Any prime `p ≡ 1 (mod 16)` dividing the char-0
obstruction norm `R_16 = 2312` is exactly the least prime `≡ 1 mod 16`, namely `17`.  This is
the arithmetic germ of `floor-bad(16) = {17}`. -/
theorem floorObstructionNorm_forces_pmin_16
    (p : ℕ) (hp : p.Prime) (hmod : p % 16 = 1) (hdvd : p ∣ R16) : p = 17 := by
  rw [R16_factorization] at hdvd
  rcases (hp.dvd_mul).mp hdvd with h2 | h17
  · -- `p ∣ 2^3` ⟹ `p = 2`, impossible since `2 % 16 = 2 ≠ 1`
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    omega
  · -- `p ∣ 17^2` ⟹ `p = 17`
    have hp17 : p ∣ 17 := hp.dvd_of_dvd_pow h17
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp17

/-- **`n = 32` floor-successor reduction.**  Any prime `p ≡ 1 (mod 32)` dividing the char-0
obstruction gcd-norm `R_32 = 602176` is exactly the least prime `≡ 1 mod 32`, namely `97`.
The off-regime prime `31 ≡ −1 mod 32` cannot occur because it is `≡ −1`, and `2` is ruled out by
the residue condition; the gcd has already stripped `31`. -/
theorem floorObstructionNorm_forces_pmin_32
    (p : ℕ) (hp : p.Prime) (hmod : p % 32 = 1) (hdvd : p ∣ R32) : p = 97 := by
  rw [R32_factorization] at hdvd
  rcases (hp.dvd_mul).mp hdvd with h2 | h97
  · -- `p ∣ 2^6` ⟹ `p = 2`, impossible since `2 % 32 = 2 ≠ 1`
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    omega
  · -- `p ∣ 97^2` ⟹ `p = 97`
    have hp97 : p ∣ 97 := hp.dvd_of_dvd_pow h97
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp97

/-- `17` is a prime `≡ 1 mod 16` dividing `R_16` — the reduction is non-vacuous. -/
theorem seventeen_witnesses_16 :
    Nat.Prime 17 ∧ 17 % 16 = 1 ∧ (17 ∣ R16) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [R16_factorization]; decide

/-- `97` is a prime `≡ 1 mod 32` dividing `R_32` — the reduction is non-vacuous. -/
theorem ninetyseven_witnesses_32 :
    Nat.Prime 97 ∧ 97 % 32 = 1 ∧ (97 ∣ R32) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [R32_factorization]; decide

end ArkLib.ProximityGap.Frontier.FloorSuccessorNorm

#print axioms ArkLib.ProximityGap.Frontier.FloorSuccessorNorm.floorObstructionNorm_forces_pmin_16
#print axioms ArkLib.ProximityGap.Frontier.FloorSuccessorNorm.floorObstructionNorm_forces_pmin_32
