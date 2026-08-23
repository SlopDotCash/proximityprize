/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# The clean-range threshold for the cyclotomic-lattice halo core (#389)

The geometry-of-numbers half of the δ* open-core reformulation
(`docs/kb/deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`). A spurious balanced
`2r`-tuple of `μ_n` is a nonzero `z ∈ ℤ[ζ_n]` with `‖σ(z)‖_∞ ≤ 2r` (a signed sum of `2r` roots
of unity) that is divisible by a prime `𝔭` above `p` — equivalently its algebraic norm
`N(z) = Π_σ σ(z)` (a nonzero rational integer) is divisible by `p`. Two elementary facts pin the
**clean range** where no spurious tuple exists:

* the embedding bound `|N(z)| ≤ (2r)^{φ(n)}` (each of the `φ(n)` conjugates `σ(z)` is a signed
  sum of `2r` unit-modulus terms), and
* `𝔭 | z ⟹ p | N(z)`.

Below we discharge the resulting **logical skeleton**: a nonzero integer divisible by `p` and
bounded by `(2r)^{φ(n)}` forces `p ≤ (2r)^{φ(n)}`; contrapositively, when `(2r)^{φ(n)} < p` the
prime sublattice `𝔭` meets the box `B_{2r}` only at `0`, so `E_r = E_r^{(0)}` is **exactly** the
char-0 (antipodal/Gaussian) value — the proven clean range `r < log_n p`.

The two inputs above (the norm IS `p`-divisible; the norm IS `≤ (2r)^{φ(n)}`) are the genuine
number-theoretic content and are stated here as explicit named hypotheses on the norm value `N`,
per the project's modularity convention (CLAUDE.md §6) — the residual that the analytic-NT lever
(or a full `NumberField` formalization) must supply. The **open** part of the prize is NOT here:
it is the high-`r` regime `(2r)^{φ(n)} ≥ p` where the box does contain sublattice points and their
representation mass must be controlled (the Bourgain–Shkredov equidistribution wall).

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.CleanRangeNorm

/-- **Spurious tuples force the norm threshold.** If `N` is the (nonzero) algebraic norm of a
signed sum `z` of `2r` roots of unity in `ℤ[ζ_n]` with `φ = φ(n)` conjugates, so `|N| ≤ (2r)^φ`,
and `z` is divisible by a prime `𝔭` above `p` (hence `p ∣ N`), then `p ≤ (2r)^φ`. -/
theorem prime_le_of_spurious_norm
    {N : ℤ} {r φ p : ℕ}
    (hN0 : N ≠ 0)
    (hbound : N.natAbs ≤ (2 * r) ^ φ)
    (hdvd : (p : ℤ) ∣ N) :
    p ≤ (2 * r) ^ φ := by
  have hNabs : (p : ℤ) ∣ (N.natAbs : ℤ) := (Int.dvd_natAbs).mpr hdvd
  have hpdvd : p ∣ N.natAbs := by exact_mod_cast hNabs
  have hNpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN0
  exact le_trans (Nat.le_of_dvd hNpos hpdvd) hbound

/-- **Clean range: the prime sublattice misses the box.** Contrapositive of
`prime_le_of_spurious_norm`: if `(2r)^{φ(n)} < p` then there is NO nonzero signed sum `z` of `2r`
roots of unity divisible by `𝔭` — every balanced `2r`-tuple mod `p` is a genuine char-0 balanced
tuple. For `n = 2^k` (Lam–Leung) these are exactly the antipodal pairings, so `E_r = E_r^{(0)}`
is exactly the Gaussian value. This is the rigorous clean range `r < log_n p`. -/
theorem no_spurious_of_lt_prime
    {N : ℤ} {r φ p : ℕ}
    (hN0 : N ≠ 0)
    (hbound : N.natAbs ≤ (2 * r) ^ φ)
    (hlt : (2 * r) ^ φ < p) :
    ¬ (p : ℤ) ∣ N := by
  intro hdvd
  exact absurd (prime_le_of_spurious_norm hN0 hbound hdvd) (Nat.not_le.mpr hlt)

end ArkLib.ProximityGap.CleanRangeNorm

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CleanRangeNorm.prime_le_of_spurious_norm
#print axioms ArkLib.ProximityGap.CleanRangeNorm.no_spurious_of_lt_prime
