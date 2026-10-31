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
of unity) that is divisible by a specified prime `𝔭` above `p`. Its algebraic norm
`N(z) = Π_σ σ(z)` (a nonzero rational integer) is then divisible by `p`. The converse is weaker:
`p ∣ N(z)` only says that **some** prime above `p` divides `z`, not necessarily the specified
`𝔭`. Two elementary facts pin a **clean range** where no spurious tuple exists:

* the embedding bound `|N(z)| ≤ (2r)^{φ(n)}` (each of the `φ(n)` conjugates `σ(z)` is a signed
  sum of `2r` unit-modulus terms), and
* `𝔭 | z ⟹ p | N(z)` (one direction only).

Below we discharge the resulting **logical skeleton**: a nonzero integer divisible by `p` and
bounded by `(2r)^{φ(n)}` forces `p ≤ (2r)^{φ(n)}`; contrapositively, when `(2r)^{φ(n)} < p`, i.e.
`r < p^{1/φ(n)}/2`, no nonzero element of the box `B_{2r}` lies in any prime above `p`, so (given
the two inputs above) `E_r = E_r^{(0)}` equals the char-0 balanced-tuple count.

Scope corrections (audit PG-044):

* The clean-range condition proved here is `(2r)^{φ(n)} < p`, equivalently `r < p^{1/φ(n)}/2`.
  It is **not** `r < log_n p`; neither condition implies the other in general (e.g. `n = 32`,
  `p = 65537`, `r = 3` has `3 < log₃₂ p` but `6^16 > p`; `n = 8`, `p = 65537`, `r = 6` has
  `12^4 = 20736 < p` but `6 > log₈ p`).
* For `n = 2^k`, Lam–Leung identifies char-0 balanced tuples with antipodal pairings, so the
  char-0 count is **at most** the Gaussian/Wick value `(2r-1)!!·|G|^r` (a union bound over
  pairings), not equal to it in general: for `G = {-1, 1}`, `r = 2` the antipodal four-term
  zero-sum count is `6`, while `(2r-1)!!·|G|^r = 12`. Neither the Lam–Leung input nor this
  count is formalized here.

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
`prime_le_of_spurious_norm`: if `(2r)^{φ(n)} < p` then a nonzero integer `N` with
`|N| ≤ (2r)^{φ(n)}` is not divisible by `p`. Applied (given the norm-bound and `𝔭 ∣ z ⟹ p ∣ N(z)`
inputs, which are not formalized here) to the norm of a nonzero signed sum `z` of `2r` roots of
unity, no such `z` is divisible by `𝔭`, so every balanced `2r`-tuple mod `p` is a char-0 balanced
tuple. The clean range is `(2r)^{φ(n)} < p`, i.e. `r < p^{1/φ(n)}/2` (not `r < log_n p`). For
`n = 2^k` (Lam–Leung) the char-0 count is the antipodal-pairing count, which is at most (not
equal to) the Gaussian value `(2r-1)!!·|G|^r`. -/
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
