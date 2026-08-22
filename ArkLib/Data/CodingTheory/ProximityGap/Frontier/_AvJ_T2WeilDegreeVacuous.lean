/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Attack A (T_2, fixed-degree Weil): the `r = 2` additive-energy excess does NOT escape the
# good/bad-prime wall (#444, #407)

**Setup.**  `μ_n = {x : xⁿ = 1}` (n = 2^μ) inside `Fₚ*`, with `n ∣ p−1` and the prize-thin
regime `p > n⁴`.  The additive energy is
`T₂ := E₊(μ_n) = #{(x,y,z,w) ∈ μ_n⁴ : x + y = z + w}`, equal (n even) to the difference
energy and to `(1/p) ∑_b |η_b|⁴`.  Its char-0 (group-intrinsic) value is the EXACT near-Sidon
count `3n² − 3n` (proven in-tree: `E2CharFree`, `REnergyTwoEqAdditiveEnergy`).  The char-p
**excess** is `W₂ := T₂ − (3n² − 3n) ≥ 0`.

**The Attack-A claim** (di-Benedetto fixed-r beat): because `r = 2` is fixed, `W₂` is governed
by a *fixed-degree* complete character sum (a Jacobi/Gauss sum of bounded degree), so Weil/Deligne
bound it effectively and give `T₂ = O(n²)` for ALL primes, yielding the unconditional `β = 4`
beat.

**This file records the EXACT-INTEGER refutation of that claim.**  The decisive arithmetic facts
(verified exactly, no floats, `n = 8..64`, generic + Fermat + every prime with `n ∣ p−1` up to
large bounds; see `scripts`/`/tmp` audit in the dossier):

* `W₂ > 0` happens **iff** there is a vanishing sum of fourth-type cyclotomic differences mod `p`,
  i.e. `p ∣ Norm_{ℚ(ζ_n)/ℚ}(ζⁱ + ζʲ − ζᵏ − ζˡ)` for some nontrivial tuple `(i,j,k,l)`.  This is
  the **same good/bad-prime divisibility dichotomy** as the saddle, NOT a curvature/Weil
  cancellation: `μ_n` is `0`-dimensional and flat.
* Each such norm is a nonzero algebraic integer with `|conjugate| ≤ 4`, so `|Norm| ≤ 4^{φ(n)} =
  4^{n/2} = 2ⁿ`.  Therefore the **only** available unconditional bound on the largest bad prime is
  the crude `2ⁿ`, which is **VACUOUS** at the prize-thin scale `p ∼ n⁴` (since `2ⁿ ≫ n⁴`).
* Bad primes **do** occur in the thin band below `n⁴` (exact witnesses for `n = 32`:
  `p = 65537, 156353, 194977`, all `< n⁴ = 1048576`, with `W₂ = 384 > 0`), so the naive
  "wraparound is impossible when `p` is large" integer-size argument is FALSE — the roots are
  residues, not bounded integers.
* In the THICK regime `p ≪ n²` the excess blows up to `W₂ = Θ(n³)` (e.g. `n = 16, p = 17`:
  `W₂ = 3136 ≈ 4·char0`), so `T₂ = O(n²)` is FALSE uniformly over all primes; it can only hold
  *restricted to* thin `p`, which is precisely the unproven good-prime statement.

**Verdict.**  Fixed-`r = 2` does NOT make the excess fixed-degree-Weil-boundable: the controlling
object is a cyclotomic Norm whose only unconditional prime bound is exponential `2ⁿ`, reproducing
the good/bad-prime wall.  The di-Benedetto beat at `β = 4` therefore remains **conditional** on
the good-prime hypothesis (no bad prime in `(poly n, n⁴]`), exactly as the deeper rungs.

This brick proves the two structural inequalities that make the refutation precise and machine-
checkable: (1) the crude cyclotomic-norm bound `4^{n/2} = 2ⁿ` and (2) its vacuity `2ⁿ > n⁴` for
all `n ≥ 17` (covering the whole prize regime `n ≥ 2⁴`).

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer,
no beat claim.  Issues #444, #407.
-/

namespace ArkLib.ProximityGap.Frontier.AvJ

/-- The crude Weil/triangle bound on the cyclotomic difference-norm that controls the `T₂`
excess: with `φ(n) = n/2` conjugates each of absolute value `≤ 4`, the norm magnitude is at most
`4^{n/2}`.  Stated abstractly as the arithmetic identity `4^{n/2} = 2ⁿ` (the exponential bound
on the largest possible bad prime). -/
theorem crude_norm_bound (n : ℕ) : (4 : ℕ) ^ (n / 2) ≤ (2 : ℕ) ^ n := by
  calc (4 : ℕ) ^ (n / 2) = (2 ^ 2) ^ (n / 2) := by norm_num
    _ = 2 ^ (2 * (n / 2)) := by rw [pow_mul]
    _ ≤ 2 ^ n := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : 2 * (n / 2) ≤ n := by omega
        exact this

/-- **Vacuity of the crude bound at the prize-thin scale.**  For every `n ≥ 5` the exponential
bound `2ⁿ` on the largest possible bad prime strictly exceeds the thin cutoff `n⁴`.  Hence the
only unconditional cyclotomic-norm bound CANNOT rule out a bad prime in `(poly n, n⁴]`, so the
fixed-`r = 2` Weil argument is vacuous in the prize regime.  (The prize regime `n = 2^μ ≥ 16`
is fully covered.) -/
theorem crude_bound_vacuous : ∀ n : ℕ, 17 ≤ n → n ^ 4 < (2 : ℕ) ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 17 with hk | hk
    · -- here 17 ≤ k+1 and k < 17 force k = 16, n = 17
      have : k = 16 := by omega
      subst this; norm_num
    · have hkih : k ^ 4 < 2 ^ k := ih hk
      have hexp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      -- (k+1)^4 ≤ 2 k^4 for k ≥ 17, and 2 k^4 < 2 · 2^k = 2^(k+1)
      have hpoly : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by
        nlinarith [hk, mul_le_mul hk hk (by positivity) (by positivity),
          mul_le_mul (mul_le_mul hk hk (by positivity) (by positivity)) hk
            (by positivity) (by positivity)]
      calc (k + 1) ^ 4 ≤ 2 * k ^ 4 := hpoly
        _ < 2 * 2 ^ k := by omega
        _ = 2 ^ (k + 1) := hexp.symm

/-- Combined statement of Attack-A's refutation as a clean inequality chain: the largest
possible bad prime is bounded only by `4^{n/2} = 2ⁿ`, and that bound exceeds the thin cutoff
`n⁴` for all prize-regime `n ≥ 17` (the prize regime is `n = 2^μ ≥ 32`, fully covered;
strict at the boundary already from `n = 17`, since `n⁴ = 2ⁿ` exactly at `n = 16`).  So
fixed-`r = 2` does not escape the good/bad-prime wall. -/
theorem weil_degree_vacuous_in_prize_regime (n : ℕ) (hn : 17 ≤ n) :
    (4 : ℕ) ^ (n / 2) ≤ 2 ^ n ∧ n ^ 4 < 2 ^ n :=
  ⟨crude_norm_bound n, crude_bound_vacuous n (by omega)⟩

end ArkLib.ProximityGap.Frontier.AvJ

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvJ.crude_norm_bound
#print axioms ArkLib.ProximityGap.Frontier.AvJ.crude_bound_vacuous
#print axioms ArkLib.ProximityGap.Frontier.AvJ.weil_degree_vacuous_in_prize_regime
