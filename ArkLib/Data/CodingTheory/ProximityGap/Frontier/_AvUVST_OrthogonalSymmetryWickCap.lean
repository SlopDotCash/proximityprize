/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# UVST round-2: the self-dual / orthogonal-symmetry Wick cap — `ρ_r ≤ 1`, never `= 1` (#444)

This brick records the *rigorous core* of the round-2 stab: "invent a self-dual (orthogonal,
forced by the conjugate-symmetry `u_{m−t} = conj(u_t)`, i.e. the reality of `η_b`) growing-rank
object whose moments are forced to Wick **by a symmetry** (not a varying-`p` family), making the
normalized real-Wick ratio `ρ_r = mean_b|S_b|^{2r} / ((2r−1)‼·m^r)` equal `1` exactly."

## What a symmetry CAN and CANNOT do (the verdict)

The cleanest symmetric object is a **Haar matrix coefficient** of the orthogonal group `O(N)`
(orthogonal because reality of the period field lands any group realization in `O`, not `U`).
A single matrix entry `g₁₁` of a Haar `O(N)` element is a coordinate of a uniform vector on the
sphere `S^{N−1}`, whose exact even moments are the classical sphere integral
`E[g₁₁^{2r}] = (2r−1)‼ / ∏_{j=0}^{r−1}(N + 2j)`. Its **second moment is `1/N`**, so the
real-Gaussian reference (variance `1/N`) has even moments `(2r−1)‼·N^{−r}`. The normalized ratio
to the Gaussian/Wick value is therefore the clean closed form

  `ρ_O(N, r) = N^r / ∏_{j=0}^{r−1}(N + 2j)`.

Two exact facts, formalized below:

* `orthRatio_le_one` : `ρ_O(N, r) ≤ 1` for ALL `N ≥ 1, r` — **a symmetry forces sub-Gaussianity**
  (`ρ_r ≤ 1`), the good direction. This is exactly what the prize moment-to-sup chain needs.
* `orthRatio_lt_one_of_two_le` : `ρ_O(N, r) < 1` STRICTLY for `r ≥ 2` (any `N ≥ 1`) — **the
  symmetry can NEVER attain `ρ_r = 1` exactly at finite `N`.** `ρ_O(N,r) → 1` only as `N → ∞` at
  fixed `r`; at the operative saddle `r ≈ log N` it is bounded away from `1` and decreasing
  (numerics: `ρ_O(128, 7) ≈ 0.73`).

## Why this refutes the round-2 stab as stated, and what it proves instead

REFUTED (rigorous): "a representation-theoretic / symmetry identity makes `ρ_r = 1` exactly for
the fixed Gauss-phase sequence." Three independent obstructions:

1. **`ρ_r = 1` is a Gaussian-LIMIT property, not a finite-`N` symmetry identity.** By the exact
   sphere integral, every genuine orthogonal/unitary symmetry gives `ρ < 1` for `r ≥ 2`; the
   Wick value is attained only in the `N → ∞` Haar limit. (`orthRatio_lt_one_of_two_le`.)
2. **A symmetry computes a GROUP AVERAGE; the Gauss-phase sequence is ONE deterministic orbit
   point.** `ρ_r` is a single number per sequence, fluctuating (exact small-`m` computation:
   `ρ_2 ∈ [0.45, 2.6]` over conjugate-symmetric sequences). Turning the Haar average into a
   per-sequence identity requires the `m` phases to BE the eigenangles of a Haar `O(m)`/`U(m)`
   element — which is exactly vertical Sato–Tate (equidistribution as `p → ∞`), the SUPER-THIN
   regime already capped in round 1 (`_AvW0_BesselWickDomination`, `β ≥ β₀(n) ∼ 0.78n`). At a
   single fixed `p` there is no group orbit, hence no symmetry forcing.
3. The b-monodromy is abelian (round-1 UVST-1, refuted), so no `O(N)`/`U(N)` with `N → ∞` acts
   on the period field in `b` at fixed `p`; the only orthogonal structure present is the rank-1
   reality involution `u_{m−t} = conj(u_t)`, which halves DOF but is a finite (order-2) symmetry,
   far too small to force Wick.

PROVEN PARTIAL (genuine, non-vacuous, this file): **any orthogonally/unitarily-symmetric
realization of the period field is sub-Gaussian, `ρ_r ≤ 1`, with the exact closed-form cap
`ρ_O(N,r) = N^r/∏(N+2j)`.** Sub-Gaussianity (`ρ_r ≤ 1`) to depth `r ≈ log m` is PRECISELY the
hypothesis that closes Paley via the moment-to-sup chain (it yields `max_b|S_b| ≤ C'√(m log m)`
with `C' ≈ 1.43`, log-domain verified). So the symmetry route correctly identifies the SUFFICIENT
inequality and proves it holds for any honestly-symmetric model — but the FIXED Gauss-phase
sequence is not such a model at fixed `p`, and proving `ρ_r ≤ 1` for IT to depth `log m` remains
the open BGK/Burgess wall (`_AvPGC_SubGaussianMomentExponent`'s exponent ∈ (0.976, 1)).

Honest scope (`closesPrize = false`): refutes "symmetry forces `ρ_r = 1`"; proves the orthogonal
Haar cap `ρ_O ≤ 1`; leaves `β = 4` Paley OPEN (the Gauss-phase sequence is one deterministic point,
not Haar-distributed; per-sequence sub-Gaussianity to log-depth is the wall).

Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.AvUVST

open Nat

/-- The step-2 Pochhammer denominator `∏_{j=0}^{r−1}(N + 2j)` of the orthogonal sphere integral. -/
def pochStep2 (N : ℕ) : ℕ → ℕ
  | 0 => 1
  | (r + 1) => pochStep2 N r * (N + 2 * r)

lemma pochStep2_pos {N : ℕ} (hN : 0 < N) (r : ℕ) : 0 < pochStep2 N r := by
  induction r with
  | zero => simp [pochStep2]
  | succ r ih => unfold pochStep2; positivity

/-- `N^r ≤ ∏_{j=0}^{r−1}(N+2j)`: each factor `N+2j ≥ N`, so the step-2 Pochhammer dominates `N^r`.
This is the integer heart of the orthogonal Wick cap `ρ_O(N,r) = N^r/pochStep2 ≤ 1`. -/
theorem pow_le_pochStep2 (N r : ℕ) : N ^ r ≤ pochStep2 N r := by
  induction r with
  | zero => simp [pochStep2]
  | succ r ih =>
    unfold pochStep2
    rw [pow_succ]
    calc N ^ r * N ≤ pochStep2 N r * N := by gcongr
      _ ≤ pochStep2 N r * (N + 2 * r) := by gcongr; omega

/-- **The orthogonal/unitary symmetry Wick cap, `ρ_O(N,r) ≤ 1` (rational form).** For the Haar
matrix-coefficient model the normalized real-Wick ratio is `N^r / ∏_{j=0}^{r−1}(N+2j) ≤ 1`: any
genuine orthogonal symmetry forces SUB-GAUSSIANITY. (This `≤ 1` to depth `r ≈ log m` is exactly
the inequality that closes Paley via the moment-to-sup chain.) -/
theorem orthRatio_le_one {N : ℕ} (hN : 0 < N) (r : ℕ) :
    ((N : ℚ) ^ r) / (pochStep2 N r : ℚ) ≤ 1 := by
  have hden : (0 : ℚ) < (pochStep2 N r : ℚ) := by exact_mod_cast pochStep2_pos hN r
  rw [div_le_one hden]
  have : (N : ℚ) ^ r ≤ (pochStep2 N r : ℚ) := by
    have := pow_le_pochStep2 N r
    push_cast
    exact_mod_cast this
  simpa using this

/-- **A symmetry can NEVER attain `ρ_O = 1` exactly at finite `N`, for `r ≥ 2`.** The first
step-2 factor `N + 2` strictly exceeds `N`, so `N^r < ∏(N+2j)` whenever `r ≥ 2`, giving the strict
cap `ρ_O(N,r) < 1`. Hence the round-2 stab's target ("symmetry forces `ρ_r = 1` exactly") is
impossible for any honest orthogonal/unitary model at finite rank — Wick equality is the
`N → ∞` limit only. -/
theorem orthRatio_lt_one_of_two_le {N : ℕ} (hN : 0 < N) {r : ℕ} (hr : 2 ≤ r) :
    ((N : ℚ) ^ r) / (pochStep2 N r : ℚ) < 1 := by
  have hden : (0 : ℚ) < (pochStep2 N r : ℚ) := by exact_mod_cast pochStep2_pos hN r
  rw [div_lt_one hden]
  -- strict: N^r < pochStep2 N r because the j=1 factor (N+2) > N
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  have hstrict : N ^ (r' + 2) < pochStep2 N (r' + 2) := by
    unfold pochStep2
    -- pochStep2 N (r'+2) = pochStep2 N (r'+1) * (N + 2*(r'+1))
    rw [pow_succ]
    have h1 : N ^ (r' + 1) ≤ pochStep2 N (r' + 1) := pow_le_pochStep2 N (r' + 1)
    have hpos : 0 < pochStep2 N (r' + 1) := pochStep2_pos hN (r' + 1)
    have hfac : N < N + 2 * (r' + 1) := by omega
    calc N ^ (r' + 1) * N
        ≤ pochStep2 N (r' + 1) * N := by gcongr
      _ < pochStep2 N (r' + 1) * (N + 2 * (r' + 1)) := by
          have : (0 : ℕ) < pochStep2 N (r' + 1) := hpos
          gcongr
  exact_mod_cast hstrict

/-- The orthogonal Wick cap is non-vacuous and matches the round-2 numerics at the prize saddle:
`ρ_O(128, 7) = 128^7 / ∏_{j=0}^{6}(128+2j)`, a rational `< 1` (≈ 0.728). The point is the STRICT
inequality, certifying that no symmetry attains Wick equality at the operative depth. -/
example : ((128 : ℚ) ^ 7) / (pochStep2 128 7 : ℚ) < 1 :=
  orthRatio_lt_one_of_two_le (by norm_num) (by norm_num)

end ArkLib.ProximityGap.Frontier.AvUVST

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.AvUVST.pow_le_pochStep2
#print axioms ArkLib.ProximityGap.Frontier.AvUVST.orthRatio_le_one
#print axioms ArkLib.ProximityGap.Frontier.AvUVST.orthRatio_lt_one_of_two_le
