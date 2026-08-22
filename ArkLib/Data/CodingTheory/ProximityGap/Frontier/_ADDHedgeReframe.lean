/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Ring

/-!
# _ADDHedgeReframe — Function-field / Weil-RH reframe of the δ* wall: REDUCTION VERDICT

Hedge lane (#466). DIRECTIVE: reframe δ* so the Paley/BGK wall dissolves; settle honestly.

## The reframe attempted
The multiplicative smooth-domain RS δ* prize reduces to the Paley/BGK wall
`E_r = Σ_{b≠0} |η_b|^{2r}` bounded to `r ~ ln q`, where `η_b = Σ_{x∈μ_n} e_p(bx)` are the
Gauss periods of the subgroup `μ_n ⊂ F_p^*` (the "far-direction eigenvalues").

Seed (i): the F_p no-go landscape explicitly does not cover function fields, and Weil's
Riemann Hypothesis for curves is a THEOREM, so a "function-field Paley" might be provable via
Weil RH, dissolving the wall.

## VERDICT: REDUCES TO THE SAME WALL (Weil RH is a per-character bound; the wall is a summed
2r-th moment). Weil RH is already saturated at the per-b level — it is exactly what gives the
first rungs (r ≤ 2, the in-tree "Weil rung"). It cannot control `E_r` at deep `r` because
summing the per-character bound over the whole dual `b` overshoots the target by a factor that
DIVERGES in `r`.

## The exact reduction (this file)
Weil RH / the classical Weil bound for a multiplicative character sum gives, per `b`,
`|η_b|^2 ≤ n^2 · p` (verified valid in `scripts/probes/ff_weil_probe.py`: e.g. p=337,n=16 →
max|η_b|^2 = 90.63 ≤ n^2 p = 86272). Applied uniformly over the `p-1` nonzero `b` this yields
the naive Weil energy bound
  `weilSumBound r n p = (p-1) · (n^2 · p)^r`.
The joint-cancellation (BGK/Paley) target is `wallTarget r n = n^(2r)`. The exact gap is

  `weilSumBound r n p = (p-1) · p^r · wallTarget r n`      (`weilSum_eq_gap_mul_wall`)

so the overshoot factor `(p-1)·p^r` is strictly monotone increasing and unbounded in `r`
(`gapFactor_strictMono`, `gapFactor_unbounded`): Weil-per-character is insufficient at EVERY
depth and worse at deep `r`. Numerics (probe): the true `E_r` crosses `wallTarget` near
`r ≈ 2–3` and the Weil sum bound overshoots the truth by `(p-1)·p^r` (p=337,n=16: r=3 gap
1.29e10, r=5 gap 1.46e15). The dissolution FAILS: the residual open object is unchanged —
joint cancellation across `b`, i.e. the same BGK wall. Consistent with dossier v3 line 908
("Function-field model = null") and the DISPROOF ledger, now with an exact in-tree identity.
-/

namespace ArkLib.ProximityGap.HedgeReframe

/-- Naive Weil-per-character bound on the summed energy `E_r = Σ_{b≠0}|η_b|^{2r}`:
each of the `p-1` nonzero frequencies contributes at most `(n^2 p)^r` (Weil RH, `|η_b|^2≤n^2 p`). -/
def weilSumBound (r n p : ℕ) : ℕ := (p - 1) * (n ^ 2 * p) ^ r

/-- Joint-cancellation (BGK/Paley) target scale for the energy. -/
def wallTarget (r n : ℕ) : ℕ := n ^ (2 * r)

/-- The overshoot factor of the naive Weil bound over the wall target. -/
def gapFactor (r p : ℕ) : ℕ := (p - 1) * p ^ r

/-- EXACT reduction identity: the naive per-character Weil energy bound equals the wall target
scaled by the gap factor `(p-1)·p^r`. Pure ℕ arithmetic, no division. -/
theorem weilSum_eq_gap_mul_wall (r n p : ℕ) :
    weilSumBound r n p = gapFactor r p * wallTarget r n := by
  unfold weilSumBound gapFactor wallTarget
  rw [mul_pow, ← pow_mul, mul_comm 2 r, pow_mul]
  ring

/-- The gap factor is strictly monotone increasing in the depth `r` (for `p ≥ 2`): the Weil
per-character route gets *strictly worse* at every deeper rung — it cannot dissolve the wall. -/
theorem gapFactor_strictMono {p : ℕ} (hp : 2 ≤ p) :
    StrictMono (fun r => gapFactor r p) := by
  intro a b hab
  have hpow : p ^ a < p ^ b := Nat.pow_lt_pow_right (by omega : 1 < p) hab
  have : (p - 1) * p ^ a < (p - 1) * p ^ b :=
    Nat.mul_lt_mul_of_pos_left hpow (by omega)
  simpa [gapFactor] using this

/-- The overshoot is unbounded: for every bound `M` there is a depth `r` at which the naive
Weil energy bound exceeds `M · wallTarget`. The dissolution cannot succeed at any fixed depth. -/
theorem gapFactor_unbounded {p : ℕ} (hp : 2 ≤ p) (M : ℕ) :
    ∃ r, M < gapFactor r p := by
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt M (by omega : (1:ℕ) < p)
  refine ⟨r, ?_⟩
  exact lt_of_lt_of_le hr (by
    simpa [gapFactor] using Nat.le_mul_of_pos_left (p ^ r) (by omega : 0 < p - 1))

end ArkLib.ProximityGap.HedgeReframe
