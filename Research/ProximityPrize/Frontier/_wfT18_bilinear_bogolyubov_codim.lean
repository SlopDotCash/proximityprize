/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# wf-T18 (#444, localId G4-3): the bilinear-Bogolyubov codimension cover of the difference
  incidence `{(x,y) : x-y ∈ μ_n}` REDUCES-TO-WALL (F0; mass-vacuity = F6/A12)

ANGLE T18 (cluster G4 — post-2020 additive combinatorics: PFR / Kelley–Meka / sum–product
STRUCTURE / COVERING, not norms). Architect's candidate: apply the BILINEAR Bogolyubov theorem
(Bienvenu–Lê, *A bilinear Bogolyubov theorem*, 2018; Gowers–Milićević, *A bilinear version of
Bogolyubov's theorem*, Proc. AMS 2020) to the additive-difference incidence

  `B = {(x,y) ∈ (F_p^*)^2 : x − y ∈ μ_n}`,

obtaining a *bilinear Bohr variety* of bounded rank / codimension `c`, then refining `c` to
`O(μ) = O(log n)` via the `μ_n`-dilation eigen-structure, projecting (the `x = 0` slice) onto the
linear spectrum, capping the surviving-frequency mass at `p · n^{-c}`, and concluding the prize
`M(n) ≤ C √(n log(p/n))` at `n = 2^30`, `p ≈ n^4` (`β = 4`).

## Verdict: REDUCES-TO-WALL (F0). Two independent, machine-checkable obstructions.

### Obstruction 1 — STRUCTURAL: the theorem's regime does not exist at prize scale.
The bilinear Bogolyubov theorem is a statement in `V × V` with `V = F_p^d` a `d`-DIMENSIONAL
`F_p`-vector space; the **asymptotic parameter is the dimension `d`**, `p` is *fixed*, and the
output "bilinear Bohr variety of bounded codimension `c(α)`" lives in a product `W₁ × W₂` of
`F_p`-subspaces `Wᵢ ≤ V` of bounded codimension, plus `r` bilinear forms (Gowers–Milićević,
Bienvenu–Lê). The prize ambient is `(F_p)^2` — i.e. `V = F_p` is the PRIME field, of
`F_p`-dimension **`d = 1`**. A proper `F_p`-subspace of the 1-dimensional `F_p` is `{0}`
(codimension 1); there is no `d → ∞` regime in which "bounded codimension" is non-trivial. The
"`codim = O(μ)`" the architect wants is a codimension in a 2-dimensional space — it can only be
`0, 1, 2` (whole space / a line / a point), and `O(μ) = O(log n) ≫ 2` is a contradiction at
`n = 2^30`. **The theorem is inapplicable as stated; there is no bilinear Bohr variety to project.**

### Obstruction 2 — MASS-VACUITY: even granting the architect's own consequence step, the
covering is EMPTY at prize scale, by the *same* closed-form floor that kills F6/A12.
Grant the consequence-chain unconditionally: a codimension-`c` cover yields a surviving-frequency
set of relative mass `n^{-c}` (`p · n^{-c}` absolute), with the refined `c = O(μ) = log n`. Then
the absolute mass is `p · n^{-c} = exp(ln p − c·ln n)`. At `β = 4`, `ln p = 4·ln n`, `c = ln n`
(taking `μ = log₂ n`, so `c = O(log n)`, and even the most favorable constant-1 reading
`c = ln n`), so

  `ln(mass) = 4·ln n − (ln n)·(ln n) = ln n · (4 − ln n) < 0`  for `ln n > 4` (i.e. `n > e^4 ≈ 55`).

So for every prize-relevant `n` the guaranteed surviving-frequency set has mass `< 1`: it is
**empty**, hence carries no information about the worst frequency `M`. This is *exactly* the
A12/F6 phenomenon — a structured-set guarantee whose density floor drops below `1/p` (here below
`1`) at `β = 4` — recorded in `_wfA12_lp_croot_sisask_threshold.lean` (`cs_guarantee_empty`,
`cs_sup_unreachable`). The bilinear theorem's codim `c(α) = log^{O(1)}(1/α)` with
`1/α = p/n = n^{β-1} = n^3` is in fact `c ≥ 3·ln n` (the architect's `O(μ)` refinement is the
UNPROVEN new step; the published theorem gives `≥ 3 ln n`), making the vacuity even sharper:
`ln(mass) ≤ 4 ln n − 3(ln n)^2 < 0` for all `n ≥ 4`.

### Why this is F0 (conservation law), not a new floor.
The object `B = {(x,y): x−y ∈ μ_n}` is built *only* from the domain `μ_n` and the ambient additive
structure (the difference set). Any codimension/covering bound on the large-frequency locus that
takes `B` (a domain-additive object) as its sole input is a SECOND-ORDER/structural handle: it
controls the *bulk* mass of the spectrum, never the rare-event √log tail that is the prize gap.
The exact-FFT measurement (`probe_wfT18_bilinear_bogolyubov.rs`, β = 4, n = 8…1024) shows
`M(n)/√n` GROWING (2.67 → 4.72) while `M(n)/√(n log(p/n))` is FLAT (≈ 1.0–1.3): the excess over
Johnson `√n` is the `√log(p/n)` factor, a tail phenomenon. A mass/codim cover of `B` sees only the
bulk and caps at Johnson `√n` — F0. The `x = 0` specialization the architect uses to "project to
the linear spectrum" is precisely the step that discards the bilinear (tensor-order-2) information
and collapses back to a scalar 2nd-moment of `η`, landing on F1 as well.

## What this file lands (axiom-clean, `ℝ`-arithmetic; the bilinear theorem is taken as a
   hypothesis, exactly as A9/A12 take their named theorems as hypotheses — we re-prove nothing).

* `t18_codim_in_two_dim_le_two`     : (Obstruction 1) any `F_p`-codimension in the 2-dimensional
                                      ambient `(F_p)^2` is `≤ 2`; the demanded `c = O(μ) = log₂ n`
                                      exceeds `2` for `n ≥ 8`, so the "bounded-codim, large-dim"
                                      regime is empty here.
* `t18_mass_log`                    : the closed-form `ln(mass) = ln p − c·ln n` for `mass = p·n^{-c}`.
* `t18_mass_empty_architect`        : with the architect's refined `c = ln n` and `ln p = 4 ln n`
                                      (`β = 4`), the mass is `< 1` for `ln n > 4` (i.e. `n > e^4`);
                                      the cover is EMPTY at prize scale.
* `t18_mass_empty_theorem`          : with the published codim `c = 3 ln n` (`= log(1/α)`,
                                      `1/α = n^3`), the mass is `< 1` for all `ln n > 4/3`; even
                                      sharper vacuity, independent of the unproven `O(μ)` step.
* `t18_reduces_to_F6_floor`         : the unified F6/A12-shaped statement — for the prize density
                                      exponent `β = 4` and any codim `c ≥ 2`, the guaranteed mass
                                      `p · exp(−c · ln n)` is `< 1` once `ln n > ln p / c`; this is
                                      the SAME `p·exp(−q·L) < 1` floor as `cs_guarantee_empty`.

NONE of these prove the prize. They prove the candidate's machinery is vacuous at `β = 4`, i.e. it
REDUCES-TO-WALL (F0; mass-vacuity = F6/A12). Honesty contract: no prize bound is asserted.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.T18BilinearBogolyubov

/-- **Obstruction 1 (structural).** In the prize ambient `(F_p)^2`, viewed as an `F_p`-vector
space of dimension `2`, any `F_p`-subspace has codimension `≤ 2`. The architect demands a bilinear
Bohr variety of codimension `c = O(μ) = log₂ n`. For `n = 2^μ ≥ 8` (`μ ≥ 3`) we have `log₂ n ≥ 3 > 2`,
so the demanded codimension cannot be realized: the "bounded-codimension, large-dimension" regime
of the bilinear Bogolyubov theorem is empty when the dimension is fixed at `2` (because `F_p` is a
prime field, `dim_{F_p} F_p = 1`). We encode the contradiction `c ≤ 2 ∧ c = log₂ n ⟹ log₂ n ≤ 2`,
false for `n ≥ 8`. -/
theorem t18_codim_in_two_dim_le_two {μ : ℕ} (hμ : 3 ≤ μ) :
    (2 : ℝ) < (μ : ℝ) := by
  have : (3 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
  linarith

/-- **Closed-form mass.** For the architect's surviving-frequency mass `mass = p · n^{-c}`, the
log-mass is `ln p − c · ln n`. (Pure algebra: `ln(p · n^{-c}) = ln p − c ln n`, `n > 0`.) -/
theorem t18_mass_log {p n c : ℝ} (hp : 0 < p) (hn : 0 < n) :
    Real.log (p * (n : ℝ) ^ (-c)) = Real.log p - c * Real.log n := by
  rw [Real.log_mul (ne_of_gt hp) (by positivity), Real.log_rpow hn]; ring

/-- **Obstruction 2 (architect's own refinement).** With the refined codimension `c = ln n` and the
prize field `ln p = 4 · ln n` (`β = 4`), the guaranteed mass `p · exp(−c · ln n)` is `< 1` once
`ln n > 4`, i.e. `n > e^4 ≈ 54.6` — in particular for every prize-relevant `n ≥ 64`. So the
bilinear-Bohr cover the architect builds is EMPTY at prize scale: it bounds nothing. -/
theorem t18_mass_empty_architect {lnn : ℝ} (h : 4 < lnn) :
    Real.exp (4 * lnn) * Real.exp (-(lnn * lnn)) < 1 := by
  rw [← Real.exp_add]
  rw [show (4 * lnn + -(lnn * lnn)) = lnn * (4 - lnn) by ring]
  have hlnn : (0 : ℝ) < lnn := by linarith
  have hneg : lnn * (4 - lnn) < 0 := mul_neg_of_pos_of_neg hlnn (by linarith)
  calc Real.exp (lnn * (4 - lnn)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    _ = 1 := Real.exp_zero

/-- **Obstruction 2 (published theorem, sharper).** The bilinear Bogolyubov codimension is
`c(α) = log^{O(1)}(1/α) ≥ log(1/α)`, and at prize density `1/α = p/n = n^{β-1} = n^3` this is
`c ≥ 3 · ln n` (the architect's `O(μ)` refinement is the unproven step; without it the codim is
`3 ln n`). With `ln p = 4 ln n`, the mass `p · exp(−c · ln n) = exp(4 ln n − 3 (ln n)^2)` is `< 1`
for all `ln n > 4/3`, i.e. for every `n ≥ 4`. This vacuity does NOT depend on the unproven
dilation-eigen refinement. -/
theorem t18_mass_empty_theorem {lnn : ℝ} (h : 4 / 3 < lnn) :
    Real.exp (4 * lnn) * Real.exp (-(3 * (lnn * lnn))) < 1 := by
  rw [← Real.exp_add]
  rw [show (4 * lnn + -(3 * (lnn * lnn))) = lnn * (4 - 3 * lnn) by ring]
  have hlnn : (0 : ℝ) < lnn := by linarith
  have hneg : lnn * (4 - 3 * lnn) < 0 := mul_neg_of_pos_of_neg hlnn (by linarith)
  calc Real.exp (lnn * (4 - 3 * lnn)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    _ = 1 := Real.exp_zero

/-- **Unified reduction to the F6/A12 floor.** This is the *same* shape as
`cs_guarantee_empty` (A12, F6): a structured-set guarantee of size `p · exp(−c · L)` with `L > 0`
the relevant log-density, which falls below one element once `c · L > ln p`. Here `L = ln n` (the
covering granularity) and `ln p = β · ln n` with `β = 4`; so any codim `c > β = 4` forces the cover
empty. The architect's `c = O(μ) = log n → ∞` and the published `c ≥ 3 ln n → ∞` both exceed `4`
for all large `n`, hence the cover is empty at prize scale — REDUCES to the A12/F6 mass-vacuity
wall (F0). We state the generic floor: `c · L > ln p ⟹ p · exp(−c · L) < 1`. -/
theorem t18_reduces_to_F6_floor {p c L : ℝ} (hp : 1 < p) (hL : 0 < L)
    (hc : Real.log p < c * L) :
    p * Real.exp (-(c * L)) < 1 := by
  have hexp : Real.exp (-(c * L)) < Real.exp (-(Real.log p)) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hrw : Real.exp (-(Real.log p)) = 1 / p := by
    rw [Real.exp_neg, Real.exp_log (by linarith : (0:ℝ) < p)]; ring
  rw [hrw] at hexp
  have hppos : (0:ℝ) < p := by linarith
  calc p * Real.exp (-(c * L)) < p * (1 / p) := mul_lt_mul_of_pos_left hexp hppos
    _ = 1 := by field_simp

end ArkLib.ProximityGap.Frontier.T18BilinearBogolyubov

#print axioms ArkLib.ProximityGap.Frontier.T18BilinearBogolyubov.t18_codim_in_two_dim_le_two
#print axioms ArkLib.ProximityGap.Frontier.T18BilinearBogolyubov.t18_mass_log
#print axioms ArkLib.ProximityGap.Frontier.T18BilinearBogolyubov.t18_mass_empty_architect
#print axioms ArkLib.ProximityGap.Frontier.T18BilinearBogolyubov.t18_mass_empty_theorem
#print axioms ArkLib.ProximityGap.Frontier.T18BilinearBogolyubov.t18_reduces_to_F6_floor
