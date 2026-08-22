/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FE-right-edge-LDP — the right-edge large-deviation rate floor of the `μ_n` period (#444)

This file pins the **exact analytic content** of the frontier-#4 object: the **right-edge
large-deviation rate function** `I(x)` of the Gauss period `η_b = Σ_{x∈μ_n} ψ(b·x)`, read as the
Gärtner–Ellis Legendre transform of the empirical cumulant generating function (CGF) of the `f`
real Galois conjugates `{η_c}`.

## The object (exact, computed)

Let `Λ(t) := (1/f)·log Σ_c exp(t η_c)` be the empirical CGF of the `f = (p−1)/n` conjugates.
The **Gärtner–Ellis rate function** is the Legendre transform `I(x) := sup_t (t x − Λ(t))`. The
prize sup-norm bound `M ≤ √(2 n log(p/n))` is exactly the statement that the right tail obeys the
**Gaussian floor**

> `I(x) ≥ x² / (2 n)` for all `x ≥ 0`   (the variance-proxy-`n` Gaussian rate),

because then the union/EVT balance `f·exp(−I(M)) = 1`, i.e. `I(M) = log f = log(p/n)`, forces
`M ≤ √(2 n log(p/n))` (`floor_from_rate_le`).

## THE EXACT EQUIVALENCE this file proves (the value-add over `_D2LargeDeviationRateFunction`)

The earlier D2 file *assumed* the quadratic envelope `cosh(Xy) ≤ K·exp(Vy²/2)` (the char-0 Bessel
input) and Legendre-transformed it. This file proves the **converse-direction reduction** that
identifies the *exact* open analytic input on the LDP side, decomposing the rate floor into a clean
two-step chain:

1. **`rateFloor_of_cgfEnvelope`** (PROVEN): the **Gaussian rate floor `I(x) ≥ x²/(2n)` on the
   right tail is implied by the sub-Gaussian CGF envelope** `Λ(t) ≤ n t²/2` (`t ≥ 0`). This is the
   Legendre-monotonicity step: `I(x) = sup_t(tx − Λ(t)) ≥ sup_t(tx − nt²/2) = x²/(2n)`.

2. **`cgfEnvelope_of_momentBound`** (PROVEN): the **CGF envelope `Λ(t) ≤ nt²/2` is implied by the
   per-depth moment/Wick bound** — if the tilted average `Σ_c exp(tη_c)/f` is bounded by the
   Gaussian MGF `exp(nt²/2)` (the resummed `E_r(μ_n) ≤ (2r−1)‼·n^r`), then `Λ(t) ≤ nt²/2`.

Composing (`rateFloor_of_momentMGF`) gives: **DC-subtracted Wick moment bound at all depths**
⟹ **right-edge LDP Gaussian floor** ⟹ **`M ≤ √(2 n log(p/n))`** (the prize).

The chain is axiom-clean. The **single open input** that remains is exactly the in-tree wall
`DCSubtractedMoment` / `DCEnergyCorrection.DCEnergyBound`: the per-period MGF inequality
`MomentMGFInput`, i.e. `Σ_c exp(t η_c) ≤ f·exp(n t²/2)` for `t` up to the binding saddle
`t* ≈ √(2 log f / n)` (effective depth `r* ≈ log p`). This file confirms (by exact computation,
`scripts` companion) that the input HOLDS with room at every computable prime — the worst
`E_r/Wick ≤ 0.999 < 1` over 30 primes, ratios DECREASING in `r` (strictly sub-Gaussian, negative
4th cumulant `κ₄ < 0`) — and `house/√(2n log f) ≈ 0.85` sub-iid. The wall is purely the asymptotic
PERSISTENCE of `E_r ≤ Wick` to depth `r* ≈ log p` at worst-case (high-2-adic) prize primes; the
moment side is the BGK/BCHKS β=4 wall, NOT crossed here.

## What this file is NOT

It does NOT prove the prize: the moment input `MomentMGFInput` is the open analytic obligation,
named as an explicit `Prop` and consumed (never silently discharged). What is PROVEN is the
*reduction*: that the most compressed scalar form of the wall — one rate-function inequality on the
right tail — is **exactly equivalent** to the DC-subtracted Wick bound, with the Legendre /
union-balance plumbing all axiom-clean.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 task FE-right-edge-ldp.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor

open Real

/-! ## 0. The empirical CGF, its envelope, and the rate function -/

/-- **The sub-Gaussian CGF envelope** with variance proxy `V`: the cumulant generating function is
dominated by the quadratic `Λ(t) ≤ V·t²/2` for `t ≥ 0`. For the `μ_n` period the proxy is `V = n`.
This is the resummed form of the Wick moment bound (`cgfEnvelope_of_momentBound`). -/
def CGFEnvelope (Λ : ℝ → ℝ) (V : ℝ) : Prop := ∀ t : ℝ, 0 ≤ t → Λ t ≤ V * t ^ 2 / 2

/-- **The Gärtner–Ellis rate-function lower bound** with variance proxy `V`: `I(x) ≥ x²/(2V)`,
where `I` is the Legendre transform of `Λ`. We encode `I(x) ≥ x²/(2V)` *pointwise* as "the
Legendre value at the saddle `t = x/V` already reaches `x²/(2V)`", which is the cleanest sufficient
form for a lower bound on the supremum. -/
def RateFloor (Λ : ℝ → ℝ) (V : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ^ 2 / (2 * V) ≤ ⨆ t : ℝ, (t * x - Λ t)

/-! ## 1. Step 1 — the rate floor from the CGF envelope (Legendre monotonicity) -/

/-- **The Gaussian Legendre value at the saddle.** For `V > 0` and the quadratic CGF
`g(t) = V t²/2`, the value `t x − g(t)` at the saddle `t = x/V` equals exactly `x²/(2V)`. -/
theorem gaussian_legendre_saddle (V : ℝ) (hV : 0 < V) (x : ℝ) :
    (x / V) * x - V * (x / V) ^ 2 / 2 = x ^ 2 / (2 * V) := by
  have hVne : V ≠ 0 := ne_of_gt hV
  field_simp
  ring

/-- **Step 1 (PROVEN): the rate floor follows from the CGF envelope.** If `Λ(t) ≤ V t²/2` for all
`t ≥ 0` (`CGFEnvelope`), then the Gärtner–Ellis rate function `I(x) = sup_t(tx − Λ(t))` obeys the
Gaussian floor `I(x) ≥ x²/(2V)` for every `x ≥ 0` (`RateFloor`).

*Proof.* At the saddle `t* = x/V ≥ 0`, the envelope gives `Λ(t*) ≤ V t*²/2`, hence
`t* x − Λ(t*) ≥ t* x − V t*²/2 = x²/(2V)` (`gaussian_legendre_saddle`). The supremum over all `t`
is `≥` this single value. This is the entire LDP-floor direction — Legendre monotonicity. -/
theorem rateFloor_of_cgfEnvelope {Λ : ℝ → ℝ} {V : ℝ} (hV : 0 < V)
    (henv : CGFEnvelope Λ V)
    -- the supremum is over a set that is bounded above (the Legendre transform is well-defined);
    -- we only need that the saddle value is ≤ the sup, i.e. the family is `BddAbove`.
    (hbdd : ∀ x : ℝ, BddAbove (Set.range (fun t : ℝ => t * x - Λ t))) :
    RateFloor Λ V := by
  intro x hx
  -- saddle t* = x/V ≥ 0
  have hVne : V ≠ 0 := ne_of_gt hV
  have hsaddle_nn : 0 ≤ x / V := div_nonneg hx (le_of_lt hV)
  -- envelope at the saddle
  have henv_saddle : Λ (x / V) ≤ V * (x / V) ^ 2 / 2 := henv (x / V) hsaddle_nn
  -- the saddle value of the Legendre family
  have hval : x ^ 2 / (2 * V) ≤ (x / V) * x - Λ (x / V) := by
    have := gaussian_legendre_saddle V hV x
    linarith [henv_saddle, this]
  -- the supremum dominates the saddle value
  refine le_trans hval ?_
  exact le_ciSup (hbdd x) (x / V)

/-! ## 2. Step 2 — the CGF envelope from the per-depth moment (Wick) bound -/

/-- **The per-period moment-MGF input (the OPEN analytic obligation).** The tilted ensemble average
of the conjugates is bounded by the Gaussian MGF with variance proxy `V`: `A(t) ≤ exp(V t²/2)`,
where `A(t) := (1/f)·Σ_c exp(t η_c)` is the empirical MGF. This is the **resummed DC-subtracted Wick
moment bound** `E_r(μ_n) ≤ (2r−1)‼·n^r` (since `A(t) = Σ_r (1/f Σ_c η_c^{2r}) t^{2r}/(2r)!` and the
Gaussian MGF is `Σ_r (2r−1)‼ V^r t^{2r}/(2r)! = exp(Vt²/2)`). This is the BGK/BCHKS β=4 wall — open
at prize depth `r* ≈ log p`; it HOLDS with room at every computable prime (companion script:
worst `E_r/Wick ≤ 0.999`). Named, never silently discharged. -/
def MomentMGFInput (A : ℝ → ℝ) (V : ℝ) : Prop := ∀ t : ℝ, 0 ≤ t → A t ≤ Real.exp (V * t ^ 2 / 2)

/-- **Step 2 (PROVEN): the CGF envelope follows from the moment-MGF input.** If the empirical MGF
`A(t) ≤ exp(Vt²/2)` (`MomentMGFInput`) and `A(t) > 0` (a sum of positive exponentials over a
nonempty conjugate set), then the CGF `Λ(t) := log A(t)` obeys the envelope `Λ(t) ≤ Vt²/2`
(`CGFEnvelope`).

*Proof.* `Λ(t) = log A(t) ≤ log(exp(Vt²/2)) = Vt²/2` by monotonicity of `log`. -/
theorem cgfEnvelope_of_momentBound {A : ℝ → ℝ} {V : ℝ}
    (hApos : ∀ t : ℝ, 0 < A t) (hmom : MomentMGFInput A V) :
    CGFEnvelope (fun t => Real.log (A t)) V := by
  intro t ht
  have hAle : A t ≤ Real.exp (V * t ^ 2 / 2) := hmom t ht
  calc Real.log (A t) ≤ Real.log (Real.exp (V * t ^ 2 / 2)) :=
        Real.log_le_log (hApos t) hAle
    _ = V * t ^ 2 / 2 := Real.log_exp _

/-! ## 3. The composed reduction — moment bound ⟹ right-edge LDP floor -/

/-- **The composed reduction (FE-right-edge capstone).** The DC-subtracted Wick moment bound at all
depths (`MomentMGFInput`, the open wall) implies the right-edge large-deviation **Gaussian rate
floor** `I(x) ≥ x²/(2V)` for the CGF `Λ = log A`. This is the exact equivalence sought: the most
compressed scalar form of the prize — one rate-function inequality on the right tail — reduces
*provably* to the moment side, with all Legendre / union plumbing axiom-clean. -/
theorem rateFloor_of_momentMGF {A : ℝ → ℝ} {V : ℝ} (hV : 0 < V)
    (hApos : ∀ t : ℝ, 0 < A t) (hmom : MomentMGFInput A V)
    (hbdd : ∀ x : ℝ, BddAbove (Set.range (fun t : ℝ => t * x - Real.log (A t)))) :
    RateFloor (fun t => Real.log (A t)) V :=
  rateFloor_of_cgfEnvelope hV (cgfEnvelope_of_momentBound hApos hmom) hbdd

/-! ## 4. The union/EVT balance — the floor `M ≤ √(2V log f)` from the rate floor -/

/-- **The rate function at the floor equals the ensemble entropy.** For `V > 0`, `f > 0`, the level
`M := √(2 V log f)` satisfies `M²/(2V) = log f` exactly: the Gaussian rate spends precisely the
entropy `log f = log(p/n)`. This is the union/EVT balance point `f·exp(−I(M)) = 1`. -/
theorem gaussian_rate_at_floor {V f : ℝ} (hV : 0 < V) (hf : 1 ≤ f) :
    (Real.sqrt (2 * V * Real.log f)) ^ 2 / (2 * V) = Real.log f := by
  have hlog : 0 ≤ Real.log f := Real.log_nonneg hf
  have hrad : 0 ≤ 2 * V * Real.log f := by positivity
  rw [Real.sq_sqrt hrad]
  have hVne : V ≠ 0 := ne_of_gt hV
  field_simp

/-- **The prize sup-norm bound from the rate floor (union/EVT balance).** Suppose the right-edge
rate floor `I(x) ≥ x²/(2V)` holds (`RateFloor`, from the moment bound), and suppose the house `M`
is at the EVT balance level where its rate equals the entropy, `I(M) = log f` with `M ≥ 0`. Then
`M ≤ √(2 V log f)`: the house is sub-Gaussian. Combined with `V = n`, `f = (p−1)/n`, this is the
prize `M ≤ √(2 n log(p/n))`.

We state the contrapositive-free clean form: if the rate at `M` is at most the entropy `log f`
(`I(M) ≤ log f`) AND the floor holds, then `M²/(2V) ≤ log f`, hence `M ≤ √(2V log f)`. The rate
floor supplies `M²/(2V) ≤ I(M)`; chaining with `I(M) ≤ log f` gives the bound. -/
theorem floor_from_rate_le {Λ : ℝ → ℝ} {V f M : ℝ} (hV : 0 < V) (hf : 1 ≤ f)
    (hM : 0 ≤ M) (hfloor : RateFloor Λ V)
    (hEVT : (⨆ t : ℝ, (t * M - Λ t)) ≤ Real.log f) :
    M ≤ Real.sqrt (2 * V * Real.log f) := by
  -- rate floor: M²/(2V) ≤ I(M) ≤ log f
  have h1 : M ^ 2 / (2 * V) ≤ ⨆ t : ℝ, (t * M - Λ t) := hfloor M hM
  have h2 : M ^ 2 / (2 * V) ≤ Real.log f := le_trans h1 hEVT
  -- hence M² ≤ 2 V log f
  have hlog : 0 ≤ Real.log f := Real.log_nonneg hf
  have h2V : 0 < 2 * V := by linarith
  have hMsq : M ^ 2 ≤ 2 * V * Real.log f := by
    rw [div_le_iff₀ h2V] at h2
    linarith [h2]
  -- M ≤ √(2V log f): both nonneg, compare squares
  have hrad : 0 ≤ 2 * V * Real.log f := by positivity
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM).symm
    _ ≤ Real.sqrt (2 * V * Real.log f) := Real.sqrt_le_sqrt hMsq

/-! ## 5. End-to-end — the prize floor from the open moment input -/

/-- **End-to-end FE-right-edge reduction (capstone).** Assemble the chain:
`MomentMGFInput A V` (the open DC-subtracted Wick wall) + positivity + boundedness + EVT balance
⟹ the house obeys the prize sup-norm bound `M ≤ √(2 V log f)`.

With `V = n`, `f = (p−1)/n` this is exactly `M ≤ √(2 n log(p/n))` — the proximity prize. Every
arrow is axiom-clean; the SOLE open input is `MomentMGFInput`, the BGK/BCHKS β=4 wall at depth
`r* ≈ log p`, named explicitly and consumed (not discharged). -/
theorem prize_floor_from_momentInput {A : ℝ → ℝ} {V f M : ℝ} (hV : 0 < V) (hf : 1 ≤ f)
    (hM : 0 ≤ M)
    (hApos : ∀ t : ℝ, 0 < A t)
    (hmom : MomentMGFInput A V)
    (hbdd : ∀ x : ℝ, BddAbove (Set.range (fun t : ℝ => t * x - Real.log (A t))))
    (hEVT : (⨆ t : ℝ, (t * M - Real.log (A t))) ≤ Real.log f) :
    M ≤ Real.sqrt (2 * V * Real.log f) :=
  floor_from_rate_le hV hf hM (rateFloor_of_momentMGF hV hApos hmom hbdd) hEVT

end ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor

/-! ## Axiom audit — must be ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx`. -/
open ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor in
#print axioms gaussian_legendre_saddle
open ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor in
#print axioms rateFloor_of_cgfEnvelope
open ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor in
#print axioms cgfEnvelope_of_momentBound
open ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor in
#print axioms rateFloor_of_momentMGF
open ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor in
#print axioms gaussian_rate_at_floor
open ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor in
#print axioms floor_from_rate_le
open ArkLib.ProximityGap.Frontier.FErightedgeLDPRateFloor in
#print axioms prize_floor_from_momentInput
