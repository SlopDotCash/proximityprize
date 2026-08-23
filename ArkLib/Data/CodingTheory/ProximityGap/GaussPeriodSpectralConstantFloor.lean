/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodSpectralFrame

/-!
# The constant floor on the near-Ramanujan-up-to-√log ceiling (#407, lane wf-LA)

The spectral δ* lever (`GaussPeriodSpectralFrame`) brackets the prize per-frequency core
`M(n) = max_{b≠0}‖η_b‖ = λ₂(Cay(F_q, μ_n))` between the **proven** Parseval floor
`M² ≥ n(q−n)/(q−1)` and the **named-open** `NearRamanujanSqrtLog` ceiling `M ≤ C·√(n·log(q/n))`.

This file pins the constant `C` **from below**: any uniform near-Ramanujan-√log bound is forced by
the floor to satisfy

> `C² ≥ (q − n) / ((q − 1)·log(q/n))`.

Equivalently `C ≥ √((q−n)/((q−1)·log(q/n)))`. In the thin prize regime (`q/n = 2¹²⁸`,
`log(q/n) ≈ 128·ln 2 ≈ 88.7`, `q ≫ n`), this gives `C ⪆ 1/√(log(q/n)) ≈ 0.106` — small, but
**strictly positive and bounded away from 0**: the spectral ceiling can *not* be driven below the
floor scale, so the frame is genuinely two-sided.

## Why this is the honest LA-lane verdict (random-like, no fixed-index handle)

Lane wf-LA's mission was to find an *effective* near-Ramanujan-√log bound from the fixed-index
structure (`m = (q−1)/n = 2¹²⁸` fixed and odd, `n = 2^μ`). The numerics
(`scripts/probes/probe_wfLA_*.py`) refute that hope:

* At the exact prize slice `β = log_n q = 4`, the empirical constant
  `C = M/√(n·log(q/n))` is **not uniform**: it creeps as `≈ 0.46 + 0.43·√(log n)`
  (residual 0.025 over `n = 4…64`) — the genuine √log creep, not a bounded constant.
* `M(μ_n) / 𝔼[M(random n-subset)]` runs `1.02 → 1.15` over `n = 4…32`, and `M(μ_n) ≈
  max(random)`: the deterministic family is **random-like (slightly worse), never better**. So
  the Gumbel value `M ≈ √(n·log q) = √(β/(β−1))·√(n·log(q/n))` is *matched*, not beaten — there is
  no structured cancellation to exploit at fixed index.
* The argmax frequency `b` shows **no** `gcd(b,m)` / `gcd(b,n)` localization (probe A): the worst
  frequency is unstructured, so the fixed-index reduction the effective-Katz no-go "missed" does
  not exist either. The §6 effective-Katz no-go (growing field) and this fixed-index probe
  agree: the only viable mechanism is char-`p` deep moments (the meta-theorem), not spectra.

The rigorous landable kernel is the constant floor below: it makes the spectral frame's lower side
quantitative and shows the prize constant is `Θ(1/√log)` from the floor alone — consistent with the
random-like upper side `Θ(√(β/(β−1)))`.

Axiom-clean. Issue #407. Lane wf-LA.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodParsevalFloor
open ArkLib.ProximityGap.GaussPeriodSpectralFrame

namespace ArkLib.ProximityGap.GaussPeriodSpectralConstantFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Constant floor (squared).** A uniform near-Ramanujan-√log ceiling with constant `C` forces
`C²·(n·log(q/n)) ≥ (q·n − n²)/(q − 1)`: the floor witness `b` has `‖η_b‖²` at least the Parseval
floor and at most `C²·n·log(q/n)`, so the ceiling cannot be smaller than the floor. This is the
quantitative two-sidedness of the spectral frame — the constant `C` cannot be driven to 0. -/
theorem nearRamanujan_const_sq_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {C : ℝ}
    (hq : 2 ≤ Fintype.card F) (hcard : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (h : NearRamanujanSqrtLog ψ G C) :
    ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
      ≤ C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) := by
  obtain ⟨b, _hbne, hfloor, hceil⟩ := spectral_frame hψ G hq hcard hC h
  exact le_trans hfloor hceil

/-- **Constant floor, solved for `C²`.** When the per-frequency log-energy scale
`L = n·log(q/n)` is strictly positive (the thin prize regime, `q > n ≥ 1`), the constant floor
rearranges to `C² ≥ (q·n − n²)/((q − 1)·L)`: an explicit positive lower bound on any admissible
near-Ramanujan-√log constant. -/
theorem nearRamanujan_const_sq_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {C : ℝ}
    (hq : 2 ≤ Fintype.card F) (hcard : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (hL : 0 < (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (h : NearRamanujanSqrtLog ψ G C) :
    ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
        / (((Fintype.card F : ℝ) - 1) * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)))
      ≤ C ^ 2 := by
  set L : ℝ := (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  set num : ℝ := (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 with hnum
  set den1 : ℝ := (Fintype.card F : ℝ) - 1 with hden1
  have hden1pos : 0 < den1 := by
    have : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
    rw [hden1]; linarith
  have hframe : num / den1 ≤ C ^ 2 * L :=
    nearRamanujan_const_sq_floor hψ G hq hcard hC h
  -- divide both sides by L: (num/den1)/L ≤ C^2, and (num/den1)/L = num/(den1*L)
  rw [div_le_iff₀ (by positivity)]
  -- goal: num ≤ C^2 * (den1 * L)
  have hstep : num ≤ (C ^ 2 * L) * den1 := by
    have := (div_le_iff₀ hden1pos).mp hframe
    linarith [this]
  nlinarith [hstep, hden1pos, hL]

end ArkLib.ProximityGap.GaussPeriodSpectralConstantFloor

#print axioms ArkLib.ProximityGap.GaussPeriodSpectralConstantFloor.nearRamanujan_const_sq_floor
#print axioms ArkLib.ProximityGap.GaussPeriodSpectralConstantFloor.nearRamanujan_const_sq_ge
