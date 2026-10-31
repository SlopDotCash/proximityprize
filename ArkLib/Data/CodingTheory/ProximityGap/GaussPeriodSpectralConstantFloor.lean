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

Equivalently `C ≥ √((q−n)/((q−1)·log(q/n)))`. In the thin prize regime (`q/n ≈ 2¹²⁸`,
`log(q/n) ≈ 128·ln 2 ≈ 88.7`, `q ≫ n`), this gives `C ⪆ 1/√(log(q/n)) ≈ 0.106` — small but
strictly positive **for that fixed ratio `q/n`** (the bound tends to `0` as `log(q/n) → ∞`): at
that ratio the spectral ceiling can *not* be driven below the floor scale, so the frame is
two-sided there.

## Empirical context for lane wf-LA (finite probes, not theorems)

Lane wf-LA's mission was to find an *effective* near-Ramanujan-√log bound from fixed-index
structure: index `m = (q−1)/n` held fixed (in the prize, `m ≈ 2¹²⁸`, which is **even**) with
`n = 2^μ`.  The probes (`scripts/probes/probe_wfLA_*.py`) did **not** sample that regime: they
fixed `β = log_n q` instead, and **fixed `β` is not fixed index** — with `β = 4`, `q ≈ n⁴` and
`m ≈ n³` grows with `n`.  So the observations below concern a varying-index family over small `n`
and do not by themselves say anything about a fixed-index mechanism:

* At `β = log_n q = 4`, the empirical constant `C = M/√(n·log(q/n))` over `n = 4…64` is fitted by
  `≈ 0.46 + 0.43·√(log n)` (residual 0.025).  A fit over this finite range does not establish that
  `C` diverges, only that it was not observed to be constant there.
* `M(μ_n) / 𝔼[M(random n-subset)]` runs `1.02 → 1.15` over `n = 4…32`, and `M(μ_n) ≈
  max(random)`: in these samples the deterministic family looked random-like (slightly worse), and
  no structured cancellation was observed.
* The argmax frequency `b` showed no `gcd(b,m)` / `gcd(b,n)` localization in the sampled
  instances (probe A).
* **Interpretation (conjectural, not proved):** these observations, together with the §6
  effective-Katz no-go (growing field), were read as suggesting that char-`p` deep moments, rather
  than spectral arguments, are the viable mechanism.  Neither the finite fits nor the formal
  results here prove that no fixed-index spectral mechanism exists.

The rigorous content is the constant floor below: it makes the spectral frame's lower side
quantitative, giving the **lower bound** `C ≳ 1/√(log(q/n))` from the Parseval floor alone.  It
supplies no matching upper bound: a `Θ(1/√log)` law for the actual prize constant, or a
`Θ(√(β/(β−1)))` upper side, is not proved here.

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
quantitative two-sidedness of the spectral frame — for given `q` and `n`, the constant `C` cannot
be driven below the floor value. -/
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
