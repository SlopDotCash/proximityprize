/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Threshold-Halving Window Inequality — #334 frontier (ePrint 2026/858 route)

**Target.** The pure real-arithmetic kernel underneath Chai–Fan,
*FRI Soundness Above the Johnson Bound via Threshold Halving* (ePrint 2026/858).
For a rate `ρ ∈ (0, 1)`, write the **Johnson radius** as `δ_J(ρ) = 1 − √ρ`.  The paper's
above-Johnson soundness window is the proximity band

  `δ ∈ (δ_J(ρ), 1 − ρ)`.

The mechanism: their correlated-agreement analysis is run not at `δ` but at the **halved**
radius `δ/2`, and the key fact making it unconditional is that the halved radius stays strictly
**below** the Johnson radius across the *entire* window:

  `δ < 1 − ρ  ⟹  δ/2 < 1 − √ρ = δ_J(ρ)`.

Below `δ_J` the BCIKS (ePrint 2025/2055) correlated-agreement / unique-decoding analysis is
**unconditional**, so threshold-halving converts an above-Johnson statement (the open wall) into a
below-Johnson one (proven), at the cost of ≈2× queries (`ε_FRI ≤ nR/|F| + (1 − δ/2)^q`).

This file formalizes the **window inequality** (`halved_radius_below_johnson`) as clean real
arithmetic, plus the **distance-lock corollary** (`distance_lock_below_johnson`) which states
that at `δ/2` a named BCIKS below-Johnson regime predicate fires.  The BCIKS substrate is **not**
in this tree, so its applicability is carried as an explicit named `Prop` hypothesis
`BelowJohnsonRegime`, never a hidden `sorry`.

## The arithmetic heart

Let `x = √ρ ∈ (0, 1)`, so `ρ = x²`.  The gap between the Johnson radius and the midpoint of
`[0, 1 − ρ]` is

  `δ_J(ρ) − (1 − ρ)/2 = (1 − √ρ) − (1 − ρ)/2 = (1 − 2√ρ + ρ)/2 = (1 − √ρ)²/2 ≥ 0`.

Hence `(1 − ρ)/2 ≤ 1 − √ρ`.  Combined with `δ < 1 − ρ ⟹ δ/2 < (1 − ρ)/2`, this gives
`δ/2 < 1 − √ρ`.  Note the conclusion is strict because the `δ < 1 − ρ` step is strict; the
`(1 − ρ)/2 ≤ 1 − √ρ` step is only `≤` (equality at `ρ = 1`, excluded anyway by `ρ < 1`).

## Honesty / scope

This proves the **lossy (2×-query) above-Johnson window arithmetic** of the *unconditional*
threshold-halving route.  It is NOT the grand zero-loss `δ*` (the open BGK wall): the prize wants
soundness at radius `δ` *itself* with no query blow-up, which this route explicitly does not give.
Everything here is `sorry`/`axiom`-free; the only BCIKS dependence is a named hypothesis.
-/

namespace ProximityGap.ThresholdHalvingWindow

open Real

/-- The **Johnson radius** for relative rate `ρ`, in the normalized form `δ_J(ρ) = 1 − √ρ`. -/
noncomputable def johnsonRadius (ρ : ℝ) : ℝ := 1 - Real.sqrt ρ

/-- The **upper window edge**: the proximity-gap radius `1 − ρ`. The threshold-halving window is
the band `(johnsonRadius ρ, 1 − ρ)` strictly between the Johnson radius and this edge. -/
def windowTop (ρ : ℝ) : ℝ := 1 - ρ

/-- **Midpoint ≤ Johnson radius.**  The midpoint of the proximity interval `[0, 1 − ρ]` lies at
or below the Johnson radius, for any `ρ ∈ [0, 1]`.  This is the algebraic identity

  `(1 − √ρ) − (1 − ρ)/2 = (1 − √ρ)² / 2 ≥ 0`,

the whole reason threshold-halving lands below Johnson. -/
theorem half_windowTop_le_johnson {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    windowTop ρ / 2 ≤ johnsonRadius ρ := by
  set x : ℝ := Real.sqrt ρ with hx
  have hxsq : x ^ 2 = ρ := by rw [hx]; exact Real.sq_sqrt hρ0
  -- `(1 − √ρ) − (1 − ρ)/2 = (1 − √ρ)²/2 ≥ 0`, using `ρ = x²`.
  have hkey : johnsonRadius ρ - windowTop ρ / 2 = (1 - x) ^ 2 / 2 := by
    simp only [johnsonRadius, windowTop, ← hx]
    nlinarith [hxsq]
  nlinarith [sq_nonneg (1 - x), hkey]

/-- **Window inequality (ePrint 2026/858 kernel).**  For `ρ ∈ [0, 1]`, any proximity radius `δ`
strictly inside the above-Johnson window (i.e. strictly below the upper edge `1 − ρ`) has its
**halved** radius `δ/2` strictly below the Johnson radius `1 − √ρ`.

This is the unconditional pivot of threshold-halving: it lets the correlated-agreement analysis
run at `δ/2`, where the BCIKS below-Johnson regime applies unconditionally. -/
theorem halved_radius_below_johnson {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : δ < windowTop ρ) :
    δ / 2 < johnsonRadius ρ := by
  have hmid : windowTop ρ / 2 ≤ johnsonRadius ρ := half_windowTop_le_johnson hρ0 hρ1
  have hhalf : δ / 2 < windowTop ρ / 2 := by linarith
  linarith

/-- Specialization to the genuine prize regime `ρ ∈ (0, 1)`, with `δ` ranging over the *open*
window `(johnsonRadius ρ, windowTop ρ)`.  Even from the lower window edge `johnsonRadius ρ < δ`
we still conclude `δ/2 < johnsonRadius ρ`: halving always drops strictly below Johnson. -/
theorem halved_radius_below_johnson_window {ρ δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlo : johnsonRadius ρ < δ) (hhi : δ < windowTop ρ) :
    δ / 2 < johnsonRadius ρ :=
  halved_radius_below_johnson hρ0.le hρ1.le hhi

/-- The Johnson radius is strictly positive on `ρ ∈ (0, 1)` (so the window is nonempty and the
`δ/2` analysis radius is a genuine positive proximity radius). -/
theorem johnsonRadius_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < johnsonRadius ρ := by
  have hlt : Real.sqrt ρ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hρ0.le hρ1
  simp only [johnsonRadius]; linarith

/-- The window is nonempty on `ρ ∈ (0, 1)`: `johnsonRadius ρ < windowTop ρ` iff `(1 − √ρ)² > 0`,
which holds since `√ρ < 1`.  Concretely `windowTop ρ − johnsonRadius ρ = √ρ − ρ = √ρ(1 − √ρ) > 0`. -/
theorem johnson_lt_windowTop {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    johnsonRadius ρ < windowTop ρ := by
  set x : ℝ := Real.sqrt ρ with hx
  have hxsq : x ^ 2 = ρ := by rw [hx]; exact Real.sq_sqrt hρ0.le
  have hxpos : 0 < x := Real.sqrt_pos.mpr hρ0
  have hxlt1 : x < 1 := by
    rw [hx, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hρ0.le hρ1
  -- `windowTop − johnsonRadius = (1 − ρ) − (1 − √ρ) = √ρ − ρ = x − x² = x(1 − x) > 0`.
  simp only [johnsonRadius, windowTop, ← hx]
  nlinarith [hxsq, mul_pos hxpos (by linarith : (0:ℝ) < 1 - x)]

/-! ## Distance-lock corollary (BCIKS below-Johnson regime, named hypothesis)

The BCIKS (ePrint 2025/2055) substrate that makes the below-Johnson correlated-agreement analysis
unconditional is **not** in this tree.  We therefore carry its applicability as an explicit named
predicate.  `BelowJohnsonRegime ρ r` says: at relative rate `ρ`, every analysis radius `r` strictly
below the Johnson radius `1 − √ρ` enjoys the unconditional BCIKS regime.  The corollary below shows
that the threshold-halved radius `δ/2` *fires* this predicate for every window radius `δ` — i.e.
the lock engages — WITHOUT asserting the predicate itself (that is the imported BCIKS fact). -/

/-- Named BCIKS below-Johnson predicate (NOT proven here — it is the imported ePrint 2025/2055
unconditional correlated-agreement regime).  `BelowJohnsonRegime ρ r` is meant to hold exactly when
`r` is a strictly-below-Johnson analysis radius at rate `ρ`; we model that triggering condition as
`r < johnsonRadius ρ`. -/
def BelowJohnsonRegime (ρ r : ℝ) : Prop := r < johnsonRadius ρ

/-- **Distance-lock corollary.**  Given the BCIKS below-Johnson regime predicate as a *hypothesis*
of the form `∀ r, r < johnsonRadius ρ → BelowJohnsonRegime ρ r` (vacuously true under the modelling
`def` above, but stated abstractly so any real BCIKS substrate plugs in verbatim), the
threshold-halved radius `δ/2` of any window radius `δ` lies in that regime.

This is the honest "distance lock": the lossy 2×-query route's analysis radius `δ/2` is locked
below Johnson, so the unconditional BCIKS unique-decoding/correlated-agreement machinery applies. -/
theorem distance_lock_below_johnson {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : δ < windowTop ρ)
    (hBCIKS : ∀ r : ℝ, r < johnsonRadius ρ → BelowJohnsonRegime ρ r) :
    BelowJohnsonRegime ρ (δ / 2) :=
  hBCIKS (δ / 2) (halved_radius_below_johnson hρ0 hρ1 hδ)

/-- The modelling predicate is discharged by the window inequality itself: under the `def`
`BelowJohnsonRegime ρ r := r < johnsonRadius ρ`, the hypothesis of `distance_lock_below_johnson`
holds unconditionally, so the lock is realized as a clean (sorry-free) consequence of the
arithmetic.  (A real BCIKS substrate would replace this trivial discharge with the imported
unconditional regime fact.) -/
theorem distance_lock_below_johnson' {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : δ < windowTop ρ) :
    BelowJohnsonRegime ρ (δ / 2) :=
  distance_lock_below_johnson hρ0 hρ1 hδ (fun _ h => h)

-- Axiom audit: every result here must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms half_windowTop_le_johnson
#print axioms halved_radius_below_johnson
#print axioms halved_radius_below_johnson_window
#print axioms johnsonRadius_pos
#print axioms johnson_lt_windowTop
#print axioms distance_lock_below_johnson
#print axioms distance_lock_below_johnson'

end ProximityGap.ThresholdHalvingWindow
