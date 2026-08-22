/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# FACE 1 (CellPackageSupply) is character-sum-free but Johnson-radius-capped (#334, B4)

**The precise scope of the BCIKS20 §5 / `CellPackageSupply` floor route.**

The Johnson lane's consumer chain (`Hab25JohnsonPackageSupply.lean`:
`CellPackageSupply → … → JohnsonDischargeStatement`) is fully proven and axiom-clean, and
its single open input `CellPackageSupply` is the [BCIKS20] §5 per-cell section production
(Proposition 5.5 / Claim 5.7).  A close reading of [BCIKS20] establishes a structural fact
that reframes Face 1's relationship to the Paley/BGK wall:

* **[BCIKS20] §5 contains NO character sum, NO Weil bound, NO `√q` cancellation.**  The
  section production is *interpolation* (Guruswami–Sudan, Step 1) + *Hensel lifting* over
  the function field `K = Fq(Z)` (Steps 3–6) + *polynomial root counting* (Lemma A.1, the
  weight `Λ`, Steps 6–8) + *pigeonholes* over `≤ DY` factor cells (Claim 5.7).  Every
  "supply" inequality is a `|S|` (good-set cell mass) vs. degree-bound comparison
  `|S| > 2·DY³·DX·DYZ = poly(n)`, i.e. the proximity-gap budget `εJ = O(n²/q)` — **never**
  a non-trivial incomplete character sum.

* Consequently the whole `CellPackageSupply` route **GENUINELY BYPASSES** the generalized
  Paley wall *for the part of the window it covers* — but it covers **only up to the Johnson
  radius**.  [BCIKS20] Theorem 5.1 decodes at `δ ≤ δ₀(ρ,m) = 1 − √ρ − √ρ/(2m)`, whose
  supremum over the multiplicity `m` is exactly `1 − √ρ` (the Johnson radius); §7 confirms
  the framework is hard-capped there ("In the Johnson bound regime, this is exactly the
  content of Proposition 5.5").  In-tree, `JohnsonDischargeStatement` is gated by
  `(δ : ℝ) < gs_johnson k n m` — the same cap.

* The prize window `(1 − √ρ, 1 − ρ − Θ(1/log n))` lies **strictly above** the Johnson
  radius.  Therefore Face 1 (CellPackageSupply), even fully discharged, lands the floor
  only on `[0, 1−√ρ)` and **cannot reach the prize window** without a new ingredient that
  breaks the Johnson barrier (= a past-Johnson list-decoding-capacity input for these
  explicit RS codes).  That new ingredient — not §5 — is where Paley re-enters.

## What this file proves (pure real arithmetic, axiom-clean)

`gs_johnson_lt_capacity` — the Johnson radius `gs_johnson k n m = 1 − √ρ − √ρ/(2m)` is
strictly below the capacity radius `1 − ρ` whenever `0 < ρ < 1` (so the prize band
`(Johnson, capacity)` is non-degenerate), and `gs_johnson_lt_one_sub_sqrt_rho` — it is
strictly below the Johnson edge `1 − √ρ` itself for finite `m`.  These pin the exact gap:
the band the §5 machinery cannot enter.

This is a **scope / no-go brick**: it does not advance the floor inside the window, it
*certifies precisely why the character-sum-free Face-1 route stops at Johnson*, separating
the genuine Paley-bypass it achieves (below Johnson) from the Paley-dependent residual
(the window, above Johnson).  Cf. `FloorNecessaryNotSufficient.lean`.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 — §5 (Thm 5.1, Prop 5.5, Claims 5.6–5.11), Appendix A
  (Lemma A.1, weight `Λ`), §7 (Thm 7.1–7.5).
* [ABF26] §5 (the LD ⇒ MCA collapse — the bypass hope above Johnson).
-/

namespace ArkLib.ProximityGap.Frontier.Face1JohnsonCap

open Real

/-- **The Johnson radius is below capacity whenever the rate is non-degenerate.**
For `0 < ρ < 1` the Guruswami–Sudan / [BCIKS20] §5 radius
`gs_johnson = 1 − √ρ − √ρ/(2m)` is strictly less than the capacity radius `1 − ρ`,
so the prize band `(gs_johnson, 1 − ρ)` is non-empty.  This is the band the
character-sum-free `CellPackageSupply` machinery provably cannot enter (it stops at
`gs_johnson`), and it contains the prize window `(1 − √ρ, 1 − ρ − Θ(1/log n))`. -/
theorem gs_johnson_lt_capacity {k n m : ℕ} (hm : 0 < m)
    (hρpos : (0 : ℝ) < (k : ℚ) / n) (hρlt : ((k : ℚ) / n : ℝ) < 1) :
    gs_johnson k n m < 1 - ((k : ℚ) / n : ℝ) := by
  classical
  -- work directly with `ρ := (↑((k:ℚ)/n) : ℝ)`, the exact term inside `gs_johnson`
  set ρ : ℝ := ((k : ℚ) / n : ℝ) with hρdef
  have hρpos' : (0 : ℝ) < ρ := hρpos
  have hρlt' : ρ < 1 := hρlt
  have hsqrt_pos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρpos'
  -- `√ρ < 1` since `0 < ρ < 1`
  have hsqrt_lt_one : Real.sqrt ρ < 1 := by
    have h := Real.sqrt_lt_sqrt (le_of_lt hρpos') hρlt'
    simpa using h
  -- `ρ < √ρ` because `ρ = (√ρ)² = √ρ·√ρ < √ρ·1`
  have hρ_lt_sqrt : ρ < Real.sqrt ρ := by
    have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (le_of_lt hρpos')
    have hstep : Real.sqrt ρ * Real.sqrt ρ < Real.sqrt ρ * 1 :=
      mul_lt_mul_of_pos_left hsqrt_lt_one hsqrt_pos
    rw [hsq, mul_one] at hstep
    exact hstep
  have hextra_pos : 0 < Real.sqrt ρ / (2 * m) := by positivity
  -- `gs_johnson k n m = 1 - √ρ - √ρ/(2m)` definitionally (same `ρ`)
  have hgs : gs_johnson k n m = 1 - Real.sqrt ρ - Real.sqrt ρ / (2 * m) := by
    rw [hρdef, gs_johnson]
    push_cast
    rfl
  rw [hgs]
  -- `1 - √ρ - √ρ/(2m) < 1 - ρ  ⟺  ρ < √ρ + √ρ/(2m)`
  linarith

/-- **The Johnson lane stops strictly below the Johnson edge `1 − √ρ` for finite `m`.**
The `√ρ/(2m)` multiplicity defect makes `gs_johnson k n m < 1 − √ρ`; the supremum
`1 − √ρ` (the Johnson radius, the lower edge of the prize window) is approached but never
reached.  So the prize window's *lower endpoint itself* is outside the §5-reachable set. -/
theorem gs_johnson_lt_one_sub_sqrt_rho {k n m : ℕ} (hm : 0 < m)
    (hρpos : (0 : ℝ) < (k : ℚ) / n) :
    gs_johnson k n m < 1 - Real.sqrt ((k : ℚ) / n : ℝ) := by
  set ρ : ℝ := ((k : ℚ) / n : ℝ) with hρdef
  have hρpos' : (0 : ℝ) < ρ := hρpos
  have hsqrt_pos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρpos'
  have hextra_pos : 0 < Real.sqrt ρ / (2 * m) := by positivity
  have hgs : gs_johnson k n m = 1 - Real.sqrt ρ - Real.sqrt ρ / (2 * m) := by
    rw [hρdef, gs_johnson]
    push_cast
    rfl
  rw [hgs]; linarith

/-- **The reachable-vs-prize separation, as one statement.**  For a non-degenerate rate
`0 < ρ < 1` and any finite multiplicity `m`, the [BCIKS20]/`CellPackageSupply` radius is
strictly below *both* the Johnson edge `1 − √ρ` (prize-window lower endpoint) and capacity
`1 − ρ`.  Hence the character-sum-free Face-1 floor route lands on `[0, gs_johnson)` only,
which is disjoint from the prize window `(1 − √ρ, 1 − ρ − Θ(1/log n))`. -/
theorem face1_radius_below_prize_window {k n m : ℕ} (hm : 0 < m)
    (hρpos : (0 : ℝ) < (k : ℚ) / n) (hρlt : ((k : ℚ) / n : ℝ) < 1) :
    gs_johnson k n m < 1 - Real.sqrt ((k : ℚ) / n : ℝ) ∧
    gs_johnson k n m < 1 - ((k : ℚ) / n : ℝ) :=
  ⟨gs_johnson_lt_one_sub_sqrt_rho hm hρpos, gs_johnson_lt_capacity hm hρpos hρlt⟩

end ArkLib.ProximityGap.Frontier.Face1JohnsonCap

/-! ## Axiom audit — expected `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.ProximityGap.Frontier.Face1JohnsonCap.gs_johnson_lt_capacity
#print axioms ArkLib.ProximityGap.Frontier.Face1JohnsonCap.gs_johnson_lt_one_sub_sqrt_rho
#print axioms ArkLib.ProximityGap.Frontier.Face1JohnsonCap.face1_radius_below_prize_window
