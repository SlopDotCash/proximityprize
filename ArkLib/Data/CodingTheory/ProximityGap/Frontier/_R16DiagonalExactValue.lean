/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15IncidenceMomentInterchange

/-!
# LANE B2 (#466 round 16): the EXACT diagonal value, orbit invariance, and the
  constant-`C` corrected Wick tower (after the probe refutation of the raw away-Wick)

## What round 16 established (probes `probe_r16_b2_quad.py`, `probe_r16_b2_spikedom.py`,
   `probe_r16_b2_spikeloc.py`; float128 independent recomputation)

1. **The r15 named hypothesis `WickForIncidenceAwayAt` (`D = {0} ∪ μ_n`, Wick constant
   `(2r−1)‼`) is FALSE in general.**  Machine countermodels (float128-verified, two independent
   computations):
   * `p = 7681, n = 64, deg = 8` (β ≈ 2.15): `S'_2/Wick₂ = 1.0048`, `S'_3/Wick₃ = 1.0364`;
   * `p = 65537, n = 16, deg = 128/256` (β = 4): ratios `1.07/1.27` and `1.23/2.05`;
   * `p ≈ 2²⁰, n = 32, deg = 128` (β = 4): `S'_3/Wick₃ = 1.038`.
   The refuting offsets are NOT algebraically structured (full multiplicative order, not in `H`,
   not in `μ_n + μ_n`): the failure is an extreme-value TAIL phenomenon of the incidence field,
   not a missed diagonal.  Failure onset: low `β` at moderate `deg`, or thin `H` (`deg ≥ 64`) even
   at `β = 4`.  In the prize-shaped bulk (`β ≈ 4`, `deg ≤ 32`) the rung holds with margins
   `0.55–0.97` rising in `deg` — the Wick constant is a knife-edge.
2. **The corrected named object** is therefore the constant-relaxed tower
   `WickAwayAtWithConstant … C` (below).  `C = 4` covers every probed cell (worst observed
   ratio `2.05` at the thinnest `H`); the moment-method bridge generalizes verbatim with the
   `√C` absorbed into the `⌈log (C·q)⌉` depth (`incidence_sq_le_of_wickAwayAtWithConstant`).
3. **The diagonal is now EXACT, not just spiked** (this file, proved axiom-clean):  when the
   frequency set `G = μ_n` is a subgroup normalizing `H` (hypotheses below), for every
   `s₀ ∈ G`
      `I_H(s₀) = (∑_{b∈H} ‖η_b‖²) / |G|`   — an exact rational value, not an estimate,
   upgrading r15's one-sided spike bound `‖I_H(s₀)‖ ≥ |H| − (q−1)M`.  Consequences:
   * `incidenceSum_mul_offset`: `I_H(u·s₀) = I_H(s₀)` for `u ∈ G` — the incidence field is
     EXACTLY `G`-orbit-invariant (spikes and tails come in `μ_n`-orbits; the probe plateaus of
     identical `‖I‖` values are orbits, not coincidences);
   * `diagMass_exact`: the excluded diagonal mass in the r15 split is the closed form
     `|G| · (Σ/|G|)^{2r}` — no analytic content;
   * `incidenceSum_zero_offset`: `I_H(0) = conj(∑_{b∈H} η_b)`, the second spike in closed form.

## Honest scope

* Nothing here closes Problem B.  The open content is now `WickAwayAtWithConstant ψ G H D r C`
  for the prize instance (some absolute `C`, `D = {0} ∪ μ_n`, `r ≈ ln q`) — probe-calibrated
  (`C = 4` suffices at every probed cell) but OPEN; the raw `C = 1` form is REFUTED as a
  universal statement (countermodels above) and stays only as the instance-level hypothesis it
  always was.
* The exact-diagonal theorems are unconditional (no primitivity of `ψ` needed — pure finite
  reindexing).

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 16, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange

namespace ArkLib.ProximityGap.Frontier.R16DiagonalExactValue

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) The subgroup-action hypotheses, stated Finset-level to match the lane API.

`G` plays `μ_n` (the smooth evaluation subgroup), `H` the thick frequency subgroup with
`μ_n ⊆ H` in the prize regime; we only ever use: `1 ∈ G`, `0 ∉ G`, `G` closed under `*` and
`⁻¹`, and `G` stabilizing `H` by multiplication. -/

/-- `G` is a finite multiplicative subgroup (Finset form). -/
structure IsMulSubgroup (G : Finset F) : Prop where
  one_mem : (1 : F) ∈ G
  zero_notMem : (0 : F) ∉ G
  mul_mem : ∀ u ∈ G, ∀ v ∈ G, u * v ∈ G
  inv_mem : ∀ u ∈ G, u⁻¹ ∈ G

/-- `G` stabilizes `H`: `u ∈ G, b ∈ H ⟹ u·b ∈ H`. -/
def Stabilizes (G H : Finset F) : Prop := ∀ u ∈ G, ∀ b ∈ H, u * b ∈ H

variable {G H : Finset F}

theorem ne_zero_of_mem (hG : IsMulSubgroup G) {u : F} (hu : u ∈ G) : u ≠ 0 :=
  fun h => hG.zero_notMem (h ▸ hu)

/-! ### (1) Reindexing: `η` and `I_H` are exactly `G`-invariant. -/

/-- `η_{b·u} = η_b` for `u ∈ G`: the Gauss-period weight is constant on `G`-orbits of
frequencies. -/
theorem eta_mul_right (hG : IsMulSubgroup G) (ψ : AddChar F ℂ) {u : F} (hu : u ∈ G) (b : F) :
    eta ψ G (b * u) = eta ψ G b := by
  classical
  unfold eta
  have hu0 : u ≠ 0 := ne_zero_of_mem hG hu
  refine Finset.sum_bij' (fun y _ => u * y) (fun y _ => u⁻¹ * y) ?_ ?_ ?_ ?_ ?_
  · intro y hy; exact hG.mul_mem u hu y hy
  · intro y hy; exact hG.mul_mem u⁻¹ (hG.inv_mem u hu) y hy
  · intro y _; dsimp only; rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  · intro y _; dsimp only; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  · intro y _; rw [mul_assoc]

/-- **Exact `G`-orbit invariance of the incidence field**: `I_H(u·s₀) = I_H(s₀)` for `u ∈ G`.
The probe plateaus (many offsets sharing one `‖I‖` value) are `μ_n`-orbits of offsets. -/
theorem incidenceSum_mul_offset (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {u : F} (hu : u ∈ G) (s₀ : F) :
    incidenceSum ψ G H (u * s₀) = incidenceSum ψ G H s₀ := by
  classical
  unfold incidenceSum
  have hu0 : u ≠ 0 := ne_zero_of_mem hG hu
  have hui : u⁻¹ ∈ G := hG.inv_mem u hu
  refine Finset.sum_bij' (fun b _ => b * u) (fun b _ => b * u⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro b hb; dsimp only; rw [mul_comm]; exact hGH u hu b hb
  · intro b hb; dsimp only; rw [mul_comm]; exact hGH u⁻¹ hui b hb
  · intro b _; dsimp only; rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  · intro b _; dsimp only; rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  · intro b _
    rw [eta_mul_right hG ψ hu b]
    congr 2
    rw [mul_assoc]

/-- Constancy of `I_H` on `G` itself: any two diagonal offsets share the value. -/
theorem incidenceSum_const_on (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {s s₀ : F} (hs : s ∈ G) (hs₀ : s₀ ∈ G) :
    incidenceSum ψ G H s = incidenceSum ψ G H s₀ := by
  have hs₀0 : s₀ ≠ 0 := ne_zero_of_mem hG hs₀
  have hu : s * s₀⁻¹ ∈ G := hG.mul_mem s hs s₀⁻¹ (hG.inv_mem s₀ hs₀)
  have hkey : (s * s₀⁻¹) * s₀ = s := by
    rw [mul_assoc, inv_mul_cancel₀ hs₀0, mul_one]
  calc incidenceSum ψ G H s
      = incidenceSum ψ G H ((s * s₀⁻¹) * s₀) := by rw [hkey]
    _ = incidenceSum ψ G H s₀ := incidenceSum_mul_offset hG hGH ψ hu s₀

/-! ### (2) The exact diagonal value. -/

/-- Summing the incidence field over the diagonal `G` telescopes to the total spectral
weight: `∑_{s∈G} I_H(s) = ∑_{b∈H} conj(η_b)·η_b`. -/
theorem sum_incidenceSum_over_G (ψ : AddChar F ℂ) (G H : Finset F) :
    ∑ s ∈ G, incidenceSum ψ G H s
      = ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * eta ψ G b := by
  classical
  unfold incidenceSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.mul_sum]
  rfl

/-- **THE EXACT DIAGONAL VALUE (round-16 upgrade of the r15 spike bound).**  For `s₀ ∈ G`,
`I_H(s₀) = (∑_{b∈H} ‖η_b‖²) / |G|` exactly.  No primitivity, no estimates — pure finite
reindexing.  In particular the all-offset Problem B fails at the exact rational value `Σ/n`,
and the r15 diagonal-subtraction removes exactly this mass. -/
theorem incidenceSum_diag_exact (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {s₀ : F} (hs₀ : s₀ ∈ G) :
    incidenceSum ψ G H s₀
      = ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) / (G.card : ℂ) := by
  classical
  have hnonempty : G.Nonempty := ⟨1, hG.one_mem⟩
  have hcard0 : (G.card : ℂ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hnonempty
  have hconst : ∑ s ∈ G, incidenceSum ψ G H s = (G.card : ℂ) * incidenceSum ψ G H s₀ := by
    calc ∑ s ∈ G, incidenceSum ψ G H s
        = ∑ _s ∈ G, incidenceSum ψ G H s₀ :=
          Finset.sum_congr rfl (fun s hs => incidenceSum_const_on hG hGH ψ hs hs₀)
      _ = (G.card : ℂ) * incidenceSum ψ G H s₀ := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hval : ∑ s ∈ G, incidenceSum ψ G H s
      = ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_incidenceSum_over_G]
    have hterm : ∀ b : F, (starRingEnd ℂ) (eta ψ G b) * eta ψ G b
        = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      intro b
      rw [mul_comm, RCLike.mul_conj]
      norm_cast
    rw [Finset.sum_congr rfl (fun b _ => hterm b)]
    push_cast
    rfl
  rw [eq_div_iff hcard0, mul_comm, ← hconst, hval]

/-- Norm form of the exact diagonal value: `‖I_H(s₀)‖ = Σ/|G|` for `s₀ ∈ G`. -/
theorem norm_incidenceSum_diag_exact (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) {s₀ : F} (hs₀ : s₀ ∈ G) :
    ‖incidenceSum ψ G H s₀‖
      = (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) / (G.card : ℝ) := by
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  rw [incidenceSum_diag_exact hG hGH ψ hs₀]
  rw [norm_div]
  rw [Complex.norm_real, Complex.norm_natCast]
  rw [Real.norm_of_nonneg hSig]

/-- **The exact diagonal mass** excluded by the r15 diagonal subtraction over `G`:
`∑_{s₀∈G} ‖I_H(s₀)‖^{2r} = |G| · (Σ/|G|)^{2r}`.  Closed form — the spike carries zero analytic
content, completing the r15 bookkeeping `incidenceMoment = incidenceMomentAway + diagonal`. -/
theorem diagMass_exact (hG : IsMulSubgroup G) (hGH : Stabilizes G H)
    (ψ : AddChar F ℂ) (r : ℕ) :
    ∑ s₀ ∈ G, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
      = (G.card : ℝ)
          * ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2) / (G.card : ℝ)) ^ (2 * r) := by
  classical
  calc ∑ s₀ ∈ G, ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
      = ∑ _s₀ ∈ G, ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2) / (G.card : ℝ)) ^ (2 * r) := by
        refine Finset.sum_congr rfl (fun s₀ hs₀ => ?_)
        rw [norm_incidenceSum_diag_exact hG hGH ψ hs₀]
    _ = (G.card : ℝ)
          * ((∑ b ∈ H, ‖eta ψ G b‖ ^ 2) / (G.card : ℝ)) ^ (2 * r) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The second spike in closed form: `I_H(0) = conj(∑_{b∈H} η_b)`. -/
theorem incidenceSum_zero_offset (ψ : AddChar F ℂ) (G H : Finset F) :
    incidenceSum ψ G H 0 = (starRingEnd ℂ) (∑ b ∈ H, eta ψ G b) := by
  classical
  unfold incidenceSum
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [mul_zero, AddChar.map_zero_eq_one, mul_one]

/-! ### (3) The constant-`C` corrected tower (post-refutation restatement).

The raw `C = 1` away-Wick is refuted by the round-16 probe countermodels (module docstring);
the corrected named object carries an absolute constant `C`.  Everything the moment method
needs survives: the bridge below pays only a deeper optimal depth `r = ⌈log (C·q)⌉`. -/

/-- **The corrected named open hypothesis (rung `r`, constant `C`)**:
`S_r^D ≤ C · q · (2r−1)‼ · Σ^r`.  `C = 1` is the (refuted-as-universal) r15 form; probes
calibrate `C = 4` as sufficient at every tested `(n, deg, p)` including thin `H` and low `β`.
OPEN for the prize instance; NOT discharged. -/
def WickAwayAtWithConstant (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ) (C : ℝ) : Prop :=
  incidenceMomentAway ψ G H D r
    ≤ C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
        * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r)

/-- Relaxation: the raw rung implies every constant-`C` rung with `C ≥ 1`. -/
theorem wickAwayAtWithConstant_of_wickForIncidenceAwayAt {ψ : AddChar F ℂ}
    (G H D : Finset F) (r : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (h : WickForIncidenceAwayAt ψ G H D r) :
    WickAwayAtWithConstant ψ G H D r C := by
  unfold WickAwayAtWithConstant
  have hX : (0 : ℝ) ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
      * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by positivity
  calc incidenceMomentAway ψ G H D r
      ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := h
    _ = 1 * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r) := by ring
    _ ≤ C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_right hC hX

/-- Base rungs survive relaxation: `r = 0` for any `C ≥ 1`. -/
theorem wickAwayAtWithConstant_zero (ψ : AddChar F ℂ) (G H D : Finset F)
    {C : ℝ} (hC : 1 ≤ C) :
    WickAwayAtWithConstant ψ G H D 0 C :=
  wickAwayAtWithConstant_of_wickForIncidenceAwayAt G H D 0 hC
    (wickForIncidenceAwayAt_zero ψ G H D)

/-- Base rungs survive relaxation: `r = 1` for any `C ≥ 1` (needs primitivity, as in r15). -/
theorem wickAwayAtWithConstant_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H D : Finset F) {C : ℝ} (hC : 1 ≤ C) :
    WickAwayAtWithConstant ψ G H D 1 C :=
  wickAwayAtWithConstant_of_wickForIncidenceAwayAt G H D 1 hC
    (wickForIncidenceAwayAt_one hψ G H D)

/-- A constant-relaxed rung with constant at most `1` collapses back to the exact R15 away-Wick
rung.  This is the threshold gate used by later lanes: once a proposed route proves
`WickAwayAtWithConstant … r C` with `C ≤ 1`, no additional bookkeeping is needed. -/
theorem wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one {ψ : AddChar F ℂ}
    (G H D : Finset F) (r : ℕ) {C : ℝ} (hC : C ≤ 1)
    (hwick : WickAwayAtWithConstant ψ G H D r C) :
    WickForIncidenceAwayAt ψ G H D r := by
  unfold WickForIncidenceAwayAt WickAwayAtWithConstant at *
  have hX : (0 : ℝ) ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
      * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by positivity
  calc incidenceMomentAway ψ G H D r
      ≤ C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r) := hwick
    _ ≤ 1 * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_right hC hX
    _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by ring

/-- The `r = 2` specialization of the constant-`≤ 1` gate, expressed in R15's raw
fourth-moment-with-diagonal target. -/
theorem rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one {ψ : AddChar F ℂ}
    (G H D : Finset F) {C : ℝ} (hC : C ≤ 1)
    (hwick : WickAwayAtWithConstant ψ G H D 2 C) :
    RawFourthMomentWithDiagonal ψ G H D :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G H D).mp
    (wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one G H D 2 hC hwick)

/-- **The corrected moment-method bridge.**  A single constant-`C` rung at the (deeper)
optimal depth `r = ⌈log (C·q)⌉` still yields off-diagonal approximate Problem B:
`‖I_H(s₀)‖² ≤ 2e·Σ·r` for every `s₀ ∉ D`.  The constant is absorbed into the depth — the
`√(2e·log)` loss shape of the r15 bridge is unchanged. -/
theorem incidence_sq_le_of_wickAwayAtWithConstant {ψ : AddChar F ℂ} (G H D : Finset F)
    {C : ℝ} (hC : 1 ≤ C) (hq : 1 ≤ (Fintype.card F : ℝ))
    (r : ℕ) (hr : r = ⌈Real.log (C * (Fintype.card F : ℝ))⌉₊) (hr1 : 1 ≤ r)
    (hwick : WickAwayAtWithConstant ψ G H D r C) {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖ ^ 2
      ≤ 2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * r := by
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by positivity
  have hCq : (1 : ℝ) ≤ C * (Fintype.card F : ℝ) := by nlinarith
  have hpow : ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
      ≤ (C * (Fintype.card F : ℝ)) * (2 * r : ℝ) ^ r
          * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by
    calc ‖incidenceSum ψ G H s₀‖ ^ (2 * r)
        ≤ incidenceMomentAway ψ G H D r := pow_le_incidenceMomentAway ψ G H D hs r
      _ ≤ C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r) := hwick
      _ ≤ (C * (Fintype.card F : ℝ)) * (2 * r : ℝ) ^ r
            * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by
          have h1 := doubleFactorial_two_sub_one_le r
          have h2 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
          have h3 : (0 : ℝ) ≤ (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ r := by positivity
          have hC0 : (0 : ℝ) ≤ C := by linarith
          nlinarith [h1, h2, h3, mul_nonneg h2 h3, mul_nonneg hC0 (mul_nonneg h2 h3)]
  exact sq_le_of_pow_ceil (norm_nonneg _) hCq hSig r hr hr1 hpow

/-- Square-rooted constant-`C` bridge.  A single constant-relaxed rung at
`r = ⌈log (Cq)⌉` gives the usual approximate-Problem-B norm bound away from `D`. -/
theorem incidence_le_of_wickAwayAtWithConstant {ψ : AddChar F ℂ} (G H D : Finset F)
    {C : ℝ} (hC : 1 ≤ C) (hq : 1 ≤ (Fintype.card F : ℝ))
    (r : ℕ) (hr : r = ⌈Real.log (C * (Fintype.card F : ℝ))⌉₊) (hr1 : 1 ≤ r)
    (hwick : WickAwayAtWithConstant ψ G H D r C) {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * r) := by
  have hsq := incidence_sq_le_of_wickAwayAtWithConstant G H D hC hq r hr hr1 hwick hs
  rw [show ‖incidenceSum ψ G H s₀‖ = Real.sqrt (‖incidenceSum ψ G H s₀‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hsq

/-- Constant-`C` corrected approximate Problem-B corollary away from the deleted set.  If the
Fourier coefficients on `H` obey `‖η_b‖ ≤ M`, then a constant-relaxed Wick rung at
`⌈log (Cq)⌉` gives
`‖I_H(s₀)‖ ≤ sqrt(2e · |H| · M² · ⌈log(Cq)⌉)` for `s₀ ∉ D`. -/
theorem approxB_away_of_wickAwayAtWithConstant {ψ : AddChar F ℂ} (G H D : Finset F)
    {C : ℝ} (hC : 1 ≤ C) (hq : 1 ≤ (Fintype.card F : ℝ))
    (r : ℕ) (hr : r = ⌈Real.log (C * (Fintype.card F : ℝ))⌉₊) (hr1 : 1 ≤ r)
    (hwick : WickAwayAtWithConstant ψ G H D r C)
    {M : ℝ} (_hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M)
    {s₀ : F} (hs : s₀ ∉ D) :
    ‖incidenceSum ψ G H s₀‖
      ≤ Real.sqrt (2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2) * r) := by
  refine le_trans (incidence_le_of_wickAwayAtWithConstant G H D hC hq r hr hr1 hwick hs)
    (Real.sqrt_le_sqrt ?_)
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hM b hb) 2
      _ = (H.card : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcoef : 0 ≤ 2 * Real.exp 1 * (r : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hsum hcoef]

end ArkLib.ProximityGap.Frontier.R16DiagonalExactValue

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.eta_mul_right
#print axioms ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.incidenceSum_mul_offset
#print axioms ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.incidenceSum_diag_exact
#print axioms ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.norm_incidenceSum_diag_exact
#print axioms ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.diagMass_exact
#print axioms ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.incidenceSum_zero_offset
#print axioms
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.wickAwayAtWithConstant_of_wickForIncidenceAwayAt
#print axioms
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.incidence_sq_le_of_wickAwayAtWithConstant
#print axioms
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.incidence_le_of_wickAwayAtWithConstant
#print axioms
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.approxB_away_of_wickAwayAtWithConstant
