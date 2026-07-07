/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15IncidenceMomentInterchange
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15GaussDecompDiagonalSpike

/-!
# LANE R2RUNG (#466 round 16): the r = 2 rung of the diagonal-subtracted incidence tower —
  what is unconditional, and the exact failing inequality for the Wick constant

Target (round-15 `WickForIncidenceAwayAt ψ G H D 2`, `D = {0} ∪ μ_n`):

  `S₂^D := ∑_{s₀∉D} ‖I_H(s₀)‖⁴ ≤ q · 3 · (∑_{b∈H}‖η_b‖²)²`   (Wick, r = 2).

## PROBE VERDICT (`probe_r16_r2rung.py`, `probe_r16_b2_r2_sweep.py`,
   `probe_r16_b2_spikedom.py`; exact FFT arithmetic)

* **The r = 2 rung is TRUE on the original n = 8/16/32, deg = 2/4 sweep with room**:
  `S₂^D/Wick ∈ [0.18, 0.57]`.  However the wider stress probe found a genuine
  **secondary-spike counterexample** outside that narrow grid:
  `n = 64, deg = 8, p = 7681`, `D = {0} ∪ μ_n`, with `S₂^D/Wick = 1.0048`.
  Thus the bare universal statement `WickForIncidenceAwayAt ψ G H ({0} ∪ μ_n) 2` is
  **probe-refuted** unless the diagonal set is enlarged or the regime is restricted.
  `probe_r16_b2_spikeloc.py` shows the largest failing offsets in that cell have full
  multiplicative order, are not in `H`, and are not in `μ_n + μ_n`, so the secondary mass is
  not explained by the primary diagonal or a naive additive-doubling deletion.  The top failing
  values form a single `μ_n`-orbit with constant `|I|` (while the containing `H`-orbit has large
  variation), so the next classification problem lives naturally on `Fˣ/μ_n` cosets.
* The once-plausible STRONGER constant-2 form `S₂^D ≤ q·2·Σ²` is also false in the wider
  sweep (`S₂^D/(2qΣ²)` reaches `1.5072` at `n = 64, deg = 8, p = 7681`).  The named
  `StrongR2Rung` below is therefore retained only as a deliberately strong conditional interface,
  not as a conjectural universal target.
* **CHAIN 1 (Hölder + pointwise) FAILS at prize-relevant scale.** The step
  `S₂^D ≤ (sup_{s∉D}‖I_H‖²)·S₁^D ≤ (sup)·q·Σ` is proven below unconditionally; closing at
  Wick constant 3 then needs `sup_{s∉D}‖I_H(s)‖² ≤ 3·Σ`, which is **probe-FALSE**:
  the measured ratio `sup²/(3Σ)` is `1.01, 2.07, 3.33, 4.25` (n = 8..16, growing like
  `M²/(3n)`) — i.e. the missing inequality is exactly Paley/Problem-A strength
  (`M² ≲ 3n` = Ramanujan) fused with corrected Problem B. **This is the exact failing
  inequality of the pointwise route, with both sides measured.**
* **CHAIN 2 (b-space quadruple split).** By offset-orthogonality
  `S₂ = q·∑_{b₁+b₂=b₃+b₄∈H} η̄₁η̄₂η₃η₄`; the diagonal quadruples (`{b₁,b₂} = {b₃,b₄}`)
  contribute exactly `q·(2Σ² − ∑_{b∈H}‖η_b‖⁴) ≤ q·2Σ²` — INSIDE the Wick budget with the
  constant `2 < 3` (this is where the Wick constant comes from).  The residual inequality
  `q·Off − spike ≤ q·Σ²` held on the original sweep, but the secondary-spike stress test shows
  that deleting only `{0} ∪ μ_n` misses further structured offset mass at larger `deg`.
  The correct next target is therefore a refined diagonal set / secondary-spike classification,
  not a blind proof of the old residual inequality.
* **CHAIN 3 (`M⁴·E(H)` with elementary `E(H) ≤ |H|⁴/p + p|H|`) is DEAD**: pulling all four
  weights by `M` destroys the diagonal/spike cancellation; measured overshoot
  `68× … 10⁸×`. (The elementary Fourier bound on the unweighted energy of the thick
  subgroup is confirmed sharp: `E(H)/(|H|⁴/p) → 1.000`; the loss is entirely the weight pull.)

## What THIS file proves unconditionally (axiom-clean)

* `awayMoment_stepdown_two` — the Hölder step `S₂^D ≤ B·S₁^D` from any pointwise away
  bound `‖I_H‖² ≤ B` off `D`.
* `awayMoment_one_le` — `S₁^D ≤ q·Σ` (from the R13/R15 exact second moment).
* `wickForIncidenceAwayAt_two_of_pointwise` — the sharp REDUCTION: pointwise
  `‖I_H(s∉D)‖² ≤ 3Σ` ⟹ the r = 2 Wick rung. (Its hypothesis is the measured-failing
  inequality above: this pins exactly where the pointwise route dies.)
* `incidence_away_pointwise_le` — UNCONDITIONAL pointwise bound off the diagonal:
  `s₀ ∉ G ⟹ ‖I_H(s₀)‖ ≤ |G|·M_H` (R15 resummation + triangle), `M_H` = the thick-subgroup
  period sup (Weil scale `O(√p)` for full multiplicative `H`).
* `awayMoment_two_le_unconditional` — the resulting **first unconditional quantitative
  r = 2 away bound**: for `G ⊆ D`, `S₂^D ≤ (|G|·M_H)²·q·Σ`. At the prize this overshoots
  Wick by the factor `(n²·M_H²)/(3Σ) ≈ n·deg/3` (measured `5×–21×`) — unconditional, but
  NOT the Wick constant.
* `wickForIncidenceAwayAt_two_of_strong` — the constant-2 form implies the rung.

## Honest scope

The r = 2 Wick rung is NOT proven unconditionally and, in the wide stress regime, the naive
`D = {0} ∪ μ_n` version is probe-FALSE. The two candidate chains fail at measured, named
inequalities: (i) pointwise `sup²≤3Σ` is FALSE (Paley-strength), and (ii) the b-space residual
after deleting only the primary diagonal misses secondary spikes. The unconditional content is
the reduction lattice plus the quantitative `n·deg/3`-lossy rung. CORE OPEN: classify/enlarge
the diagonal set or restrict to a provably stable regime before attacking higher moments.

Issue #466, round 16, lane R2RUNG.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange

namespace ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The two round-15 lane-local `incidenceSum`s are definitionally the same object. -/
theorem incidenceSum_defs_agree (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) :
    incidenceSum ψ G H s₀
      = ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.incidenceSum ψ G H s₀ := rfl

/-! ### (0) Orbit structure of the secondary spikes. -/

/-- **Multiplicative orbit invariance of the incidence sum.**  If both the thin set `G` and the
frequency set `H` are stable under multiplication by `u ≠ 0`, then
`I_H(u·s₀) = I_H(s₀)`.  This explains why the secondary spikes detected by
`probe_r16_b2_spikeloc.py` occur as whole `μ_n`-orbits: for the intended setting
`u ∈ μ_n ⊆ H`, both `G = μ_n` and every compatible thick subgroup `H` are `u`-stable. -/
theorem incidenceSum_mul_left_invariant (ψ : AddChar F ℂ) (G H : Finset F)
    (u s₀ : F) (hu : u ≠ 0)
    (hG : ∀ x : F, u⁻¹ * x ∈ G ↔ x ∈ G)
    (hH : ∀ b : F, u * b ∈ H ↔ b ∈ H) :
    incidenceSum ψ G H (u * s₀) = incidenceSum ψ G H s₀ := by
  classical
  unfold incidenceSum
  refine Finset.sum_nbij' (fun b => u * b) (fun c => u⁻¹ * c) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact (hH b).mpr hb
  · intro c hc
    exact (hH (u⁻¹ * c)).mp (by rwa [mul_inv_cancel_left₀ hu])
  · intro b _
    exact inv_mul_cancel_left₀ hu b
  · intro c _
    exact mul_inv_cancel_left₀ hu c
  · intro b hb
    have heta : eta ψ G (u * b) = eta ψ G b := by
      unfold eta
      refine Finset.sum_nbij' (fun x => u * x) (fun y => u⁻¹ * y) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        exact (hG (u * x)).mp (by rwa [inv_mul_cancel_left₀ hu])
      · intro y hy
        exact (hG y).mpr hy
      · intro x _
        exact inv_mul_cancel_left₀ hu x
      · intro y _
        exact mul_inv_cancel_left₀ hu y
      · intro x hx
        have harg : (u * b) * x = b * (u * x) := by ring
        exact congrArg (fun z : F => ψ z) harg
    rw [heta]
    congr 1
    ring

/-! ### (1) The unconditional Hölder step-down on the away tower. -/

/-- **Hölder step (r = 2 → r = 1).**  Any pointwise square bound `‖I_H(s)‖² ≤ B` off the
deleted diagonal `D` steps the fourth away-moment down to the second:
`S₂^D ≤ B · S₁^D`. -/
theorem awayMoment_stepdown_two (ψ : AddChar F ℂ) (G H D : Finset F) {B : ℝ}
    (hB : ∀ s₀ : F, s₀ ∉ D → ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ B) :
    incidenceMomentAway ψ G H D 2 ≤ B * incidenceMomentAway ψ G H D 1 := by
  classical
  unfold incidenceMomentAway
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsD : s ∉ D := (Finset.mem_sdiff.mp hs).2
  have h2 := hB s hsD
  calc ‖incidenceSum ψ G H s‖ ^ (2 * 2)
      = ‖incidenceSum ψ G H s‖ ^ 2 * ‖incidenceSum ψ G H s‖ ^ (2 * 1) := by ring
    _ ≤ B * ‖incidenceSum ψ G H s‖ ^ (2 * 1) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)

/-- **The away second moment is inside the exact budget**: `S₁^D ≤ q · ∑_{b∈H}‖η_b‖²`
(equality holds for `D = ∅`; deleting offsets only helps). -/
theorem awayMoment_one_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G H D : Finset F) :
    incidenceMomentAway ψ G H D 1
      ≤ (Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  calc incidenceMomentAway ψ G H D 1
      ≤ incidenceMoment ψ G H 1 := incidenceMomentAway_le_incidenceMoment ψ G H D 1
    _ = (Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
        unfold incidenceMoment
        have h21 : (2 * 1 : ℕ) = 2 := rfl
        rw [show (fun s₀ : F => ‖incidenceSum ψ G H s₀‖ ^ (2 * 1))
              = fun s₀ : F => ‖incidenceSum ψ G H s₀‖ ^ 2 from by
            funext s₀; rw [h21]]
        exact incidenceSum_sq_sum_offsets hψ G H

/-! ### (2) The sharp reduction: pointwise `3Σ` bound ⟹ the r = 2 Wick rung.
The hypothesis is the EXACT failing inequality of the pointwise route — probe-FALSE at
large scale (`sup²/(3Σ)` up to 4.25, growing like `M²/(3n)` = Paley strength). -/

/-- **Pointwise-to-rung reduction.**  If every off-diagonal offset satisfies
`‖I_H(s₀)‖² ≤ 3·Σ` (`Σ = ∑_{b∈H}‖η_b‖²`), then the r = 2 diagonal-subtracted Wick rung
`WickForIncidenceAwayAt ψ G H D 2` holds.  This pins exactly what the Hölder route needs;
probes refute the hypothesis at scale, so this consumer is honest-conditional. -/
theorem wickForIncidenceAwayAt_two_of_pointwise {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H D : Finset F)
    (hB : ∀ s₀ : F, s₀ ∉ D →
      ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ 3 * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :
    WickForIncidenceAwayAt ψ G H D 2 := by
  have h2 := awayMoment_stepdown_two ψ G H D hB
  have h1 := awayMoment_one_le hψ G H D
  unfold WickForIncidenceAwayAt
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [hdf]
  calc incidenceMomentAway ψ G H D 2
      ≤ (3 * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) * incidenceMomentAway ψ G H D 1 := h2
    _ ≤ (3 * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
          * ((Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (Fintype.card F : ℝ) * 3 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 := by ring

/-! ### (3) The unconditional pointwise bound off the diagonal, and the resulting
quantitative (non-Wick-constant) r = 2 rung. -/

/-- **Unconditional off-diagonal pointwise bound** (round-15 resummation + triangle):
for `s₀ ∉ G`, `‖I_H(s₀)‖ ≤ |G|·M_H` where `M_H` bounds all nonzero-frequency Gauss periods
of the thick set `H`.  (For full multiplicative `H`, `M_H = O(√p)` — Weil scale.) -/
theorem incidence_away_pointwise_le (ψ : AddChar F ℂ) (G H : Finset F) {s₀ : F}
    (hs₀ : s₀ ∉ G) {MH : ℝ}
    (hMH : ∀ c : F, c ≠ 0 → ‖eta ψ H c‖ ≤ MH) :
    ‖incidenceSum ψ G H s₀‖ ≤ (G.card : ℝ) * MH := by
  classical
  rw [incidenceSum_defs_agree,
    ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike.incidenceSum_eq_period_resummation]
  calc ‖∑ x ∈ G, eta ψ H (s₀ - x)‖
      ≤ ∑ x ∈ G, ‖eta ψ H (s₀ - x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ G, MH := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        have hne : s₀ - x ≠ 0 := sub_ne_zero.mpr (by
          intro h; subst h; exact hs₀ hx)
        exact hMH _ hne
    _ = (G.card : ℝ) * MH := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The first unconditional quantitative r = 2 away bound.**  For any deleted diagonal
`D ⊇ G` and any nonzero-period bound `M_H` on the thick set `H`,

`S₂^D ≤ (|G|·M_H)² · q · Σ`.

At the prize (`|G| = n`, `M_H ≈ √p`, `Σ ≈ n·|H| = n·p/deg`) this is
`≈ (n·deg/3) × Wick` — unconditional but with the measured `5×–21×` overshoot; the gap to
the Wick constant 3 is exactly the failing pointwise inequality of section (2). -/
theorem awayMoment_two_le_unconditional {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G H D : Finset F) (hGD : G ⊆ D) {MH : ℝ}
    (hMH : ∀ c : F, c ≠ 0 → ‖eta ψ H c‖ ≤ MH) :
    incidenceMomentAway ψ G H D 2
      ≤ ((G.card : ℝ) * MH) ^ 2
          * ((Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) := by
  have hB : ∀ s₀ : F, s₀ ∉ D →
      ‖incidenceSum ψ G H s₀‖ ^ 2 ≤ ((G.card : ℝ) * MH) ^ 2 := by
    intro s₀ hs₀
    have hsG : s₀ ∉ G := fun h => hs₀ (hGD h)
    have hpt := incidence_away_pointwise_le ψ G H hsG hMH
    exact pow_le_pow_left₀ (norm_nonneg _) hpt 2
  have h2 := awayMoment_stepdown_two ψ G H D hB
  have h1 := awayMoment_one_le hψ G H D
  calc incidenceMomentAway ψ G H D 2
      ≤ ((G.card : ℝ) * MH) ^ 2 * incidenceMomentAway ψ G H D 1 := h2
    _ ≤ ((G.card : ℝ) * MH) ^ 2
          * ((Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### (4) The named residual: the probe-validated constant-2 form. -/

/-- **The constant-2 strong rung (named strong hypothesis; probe-refuted as a universal target).**
`S₂^D ≤ q·2·Σ²`.  By the b-space quadruple split this is exactly
"the signed off-diagonal quadruple sum is dominated by the diagonal spike it generates plus
`q·Σ²` headroom minus the `∑‖η‖⁴` slack".  The wide stress probe refutes this for
`D = {0} ∪ μ_n` (secondary spikes), so the definition is only a conditional interface. -/
def StrongR2Rung (ψ : AddChar F ℂ) (G H D : Finset F) : Prop :=
  incidenceMomentAway ψ G H D 2
    ≤ (Fintype.card F : ℝ) * 2 * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2

/-- Enlarging the deleted offset set can only make the strong r=2 target easier.

This is the formal hook for the round-17 secondary-spike strategy: once a refined deletion set
`D'` removes whole secondary `μ_n`-orbits, any strong-rung proof for the smaller deleted set
automatically transfers to the larger one. -/
theorem strongR2Rung_mono_deleted (ψ : AddChar F ℂ) (G H : Finset F) {D D' : Finset F}
    (hDD' : D ⊆ D') (h : StrongR2Rung ψ G H D) : StrongR2Rung ψ G H D' := by
  unfold StrongR2Rung at h ⊢
  exact le_trans (incidenceMomentAway_antitone_deleted ψ G H hDD' 2) h

/-- The constant-2 form implies the r = 2 Wick rung (constant 3). -/
theorem wickForIncidenceAwayAt_two_of_strong (ψ : AddChar F ℂ) (G H D : Finset F)
    (h : StrongR2Rung ψ G H D) : WickForIncidenceAwayAt ψ G H D 2 := by
  unfold StrongR2Rung at h
  unfold WickForIncidenceAwayAt
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [hdf]
  have hnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) * (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ^ 2 := by positivity
  nlinarith [h]

end ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung.awayMoment_stepdown_two
#print axioms ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung.awayMoment_one_le
#print axioms
  ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung.wickForIncidenceAwayAt_two_of_pointwise
#print axioms ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung.incidence_away_pointwise_le
#print axioms ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung.awayMoment_two_le_unconditional
#print axioms ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung.strongR2Rung_mono_deleted
#print axioms
  ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung.wickForIncidenceAwayAt_two_of_strong
