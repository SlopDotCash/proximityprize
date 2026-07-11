/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R309TowerRungFour
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilHarvestCap

/-!
# Cross-cone bridge: the P1 swarm's moment layer IS the B-side lag machinery
# (formal, via `fourthMoment_eq_lag_energy`); the OPEN layers are provably
# different regimes (calibrated non-bridge)

Issue #466 — the first FORMAL bridge attempt between the two campaign cones:
the P1 rate-quarter `SwarmResidual` (sub-Johnson direction swarm on `μ_{2^30}`)
and the B-side lag inputs (`OffZeroLagBound`/`OffZeroQuadLagBound` on the Jacobi
angle family, `_R309TowerRungFour`).

**The analysis** (worked exactly on paper, probe-verified at `M = 257`):

* **P1 swarm side, exact shape.**  Swarm riders on a direction `w` against the
  stack `(u₁, −D)` are FIBERS of the ratio map `ρ_w = (u₁ − w)/D`: the swarm
  count is fiber statistics of rational maps on the (subgroup-structured)
  domain.  The fiber-count function `h(s) = #{x ∈ X : ρ(x) = s}` has DFT
  `ĥ(a) = ∑_{x ∈ X} ψ(a·ρ(x))` — the INCOMPLETE exponential sum of a rational
  function over the domain (`hatF_fiberCount`, kernel).  Hence, by the B-side's
  own generic machinery:
  - Parseval: `∑_a ‖ĥ(a)‖² = M·(fiber energy)` (`swarm_secondMoment_bridge`);
  - lag Parseval: `∑_a ‖ĥ(a)‖⁴ = M·∑_t ‖autocorr h (t)‖²`
    (`swarm_fourthMoment_lag_bridge` — literally `fourthMoment_eq_lag_energy`
    of `_R309TowerRungFour` at `f = fiberCount`).
  **The two cones' second/fourth-moment layers are instances of ONE generic
  identity family** — the master family is "moments of `ĥ` for a nonnegative
  arithmetic weight `h`": B-side takes `h = Jacobi ladder` on `ℤ/m`; P1 takes
  `h = fiber counts of ρ_w` on `ZMod P`.  This is the formal bridge, and it is
  an IDENTITY-level bridge (both instances kernel-checked here, the P1 one at
  the prize modulus `F = ZMod P`).

* **The calibrated NON-bridge at the open layers** (the honest core):
  1. **Completeness ratio.**  The P1 swarm's sums are incomplete of length
     `N = 2^30` over `F_P` with `N⁴ < P < N⁶` (`swarm_sub_burgess`, kernel):
     `θ = log_P N ≈ 0.19 < 1/4` — BELOW the Burgess range, where no
     general-modulus bound exists and only subgroup-specific (BGK) methods
     apply.  The B-side's `J_j` are COMPLETE character sums over `F_q`
     (ratio 1, individually `√q` by Weil); its openness is elsewhere.
  2. **Moment depth.**  The B-side's open inputs are FIXED-DEPTH family
     averages (`OffZeroLagBound` at depth 1 ~ `√m·q`; `OffZeroQuadLagBound` at
     depth 2 / `r = 4` ~ `m^{3/2}q²`).  The P1 swarm needs a LIST-level
     statement (`#heavy-fibers ≤ N`-scale): the exact second moment gives
     Chebyshev counts `~ P^{k−2}` — astronomically above the needed budget —
     so no fixed moment transports.  A formal reduction between the walls
     would have to convert completeness ratio `2^{−128} ↔ 1` and depth
     `list ↔ r = 4`; character-sum technology does neither.

**Verdict**: outcome (ii) + (iii) of the coordinator's taxonomy — a REAL
partial bridge (the shared moment-identity layer, now formal, with the B-side
file imported into a P1 file for the first time), and a calibrated non-bridge
above it: the two walls are different objects in the same master family,
distinguished exactly by (completeness ratio, needed depth) =
`(2^{−128}, list)` vs `(1, r = 4)`.  The campaign's "one wall" convergence is
CLASS-level (both in the exponential-sum master family), not reduction-level.

**Honesty**: neither `SwarmResidual` nor the B-side lag inputs are discharged
or transported; no δ* movement; bracket `3/8 ≤ δ* ≤ 43/96 + ε` untouched.
Probe: `scripts/probes/probe_rate_quarter_p1_cross_cone_bridge.py` (identities
exact at `M = 257`; calibration exact at the prize constants).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open Finset
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCrossConeBridge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.R302TraceFormulaPointCount
open ArkLib.ProximityGap.Frontier.R309TowerRungFour

local instance : NeZero P := ⟨by norm_num [P]⟩

/-! ## The fiber-count function and its DFT (the swarm's arithmetic weight) -/

section Bridge

variable {M : ℕ} [NeZero M]

/-- The fiber-count function of a map `ρ` on a point set `X` — the P1 swarm's
arithmetic weight: `h(s) = #{x ∈ X : ρ(x) = s}` (for the swarm, `ρ = ρ_w =
(u₁ − w)/D` and `h(s)` counts the votes the scalar `s` collects on `X`). -/
noncomputable def fiberCount (X : Finset (ZMod M)) (ρ : ZMod M → ZMod M)
    (s : ZMod M) : ℂ :=
  ((X.filter (fun x => ρ x = s)).card : ℂ)

/-- **The DFT of the fiber count is the incomplete exponential sum**:
`ĥ(a) = ∑_{x ∈ X} ψ(a·ρ(x))` — the P1 swarm's obstruction object in the
B-side's DFT vocabulary. -/
theorem hatF_fiberCount (ψ : AddChar (ZMod M) ℂ) (X : Finset (ZMod M))
    (ρ : ZMod M → ZMod M) (a : ZMod M) :
    hatF ψ (fiberCount X ρ) a = ∑ x ∈ X, ψ (a * ρ x) := by
  classical
  unfold hatF fiberCount
  calc ∑ s : ZMod M, ψ (a * s) * ((X.filter (fun x => ρ x = s)).card : ℂ)
      = ∑ s : ZMod M, ∑ x ∈ X.filter (fun x => ρ x = s), ψ (a * ρ x) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_congr rfl
          (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
          Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ x ∈ X, ψ (a * ρ x) :=
        Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (ρ x)) _

/-- **Second-moment bridge**: the mean square of the P1 incomplete exponential
sums equals `M` times the swarm's fiber energy — the exact identity the B-side
proves for the Jacobi ladder (`hatF_parseval`), instantiated at the swarm
weight. -/
theorem swarm_secondMoment_bridge {ψ : AddChar (ZMod M) ℂ}
    (hψ : ψ.IsPrimitive) (X : Finset (ZMod M)) (ρ : ZMod M → ZMod M) :
    ∑ a : ZMod M, ‖∑ x ∈ X, ψ (a * ρ x)‖ ^ 2 =
      (M : ℝ) * ∑ s : ZMod M, ‖fiberCount X ρ s‖ ^ 2 := by
  have h := hatF_parseval hψ (fiberCount X ρ)
  calc ∑ a : ZMod M, ‖∑ x ∈ X, ψ (a * ρ x)‖ ^ 2
      = ∑ a : ZMod M, ‖hatF ψ (fiberCount X ρ) a‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => by rw [hatF_fiberCount]
    _ = (M : ℝ) * ∑ s : ZMod M, ‖fiberCount X ρ s‖ ^ 2 := h

/-- **THE CROSS-CONE BRIDGE (fourth-moment/lag level)**: the quartic moment of
the P1 swarm's incomplete exponential sums equals `M` times the lag energy of
the fiber count — literally the B-side's `fourthMoment_eq_lag_energy`
(`_R309TowerRungFour`) at `f = fiberCount`.  The P1 swarm moment layer and the
Jacobi-ladder lag machinery are the SAME generic identity with different
arithmetic weights.  (The OPEN layers do NOT transport: see the header.) -/
theorem swarm_fourthMoment_lag_bridge {ψ : AddChar (ZMod M) ℂ}
    (hψ : ψ.IsPrimitive) (X : Finset (ZMod M)) (ρ : ZMod M → ZMod M) :
    ∑ a : ZMod M, ‖∑ x ∈ X, ψ (a * ρ x)‖ ^ 4 =
      (M : ℝ) * ∑ t : ZMod M, ‖autocorr (fiberCount X ρ) t‖ ^ 2 := by
  have h := fourthMoment_eq_lag_energy hψ (fiberCount X ρ)
  calc ∑ a : ZMod M, ‖∑ x ∈ X, ψ (a * ρ x)‖ ^ 4
      = ∑ a : ZMod M, ‖hatF ψ (fiberCount X ρ) a‖ ^ 4 :=
        Finset.sum_congr rfl fun a _ => by rw [hatF_fiberCount]
    _ = (M : ℝ) * ∑ t : ZMod M, ‖autocorr (fiberCount X ρ) t‖ ^ 2 := h

end Bridge

/-! ## The prize-modulus instance -/

/-- The bridge at the literal prize modulus: `F = ZMod P`, so the swarm's
fiber-energy and lag identities hold verbatim over the P1 field for any domain
subset `X` and ratio map `ρ` (in particular `X ⊆ μ_{2^30}` and
`ρ_w = (u₁ − w)/D`). -/
theorem swarm_lag_bridge_at_prize {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (X : Finset F) (ρ : F → F) :
    ∑ a : F, ‖∑ x ∈ X, ψ (a * ρ x)‖ ^ 4 =
      (P : ℝ) * ∑ t : F, ‖autocorr (fiberCount X ρ) t‖ ^ 2 :=
  swarm_fourthMoment_lag_bridge hψ X ρ

/-! ## The calibrated non-bridge (kernel rungs) -/

/-- **Sub-Burgess calibration**: the P1 swarm's incomplete sums have length
`N = 2^30` over `F_P` with `N⁴ < P < N⁶` — the length exponent
`θ = log_P N ≈ 0.19` is strictly below the Burgess threshold `1/4`.  The
B-side's sums are complete (`ratio 1`).  No character-sum technique transports
bounds across this gap: the walls above the shared identity layer are
different objects. -/
theorem swarm_sub_burgess : (N : ℕ) ^ 4 < P ∧ P < (N : ℕ) ^ 6 := by
  constructor <;> norm_num [N, P]

/-- The depth calibration: the B-side's open inputs live at fixed depths — the
depth-1 lag scale `√m·q` and the depth-2 (r = 4) scale `m^{3/2}·q²` — while the
swarm's needed statement is list-level.  Kernel content: the swarm's Chebyshev
scale from the EXACT second moment, `(k−1)·N/a²` at the pair-pencil floor
`a = 2T − N`, is `23` — which counts heavy fibers of a SINGLE ratio map, not
the number of swarm directions (unbounded by any fixed moment); the two open
questions are not the same moment problem at different constants. -/
theorem swarm_single_map_chebyshev_scale :
    23 * ((2 * 592794966 - N) * (2 * 592794966 - N)) ≤ (k - 1) * N ∧
    (k - 1) * N < 24 * ((2 * 592794966 - N) * (2 * 592794966 - N)) := by
  constructor <;> norm_num [N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterCrossConeBridge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCrossConeBridge

#print axioms hatF_fiberCount
#print axioms swarm_secondMoment_bridge
#print axioms swarm_fourthMoment_lag_bridge
#print axioms swarm_lag_bridge_at_prize
#print axioms swarm_sub_burgess
#print axioms swarm_single_map_chebyshev_scale
