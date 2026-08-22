/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedBaseThreshold
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedTelescopeBridge

/-!
# Door-(iv) Lane-3: the gate-threshold base correction, on the REAL `levelWorst` character sum (#444)

`_DoorIVXGatedBaseThreshold` (`02b179c9d`) proved the gate-threshold split telescope ABSTRACTLY (over
an abstract sequence `M : ℕ → ℝ`).  This file instantiates it on the ACTUAL Gauss-period worst-period object
`levelWorst ψ G ζ k = ⨆_{c≠0} ‖eta ψ (levelTower ψ G ζ k) c‖`, getting a CONCRETE base-corrected
prize-scale bound on the real character sum.

The instantiation is honest because the two ingredients are real:
1. The **base factor-2 step is UNCONDITIONAL** on `levelWorst`: `levelWorst (k+1) ≤ 2 · levelWorst k`
   always holds (the level-`(k+1)` value is its own level-`k` value plus the dilate's level-`k` value,
   triangle ⟹ factor 2; `_TowerSpikeBetaGate.levelTower_succ_le_of_bound`).  So the `k*` thin base
   levels — where the `XGatedRatio` `x`-gate is unsatisfiable — pay the *proven* factor 2, no
   assumption needed.
2. The **cancellation levels carry the open `√2` gate** `LevelRatioBoundNZ` (the corrected `b ≠ 0`
   object, `_BetaGatedRatioGate`), but only for the levels `k* ≤ k < μ` actually in the cancellation
   regime — exactly the realistic hypothesis the `x`-gate provides.

> **(unconditional factor-2 base, `k < k*`) ∧ (open `√2` gate, `k* ≤ k < μ`)
>   ⟹  `levelWorst μ ≤ 2^{k*} · (√2)^{μ−k*} · levelWorst 0 = √(2^{k*}) · √n · levelWorst 0`.**

At `2^μ = n` this is the concrete base-corrected prize floor on the real Gauss period: the `√2`-saving
covers only the `μ − k*` cancelling levels; the `k*` thin base levels are proven-non-cancelling
(factor 2), costing the explicit `√(2^{k*})` factor over the clean `√n`.  Since `k* = O(log log p)` is
`μ`-independent, the prize-scale saving survives — but on the REAL object, not just abstractly.

Lane-3 constraint companion to the XGate reduction, on the concrete character sum.  NO CORE /
cancellation / completion / moment / anti-concentration / capacity claim.  CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope
open ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge
open ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold

namespace ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The base factor-2 step is UNCONDITIONAL on `levelWorst`.**  For every tower level `k` (with the
disjointness of the level from its dilate, automatic for `ζ ≠ 0` on a proper tower), the level worst
period at most doubles: `levelWorst (k+1) ≤ 2 · levelWorst k`.  This is the trivial triangle step
(`levelTower_succ_le_of_bound`, ratio `2`) lifted to the nonzero-frequency supremum — the proven
factor the thin base levels pay when the `√2` `x`-gate is unavailable. -/
theorem levelWorst_step_two [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (hζ : ζ ≠ 0) (k : ℕ)
    (hdisj : Disjoint (levelTower ψ G ζ k) (dilate ζ (levelTower ψ G ζ k))) :
    levelWorst ψ G ζ (k + 1) ≤ 2 * levelWorst ψ G ζ k := by
  obtain ⟨c₀, hc₀⟩ := exists_ne (0 : F)
  haveI : Nonempty { c : F // c ≠ 0 } := ⟨⟨c₀, hc₀⟩⟩
  -- The level-`k` worst period bounds every level-`k` value (over ALL c, including c = 0? no — we
  -- only need it over the c that appear; use the FULL sup `M = ⨆_c ‖eta (level k) c‖` as the
  -- triangle envelope, then bound that by 2·levelWorst).  Simpler: bound the (k+1) nonzero sup by
  -- 2·(level-k full sup), and the level-k full sup equals levelWorst when... not in general.
  -- Honest route: use `levelTower_succ_le_of_bound` with M := levelWorst k IS NOT valid (levelWorst
  -- is the c≠0 sup, the bound `hM` ranges over ALL c incl 0). So bound via the per-frequency
  -- triangle `levelTower_succ_eq` directly on the nonzero sup.
  unfold levelWorst
  apply ciSup_le
  rintro ⟨b, hb⟩
  -- ‖eta (level (k+1)) b‖ = ‖eta (level k) b + eta (level k) (ζ*b)‖ ≤ ‖..b‖ + ‖..ζb‖ ≤ 2·sup_{c≠0}
  rw [levelTower_succ_eq ψ G hζ k hdisj b]
  have hbdd : BddAbove (Set.range (fun c : { c : F // c ≠ 0 } =>
      ‖eta ψ (levelTower ψ G ζ k) (c : F)‖)) := Set.Finite.bddAbove (Set.finite_range _)
  -- both b and ζ*b are nonzero (b ≠ 0, ζ ≠ 0), so each value ≤ the c≠0 sup.
  have hζb : ζ * b ≠ 0 := mul_ne_zero hζ hb
  have h1 : ‖eta ψ (levelTower ψ G ζ k) b‖
      ≤ ⨆ c : { c : F // c ≠ 0 }, ‖eta ψ (levelTower ψ G ζ k) (c : F)‖ :=
    le_ciSup hbdd ⟨b, hb⟩
  have h2 : ‖eta ψ (levelTower ψ G ζ k) (ζ * b)‖
      ≤ ⨆ c : { c : F // c ≠ 0 }, ‖eta ψ (levelTower ψ G ζ k) (c : F)‖ :=
    le_ciSup hbdd ⟨ζ * b, hζb⟩
  calc ‖eta ψ (levelTower ψ G ζ k) b + eta ψ (levelTower ψ G ζ k) (ζ * b)‖
      ≤ ‖eta ψ (levelTower ψ G ζ k) b‖ + ‖eta ψ (levelTower ψ G ζ k) (ζ * b)‖ := norm_add_le _ _
    _ ≤ (⨆ c : { c : F // c ≠ 0 }, ‖eta ψ (levelTower ψ G ζ k) (c : F)‖)
          + (⨆ c : { c : F // c ≠ 0 }, ‖eta ψ (levelTower ψ G ζ k) (c : F)‖) := by
        exact add_le_add h1 h2
    _ = 2 * ⨆ c : { c : F // c ≠ 0 }, ‖eta ψ (levelTower ψ G ζ k) (c : F)‖ := by ring

/-- **The `√2` cancellation step from a `k*`-restricted gate.**  If the corrected `b ≠ 0` ratio bound
`LevelRatioBoundNZ ψ G ζ μ (√2)` holds (the open `x`-gated cancellation-regime object), then for every
cancellation level `j < r` (i.e. `k* ≤ k* + j < k* + r = μ`) the level worst period obeys the `√2`
step.  Direct specialization of `levelWorst_step_of_levelRatioBoundNZ`. -/
theorem levelWorst_step_sqrt2_shifted [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {kstar r : ℕ}
    (hr : LevelRatioBoundNZ ψ G ζ (kstar + r) (Real.sqrt 2)) {j : ℕ} (hj : j < r) :
    levelWorst ψ G ζ (kstar + j + 1) ≤ Real.sqrt 2 * levelWorst ψ G ζ (kstar + j) :=
  levelWorst_step_of_levelRatioBoundNZ hr (by omega)

/-- **★ Concrete base-corrected prize bound on the real `levelWorst` character sum.**
Let the tower have height `μ = k* + r` with the disjointness holding at every level (`ζ ≠ 0`, proper
tower).  Then with
- the **unconditional** factor-2 base steps for the `k*` thin levels (`levelWorst_step_two`), and
- the **open** `√2` gate `LevelRatioBoundNZ … (√2)` for the `r` cancellation levels above `k*`,

the real Gauss-period worst period obeys
`levelWorst (k*+r) ≤ 2^{k*} · (√2)^r · levelWorst 0`.

At `2^{k*+r} = n` and `2^r = n / 2^{k*}` this is `levelWorst μ ≤ √(2^{k*}) · √n · levelWorst 0`: the
concrete base-corrected prize floor.  The `√2`-saving covers only the `r = μ − k*` cancelling levels;
the `k*` thin base levels pay the *proven* factor 2 (the `x`-gate cannot reach them), costing the
explicit `√(2^{k*})` factor — `μ`-independent, so the prize-scale saving survives on the real object.
Pure assembly of the proven unconditional base step + the open gated cancellation step through the
abstract `split_telescope_two_then_c`. -/
theorem levelWorst_le_base_corrected_of_gate [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (hζ : ζ ≠ 0) (kstar r : ℕ)
    (hdisj : ∀ k, Disjoint (levelTower ψ G ζ k) (dilate ζ (levelTower ψ G ζ k)))
    (hgate : LevelRatioBoundNZ ψ G ζ (kstar + r) (Real.sqrt 2)) :
    levelWorst ψ G ζ (kstar + r)
      ≤ 2 ^ kstar * (Real.sqrt 2) ^ r * levelWorst ψ G ζ 0 := by
  refine split_telescope_sqrt2 (fun k => levelWorst ψ G ζ k)
    (fun k => levelWorst_nonneg ψ G ζ k) kstar r ?_ ?_
  · intro k _
    exact levelWorst_step_two hζ k (hdisj k)
  · intro j hj
    exact levelWorst_step_sqrt2_shifted hgate hj

/-- **The concrete base correction is exactly `√(2^{k*})` over the clean prize floor.**
Rewriting the concrete bound's factor `2^{k*}·(√2)^r` as `√(2^{k*})·(√2)^{k*+r}` (= `√(2^{k*})·√n` at
`2^{k*+r} = n`) makes the real-object base correction explicit: the clean `√n` floor times the
`√(2^{k*})` excess the thin base costs. -/
theorem levelWorst_base_corrected_eq_sqrt_form [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (hζ : ζ ≠ 0) (kstar r : ℕ)
    (hdisj : ∀ k, Disjoint (levelTower ψ G ζ k) (dilate ζ (levelTower ψ G ζ k)))
    (hgate : LevelRatioBoundNZ ψ G ζ (kstar + r) (Real.sqrt 2)) :
    levelWorst ψ G ζ (kstar + r)
      ≤ Real.sqrt (2 ^ kstar) * (Real.sqrt 2) ^ (kstar + r) * levelWorst ψ G ζ 0 := by
  have h := levelWorst_le_base_corrected_of_gate hζ kstar r hdisj hgate
  rwa [split_cost_eq_sqrt_two_pow kstar r] at h

end ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_step_two
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_step_sqrt2_shifted
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_le_base_corrected_of_gate
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_base_corrected_eq_sqrt_form
