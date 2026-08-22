/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharSumDeltaStarBridge
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15GaussDecompDiagonalSpike
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15IncidenceMomentInterchange

/-!
# LANE OFFDIAG (#466 round 16): the Problem-B Prop layer, repaired

Round 15 proved (`_R15GaussDecompDiagonalSpike.problemB_fails_at_diagonal_offset`) that the
ALL-offset hyperplane cancellation `∀ s₀, ‖I_H(s₀)‖ ≤ C·√|H|·M` is **false**: at `s₀ ∈ μ_n` the
χ₀/diagonal term forces `I_H(s₀) = (Σ_{b∈H}‖η_b‖²)/n ≈ |H|`-scale.  This lane settles what that
spike touches in the campaign's *formal* Prop layer, and lands the corrected Prop.

## (a) The audit verdict (adversarial, read against the actual definitions)

1. **`HyperplaneCancellation` was never a Lean `Prop`.**  `grep 'def HyperplaneCancellation'`
   over the tree is EMPTY: the all-offset statement lives only in docstrings
   (`_R13HyperplaneSecondMoment`, `_R14SupNormWeakerThanWall`, `_TwoSidedCapstone`, the expert
   statement).  No axiom-clean theorem consumes it as a hypothesis, so nothing machine-checked
   is falsified by the spike.  The *prose* Prop was false; the corrected off-diagonal form is
   defined below (`OffDiagonalHyperplaneCancellation`) — its first formalization.

2. **`RealizedIncidenceBudget` (`_WallCapstone`) and `IncidenceFromWallGlue`
   (`_TwoSidedCapstone`) are SOUND as consumed.**  Both consist of (i) the structural count
   bound `badCount u ≤ lineIncidence G (s₀ u) (s₁ u)` and (ii) the NAIVE budget
   `⌈|G| + q·B⌉ ≤ E` — the triangle bound, valid at EVERY offset including the spike offsets.
   No consumer anywhere hypothesizes sub-triangle cancellation at a spike offset.  They remain
   exactly as honest (and as vacuous-at-prize) as their docstrings say.

3. **Farness does NOT exclude the spike** — `FarCosetExplosion.FarFromCode` constrains the
   DIRECTION word `u₁` (hence `s₁`) only; the offset `s₀ u` (syndrome of `u₀`) is unconstrained
   and may lie in `μ_n`.  BUT the spike still cannot enter any in-tree consumer, for a stronger
   geometric reason proved below (`lineIncidence_offset_blind`): in the only formalized syndrome
   geometry `V = F`, the affine map `γ ↦ s₀ + γ·s₁` is a bijection for `s₁ ≠ 0`, so
   `lineIncidence G s₀ s₁ = |G|` for **every** offset — the consumed incidence object is
   offset-independent, hence spike-immune.  (The spike lives in the higher-dimensional
   `incidenceSum` model with `|H| > 1`, which is analytically motivated but never wired to
   `lineIncidence` in the tree; the `V = F` annihilator of `s₁ ≠ 0` is `{0}`.)

4. **Consequently the only repair needed is at the Prop-DEFINITION layer** (the object future
   rounds attack), not at the consumer layer.  Still, we re-prove the consumer chain with the
   restricted quantifier so the round-14 outer `iff` demonstrably survives the correction.

## (b) What this file lands (all axiom-clean)

* `OffDiagonalHyperplaneCancellation` — the corrected Problem-B Prop (offsets restricted to
  `s₀ ∉ G`), stated on the round-15 `incidenceSum`.
* `incidenceSum_defs_agree` — the two round-15 local copies of `incidenceSum` are definitionally
  equal (so building on either is compatible).
* `offDiagonal_of_wickAwayAt` — the corrected Prop FOLLOWS from the round-15
  diagonal-subtracted Wick rung at moment-optimal depth, with the explicit constant
  `C = √(2e·⌈ln q⌉)`; i.e. the corrected B is exactly the reduction target
  `WickForIncidenceAwayAt` already banked in round 15 — the Prop layer and the moment layer
  now match.
* `allOffset_bound_of_offDiagonal`(+`_concrete`) — the glue-consumer shape restored with the
  restricted quantifier: corrected-B + the exact diagonal split give a bound at EVERY offset
  (`max` of the diagonal value and the off-diagonal √-scale), which is the per-offset numeric
  interface any future `incidenceSum → lineIncidence` wiring needs.
* `lineIncidence_offset_blind` + `badCount_le_card_of_struct` + `deltaStar_floor_offset_blind` —
  the spike-immunity certificate for the existing consumers: with any nonzero directions, the
  `V = F` glue's incidence is the constant `|G|`, and the δ*-floor consumer chain re-proves with
  NO cancellation hypothesis at all (offset quantifier eliminated, not merely restricted).

NOTHING here closes Problem B: `WickForIncidenceAwayAt` (equivalently
`OffDiagonalHyperplaneCancellation`) remains the open input.  Issue #466, round 16, lane OFFDIAG.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open Finset
open ProximityGap Code
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike

namespace ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation

/-! ### (1) The corrected Problem-B Prop and compatibility of the round-15 objects. -/

section Analytic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The two round-15 local copies of the signed incidence sum are definitionally equal; this
brick may build on either without incompatibility. -/
theorem incidenceSum_defs_agree (ψ : AddChar F ℂ) (G H : Finset F) (s₀ : F) :
    incidenceSum ψ G H s₀
      = ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceSum ψ G H s₀ := rfl

/-- **The corrected Problem-B Prop (round-15 correction, formalized).**  For offsets OFF the
diagonal set `G = μ_n` — the only regime where it can hold, by
`R15GaussDecompDiagonalSpike.problemB_fails_at_diagonal_offset` — the signed hyperplane incidence
sum obeys worst-case square-root cancellation `‖I_H(s₀)‖ ≤ C·√|H|·M`.  This replaces the refuted
all-offset prose Prop `HyperplaneCancellation` (which was never a Lean `Prop`; docstrings only).
OPEN: this is BCHKS Conj 1.12 in the thin-2-power regime, restated off-diagonal. -/
def OffDiagonalHyperplaneCancellation (ψ : AddChar F ℂ) (G H : Finset F)
    (C M : ℝ) : Prop :=
  ∀ s₀ : F, s₀ ∉ G → ‖incidenceSum ψ G H s₀‖ ≤ C * Real.sqrt (H.card : ℝ) * M

/-- **The corrected Prop follows from the round-15 diagonal-subtracted Wick rung** at the
moment-optimal depth `r = ⌈ln q⌉`, with the explicit constant `C = √(2e·r)`.  This is the
wiring lemma that makes the Prop layer match the round-15 moment layer: the open input behind
`OffDiagonalHyperplaneCancellation` is exactly `WickForIncidenceAwayAt ψ G H G r` (the object the
round-15 probes verified empirically at every accessible scale). -/
theorem offDiagonal_of_wickAwayAt {ψ : AddChar F ℂ} (G H : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwick : ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G H G r)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M) :
    OffDiagonalHyperplaneCancellation ψ G H
      (Real.sqrt (2 * Real.exp 1 * (r : ℝ))) M := by
  intro s₀ hs
  have h := ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.approxB_away_of_wickAwayAt
    G H G r hr hr1 hq hwick hM0 hM hs
  rw [← incidenceSum_defs_agree] at h
  refine le_trans h (le_of_eq ?_)
  have hassoc : 2 * Real.exp 1 * ((H.card : ℝ) * M ^ 2) * (r : ℝ)
      = (2 * Real.exp 1 * (r : ℝ)) * (H.card : ℝ) * M ^ 2 := by ring
  rw [hassoc,
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.exp 1 * (r : ℝ) * (H.card : ℝ)),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.exp 1 * (r : ℝ)),
    Real.sqrt_sq hM0]

/-- **The glue-consumer shape, restored with the restricted quantifier.**  The corrected
off-diagonal Prop, together with ANY bound `D` on the diagonal offsets (`s₀ ∈ G`), yields a
per-offset numeric bound at EVERY offset — the `max` of the diagonal value and the off-diagonal
√-scale.  This is the interface shape a consumer of the (falsified) all-offset Prop needed; the
correction costs exactly the replacement `C√|H|·M ⟶ max(D, C√|H|·M)`. -/
theorem allOffset_bound_of_offDiagonal {ψ : AddChar F ℂ} {G H : Finset F} {C M D : ℝ}
    (hoff : OffDiagonalHyperplaneCancellation ψ G H C M)
    (hdiag : ∀ s₀ ∈ G, ‖incidenceSum ψ G H s₀‖ ≤ D) :
    ∀ s₀ : F, ‖incidenceSum ψ G H s₀‖
      ≤ max D (C * Real.sqrt (H.card : ℝ) * M) := by
  intro s₀
  by_cases h : s₀ ∈ G
  · exact le_max_of_le_left (hdiag s₀ h)
  · exact le_max_of_le_right (hoff s₀ h)

/-- The concrete diagonal bound from the round-15 exact split: at `s₀ ∈ G`, the spike value plus
the off-diagonal tail give `‖I_H(s₀)‖ ≤ |H| + (|G|−1)·M_H` where `M_H` bounds the nonzero periods
of the THICK set `H`.  (Triangle on `R15`'s `diagonal_subtracted_incidence_norm_le`.) -/
theorem diagonal_bound_concrete (ψ : AddChar F ℂ) (G H : Finset F)
    {s₀ : F} (hs₀ : s₀ ∈ G) {MH : ℝ}
    (hMH : ∀ c : F, c ≠ 0 → ‖eta ψ H c‖ ≤ MH) :
    ‖incidenceSum ψ G H s₀‖ ≤ (H.card : ℝ) + ((G.card : ℝ) - 1) * MH := by
  have hsplit := diagonal_subtracted_incidence_norm_le ψ G H hs₀ hMH
  calc ‖incidenceSum ψ G H s₀‖
      = ‖(incidenceSum ψ G H s₀ - (H.card : ℂ)) + (H.card : ℂ)‖ := by ring_nf
    _ ≤ ‖incidenceSum ψ G H s₀ - (H.card : ℂ)‖ + ‖(H.card : ℂ)‖ := norm_add_le _ _
    _ ≤ ((G.card : ℝ) - 1) * MH + (H.card : ℝ) := by
        have hc : ‖(H.card : ℂ)‖ = (H.card : ℝ) := by
          simp
        rw [hc]
        linarith
    _ = (H.card : ℝ) + ((G.card : ℝ) - 1) * MH := by ring

/-- **The fully concrete all-offset consumer bound** from the corrected Prop alone (no extra
diagonal hypothesis): every offset obeys
`‖I_H(s₀)‖ ≤ max (|H| + (|G|−1)·M_H) (C·√|H|·M)`. -/
theorem allOffset_bound_of_offDiagonal_concrete {ψ : AddChar F ℂ} {G H : Finset F} {C M MH : ℝ}
    (hoff : OffDiagonalHyperplaneCancellation ψ G H C M)
    (hMH : ∀ c : F, c ≠ 0 → ‖eta ψ H c‖ ≤ MH) :
    ∀ s₀ : F, ‖incidenceSum ψ G H s₀‖
      ≤ max ((H.card : ℝ) + ((G.card : ℝ) - 1) * MH)
          (C * Real.sqrt (H.card : ℝ) * M) :=
  allOffset_bound_of_offDiagonal hoff
    (fun s₀ hs₀ => diagonal_bound_concrete ψ G H hs₀ hMH)

end Analytic

/-! ### (2) Spike-immunity of the existing consumers: the `V = F` incidence is offset-blind. -/

section Consumers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The `V = F` far-line incidence is OFFSET-BLIND (spike-immunity certificate).**  For any
nonzero direction `s₁`, the affine map `γ ↦ s₀ + γ·s₁` is a bijection of `F`, so
`lineIncidence G s₀ s₁ = |G|` for EVERY offset `s₀` — including the diagonal-spike offsets
`s₀ ∈ G`.  Hence the incidence object actually consumed by `RealizedIncidenceBudget`
(`_WallCapstone`) and `IncidenceFromWallGlue` (`_TwoSidedCapstone`) carries NO offset dependence
at all in the formalized geometry: the round-15 diagonal spike cannot enter any in-tree consumer
through `lineIncidence`.  (The spike lives only in the `|H| > 1` `incidenceSum` model, which is
not wired to `lineIncidence` in the tree; for `s₁ ≠ 0` over `V = F` the annihilating frequency
set is `{0}`.) -/
theorem lineIncidence_offset_blind (G : Finset F) (s₀ : F) {s₁ : F} (hs₁ : s₁ ≠ 0) :
    ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence G s₀ s₁ = G.card := by
  classical
  unfold ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence
  refine Finset.card_bij (fun γ _ => s₀ + γ * s₁) ?_ ?_ ?_
  · intro γ hγ
    exact (Finset.mem_filter.mp hγ).2
  · intro a _ b _ hab
    have h1 : a * s₁ = b * s₁ := by
      have := add_left_cancel hab
      exact this
    exact mul_right_cancel₀ hs₁ h1
  · intro y hy
    refine ⟨(y - s₀) / s₁, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have : s₀ + (y - s₀) / s₁ * s₁ = y := by
        rw [div_mul_cancel₀ _ hs₁]
        abel
      simpa [this] using hy
    · have : s₀ + (y - s₀) / s₁ * s₁ = y := by
        rw [div_mul_cancel₀ _ hs₁]
        abel
      simpa using this

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F' : Type} [Field F'] [Fintype F'] [DecidableEq F']
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F' A]

open Classical in
/-- Under the structural half of the glue (`badCount ≤ lineIncidence`) with nonzero directions,
every stack's bad-scalar count is at most `|G|` — uniformly, with NO dependence on the offsets
`s₀ u` and hence no exposure to the diagonal spike. -/
theorem badCount_le_card_of_struct
    (C : Set (ι → A)) (δ : ℝ≥0) (G : Finset F')
    (s₀ s₁ : WordStack A (Fin 2) ι → F')
    (hdir : ∀ u : WordStack A (Fin 2) ι, s₁ u ≠ 0)
    (hStruct : ∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F' => mcaEvent (F := F') C δ (u 0) (u 1) γ)).card
        ≤ ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence G (s₀ u) (s₁ u)) :
    ∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F' => mcaEvent (F := F') C δ (u 0) (u 1) γ)).card
        ≤ G.card := fun u =>
  le_trans (hStruct u) (le_of_eq (lineIncidence_offset_blind G (s₀ u) (hdir u)))

open Classical in
/-- **The δ*-floor consumer chain, re-proved with the offset quantifier ELIMINATED (round-14
outer chain survives the round-15 correction).**  With the structural glue, nonzero directions,
and the budget `|G|/q ≤ ε*`, the threshold reaches `δ` — consuming NO hyperplane-cancellation
Prop at any offset, spike or not.  This is the machine-checked verdict that the existing
campaign consumers are sound as consumed: in the formalized `V = F` geometry the corrected (or
even the refuted) Problem B is never instantiated.  (As before, the budget `|G|/q ≈ n/q ≈ ε*` is
exactly borderline at the prize; no prize closure is claimed.) -/
theorem deltaStar_floor_offset_blind
    (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ : ℝ≥0) (G : Finset F')
    (s₀ s₁ : WordStack A (Fin 2) ι → F')
    (hdir : ∀ u : WordStack A (Fin 2) ι, s₁ u ≠ 0)
    (hStruct : ∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F' => mcaEvent (F := F') C δ (u 0) (u 1) γ)).card
        ≤ ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence G (s₀ u) (s₁ u))
    (hBudget : (G.card : ℝ≥0∞) / (Fintype.card F' : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F') (A := A) C εstar :=
  ArkLib.ProximityGap.CharSumDeltaStarBridge.le_mcaDeltaStar_of_uniformCharSumBound
    C εstar δ (badCount_le_card_of_struct C δ G s₀ s₁ hdir hStruct) hBudget hδ1

end Consumers

end ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation.incidenceSum_defs_agree
#print axioms
  ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation.offDiagonal_of_wickAwayAt
#print axioms
  ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation.allOffset_bound_of_offDiagonal
#print axioms
  ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation.diagonal_bound_concrete
open ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation in
#print axioms allOffset_bound_of_offDiagonal_concrete
#print axioms
  ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation.lineIncidence_offset_blind
#print axioms
  ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation.badCount_le_card_of_struct
#print axioms
  ArkLib.ProximityGap.Frontier.R16OffDiagonalHyperplaneCancellation.deltaStar_floor_offset_blind
