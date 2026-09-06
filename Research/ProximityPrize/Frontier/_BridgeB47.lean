/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B47 (target E4) — the cascade tail: full over-determination leaves only the trivial γ

**Context (kb `deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, E4 / E2).**
The binding cascade `D*(m)` (`m = s − k` = over-determination depth) is observed to terminate
at the value `1`: the measured cascades end `… , 1, 1, 1`
(`n=8`: `[40,9,5,1,1]`; `n=16`: `[3936,89,9,9,9,8,1,1,1]`). E4's *tail* asserts that at **full
over-determination** (`s = n`, depth `m = n − k` maximal) the worst far-line incidence collapses
to the single trivial Reed–Solomon-membership direction `γ`: `D*(n − k) ≤ 1` (in fact `= 1` when
the line meets the code).

The substrate object is `IncidencePeriodBridge.lineIncidence G s₀ s₁`, the number of scalars
`γ` with `s₀ + γ·s₁ ∈ G`. Over-determination shrinks the admissible ball `G`. At *full*
over-determination the ball has collapsed to **at most one point** (the unique syndrome
compatible with `n` linear constraints — the trivial RS membership). This file proves the
**tail collapse** directly on the substrate object:

* `lineIncidence_le_card` — for **any** direction `s₁`, `lineIncidence G s₀ s₁ ≤ G.card`
  is *not* generally true (a constant direction `s₁ = 0` blows the count up to `q`); but for a
  **generic** (nonzero) direction the line is a bijection of `F`, so the incidence equals
  `G.card` exactly. We record both: `lineIncidence_nonzero_dir_eq_card` (the substrate's own
  bijection, re-exported) and, the tail proper,
* `lineIncidence_tail_le_one` — if the fully-over-determined ball is a **subsingleton**
  (`G.card ≤ 1`) and the direction is **nonzero** (generic far-coset direction), then
  `lineIncidence G s₀ s₁ ≤ 1`: only the trivial RS-membership `γ` survives.
* `lineIncidence_tail_eq_one` — if the ball is a **singleton** `{g}` and the direction is
  nonzero, the incidence is *exactly* `1`: the unique `γ` solving `s₀ + γ·s₁ = g`.
* `lineIncidence_tail_eq_zero_or_one` — packaged tail dichotomy: a subsingleton ball and a
  nonzero direction force `D* ∈ {0, 1}`.

Axiom-clean; pure field algebra + the substrate bijection. Issue #444, target E4 (cascade tail).
-/

open Finset
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.BridgeB47

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Generic-direction incidence equals the ball size (substrate bijection).**
For a *nonzero* direction `s₁ ≠ 0`, the affine map `γ ↦ s₀ + γ·s₁` is a bijection of `F`, so its
preimage of the ball `G` has cardinality exactly `G.card`. This is the over-determination
mechanism: deepening the constraint shrinks `G`, and at a generic direction the line incidence
tracks `G.card` one-for-one. (Re-derivation of the `s₁ ≠ 0` branch inside
`IncidencePeriodBridge.lineIncidence_period_sum`.) -/
theorem lineIncidence_nonzero_dir_eq_card (G : Finset F) (s₀ s₁ : F) (hs₁ : s₁ ≠ 0) :
    lineIncidence G s₀ s₁ = G.card := by
  unfold lineIncidence
  have hinj : Function.Injective (fun γ : F => s₀ + γ * s₁) := by
    intro a b hab
    simp only at hab
    have : a * s₁ = b * s₁ := by linear_combination hab
    exact mul_right_cancel₀ hs₁ this
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨γ, hγ, rfl⟩; exact hγ
  · intro hz
    refine ⟨(z - s₀) * s₁⁻¹, ?_, ?_⟩
    · have : (z - s₀) * s₁⁻¹ * s₁ = z - s₀ := by field_simp
      rw [this]; simpa using hz
    · have : (z - s₀) * s₁⁻¹ * s₁ = z - s₀ := by field_simp
      rw [this]; ring

/-- **The cascade tail (E4).** At full over-determination the admissible ball is a subsingleton
(`G.card ≤ 1`) — `n` linear constraints pin at most one syndrome. For a generic (nonzero)
direction the worst far-line incidence collapses to at most the single trivial RS-membership `γ`:

  `lineIncidence G s₀ s₁ ≤ 1`.

This is the `D*(n − k) ≤ 1` tail of the binding cascade, proven directly on the substrate
incidence object. -/
theorem lineIncidence_tail_le_one {G : Finset F} (hG : G.card ≤ 1)
    (s₀ s₁ : F) (hs₁ : s₁ ≠ 0) :
    lineIncidence G s₀ s₁ ≤ 1 := by
  rw [lineIncidence_nonzero_dir_eq_card G s₀ s₁ hs₁]
  exact hG

/-- **The cascade tail, singleton case (E4, exact).** If the fully-over-determined ball is a
single point `G = {g}` and the direction is nonzero, the incidence is *exactly* `1`: the unique
`γ = (g − s₀)·s₁⁻¹` solving `s₀ + γ·s₁ = g`. The trivial RS-membership `γ` is the sole survivor —
the `… , 1, 1` tail observed in every measured cascade. -/
theorem lineIncidence_tail_eq_one (g s₀ s₁ : F) (hs₁ : s₁ ≠ 0) :
    lineIncidence ({g} : Finset F) s₀ s₁ = 1 := by
  rw [lineIncidence_nonzero_dir_eq_card _ s₀ s₁ hs₁]
  simp

/-- **Tail dichotomy (E4).** A subsingleton ball (full over-determination) and a generic nonzero
direction force the worst far-line incidence into `{0, 1}` — either the line misses the unique
admissible syndrome, or it meets it in the single trivial `γ`. No higher value is possible at the
cascade tail. -/
theorem lineIncidence_tail_eq_zero_or_one {G : Finset F} (hG : G.card ≤ 1)
    (s₀ s₁ : F) (hs₁ : s₁ ≠ 0) :
    lineIncidence G s₀ s₁ = 0 ∨ lineIncidence G s₀ s₁ = 1 := by
  rw [lineIncidence_nonzero_dir_eq_card G s₀ s₁ hs₁]
  interval_cases h : G.card
  · left; rfl
  · right; rfl

end ArkLib.ProximityGap.BridgeB47

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.BridgeB47.lineIncidence_nonzero_dir_eq_card
#print axioms ArkLib.ProximityGap.BridgeB47.lineIncidence_tail_le_one
#print axioms ArkLib.ProximityGap.BridgeB47.lineIncidence_tail_eq_one
#print axioms ArkLib.ProximityGap.BridgeB47.lineIncidence_tail_eq_zero_or_one
