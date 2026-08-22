/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountFreeActionWeld

/-!
# Orbit-count fixed-point split (#444) — `I = z + S·O` with `z ≤ 1` *derived*, not assumed

The far-line incidence decomposes (wf-D5 / wf-D6) as

  `I = z + S·O`,  `z = [α=0 ∈ B] ∈ {0,1}` (the `α=0` in-code coincidence),  `O` = `#`free orbits,

and `_wf3D6_overdet_johnson_lock.lean` runs the budget-crossing arithmetic (`I ≤ n ⟺ O ≤ 2`, etc.)
taking **`z ≤ 1` and the decomposition as hypotheses**.  This file **derives** that decomposition
and the `z ≤ 1` bound from the free-action partition: split the bad set `B` at the distinguished
fixed point `x₀` (the `α = 0` scalar), count the fixed part as the indicator `[x₀ ∈ B] ≤ 1`, and
the remaining `B \ {x₀}` by the free-action orbit-count identity (`OrbitCountFreeActionWeld`).

After this, `I = z + S·O` is an **exact in-tree identity** with `z ≤ 1` a theorem — the wf-D6
hypotheses `hz : z ≤ 1` and the `z + half·O` shape are sourced from structure, not supplied.

## What is formalized here (axiom-clean, no `sorry`)

* `fixedPart_card_le_one` — the `α=0` coincidence contributes at most one:
  `(B.filter (· = x₀)).card ≤ 1` (a Finset filter to a single value has card `≤ 1`).
* `card_eq_fixed_add_free` — the split: `|B| = [x₀∈B] + |B \ {x₀}|`, the fixed point peeled off.
* `card_eq_fixedIndicator_add_orbitCount` — the **welded `I = z + S·O` identity**: with `B \ {x₀}`
  a free `G`-orbit partition (constant fibre size `|G|`), `|B| = z + (#free orbits)·|G|` where
  `z = (B.filter (· = x₀)).card ≤ 1`.  Discharges the wf-D6 decomposition + `hz` from freeness.

## Honest scope

Structural derivation of the `I = z + S·O` decomposition's *shape* and the `z ≤ 1` bound from the
free-action partition off the `α=0` fixed point.  It does **NOT** bound the free-orbit count `O`
(`= BGK` at the window interior, refuted as `O(1)` at `n=8`) — the genuine wall.  Probe
`scripts/probes/probe_orbit_freeaction_weld.py` confirms the split exactly in the prize regime
(`(a,b)=(2,4)`: `z=0`, `O=1`, `S=4`; `(a,b)=(6,1)`: `z=1`, `O=24`, `S=8`; `n=2^a`, `n∣p−1`,
`p≫n³`, NEVER `n=q−1`).  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset

namespace ArkLib.ProximityGap.OrbitCountFixedPointSplit

open ArkLib.ProximityGap.OrbitCountFreeActionWeld

variable {β : Type*} [DecidableEq β]

/-- **The `α=0` coincidence contributes at most one.**  The fixed part `{a ∈ B : a = x₀}` is a
filter to a single value, so its cardinality is `≤ 1`.  This is the `z ≤ 1` bound of the
`I = z + S·O` decomposition, proven structurally (no numerical supply). -/
theorem fixedPart_card_le_one (B : Finset β) (x₀ : β) :
    (B.filter (fun a => a = x₀)).card ≤ 1 := by
  classical
  have hsub : B.filter (fun a => a = x₀) ⊆ {x₀} := by
    intro a ha
    rw [Finset.mem_filter] at ha
    simp [ha.2]
  calc (B.filter (fun a => a = x₀)).card ≤ ({x₀} : Finset β).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton x₀

/-- **The fixed-point split.**  `|B| = |{a∈B : a=x₀}| + |{a∈B : a≠x₀}|`: the bad set is the disjoint
union of the `α=0` fixed part and the free-orbit part `B \ {x₀}`. -/
theorem card_eq_fixed_add_free (B : Finset β) (x₀ : β) :
    B.card = (B.filter (fun a => a = x₀)).card + (B.filter (fun a => a ≠ x₀)).card := by
  classical
  rw [Finset.card_filter_add_card_filter_not]

/-- **The welded `I = z + S·O` identity.**  Splitting the bad set `B` at the `α=0` fixed point `x₀`,
the fixed part contributes `z = |{a∈B : a=x₀}| ≤ 1` and the free-orbit part `B' = {a∈B : a≠x₀}`
contributes `(#free orbits)·|G|` via the free-action orbit-count identity
(`card_eq_orbitCount_mul_card_group`).  Hence

  `|B| = z + (#free orbits)·|G|`,  `z ≤ 1`,

the exact decomposition wf-D6 takes as a hypothesis, now derived from the free action.  `rep` is the
orbit-representative map on `B'` (each fibre a full free `G`-orbit of size `|G|`). -/
theorem card_eq_fixedIndicator_add_orbitCount
    {G : Type*} [Group G] [Fintype G]
    (B : Finset β) (x₀ : β) (rep : β → β)
    (hmap : ∀ a ∈ B.filter (fun a => a ≠ x₀), rep a ∈ B.filter (fun a => a ≠ x₀))
    (hfib : ∀ u ∈ (B.filter (fun a => a ≠ x₀)).image rep,
        ((B.filter (fun a => a ≠ x₀)).filter (fun a => rep a = u)).card = Fintype.card G) :
    B.card = (B.filter (fun a => a = x₀)).card
      + ((B.filter (fun a => a ≠ x₀)).image rep).card * Fintype.card G := by
  rw [card_eq_fixed_add_free B x₀]
  rw [card_eq_orbitCount_mul_card_group (B.filter (fun a => a ≠ x₀)) rep hmap hfib]

/-- **The `z ≤ 1` bound packaged with the identity** — feeds wf-D6's `hz` directly. -/
theorem orbitCount_decomposition_z_le_one
    {G : Type*} [Group G] [Fintype G]
    (B : Finset β) (x₀ : β) (rep : β → β)
    (hmap : ∀ a ∈ B.filter (fun a => a ≠ x₀), rep a ∈ B.filter (fun a => a ≠ x₀))
    (hfib : ∀ u ∈ (B.filter (fun a => a ≠ x₀)).image rep,
        ((B.filter (fun a => a ≠ x₀)).filter (fun a => rep a = u)).card = Fintype.card G) :
    ∃ z O : ℕ, z ≤ 1 ∧ B.card = z + O * Fintype.card G := by
  refine ⟨(B.filter (fun a => a = x₀)).card,
    ((B.filter (fun a => a ≠ x₀)).image rep).card,
    fixedPart_card_le_one B x₀,
    card_eq_fixedIndicator_add_orbitCount B x₀ rep hmap hfib⟩

end ArkLib.ProximityGap.OrbitCountFixedPointSplit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.OrbitCountFixedPointSplit.fixedPart_card_le_one
#print axioms ArkLib.ProximityGap.OrbitCountFixedPointSplit.card_eq_fixed_add_free
#print axioms ArkLib.ProximityGap.OrbitCountFixedPointSplit.card_eq_fixedIndicator_add_orbitCount
#print axioms ArkLib.ProximityGap.OrbitCountFixedPointSplit.orbitCount_decomposition_z_le_one
