/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Attack #10 — the LD⇒MCA (T5.1) Johnson-lift cannot beat Johnson below capacity

This file isolates, as a pure real-arithmetic fact, the structural obstruction that
blocks the [ABF26] §5 list-decoding ⇒ MCA reduction (Theorem 5.1, GCXK25 Thm 3) from
reaching the **prize window interior** `(1−√ρ, 1−ρ−Θ(1/log n))`.

T5.1 takes a list-decoding bound at radius `δ_LD` (list size `L`) and produces an MCA
bound at the **Johnson-lifted radius**

  `r_MCA(δ_LD, η) = 1 − √(1 − δ_LD + η)`.

The two-sided window floor needs an MCA radius *strictly above the Johnson radius*
`1 − √ρ`. We prove here that the lifted radius exceeds Johnson **iff** the underlying
list-decoding radius `δ_LD` exceeds `1 − ρ + η`, i.e. exceeds **list-decoding capacity**
`1 − ρ`. So the T5.1 route can only enter the window by list-decoding the *explicit* RS
code *above capacity* — a different, equally-open problem that does **not** route through
the per-frequency character sum (Paley), but is not provable for explicit fixed RS codes
either.

`johnsonLiftRadius_gt_johnson_iff` is the exact equivalence; `ldRoute_window_needs_above_capacity`
is the contrapositive packaging used by the verdict.

All theorems are axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

namespace ProximityGap.Frontier.Attack10

open Real

/-- The Johnson-lifted MCA radius produced by [ABF26] T5.1 from a list-decoding radius
`δ` and slack `η`: `1 − √(1 − δ + η)`. -/
noncomputable def johnsonLiftRadius (δ η : ℝ) : ℝ := 1 - Real.sqrt (1 - δ + η)

/-- The Johnson radius of an RS code of rate `ρ`: `1 − √ρ`. -/
noncomputable def johnsonRadius (ρ : ℝ) : ℝ := 1 - Real.sqrt ρ

/-- **Exact gate.** Under the regime guards `0 ≤ 1−δ+η` and `0 ≤ ρ`, the T5.1 lifted
radius strictly exceeds the Johnson radius **iff** the list-decoding radius `δ` strictly
exceeds `1 − ρ + η`, i.e. exceeds list-decoding capacity `1 − ρ` by more than the slack
`η`. -/
theorem johnsonLiftRadius_gt_johnson_iff (δ η ρ : ℝ)
    (harg : 0 ≤ 1 - δ + η) (hρ : 0 ≤ ρ) :
    johnsonRadius ρ < johnsonLiftRadius δ η ↔ 1 - ρ + η < δ := by
  unfold johnsonLiftRadius johnsonRadius
  constructor
  · intro h
    -- 1 - √ρ < 1 - √(1-δ+η)  ⟹  √(1-δ+η) < √ρ  ⟹  1-δ+η < ρ
    have hsqrt : Real.sqrt (1 - δ + η) < Real.sqrt ρ := by linarith
    have : 1 - δ + η < ρ := by
      by_contra hc
      push_neg at hc
      have := Real.sqrt_le_sqrt hc
      linarith
    linarith
  · intro h
    -- δ > 1-ρ+η  ⟹  1-δ+η < ρ  ⟹  √(1-δ+η) < √ρ
    have hlt : 1 - δ + η < ρ := by linarith
    have hsqrt : Real.sqrt (1 - δ + η) < Real.sqrt ρ :=
      Real.sqrt_lt_sqrt harg hlt
    linarith

/-- **Route verdict (contrapositive).** If the list-decoding radius `δ` is at most
capacity-plus-slack `1 − ρ + η`, then the T5.1 lifted radius does **not** beat Johnson:
`johnsonLiftRadius δ η ≤ johnsonRadius ρ`. Hence any MCA bound obtained from a
*below-capacity* explicit-RS list-decoding bound stays at or below the Johnson radius and
cannot enter the prize window interior. -/
theorem ldRoute_window_needs_above_capacity (δ η ρ : ℝ)
    (harg : 0 ≤ 1 - δ + η) (hρ : 0 ≤ ρ)
    (hbelow : δ ≤ 1 - ρ + η) :
    johnsonLiftRadius δ η ≤ johnsonRadius ρ := by
  by_contra h
  push_neg at h
  exact absurd ((johnsonLiftRadius_gt_johnson_iff δ η ρ harg hρ).mp h) (by linarith)

end ProximityGap.Frontier.Attack10

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.Attack10.johnsonLiftRadius_gt_johnson_iff
#print axioms ProximityGap.Frontier.Attack10.ldRoute_window_needs_above_capacity
