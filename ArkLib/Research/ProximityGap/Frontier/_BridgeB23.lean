/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B23 (target E4) — the over-determination cascade `D*(m)` is non-increasing and,
under a measured decay factor `c > 1`, reaches the budget geometrically

**Context (kb `deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, E4).**
The worst-direction over-determined far-line incidence `D*(m)` (`m = s − k` = over-determination
depth) is observed to start near `n³` and *decay geometrically* down the cascade:
`n=16` gives `D* = 3936, 89, 9, …` (factors `≈ ×44, ×10`), reaching the budget `n` within
`≈ 2` decay steps plus the plateau width. E4 asserts two things:

1. **(provable from substrate)** `D*` is *non-increasing* in the depth `m`. Increasing the
   over-determination depth tightens the constraint defining the bad set, so the bad set
   *shrinks* (`A (m+1) ⊆ A m`); its cardinality can only drop. This is the monotonicity half
   (the spec's `B48`).
2. **(empirical — a hypothesis)** each step drops `D*` by a factor *strictly greater than `1`*,
   `c · D*(m+1) ≤ D*(m)` with `c > 1`, *in the measured regime* `m ∈ [start, start+steps)`.
   This is a numerically-measured fact, not derivable from the proven substrate, so we carry it
   as a named hypothesis (honesty contract).

This file delivers:

* `cascade_card_antitone` / `cascade_card_le` — the **monotonicity half**, fully proven: the bad
  set is a decreasing chain `A : ℕ → Finset ι`, `A (m+1) ⊆ A m`, hence `D*(m) := (A m).card` is
  non-increasing.
* `lineIncidence_cascade_antitone` — the monotonicity instantiated on the *actual* substrate
  object `IncidencePeriodBridge.lineIncidence`: a shrinking ball chain `G (m+1) ⊆ G m` makes the
  far-line incidence non-increasing in `m`.
* `cascade_geometric_decay` — the **geometric reach**, proven *modulo* the named decay hypothesis:
  from `c · D*(m+1) ≤ D*(m)` over the window, `D*(start + j) · c^j ≤ D*(start)` for every
  `j ≤ steps`, i.e. the cascade falls by `c^j` after `j` steps. Combined with the start value
  `D*(start) ≈ n³` and the budget `n`, this pins the binding depth `m*` to
  `O(log_c(D*(start)/budget))` steps — the quantitative form of E4.

The decay factor `c > 1` is the *only* non-substrate input, and it is an honest `variable`
hypothesis, never silently discharged. Issue #444, target E4.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB23

/-! ## Part 1 — the monotonicity half (E4.1), fully proven from substrate -/

variable {ι : Type*} [DecidableEq ι]

/-- **The cascade value.** `D*(m) := (A m).card`, the size of the depth-`m` bad set `A m`. -/
def cascadeCard (A : ℕ → Finset ι) (m : ℕ) : ℕ := (A m).card

/-- **One-step monotonicity (E4.1, the spec's `B48`).** If increasing the over-determination
depth by one tightens the constraint — `A (m+1) ⊆ A m` — then the cascade value drops:
`D*(m+1) ≤ D*(m)`. Pure `Finset.card_le_card`; no analytic or regime input. -/
theorem cascade_card_step_le {A : ℕ → Finset ι}
    (hchain : ∀ m, A (m + 1) ⊆ A m) (m : ℕ) :
    cascadeCard A (m + 1) ≤ cascadeCard A m :=
  Finset.card_le_card (hchain m)

/-- **The cascade is non-increasing (E4.1).** From the decreasing-chain hypothesis, `D*` is an
antitone function of the depth: `m₁ ≤ m₂ ⟹ D*(m₂) ≤ D*(m₁)`. -/
theorem cascade_card_antitone {A : ℕ → Finset ι}
    (hchain : ∀ m, A (m + 1) ⊆ A m) :
    Antitone (cascadeCard A) := by
  apply antitone_nat_of_succ_le
  intro m
  exact cascade_card_step_le hchain m

/-- **Non-increasing, range form.** For any `m₁ ≤ m₂`, `D*(m₂) ≤ D*(m₁)`. -/
theorem cascade_card_le {A : ℕ → Finset ι}
    (hchain : ∀ m, A (m + 1) ⊆ A m) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    cascadeCard A m₂ ≤ cascadeCard A m₁ :=
  cascade_card_antitone hchain h

/-! ## Part 2 — monotonicity on the substrate object `lineIncidence` -/

open ArkLib.ProximityGap.IncidencePeriodBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Far-line incidence is monotone in a shrinking ball.** For a fixed line `(s₀, s₁)`, a
nested family of balls `G (m+1) ⊆ G m` makes the substrate far-line incidence
`lineIncidence (G m) s₀ s₁` non-increasing in the depth `m`. This is E4.1 instantiated directly
on `IncidencePeriodBridge.lineIncidence`: deepening the over-determination shrinks the admissible
ball, so the count of line points landing in it can only drop. -/
theorem lineIncidence_cascade_antitone
    (G : ℕ → Finset F) (hchain : ∀ m, G (m + 1) ⊆ G m) (s₀ s₁ : F) :
    Antitone (fun m => lineIncidence (G m) s₀ s₁) := by
  apply antitone_nat_of_succ_le
  intro m
  unfold lineIncidence
  apply Finset.card_le_card
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, hchain m hγ.2⟩

/-! ## Part 3 — the geometric-decay half (E4.2), reduced to the measured decay factor -/

/-- **The measured decay hypothesis (E4.2).** In the measured window `[start, start+steps)`, each
cascade step drops the value by a factor at least `c`: `c · D*(m+1) ≤ D*(m)`. This is the
empirical content of E4 ("drops by a factor `>1` per step"); it is *not* derivable from the
proven substrate and is carried as a named hypothesis. We work with the cast `(D*(m) : ℝ)`. -/
def MeasuredDecay (D : ℕ → ℕ) (c : ℝ) (start steps : ℕ) : Prop :=
  ∀ j, j < steps → c * (D (start + j + 1) : ℝ) ≤ (D (start + j) : ℝ)

/-- **Geometric reach (E4.2), modulo the measured decay factor.** If `c > 1` and the cascade
satisfies `MeasuredDecay D c start steps`, then after `j ≤ steps` steps the value has fallen by
`c^j`:

  `(D (start + j) : ℝ) · c ^ j ≤ (D start : ℝ)`.

Equivalently `D (start + j) ≤ D start / c^j`. With `D start ≈ n³` and budget `n`, the binding
depth is reached within `j ≈ log_c (n³ / n) = 2 log_c n` steps — the quantitative form of E4
("from `~n³` to budget `n` is `≈ 2` decay steps plus the plateau"). The decay factor `c > 1` is
the only non-substrate input. -/
theorem cascade_geometric_decay {D : ℕ → ℕ} {c : ℝ} (hc : 1 < c)
    {start steps : ℕ} (hdec : MeasuredDecay D c start steps) :
    ∀ j, j ≤ steps → (D (start + j) : ℝ) * c ^ j ≤ (D start : ℝ) := by
  have hc0 : (0 : ℝ) < c := lt_trans one_pos hc
  intro j hj
  induction j with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ steps := Nat.le_of_succ_le hj
    have hklt : k < steps := hj
    -- decay at step k: c * D(start+k+1) ≤ D(start+k)
    have hstep : c * (D (start + k + 1) : ℝ) ≤ (D (start + k) : ℝ) := hdec k hklt
    -- IH: D(start+k) * c^k ≤ D start
    have ihk := ih hk
    -- multiply the decay by c^k (≥ 0) and chain:
    have hck : (0 : ℝ) ≤ c ^ k := le_of_lt (pow_pos hc0 k)
    have : (D (start + (k + 1)) : ℝ) * c ^ (k + 1)
        = (c * (D (start + k + 1) : ℝ)) * c ^ k := by
      rw [pow_succ]
      have : start + (k + 1) = start + k + 1 := by ring
      rw [this]
      ring
    rw [this]
    calc (c * (D (start + k + 1) : ℝ)) * c ^ k
        ≤ (D (start + k) : ℝ) * c ^ k := by
          exact mul_le_mul_of_nonneg_right hstep hck
      _ ≤ (D start : ℝ) := ihk

/-- **Binding depth bound (E4 corollary).** Under the same hypotheses, once `c ^ j` exceeds
`D start / budget` the cascade has dropped to or below the budget. Concretely: if
`(budget : ℝ) * c ^ j ≥ (D start : ℝ)` and `0 < budget`, the depth-`(start+j)` value is at most
the budget — the cascade *binds* by depth `start + j`. This makes E4's "reaches budget `n` within
a few decay steps" an explicit consequence of the decay factor. -/
theorem cascade_binds_by_depth {D : ℕ → ℕ} {c : ℝ} (hc : 1 < c)
    {start steps : ℕ} (hdec : MeasuredDecay D c start steps)
    {j : ℕ} (hj : j ≤ steps) {budget : ℝ} (hbud : 0 < budget)
    (hreach : (D start : ℝ) ≤ budget * c ^ j) :
    (D (start + j) : ℝ) ≤ budget := by
  have hc0 : (0 : ℝ) < c := lt_trans one_pos hc
  have hcj : (0 : ℝ) < c ^ j := pow_pos hc0 j
  have hgeo := cascade_geometric_decay hc hdec j hj
  -- D(start+j) * c^j ≤ D start ≤ budget * c^j, so D(start+j) ≤ budget.
  have hchain : (D (start + j) : ℝ) * c ^ j ≤ budget * c ^ j := le_trans hgeo hreach
  exact le_of_mul_le_mul_right hchain hcj

end ArkLib.ProximityGap.BridgeB23

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.BridgeB23.cascade_card_step_le
#print axioms ArkLib.ProximityGap.BridgeB23.cascade_card_antitone
#print axioms ArkLib.ProximityGap.BridgeB23.cascade_card_le
#print axioms ArkLib.ProximityGap.BridgeB23.lineIncidence_cascade_antitone
#print axioms ArkLib.ProximityGap.BridgeB23.cascade_geometric_decay
#print axioms ArkLib.ProximityGap.BridgeB23.cascade_binds_by_depth
