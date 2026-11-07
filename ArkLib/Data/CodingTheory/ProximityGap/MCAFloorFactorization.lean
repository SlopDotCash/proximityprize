/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DecoupledJohnsonBound

/-!
# The MCA floor factorization: far regime PROVEN, structured regime NAMED-OPEN (#389)

This file factors the MCA bad-scalar count into two regimes, separated by a threshold `A₁*` on
the *self-agreement of the direction word* `u₁`, and discharges one of them unconditionally:

* **far regime** (`u₁` far from the code: every codeword agrees with `u₁` on `≤ A₁*` points):
  the **decoupled-Johnson** packing bound (`DecoupledJohnsonBound.mca_badScalars_card_le_div`)
  gives `#bad ≤ n²/(a²−n·A₁*)` — **PROVEN, axiom-clean**;
* **structured regime** (`u₁` near the code: some codeword agrees with `u₁` on `> A₁*` points):
  carried as an explicit **named obligation** `StructuredFloorBound`, NOT proven. For RS beyond
  Johnson this regime contains **every** direction (see the PG-106 correction below), so it is the
  full bad-count problem there, not a sub-case of it.

The factorization theorem `badScalars_le_max_of_structuredFloor` is a correct, exhaustive case
split: every stack is either far (handled by the packing bound) or near (handled by the named
obligation `StructuredFloorBound`).

## Correction (audit 2026-10-28, PG-106): beyond Johnson the far regime is empty for RS

An earlier version of this header described the far half as discharging part of the beyond-Johnson
problem and `StructuredFloorBound` as a strictly smaller, independently localized residual. For
Reed–Solomon codes in the beyond-Johnson range this is false — the split is **degenerate** there:

* For RS of dimension `k`, every received direction `u₁` agrees with some codeword on at least `k`
  points (interpolate `u₁` on any `k` evaluation points by a polynomial of degree `< k`).
* The strict gap `n·A₁* < a²` together with `a² ≤ n·k` (in particular the beyond-Johnson range
  `a² ≤ n·(k−1)`) forces `A₁* < k`, so **every** direction is near / structured and the far case
  is empty.
* Concrete instance: `n = 16`, `k = 4`, `a = 6`, `A₁* = 2` has `n·A₁* = 32 < 36 = a² ≤ 48 = n(k−1)`,
  while each direction has a 4-point polynomial explanation (agreement `≥ 4 > 2`).

So in that range `StructuredFloorBound C δ A₁* B` is exactly the all-stack bad-count target
`∀ u₀ u₁, badCount C δ u₀ u₁ ≤ B`; the factorization gives **no narrowing** of the open problem
there. The far-regime packing bound only has content when `A₁* ≥ k`, i.e. `a² > n·k`
(at or above the Johnson-type agreement `√(n·k)`).

**Honest scope.** `StructuredFloorBound` is a named open obligation; it is NOT discharged here, and
for RS beyond Johnson it is not smaller than the original bad-count bound.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal
open Classical

namespace ArkLib.ProximityGap.MCAFloorFactorization

open ProximityGap ArkLib.ProximityGap.DecoupledJohnson

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Abbreviation: the number of MCA-bad scalars of a stack. -/
noncomputable def badCount (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ :=
  (Finset.univ.filter
    (fun γ : F => _root_.ProximityGap.mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card

/-- **The named open obligation: the structured-regime floor.**  For every stack whose direction
word `u₁` is *near the code* — some codeword agrees with `u₁` on more than `A₁*` of the `n`
coordinates — the bad-scalar count is bounded by `B`.  It is the *only* regime not handled by the
decoupled-Johnson packing.  Left as an explicit `Prop`, never proven here.

Caveat (PG-106): for an RS code of dimension `k`, every `u₁` agrees with some codeword on `≥ k`
points, so whenever `A₁star < k` the hypothesis of this `Prop` holds for every `u₁` and the `Prop`
is literally the all-stack bound `∀ u₀ u₁, badCount C δ u₀ u₁ ≤ B`. Under the gap `n·A₁star < a²`
this is the case throughout the beyond-Johnson range `a² ≤ n·k`. -/
def StructuredFloorBound
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (A₁star B : ℕ) : Prop :=
  ∀ u₀ u₁ : ι → A,
    (∃ c ∈ C, A₁star < (Finset.univ.filter (fun i => c i = u₁ i)).card) →
    badCount C δ u₀ u₁ ≤ B

/-- **The floor factorization (the δ\* floor reduces to the structured regime).**  Fix an agreement
floor `a` (`(a:ℝ≥0) ≤ (1−δ)·n`), a direction-proximity threshold `A₁*` with the strict Johnson gap
`n·A₁* < a²`, and a structured-regime bound `B` (the named obligation `StructuredFloorBound`).  Then
**every** stack has

    `#bad ≤ max (n²/(a²−n·A₁*)) B`.

The far half (`u₁` agrees with every codeword on `≤ A₁*` points) is discharged unconditionally by
the decoupled-Johnson packing; the near half is exactly `StructuredFloorBound`.  No other regime
exists, so this is a *complete* case split. It does not by itself narrow the open problem: for RS of
dimension `k` with `a² ≤ n·k` the gap forces `A₁star < k`, the far case is empty, and the bound is
just `hstruct` (PG-106). -/
theorem badScalars_le_max_of_structuredFloor
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (a A₁star B : ℕ)
    (ha : (a : ℝ≥0) ≤ (1 - δ) * Fintype.card ι)
    (hgap : Fintype.card ι * A₁star < a ^ 2)
    (hstruct : StructuredFloorBound C δ A₁star B) :
    badCount C δ u₀ u₁
      ≤ max ((Fintype.card ι) ^ 2 / (a ^ 2 - Fintype.card ι * A₁star)) B := by
  classical
  by_cases hfar : ∀ c ∈ C, (Finset.univ.filter (fun i => c i = u₁ i)).card ≤ A₁star
  · -- FAR: decoupled-Johnson packing applies with `A₁ = A₁*`.
    have hd : badCount C δ u₀ u₁
        ≤ (Fintype.card ι) ^ 2 / (a ^ 2 - Fintype.card ι * A₁star) :=
      mca_badScalars_card_le_div C δ u₀ u₁ a A₁star ha hfar hgap
    exact le_trans hd (le_max_left _ _)
  · -- NEAR (structured): some codeword over-agrees with `u₁` ⟹ the named obligation fires.
    push_neg at hfar
    obtain ⟨c, hcC, hcAgr⟩ := hfar
    have hB := hstruct u₀ u₁ ⟨c, hcC, hcAgr⟩
    exact le_trans hB (le_max_right _ _)

/-- **Corollary — the floor is `≤ B` once the field is large enough to absorb the far term.**
If additionally `n² ≤ B·(a²−n·A₁*)` (the far packing term is itself `≤ B`, automatic when `B` is
the dominant production budget), then *every* stack has `#bad ≤ B` — so the structured obligation
`B` is the *single* number controlling the whole floor. -/
theorem badScalars_le_of_structuredFloor_dominant
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (a A₁star B : ℕ)
    (ha : (a : ℝ≥0) ≤ (1 - δ) * Fintype.card ι)
    (hgap : Fintype.card ι * A₁star < a ^ 2)
    (hdom : (Fintype.card ι) ^ 2 ≤ B * (a ^ 2 - Fintype.card ι * A₁star))
    (hstruct : StructuredFloorBound C δ A₁star B) :
    badCount C δ u₀ u₁ ≤ B := by
  have hmax := badScalars_le_max_of_structuredFloor C δ u₀ u₁ a A₁star B ha hgap hstruct
  have hfar_le : (Fintype.card ι) ^ 2 / (a ^ 2 - Fintype.card ι * A₁star) ≤ B :=
    Nat.div_le_of_le_mul (by rwa [Nat.mul_comm])
  exact le_trans hmax (max_le hfar_le le_rfl)

end ArkLib.ProximityGap.MCAFloorFactorization

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.MCAFloorFactorization.badScalars_le_max_of_structuredFloor
#print axioms ArkLib.ProximityGap.MCAFloorFactorization.badScalars_le_of_structuredFloor_dominant
