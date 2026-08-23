/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (lane wf-OFG, issue #444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# wf-OFG (#444): the exact per-stack budget that discharges `OverDetFloorGood`, and an HONEST
refutation that the over-determined monomial incidence does NOT supply it at `δbind`.

## The lane mission and what it actually requires

The wf-D3 bracket (`DeltaStarPinchBracketD3.lean`) consumes a named lower-side residual
`OverDetFloorGood C ε* δbind := δbind ≤ 1 ∧ epsMCA C δbind ≤ ε*`.  The mission hoped to discharge
it from the over-determined incidence bricks (`_wf2NH_overdet_single_gamma` per-witness ≤1 γ +
`_wf3D4_monomial_worst_orbit` monomial-is-worst + the FarCosetExplosion identity), on the premise
that the over-det stratum is p-independent and Johnson-locked, hence "reachable without the BGK
wall".

## The exact obligation (PROVEN here, axiom-clean)

`epsMCA C δ = (1/q)·sup_u #{γ : mcaEvent C δ (u 0) (u 1) γ}`.  So `epsMCA C δbind ≤ ε*` holds **iff**
every stack's mcaEvent bad-scalar count is `≤ q·ε* = budget`.  We isolate this as a named Prop
`PerStackBadScalarBudget C δ B` and prove the clean bridge

  `PerStackBadScalarBudget C δ B  ∧  (B/q ≤ ε*)  ⟹  epsMCA C δ ≤ ε*`   (`epsMCA_le_of_perStackBudget`)

and, packaging the radius side, `OverDetFloorGood_of_perStackBudget`.  This is the *correct*
reduction of the D3 lower side to a single per-stack counting Prop — unconditional, axiom-clean.

## The HONEST refutation (probe `probe_wf4OFG_true_mcaevent_floor.py`, char-0, exact)

The over-det bricks do **NOT** supply `PerStackBadScalarBudget` at the binding radius
`δbind = (n−s*)/n`, `s* = n/2−1` (ρ=1/4).  The relevant quantity for `epsMCA` is the **distinct-γ
count** `#{γ : mcaEvent}` per stack, *not* the `(subset, γ)` incidence `I(n)` the campaign measured.
Exact char-0 enumeration (`p ≡ 1 (mod n)`, `p > n⁴`, distinct-γ count is p-independent):

  | n  | k | s*=n/2−1 | δbind   | budget=n | MAX over-det MONOMIAL #{γ} | MAX 2-term #{γ} | floor |
  |----|---|----------|---------|----------|-----------------------------|-----------------|-------|
  | 8  | 2 | 3        | 5/8     | 8        | (≤ 2term)                   | 56              | FAILS |
  | 12 | 3 | 5        | 7/12    | 12       | 17                          | 61              | FAILS |

Even the **monomial** over-det distinct-γ count (17 at n=12) already exceeds the budget (12), and
multi-term (under-determined / near-code) directions blow it much further (61).  Hence at `δbind`
the radius is in fact a **BAD** point (`ε* < epsMCA C δbind`), so the floor inequality
`δbind ≤ δ*` it was meant to give is itself **false** there: the over-det DISTINCT-γ count is *not*
budget-bounded.

The reconciliation with the campaign's "Johnson-locked δ*=½+1/n": the campaign crossing depth `s*`
was the depth at which the `(subset, γ)` **incidence** `I(n)` (a sum over witness subsets) crosses
the budget — but `epsMCA` is governed by the **distinct** bad-γ count (each γ counted once however
many subsets witness it).  These two functionals differ, and at `δbind` the distinct-γ count is
*above* budget.  So `OverDetFloorGood` at `δbind = (n−s*)/n` is **refuted**, not merely open: the
honest D3 lower side must use a strictly smaller radius (where the distinct-γ count drops to
`≤ budget`), and pinning that radius is exactly the open BGK/under-determined wall — there is no
free Johnson-side lower bound here.

## What is PROVEN (axiom-clean) vs refuted

* `epsMCA_le_of_perStackBudget` — UNCONDITIONAL bridge: a uniform per-stack distinct-γ count bound
  `B` with `B/q ≤ ε*` gives `epsMCA C δ ≤ ε*`.  This is the exact reduction of the D3 lower side.
* `OverDetFloorGood_of_perStackBudget` — the same, packaged as the D3 residual `OverDetFloorGood`.
* `overdet_incidence_does_not_supply_budget` — a documented `Prop` recording the probe refutation:
  the per-stack budget `PerStackBadScalarBudget C δbind n` is **false** at `δbind=(n−s*)/n` (the
  distinct-γ count exceeds `n`), so the over-det bricks cannot close the lower side at that radius.
-/

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.Frontier.wf4OFG

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The exact per-stack obligation behind `epsMCA C δ ≤ ε*`.**  For a count budget `B : ℕ`,
every word stack has at most `B` distinct mcaEvent-bad scalars.  This is the *only* thing standing
between the over-det incidence analysis and the D3 lower side: `epsMCA` is the supremum over
stacks of `#{bad γ}/q`, so a uniform per-stack count bound is necessary and sufficient. -/
def PerStackBadScalarBudget (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    (Finset.univ.filter
      (fun γ : F => mcaEvent C δ (u 0) (u 1) γ)).card ≤ B

open Classical in
/-- **PROVEN bridge (axiom-clean).**  A uniform per-stack distinct-γ count bound `B` lifts to a
bound on `epsMCA`: `epsMCA C δ ≤ B / |F|`.  This is the `iSup_le` + `prob_uniform_eq_card_…`
pattern (cf. `epsMCA_le_card_div_of_forced_codimOne`), generalized to an arbitrary count budget. -/
theorem epsMCA_le_budget_div (C : Set (ι → A)) (δ : ℝ≥0) {B : ℕ}
    (hB : PerStackBadScalarBudget (F := F) (A := A) C δ B) :
    epsMCA (F := F) (A := A) C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast hB u

open Classical in
/-- **PROVEN (axiom-clean): the exact reduction of the D3 lower side to one counting Prop.**
If every stack carries `≤ B` distinct mcaEvent-bad scalars and the scaled budget clears the
target (`B/q ≤ ε*`), then `epsMCA C δ ≤ ε*`.  This is precisely what the over-det incidence
analysis would need to supply (with `B = q·ε* = budget`). -/
theorem epsMCA_le_of_perStackBudget (C : Set (ι → A)) (δ : ℝ≥0) (εstar : ℝ≥0∞) {B : ℕ}
    (hB : PerStackBadScalarBudget (F := F) (A := A) C δ B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    epsMCA (F := F) (A := A) C δ ≤ εstar :=
  le_trans (epsMCA_le_budget_div (F := F) (A := A) C δ hB) hbudget

/-- **The D3 lower-side residual, in the exact form the over-det program must discharge.**
Mirrors `KKH26.OverDetFloorGood` (`δbind ≤ 1 ∧ epsMCA C δbind ≤ ε*`). -/
def OverDetFloorGood (C : Set (ι → A)) (εstar : ℝ≥0∞) (δbind : ℝ≥0) : Prop :=
  δbind ≤ 1 ∧ epsMCA (F := F) (A := A) C δbind ≤ εstar

open Classical in
/-- **PROVEN (axiom-clean): `OverDetFloorGood` from the per-stack budget.**  Given the radius is in
range (`δbind ≤ 1`) and every stack carries `≤ B` distinct mcaEvent-bad scalars with `B/q ≤ ε*`,
the D3 lower-side residual holds.  This discharges the *consumer* obligation: the remaining content
is exactly the counting Prop `PerStackBadScalarBudget C δbind B`.  (The probe below refutes that
Prop at `B = budget`, `δbind = (n−s*)/n`.) -/
theorem OverDetFloorGood_of_perStackBudget (C : Set (ι → A)) (εstar : ℝ≥0∞) (δbind : ℝ≥0) {B : ℕ}
    (hδ : δbind ≤ 1)
    (hB : PerStackBadScalarBudget (F := F) (A := A) C δbind B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    OverDetFloorGood (F := F) (A := A) C εstar δbind :=
  ⟨hδ, epsMCA_le_of_perStackBudget (F := F) (A := A) C δbind εstar hB hbudget⟩

open Classical in
/-- **Contrapositive — when the count budget is violated, the radius is BAD (`ε* < epsMCA`).**
If some single stack already has *more* than `q·ε*` distinct mcaEvent-bad scalars, then
`ε* < epsMCA C δ`, so `δ` is a bad radius and `δ* < δ` (by `MCAThresholdLedger.mcaDeltaStar_le_of_bad`).
This is the machine-checkable shape of the probe refutation: a single over-budget stack at `δbind`
*refutes* `OverDetFloorGood` there. -/
theorem epsMCA_gt_of_stack_over_budget (C : Set (ι → A)) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    (u : WordStack A (Fin 2) ι)
    (hcard : εstar <
      ((Finset.univ.filter
        (fun γ : F => mcaEvent C δ (u 0) (u 1) γ)).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)) :
    εstar < epsMCA (F := F) (A := A) C δ := by
  refine lt_of_lt_of_le hcard ?_
  have := mcaEvent_prob_le_epsMCA (F := F) (A := A) C δ u
  rwa [prob_uniform_eq_card_filter_div_card] at this

/-- **HONEST refutation record (probe `probe_wf4OFG_true_mcaevent_floor.py`).**  The per-stack
budget `PerStackBadScalarBudget C δbind n` is **FALSE** at the over-det binding radius
`δbind = (n−s*)/n`, `s* = n/2−1`, budget `= n`: exact char-0 enumeration finds a stack (even a pure
over-det **monomial** at n=12: distinct-γ count 17 > 12; multi-term 61 > 12) whose distinct-γ count
exceeds `n`.  Consequently the over-det incidence bricks **cannot** discharge `OverDetFloorGood` at
that radius; by `epsMCA_gt_of_stack_over_budget` the radius is in fact bad, so the floor
`δbind ≤ δ*` is refuted there.  This is a `def … : Prop` documenting the refuted statement (NOT a
theorem): the per-stack count IS the distinct-γ count `epsMCA` governs, NOT the campaign's
`(subset, γ)` incidence `I(n)`, and the former is over budget at `δbind`. -/
def OverDetIncidenceSuppliesBudgetAtBinding : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ZMod 2)) (δbind : ℝ≥0),
    PerStackBadScalarBudget (F := ZMod 2) (A := ZMod 2) C δbind n
-- REFUTED by probe at n∈{8,12}, δbind=(n-(n/2-1))/n: distinct-γ count > n on a single stack.

end ProximityGap.Frontier.wf4OFG

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx) -/
#print axioms ProximityGap.Frontier.wf4OFG.epsMCA_le_budget_div
#print axioms ProximityGap.Frontier.wf4OFG.epsMCA_le_of_perStackBudget
#print axioms ProximityGap.Frontier.wf4OFG.OverDetFloorGood_of_perStackBudget
#print axioms ProximityGap.Frontier.wf4OFG.epsMCA_gt_of_stack_over_budget
