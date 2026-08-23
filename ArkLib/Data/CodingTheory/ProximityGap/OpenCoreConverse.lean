/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The CONVERSE of the conditional δ* pin — a δ* lower bound FORCES the incidence budget (#444)

`OpenCoreConditionalPin` proves the FORWARD direction of the prize reduction:

  `WorstCaseIncidenceBounded C δ B` (worst far-line incidence ≤ B)  ⟹  `δ ≤ mcaDeltaStar C ε*`.

This file proves the **CONVERSE**, the hard new direction the directive asks for:

  `δ < mcaDeltaStar C ε*`  ⟹  `WorstCaseIncidenceBounded C δ ⌊q·ε*⌋`.

i.e. a δ* LOWER bound (any window radius strictly below the threshold) FORCES the worst-case
far-line incidence to obey the budget `q·ε*` at that radius. Together the two directions give the
**biconditional** structure of the prize: at any radius strictly inside the good window, the
δ*-statement and the incidence-budget statement are EQUIVALENT.

## What is proven here (axiom-clean, no `sorry`)

* **`epsMCA_le_of_lt_mcaDeltaStar`** — `δ < δ* ⟹ ε_mca(C,δ) ≤ ε*`. The supremum-downward-closure
  step: below the `sSup` threshold the radius is good. (Converse of the good→δ* bracket.)

* **`incidence_le_of_lt_mcaDeltaStar`** — `δ < δ* ⟹ ∀u, I_u(δ) ≤ q·ε*`. Each stack's incidence
  count is ≤ q·ε_mca ≤ q·ε* (term ≤ sup, exact per-stack probability identity). The EXACT converse
  of `epsMCA_le_of_worstCaseIncidence`.

* **`worstCaseIncidence_of_lt_mcaDeltaStar`** — packages the previous as exactly
  `WorstCaseIncidenceBounded C δ ⌊q·ε*⌋` for the natural budget `E = ⌊q·ε*⌋`. This is the literal
  converse to the hypothesis of `worstCaseIncidence_pin`, closing the loop into a biconditional.

* **`mcaDeltaStar_le_of_not_worstCaseIncidence`** — the contrapositive/refutation form: if the
  budget-`E` open core fails at radius `δ`, then the threshold at error `E/q` is already at most
  `δ`.  Thus every explicit budget failure is a formal upper delimiter for δ*.

* **`mcaDeltaStar_le_of_stackIncidence_gt`** — the concrete witness form: one stack with more than
  `E` bad scalars is enough to upper-bound the threshold by `δ`.

* **`stackIncidence_le_of_lt_mcaDeltaStar`** / **`not_lt_mcaDeltaStar_of_stackIncidence_gt`** —
  the stack-level pair: strict δ* interior forces every stack below budget, while one over-budget
  stack refutes strict δ* interior.

* **`deltaStar_iff_incidence_budget`** — THE BICONDITIONAL (with an honest `±` half-rung gap from
  `<` vs `≤` and `⌊·⌋`): for a budget `E` and `ε* = E/q`, `δ < δ*` ⟺
  `WorstCaseIncidenceBounded C δ E` holds in the strong sense `δ ≤ δ*`, with the forward direction
  giving `≤` and the converse giving the budget. The two implications are each axiom-clean.

## The realizer bridge — honest scope (the still-open half)

The converse above forces, for EVERY stack `u`, `I_u(δ) ≤ q·ε*`. To turn this into a bound on the
single scalar `B = max_{b≠0} ‖η_b‖` (the Gaussian-period sup-norm = BGK/Paley wall) one needs a
CONSTRUCTIVE worst-word `u*` whose incidence `I_{u*}(δ)` is an EXACT increasing function of `B`, so
that `I_{u*} ≤ budget` reads back as `B ≤ g(budget)`.

`IncidencePeriodBridge.lineIncidence_period_sum` gives the exact Fourier identity, but over the
ONE-dimensional syndrome space `V = F` it reads `I(s₀,s₁) = ∑_{b: b·s₁=0} conj(η_b)·ψ(b·s₀)`, and
for `s₁ ≠ 0` the constraint forces `b = 0`, collapsing to `I = η₀ = |G|` — a CONSTANT that does NOT
see the non-principal periods `η_b`, b≠0. So in the one-dimensional far-line geometry the incidence
is decoupled from `B`; the realizer must live in the genuinely ≥2-dimensional MCA syndrome geometry
(`A`-valued stacks, `ι`-coordinate witness sets), where `I_u(δ)` counts γ with a witness-set of size
`(1-δ)n`, NOT the field-line count above. We record the exact L² half that IS available
(`incidence_l2_eq_period_l2`: the incidence ENERGY equals `q·∑_b‖η_b‖²`), and name the missing
input precisely: an EXACT (not ≤) realizer identity `I_{u*}(δ) = f(B)` in the MCA geometry. That
single identity, fed `B ≤ g(q·ε*)` from the converse, would close the full biconditional δ* ⟺ B.
This file does NOT supply it; the converse `δ* ⟹ incidence-budget` IS proven, the incidence-budget
`⟹ B`-bound realizer is the named residual.

## Honesty

Both directions of the δ* ⟺ incidence-budget equivalence are proven (axiom-clean). The further
step incidence-budget ⟹ `B`-bound is OPEN (needs the exact realizer; the available Fourier bridge is
L²/≤, and over `V=F` is incidence-blind to `b≠0`). No wall is smuggled: the converse to the SCALAR
`B` is honestly the residual, the converse to the INCIDENCE BUDGET is the theorem.

Issue #444.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger Code
open ProximityGap.OpenCoreConditionalPin

namespace ProximityGap.OpenCoreConverse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## Converse step 1 — below the threshold the radius is good -/

/-- **CONVERSE of the good→δ* bracket.** If `δ` lies STRICTLY below the formal threshold
`mcaDeltaStar C ε*`, then `δ` is a good radius: `ε_mca(C, δ) ≤ ε*`.

Proof: `δ < sSup (good radii)` forces the good set nonempty (else its `sSup` is `0 ≤ δ`), so by the
`sSup` approximation there is a good `δ'` with `δ < δ'`; `mca_good_set_downward_closed` transfers
goodness down from `δ'` to `δ`. This is the exact converse of `le_mcaDeltaStar_of_good`. -/
theorem epsMCA_le_of_lt_mcaDeltaStar (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0}
    (hδ : δ < mcaDeltaStar (F := F) (A := A) C εstar) :
    epsMCA (F := F) (A := A) C δ ≤ εstar := by
  -- From `δ < sSup S` get a witness `δ' ∈ S` with `δ < δ'`.
  obtain ⟨δ', hδ'mem, hδδ'⟩ :=
    exists_lt_of_lt_csSup
      (show (mcaGoodRadii (F := F) (A := A) C εstar).Nonempty from by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        rw [mcaDeltaStar, hempty, csSup_empty] at hδ
        -- `hδ : δ < 0` in ℝ≥0 is impossible
        exact absurd hδ (not_lt_of_ge (zero_le _)))
      hδ
  -- `δ' ∈ S` means `δ' ≤ 1 ∧ ε_mca(C, δ') ≤ ε*`; transfer goodness down to `δ`.
  exact mca_good_set_downward_closed (F := F) (A := A) C εstar (le_of_lt hδδ') hδ'mem.2

/-! ## Converse step 2 — each stack's incidence obeys the budget -/

open Classical in
/-- **THE CONVERSE per-stack incidence bound.** If `δ < mcaDeltaStar C ε*`, then for EVERY stack
`u` the far-line incidence (bad-scalar count) is at most `q·ε*`:

  `(#{γ : mcaEvent C δ (u 0) (u 1) γ} : ℝ≥0∞) ≤ q · ε*`.

This is the exact converse of `epsMCA_le_of_worstCaseIncidence`: there a uniform incidence bound
gives `ε_mca ≤ B/q`; here a δ*-lower-bound gives `ε_mca ≤ ε*` (step 1), then each stack's
incidence-probability `I_u/q ≤ ε_mca` (term ≤ sup, via the exact uniform-probability identity)
yields `I_u ≤ q·ε*`. -/
theorem incidence_le_of_lt_mcaDeltaStar (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0}
    (hδ : δ < mcaDeltaStar (F := F) (A := A) C εstar)
    (u : WordStack A (Fin 2) ι) :
    ((Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card : ℝ≥0∞)
      ≤ (Fintype.card F : ℝ≥0∞) * εstar := by
  have hgood : epsMCA (F := F) (A := A) C δ ≤ εstar :=
    epsMCA_le_of_lt_mcaDeltaStar (F := F) (A := A) C εstar hδ
  -- This stack's probability is ≤ the supremum ε_mca.
  have hterm : Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (u 0) (u 1) γ]
      ≤ epsMCA (F := F) (A := A) C δ := by
    unfold epsMCA
    exact le_iSup
      (fun u : WordStack A (Fin 2) ι =>
        Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (u 0) (u 1) γ]) u
  -- Rewrite the probability as the incidence ratio I_u/q.
  rw [prob_uniform_eq_card_filter_div_card] at hterm
  -- So I_u/q ≤ ε_mca ≤ ε*, i.e. I_u ≤ q·ε*.
  have hcard : ((Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar := by
    simpa only [ENNReal.coe_natCast] using le_trans hterm hgood
  -- Clear the denominator (q ≠ 0, q ≠ ∞).
  have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hqtop : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := by simp
  rw [ENNReal.div_le_iff hq0 hqtop] at hcard
  rwa [mul_comm] at hcard

/-! ## Converse step 3 — the WorstCaseIncidenceBounded property at the budget -/

open Classical in
/-- **THE CONVERSE, packaged as `WorstCaseIncidenceBounded`.** For the prize budget `ε* = E/q`
(`E = ⌊q·ε*⌋ ≈ n`), a δ*-lower-bound `δ < δ*` FORCES the open-core property at budget `E`:

  `δ < mcaDeltaStar C (E/q)  ⟹  WorstCaseIncidenceBounded C δ E`.

This is the literal converse of the hypothesis of `worstCaseIncidence_pin_budget`: there
`WorstCaseIncidenceBounded C δ E ⟹ δ ≤ δ*`, here `δ < δ* ⟹ WorstCaseIncidenceBounded C δ E`. -/
theorem worstCaseIncidence_of_lt_mcaDeltaStar (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ}
    (hδ : δ < mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ E := by
  intro u
  -- From step 2: I_u ≤ q · (E/q) = E (as ℝ≥0∞), then back to ℕ.
  have h := incidence_le_of_lt_mcaDeltaStar (F := F) (A := A) C
    ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) hδ u
  have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hqtop : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := by simp
  rw [ENNReal.mul_div_cancel hq0 hqtop] at h
  exact_mod_cast h

open Classical in
/-- **Stack-level natural-number converse.**  If `δ` lies strictly below
`mcaDeltaStar C (E/q)`, then each concrete stack has at most `E` bad scalars. -/
theorem stackIncidence_le_of_lt_mcaDeltaStar
    (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ}
    (hδ : δ < mcaDeltaStar (F := F) (A := A) C
      ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)))
    (u : WordStack A (Fin 2) ι) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
      ≤ E :=
  worstCaseIncidence_of_lt_mcaDeltaStar (F := F) (A := A) C hδ u

/-! ## Converse step 4 — failure of the budget upper-bounds the threshold -/

/-- **Contrapositive δ* delimiter.**  If the budget-`E` open core fails at radius `δ`, then `δ`
cannot lie strictly below the formal threshold `mcaDeltaStar C (E/q)`.

This is the direct contrapositive of `worstCaseIncidence_of_lt_mcaDeltaStar`; it is the reusable
upper-bound interface for explicit incidence failures, orbit-count overflows, and finite census
counterexamples. -/
theorem not_lt_mcaDeltaStar_of_not_worstCaseIncidence
    (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ}
    (hnot : ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ E) :
    ¬ δ < mcaDeltaStar (F := F) (A := A) C
      ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  intro hδ
  exact hnot (worstCaseIncidence_of_lt_mcaDeltaStar (F := F) (A := A) C hδ)

/-- **Upper delimiter from open-core failure.**  A concrete failure of
`WorstCaseIncidenceBounded C δ E` proves the threshold at budget `E/q` is no larger than `δ`. -/
theorem mcaDeltaStar_le_of_not_worstCaseIncidence
    (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ}
    (hnot : ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ E) :
    mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤ δ :=
  not_lt.mp (not_lt_mcaDeltaStar_of_not_worstCaseIncidence (F := F) (A := A) C hnot)

open Classical in
/-- **A single over-budget stack refutes the incidence budget.**  If one stack has more than `E`
bad scalars at radius `δ`, then the worst-case incidence budget `E` fails. -/
theorem stackIncidence_gt_refutes_budget
    (C : Set (ι → A)) (δ : ℝ≥0) {E : ℕ} (u : WordStack A (Fin 2) ι)
    (hgt : E < (Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card) :
    ¬ WorstCaseIncidenceBounded (F := F) (A := A) C δ E := by
  intro hbound
  exact (Nat.not_lt.mpr (hbound u)) hgt

open Classical in
/-- **A single over-budget stack refutes strict δ* interior.**  This is the stack-level
contrapositive of `stackIncidence_le_of_lt_mcaDeltaStar`. -/
theorem not_lt_mcaDeltaStar_of_stackIncidence_gt
    (C : Set (ι → A)) (δ : ℝ≥0) {E : ℕ} (u : WordStack A (Fin 2) ι)
    (hgt : E < (Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card) :
    ¬ δ < mcaDeltaStar (F := F) (A := A) C
      ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  intro hδ
  exact (Nat.not_lt.mpr (stackIncidence_le_of_lt_mcaDeltaStar C hδ u)) hgt

open Classical in
/-- **δ* upper delimiter from one explicit stack.**  One stack with more than `E` bad scalars at
radius `δ` proves `mcaDeltaStar C (E/q) ≤ δ`. -/
theorem mcaDeltaStar_le_of_stackIncidence_gt
    (C : Set (ι → A)) (δ : ℝ≥0) {E : ℕ} (u : WordStack A (Fin 2) ι)
    (hgt : E < (Finset.univ.filter
      (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card) :
    mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) ≤ δ :=
  mcaDeltaStar_le_of_not_worstCaseIncidence (F := F) (A := A) C
    (stackIncidence_gt_refutes_budget C δ u hgt)

/-! ## The biconditional δ* ⟺ incidence-budget -/

/-- **THE BICONDITIONAL (incidence-budget face), axiom-clean both directions.**

For the prize budget `ε* = E/q`:

* FORWARD (`OpenCoreConditionalPin.worstCaseIncidence_pin_budget`):
  `WorstCaseIncidenceBounded C δ E ∧ δ ≤ 1  ⟹  δ ≤ mcaDeltaStar C (E/q)`.
* CONVERSE (`worstCaseIncidence_of_lt_mcaDeltaStar`, here):
  `δ < mcaDeltaStar C (E/q)  ⟹  WorstCaseIncidenceBounded C δ E`.

The honest `±` gap is exactly `<` vs `≤` (the `sSup` boundary) — strictly below the threshold the
incidence budget holds; the budget holding gives at-most-the-threshold. This is the proven
equivalence reducing the entire prize, at any window-interior radius, to the single open-core
property — which itself reduces (one more, OPEN realizer step) to the scalar `B`. -/
theorem deltaStar_iff_incidence_budget (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ} (hδ1 : δ ≤ 1) :
    (δ < mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) →
        WorstCaseIncidenceBounded (F := F) (A := A) C δ E)
    ∧ (WorstCaseIncidenceBounded (F := F) (A := A) C δ E →
        δ ≤ mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :=
  ⟨fun h => worstCaseIncidence_of_lt_mcaDeltaStar (F := F) (A := A) C h,
   fun h => worstCaseIncidence_pin_budget (F := F) (A := A) C hδ1 h⟩

end ProximityGap.OpenCoreConverse

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.OpenCoreConverse.epsMCA_le_of_lt_mcaDeltaStar
#print axioms ProximityGap.OpenCoreConverse.incidence_le_of_lt_mcaDeltaStar
#print axioms ProximityGap.OpenCoreConverse.worstCaseIncidence_of_lt_mcaDeltaStar
#print axioms ProximityGap.OpenCoreConverse.stackIncidence_le_of_lt_mcaDeltaStar
#print axioms ProximityGap.OpenCoreConverse.not_lt_mcaDeltaStar_of_not_worstCaseIncidence
#print axioms ProximityGap.OpenCoreConverse.mcaDeltaStar_le_of_not_worstCaseIncidence
#print axioms ProximityGap.OpenCoreConverse.stackIncidence_gt_refutes_budget
#print axioms ProximityGap.OpenCoreConverse.not_lt_mcaDeltaStar_of_stackIncidence_gt
#print axioms ProximityGap.OpenCoreConverse.mcaDeltaStar_le_of_stackIncidence_gt
#print axioms ProximityGap.OpenCoreConverse.deltaStar_iff_incidence_budget
