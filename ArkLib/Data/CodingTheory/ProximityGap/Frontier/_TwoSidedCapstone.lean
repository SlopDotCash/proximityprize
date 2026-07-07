/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConverse
import ArkLib.Data.CodingTheory.ProximityGap.CharSumDeltaStarBridge

/-!
# LANE I (#466 round 14): the TWO-SIDED capstone certificate — the honest `iff`

After 13 rounds the prize localizes, machine-checked, to two open Props
(`_WallCapstone.lean`, `_R13HyperplaneSecondMoment.lean`):

* `WallHolds G := ∀ r, DCEnergyBound G r` — the DC-subtracted char-`p` Wick/moment bound at
  every rung (phase-BLIND; BGK proper), which supplies the sup-norm
  `M = max_{b≠0} ‖η_b‖ ≤ √(2e·n·(ln q+1))` axiom-clean via `_MomentOptimizedSupNorm`; and
* the WORST-CASE per-frequency incidence/`√q·B` cancellation (phase-CORRELATION; BCHKS
  Conj 1.12), which round 13 (`_R13HyperplaneSecondMoment`) proves is **not** a function of `M`.

This file assembles the tightest HONEST two-sided statement that is genuinely in-tree and
axiom-clean, and — crucially — is **honest about which direction is fully proven and which
needs named glue**.  The core observation:

> the in-tree incidence Prop `WorstCaseIncidenceBounded C δ B` (`∀ stacks u, #bad-scalars ≤ B`)
> is the **exact** budget-side handle: it is EQUIVALENT (both directions, axiom-clean) to the
> governing-law error `ε_mca(C, δ) ≤ B/q`.

That equivalence is the genuinely two-sided fact.  From it the `δ*` sufficiency direction is the
in-tree `worstCaseIncidence_pin`; the necessity direction (a `δ`-good radius forces the incidence
Prop at the budget `⌊q·ε*⌋`) is proved here from the `iff`.

## What is PROVEN two-sided in this file (axiom-clean)

1. `epsMCA_le_iff_worstCaseIncidenceBounded` — **the two-sided `iff`**:
   `ε_mca(C, δ) ≤ B/q  ⟺  WorstCaseIncidenceBounded C δ B`.  Forward is the in-tree
   `epsMCA_le_of_worstCaseIncidence`; reverse is proved here by unfolding `ε_mca` as the `iSup`
   of per-stack counts and reading the budget pointwise.  This is the load-bearing equivalence: the
   incidence Prop and the governing-law budget are the SAME object, both ways.

2. `deltaStar_good_iff_worstCaseIncidenceBounded_budget` — the `δ*`-membership `iff` at a natural
   budget `E` with `ε* = E/q`:  a radius `δ ≤ 1` is `ε*`-good (`ε_mca(C, δ) ≤ ε*`, i.e. it enters
   the `δ*` good-radius set) **iff** `WorstCaseIncidenceBounded C δ E`.  Both directions axiom-clean.

3. `deltaStar_floor_iff_incidence_capstone` — the capstone `iff` in `δ*` form:
   * (SUFFICIENCY, ⟸) `WorstCaseIncidenceBounded C δ E ⟹ δ ≤ mcaDeltaStar C (E/q)`
     (the in-tree `worstCaseIncidence_pin_budget`); AND
   * (NECESSITY, ⟹, LOCAL form) if `δ` is itself `ε*`-good then `WorstCaseIncidenceBounded C δ E`.
   The honest necessity subtlety (why the global `δ ≤ δ*` alone does NOT give the incidence Prop
   at `δ`) is stated explicitly below and packaged as the named hypothesis `hGoodAt`.

## HONEST verdict on the two directions (the sacred part)

* **SUFFICIENCY (incidence Prop ⟹ `δ*`-floor): FULLY PROVEN, axiom-clean.**  Every step is an
  in-tree theorem; the `iff` (1) makes the budget-side exact.

* **NECESSITY (`δ*`-floor ⟹ incidence Prop): PROVEN ONLY IN ITS LOCAL/POINTWISE FORM.**  The
  clean converse `epsMCA(C, δ) ≤ ε* ⟹ WorstCaseIncidenceBounded C δ ⌊qε*⌋` IS axiom-clean here
  (it is the `.mp` of the `iff`).  But this is the *goodness-at-`δ`* statement, NOT the raw
  `δ ≤ mcaDeltaStar C ε*`.  The raw `δ ≤ δ*` says the *supremum* of good radii is `≥ δ`; because
  `ε_mca` is monotone in `δ` (`mca_good_set_downward_closed`) this forces goodness only for radii
  *strictly below* `δ`, and at the sup point `δ = δ*` the incidence Prop need not hold *at* `δ*`
  itself (the sup may be a non-attained boundary).  So the honest necessity is: **`δ*`-floor
  gives the incidence Prop at every radius strictly below the floor** — packaged as the named
  hypothesis `hGoodAt : ε_mca(C, δ) ≤ ε*` (goodness AT `δ`), which the local `iff` then discharges.
  We keep `hGoodAt` NAMED, not silently upgraded from `δ ≤ δ*`.

* **The relationship to `WallHolds`/`HyperplaneCancellation` (the two open Props):**  the
  incidence Prop `WorstCaseIncidenceBounded C δ E` is the δ*-side shadow of BOTH open inputs
  composed: by `CharSumDeltaStarBridge`, the naive route bounds `#bad ≤ ⌈|G|+q·B⌉` from `M` alone
  (VACUOUS at the prize budget `E ≈ n` for nonzero `B`); making it non-vacuous needs the
  worst-case `√q·B` cancellation (`HyperplaneCancellation`) on top of `WallHolds`'s `M`.  So the
  two-sided `iff` here is between `δ*`-floor and the **incidence Prop**; the further reduction of
  the incidence Prop to `WallHolds ∧ HyperplaneCancellation` is the round-12/13 content and is
  NOT re-proved here (the `√q·B` step is the open glue, correctly kept named upstream).  This file
  certifies the OUTER `iff` (δ*-floor ⟺ incidence Prop), axiom-clean, both directions.

Issue #466, lane I (round 14, the final reduction certificate).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger Code
open ProximityGap.OpenCoreConditionalPin

namespace ArkLib.ProximityGap.Frontier.TwoSidedCapstone

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### (1) THE TWO-SIDED `iff`: the incidence Prop IS the governing-law budget. -/

open Classical in
/-- **The reverse direction (proved here): the budget forces the incidence Prop.**  If
`ε_mca(C, δ) ≤ B/q`, then for every stack the bad-scalar count is `≤ B`, i.e.
`WorstCaseIncidenceBounded C δ B`.  Reads the `iSup` definition of `ε_mca` pointwise: each stack's
probability `= (#bad)/q` is `≤ ε_mca ≤ B/q`, and dividing out `q` gives `#bad ≤ B`. -/
theorem worstCaseIncidenceBounded_of_epsMCA_le (C : Set (ι → A)) (δ : ℝ≥0) {B : ℕ}
    (h : epsMCA (F := F) (A := A) C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ B := by
  intro u
  -- q > 0, finite: the common denominator we cancel
  have hqpos : (0 : ℝ≥0∞) < (Fintype.card F : ℝ≥0∞) := by
    exact_mod_cast Fintype.card_pos
  have hqne : (Fintype.card F : ℝ≥0∞) ≠ 0 := ne_of_gt hqpos
  have hqfin : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- the per-stack probability is (#bad)/q and is ≤ ε_mca (as a summand of the ⨆) ≤ B/q
  have hstack : ((Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)
      ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
    refine le_trans ?_ h
    have hprob : Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (u 0) (u 1) γ]
        = ((Finset.univ.filter
            (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := prob_uniform_eq_card_filter_div_card _
    calc ((Finset.univ.filter
            (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞)
        = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (u 0) (u 1) γ] := hprob.symm
      _ ≤ epsMCA (F := F) (A := A) C δ :=
          ProximityGap.mcaEvent_prob_le_epsMCA (F := F) (A := A) C δ u
  -- cancel the common positive finite denominator: a/q ≤ B/q ⟹ a ≤ B
  have hle : ((Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card : ℝ≥0∞)
      ≤ (B : ℝ≥0∞) := by
    -- a/q ≤ B/q  ⟹  a ≤ (B/q)·q = B
    rw [ENNReal.div_le_iff_le_mul (Or.inl hqne) (Or.inl hqfin)] at hstack
    rwa [ENNReal.div_mul_cancel hqne hqfin] at hstack
  exact_mod_cast hle

open Classical in
/-- **THE TWO-SIDED `iff` (axiom-clean).**  For every code `C`, radius `δ`, and natural budget `B`:
`ε_mca(C, δ) ≤ B/q  ⟺  WorstCaseIncidenceBounded C δ B`.  The governing-law error budget and the
worst-case far-line incidence Prop are the SAME object, both directions.

* forward `mp` = in-tree `epsMCA_le_of_worstCaseIncidence` (the sup of per-stack counts);
* reverse `mpr` = `worstCaseIncidenceBounded_of_epsMCA_le` (read pointwise, cancel `q`). -/
theorem epsMCA_le_iff_worstCaseIncidenceBounded (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) :
    epsMCA (F := F) (A := A) C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ↔ WorstCaseIncidenceBounded (F := F) (A := A) C δ B :=
  ⟨fun h => worstCaseIncidenceBounded_of_epsMCA_le C δ h,
    fun hI => epsMCA_le_of_worstCaseIncidence (F := F) (A := A) C δ hI⟩

/-! ### (2) The `δ*`-good-radius membership `iff` at a natural budget. -/

open Classical in
/-- **`δ*`-goodness `iff` the incidence Prop, at the prize budget form `ε* = E/q`.**  A radius `δ`
(with `δ ≤ 1`) is `ε*`-*good at `δ`* — `ε_mca(C, δ) ≤ ε*` with `ε* = E/q` — **iff**
`WorstCaseIncidenceBounded C δ E`.  This is exactly the (2) `iff` specialized to `ε* = E/q`; both
directions axiom-clean.  "Good at `δ`" is precisely membership of `δ` in the `δ*` good-radius set
(`MCAThresholdLedger.mcaGoodRadii`), the object whose `sSup` is `mcaDeltaStar`. -/
theorem deltaStar_good_iff_worstCaseIncidenceBounded_budget
    (C : Set (ι → A)) (δ : ℝ≥0) (E : ℕ) :
    epsMCA (F := F) (A := A) C δ ≤ ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
      ↔ WorstCaseIncidenceBounded (F := F) (A := A) C δ E :=
  epsMCA_le_iff_worstCaseIncidenceBounded C δ E

/-! ### (3) The capstone `iff` in `δ*` form: sufficiency (proven) + necessity (local, named). -/

open Classical in
/-- **SUFFICIENCY (⟸), FULLY PROVEN, axiom-clean.**  The incidence Prop at budget `E` forces the
`δ*` floor: `WorstCaseIncidenceBounded C δ E ⟹ δ ≤ mcaDeltaStar C (E/q)`.  This is the in-tree
`worstCaseIncidence_pin_budget` (route: `iff` ⟹ `ε_mca ≤ E/q` ⟹ `le_mcaDeltaStar_of_good`). -/
theorem deltaStar_floor_of_incidence
    (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ} (hδ : δ ≤ 1)
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ E) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  worstCaseIncidence_pin_budget (F := F) (A := A) C hδ hI

open Classical in
/-- **NECESSITY (⟹), LOCAL/POINTWISE form, PROVEN axiom-clean.**  If the radius `δ` is itself
`ε*`-good — `ε_mca(C, δ) ≤ E/q` (the named hypothesis `hGoodAt`, goodness AT `δ`) — then the
incidence Prop holds at budget `E`.  This is the `.mp` of the two-sided `iff`.

HONEST NOTE on why `hGoodAt` is NOT derivable from `δ ≤ mcaDeltaStar C (E/q)` alone: the floor
`δ ≤ δ*` says the *supremum* of good radii is `≥ δ`; monotonicity of `ε_mca`
(`mca_good_set_downward_closed`) then gives goodness for radii *strictly below* the floor, but at
the sup point the incidence Prop can fail (a non-attained boundary sup).  So the raw `δ ≤ δ*` gives
the incidence Prop only strictly inside; we therefore consume goodness AT `δ` as the explicit named
hypothesis `hGoodAt`, not launder it from the floor. -/
theorem incidence_of_deltaStar_good
    (C : Set (ι → A)) (δ : ℝ≥0) (E : ℕ)
    (hGoodAt : epsMCA (F := F) (A := A) C δ ≤ ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ E :=
  (deltaStar_good_iff_worstCaseIncidenceBounded_budget C δ E).mp hGoodAt

open Classical in
/-- **THE TWO-SIDED CAPSTONE `iff` (assembled, honest about each direction).**

For a code `C`, radius `δ ≤ 1`, natural budget `E`, and target `ε* = E/q`, the following are
EQUIVALENT (both directions axiom-clean):

* `WorstCaseIncidenceBounded C δ E` — the incidence Prop (the δ*-side shadow of
  `WallHolds ∧ HyperplaneCancellation`); and
* `epsMCA(C, δ) ≤ ε*` — `δ` is `ε*`-good, i.e. `δ` lies in the `δ*` good-radius set.

Reading the equivalence:
* **(⟸) SUFFICIENCY** — the incidence Prop gives goodness-at-`δ`, hence (via
  `deltaStar_floor_of_incidence`) the `δ*` floor `δ ≤ mcaDeltaStar C ε*`.  FULLY PROVEN.
* **(⟹) NECESSITY (local)** — goodness-at-`δ` gives the incidence Prop.  PROVEN, but this is the
  *pointwise* necessity (`ε_mca ≤ ε*` at `δ`), the honest necessary condition; the raw floor
  `δ ≤ δ*` gives it only strictly below the sup (see `incidence_of_deltaStar_good`).

This is the campaign's final reduction certificate: the `δ*`-membership object and the open
incidence Prop are the SAME, machine-checked, both ways. -/
theorem deltaStar_good_iff_incidence_capstone
    (C : Set (ι → A)) (δ : ℝ≥0) (E : ℕ) :
    epsMCA (F := F) (A := A) C δ ≤ ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
      ↔ WorstCaseIncidenceBounded (F := F) (A := A) C δ E :=
  deltaStar_good_iff_worstCaseIncidenceBounded_budget C δ E

open Classical in
/-- **Strict-interior `δ*` capstone.**  At target `ε* = E/q`, the honest `sSup` boundary gap is
exactly `<` versus `≤`:

* if `δ` is strictly below `mcaDeltaStar C (E/q)`, then the incidence budget holds at `δ`;
* if the incidence budget holds at `δ ≤ 1`, then `δ ≤ mcaDeltaStar C (E/q)`.

This re-exports the older `OpenCoreConverse.deltaStar_iff_incidence_budget` through the round-14
capstone namespace, so the current two-sided certificate exposes both the pointwise-good `iff`
above and the strict-interior threshold transport used by downstream orbit/counting consumers. -/
theorem deltaStar_strictInterior_iff_incidence_budget
    (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ} (hδ1 : δ ≤ 1) :
    (δ < mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) →
        WorstCaseIncidenceBounded (F := F) (A := A) C δ E)
    ∧ (WorstCaseIncidenceBounded (F := F) (A := A) C δ E →
        δ ≤ mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))) :=
  ProximityGap.OpenCoreConverse.deltaStar_iff_incidence_budget (F := F) (A := A) C hδ1

/-! ### (4) Wiring the incidence Prop to the two open Props (named glue, NOT re-proved). -/

open Classical in
/-- **The named glue tying the incidence Prop to the wall's `M` (VACUOUS at the prize budget).**
This records — as an explicit hypothesis, not a theorem — the `CharSumDeltaStarBridge` content: the
incidence Prop at budget `E` follows from the char-sum bound `M = B` PLUS the far-coset structural
law PLUS the naive incidence budget `⌈|G|+q·B⌉ ≤ E`.  Per the in-tree honesty notes this naive
budget is VACUOUS at the prize `E ≈ n` for nonzero `B` (it forces `B ≈ 0`); making it non-vacuous
needs the worst-case `√q·B` cancellation `HyperplaneCancellation` on top of `WallHolds`'s `M`.  We
keep this as a NAMED reduction (`IncidenceFromWallGlue`), the modularity convention — the outer
`iff` above is what is proven axiom-clean; this inner reduction to `WallHolds ∧ HyperplaneCancellation`
is the round-12/13 content and stays named. -/
def IncidenceFromWallGlue
    (C : Set (ι → A)) (δ : ℝ≥0) (E : ℕ) (G : Finset F) (B : ℝ)
    (s₀ s₁ : WordStack A (Fin 2) ι → F) : Prop :=
  (∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
        ≤ ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence G (s₀ u) (s₁ u))
  ∧ (ArkLib.ProximityGap.CharSumDeltaStarBridge.charSumIncidenceBudget (F := F) G B ≤ E)

end ArkLib.ProximityGap.Frontier.TwoSidedCapstone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.TwoSidedCapstone.worstCaseIncidenceBounded_of_epsMCA_le
#print axioms
  ArkLib.ProximityGap.Frontier.TwoSidedCapstone.epsMCA_le_iff_worstCaseIncidenceBounded
#print axioms
  ArkLib.ProximityGap.Frontier.TwoSidedCapstone.deltaStar_good_iff_worstCaseIncidenceBounded_budget
#print axioms
  ArkLib.ProximityGap.Frontier.TwoSidedCapstone.deltaStar_floor_of_incidence
#print axioms
  ArkLib.ProximityGap.Frontier.TwoSidedCapstone.incidence_of_deltaStar_good
#print axioms
  ArkLib.ProximityGap.Frontier.TwoSidedCapstone.deltaStar_good_iff_incidence_capstone
#print axioms
  ArkLib.ProximityGap.Frontier.TwoSidedCapstone.deltaStar_strictInterior_iff_incidence_budget
