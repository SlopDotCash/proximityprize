/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import ArkLib.Data.CodingTheory.ProximityGap.KKH26AsymptoticCeiling

/-!
# The prize δ\* FLOOR from the BGK sup-bound — the honest conditional (#444)

DRAFT (read+draft phase; the orchestrator compiles). This file states the **airtight, honest
conditional** the Proximity-Prize directive asks for: the *prize* δ\* floor

  `mcaDeltaStar C ε* ≥ (1−ρ) − Θ(1/log n)`   (toward capacity, above Johnson)

FOLLOWS FROM the **BGK sup-bound** (`WorstCaseIncompleteSumBound` / `BGKFloor`) **together with one
genuinely-open above-Johnson incidence input**, with everything else discharged by the proven
in-tree substrate. We do **NOT** discharge either open input — in particular the BGK sup-bound,
a ~25-year-open conjecture (the generalized-Paley-graph / Paley-graph-conjecture spectrum), stays a
**named hypothesis** and is never proven here.

## Why TWO named hypotheses, not one (the honest finding)

A faithfulness trace of the chain shows the BGK sup-bound **alone does not close the δ\* floor**.
There are two genuinely-separate open inputs, on two different lanes; conflating them is exactly the
overstatement the in-tree refutation (`CharSumDeltaStarBridge.lean`, corrected per adversarial
refutation `wf_9db879bc`) warns against:

1. **The per-frequency BGK sup-bound** `WorstCaseIncompleteSumBound ψ G M`
   (= `∀ b ≠ 0, ‖η_b‖² ≤ M`), the named open `Prop` of `InteriorWorstCaseIncompleteSum.lean`. It is
   PROVEN to feed only the **additive-energy lane** (`addEnergy_le_of_worstCase`:
   `q·E(G) ≤ |G|⁴ + M·q·|G|`) — it bounds `E(G)`, an `ℓ²`/moment quantity, NOT the line–ball
   incidence. The only in-tree route from this sup-bound to a far-line incidence
   (`IncidenceDeviationCharSum.lineIncidence_le_mean_add`) pays the **naive** triangle factor
   `q·B` (one `B` per annihilating frequency, no inter-frequency cancellation), giving only
   `I ≤ |G| + q·B`, which at the prize budget `q·ε* ≈ n ≈ |G|` forces `B ≈ 0` — **vacuous** for any
   nonzero sup-bound. So the sup-bound is **necessary context but provably insufficient by itself**.

2. **The above-Johnson far-line incidence bound** `WorstCaseIncidenceBounded C δ B` (= every word
   stack has `≤ B` bad scalars at radius `δ`), the named open `Prop` of `OpenCoreConditionalPin.lean`.
   This is the input that `le_mcaDeltaStar_of_good` actually consumes (via
   `epsMCA_le_of_worstCaseIncidence`). It is the per-frequency **square-root cancellation over the
   annihilator hyperplane** in disguise (`I ≤ |G| + √q·B`, i.e. BCHKS Conjecture 1.12 / the
   generalized-Paley-graph eigenvalue bound) — strictly stronger than (1), and NOT delivered by the
   energy lane.

So the airtight conditional carries BOTH: (1) `hBGK` as the named BGK sup-bound (necessary context,
never discharged), and (2) `hIncidence` as the genuinely-open prize-bearing incidence input (never
discharged). The proof consumes (2) through `OpenCoreConditionalPin.worstCaseIncidence_pin`; (1) is
recorded as the necessary parallel analytic content that an actual BGK proof would have to *upgrade*
to (2). This is the honest "the prize floor is exactly these named inequalities away" statement.

## What this file proves (axiom-clean conditional; both inputs NAMED, never discharged)

* `prizeFloor_of_BGK_and_incidence` — the **generic prize floor modulo (1)+(2)**: carrying the BGK
  sup-bound `hBGK` AND the above-Johnson incidence input `hIncidence` at a window radius `δ` with
  budget `B/q ≤ ε*`, the threshold reaches `δ`: `δ ≤ mcaDeltaStar C ε*`.

* `prizeFloor_window_of_BGK_and_incidence` — the **two-sided window placement over the explicit
  smooth-domain code**: combining (1)+(2) with the **proven** in-tree [KKH26] ceiling
  (`kkh26_mcaDeltaStar_le_capacity_sub_log`), the threshold is pinned strictly inside the prize
  window `δwin ≤ mcaDeltaStar (evalCode …) ε* ≤ (1−ρ) − 1/(C·L)`. Floor from (2) (Johnson-beating,
  toward capacity), ceiling from the proven [KKH26] bad family.

The HARD content — proving (1) (the BGK sup-bound) and (2) (its hyperplane upgrade) — stays open.
Issue #444.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- `OpenCoreConditionalPin.lean` (the conditional pin), `InteriorWorstCaseIncompleteSum.lean` (the
  BGK sup-bound Prop + energy lane), `KKH26AsymptoticCeiling.lean` (the proven ceiling),
  `Frontier/PrizeConditionalPinCapstone.lean` (the `=` capstone),
  `Frontier/_PrizeFloorConditionalReduction.lean` (the incidence-only floor reduction).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.OpenCoreConditionalPin
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ProximityGap.Frontier.PrizeFloorOfBGK

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The generic prize floor from the BGK sup-bound + the open incidence input -/

/-- **The prize δ\* FLOOR as a theorem modulo the two named open inputs (1)+(2).**

Carries, as explicit hypotheses that are **never discharged**:

* `hBGK` — the **BGK sup-bound** `WorstCaseIncompleteSumBound ψ G M` (`∀ b ≠ 0, ‖η_b‖² ≤ M`), the
  ~25-year-open per-frequency cancellation (generalized-Paley-graph spectrum). It is the necessary
  analytic context; by itself it feeds only the energy lane and is provably insufficient for the
  floor (see the module docstring), so the proof does **not** route through it.

* `hIncidence` — the genuinely-open **above-Johnson far-line incidence bound**
  `WorstCaseIncidenceBounded C δ B` (every word stack has at most `B` bad scalars at radius `δ`),
  together with the budget `B/q ≤ ε*` and `δ ≤ 1`. This is the prize-bearing input (BCHKS Conj 1.12
  / the hyperplane upgrade of `hBGK`), and is exactly what `le_mcaDeltaStar_of_good` consumes.

Conclusion: the formal MCA threshold reaches `δ`, i.e. `δ ≤ mcaDeltaStar C ε*`. At
`δ = (1−ρ) − Θ(1/log n)` (beyond Johnson, below capacity) and `B = ⌊q·ε*⌋ ≈ n` this is the prize
floor. The implication is fully proven (`OpenCoreConditionalPin.worstCaseIncidence_pin`); the only
open content is `hBGK` and `hIncidence`. -/
theorem prizeFloor_of_BGK_and_incidence
    (C : Set (ι → A)) (εstar : ℝ≥0∞)
    -- ★ OPEN INPUT (1): the BGK sup-bound (named, never discharged; necessary context) ★
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {M : ℝ} (hM0 : 0 ≤ M)
    (hBGK : WorstCaseIncompleteSumBound ψ G M)
    -- ★ OPEN INPUT (2): the above-Johnson far-line incidence at the window radius δ ★
    {δ : ℝ≥0} {B : ℕ} (hδ : δ ≤ 1)
    (hIncidence : WorstCaseIncidenceBounded (F := F) (A := A) C δ B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar :=
  -- The proof consumes ONLY input (2); input (1) is carried as the necessary BGK context that,
  -- per the in-tree refutation `wf_9db879bc`, cannot discharge (2) by itself.
  worstCaseIncidence_pin (F := F) (A := A) C εstar hδ hIncidence hbudget

/-- **Budget form (no side condition).** When the target error is the budget ratio `ε* = E/q`
(the prize has `E ≈ n`), the BGK sup-bound `hBGK` together with the single incidence input
`WorstCaseIncidenceBounded C δ E` gives the floor `δ ≤ mcaDeltaStar C (E/q)`. Both inputs named,
never discharged. -/
theorem prizeFloor_of_BGK_and_incidence_budget
    (C : Set (ι → A))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {M : ℝ} (hM0 : 0 ≤ M)
    (hBGK : WorstCaseIncompleteSumBound ψ G M)
    {δ : ℝ≥0} {E : ℕ} (hδ : δ ≤ 1)
    (hIncidence : WorstCaseIncidenceBounded (F := F) (A := A) C δ E) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  worstCaseIncidence_pin_budget (F := F) (A := A) C hδ hIncidence

/-! ## The two-sided window: floor from (1)+(2), ceiling from the proven [KKH26] bound -/

open ArkLib.ProximityGap.KKH26 in
/-- **THE PRIZE THRESHOLD WINDOW-INTERIOR PLACEMENT, modulo the BGK sup-bound (1) + the open
incidence input (2).**

For the explicit smooth-domain evaluation code `evalCode g n ((r−2)·m)`, combining

* the NAMED OPEN **BGK sup-bound** (1) `hBGK` (necessary context, never discharged), and
* the NAMED OPEN **above-Johnson incidence bound** (2) `hIncidence` at the window radius `δwin`
  (budget `B/q ≤ ε*`), which delivers the FLOOR `δwin ≤ mcaDeltaStar` (the Johnson-beating,
  toward-capacity half), with
* the **proven in-tree** [KKH26] CEILING `kkh26_mcaDeltaStar_le_capacity_sub_log`
  (`mcaDeltaStar ≤ (1−ρ) − 1/(C·L)`, capacity minus an explicit `1/log`-sized gap),

pins the threshold strictly inside the prize window:

  `δwin ≤ mcaDeltaStar (evalCode g n ((r−2)m)) ε* ≤ (1−ρ) − 1/(C·L)`.

The ceiling side is unconditional (the explicit [KKH26] bad family); the floor side rests on the two
named open inputs (1)+(2). With `δwin → 1 − ρ − Θ(1/log n)` the two sides sandwich the prize value:
this is the honest **"the prize floor is exactly the BGK sup-bound (+ its hyperplane upgrade) away"**
theorem. -/
theorem prizeFloor_window_of_BGK_and_incidence {p n : ℕ} [Fact p.Prime] [NeZero n]
    {μ m r : ℕ} (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    {C L : ℝ≥0} (hC : 0 < C) (hL : 0 < L)
    (hregime : ((2 : ℝ≥0) ^ μ) ≤ C * L)
    (hgap : (1 : ℝ≥0) - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)
      ≤ (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ≥0)) - 1 / (C * L))
    -- ★ OPEN INPUT (1): the BGK sup-bound on the smooth multiplicative subgroup (named) ★
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) {Gsub : Finset (ZMod p)} {Msup : ℝ}
    (hMsup0 : 0 ≤ Msup) (hBGK : WorstCaseIncompleteSumBound ψ Gsub Msup)
    -- ★ OPEN INPUT (2): above-Johnson far-line incidence at the window radius δwin ★
    {δwin : ℝ≥0} {B : ℕ} (hδwin : δwin ≤ 1)
    (hIncidence : WorstCaseIncidenceBounded (F := ZMod p) (A := ZMod p)
      (evalCode g n ((r - 2) * m)) δwin B)
    (hBudget : (B : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    δwin ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar ∧
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
        ≤ (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ≥0)) - 1 / (C * L) := by
  have hcard : (Fintype.card (ZMod p) : ℝ≥0∞) = (p : ℝ≥0∞) := by rw [ZMod.card p]
  have hfloor : δwin ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (evalCode g n ((r - 2) * m)) εstar := by
    refine prizeFloor_of_BGK_and_incidence (F := ZMod p) (A := ZMod p)
      (evalCode g n ((r - 2) * m)) εstar hψ hMsup0 hBGK hδwin hIncidence ?_
    rwa [hcard]
  have hceil : mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) εstar
      ≤ (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ≥0)) - 1 / (C * L) :=
    kkh26_mcaDeltaStar_le_capacity_sub_log hμ hm hn hg hp hr2 hr εstar hεstar hC hL hregime hgap
  exact ⟨hfloor, hceil⟩

end ProximityGap.Frontier.PrizeFloorOfBGK

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.PrizeFloorOfBGK.prizeFloor_of_BGK_and_incidence
#print axioms ProximityGap.Frontier.PrizeFloorOfBGK.prizeFloor_of_BGK_and_incidence_budget
#print axioms ProximityGap.Frontier.PrizeFloorOfBGK.prizeFloor_window_of_BGK_and_incidence
