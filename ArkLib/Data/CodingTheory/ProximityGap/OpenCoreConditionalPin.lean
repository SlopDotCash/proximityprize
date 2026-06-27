/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# The single open core as one named `Prop`, with the conditional `δ*` pin (#407)

This file does the honest "closed conditional conjecture" the Proximity Prize directive asks for:
it isolates the **entire** remaining open content of the mutual-correlated-agreement threshold
`δ*` into ONE explicit, precisely-stated `Prop`, and then **proves** (axiom-clean, no `sorry`)
that this `Prop` implies the `δ*` lower pin via the governing law `MCAThresholdLedger`.

## The governing law (in-tree, exact)

`δ* = sup { δ : ε_mca(C, δ) ≤ ε* }`  with  `ε* = 2^-128` and field size `q = |F| ≈ n·2^128`,
so the budget is `q·ε* ≈ n`.  The threshold object is `MCAThresholdLedger.mcaDeltaStar C ε*`
(the `sSup` of the good radii inside `[0,1]`); the lower-bracket lemma is
`MCAThresholdLedger.le_mcaDeltaStar_of_good`.

## The open core, stated as one `Prop`

By `prob_uniform_eq_card_filter_div_card`, the per-stack MCA probability is exactly
`(#bad-scalars)/q`, so

  `ε_mca(C, δ) = sup_u  #{ γ : mcaEvent C δ (u 0) (u 1) γ } / q`.

The bad-scalar count `#{γ : ...}` is the **far-line incidence** `I(δ)` of the governing law: for a
monomial pencil `(a, b)` it is `#{α : xᵃ + α xᵇ is δ-close to RS[k]}` (the line–syndrome-ball
incidence; see `FarCosetExplosion.epsMCA_ge_far_incidence`).  Therefore the *single* open
statement that pins `δ*` from below at a window radius `δ` is:

  **`WorstCaseIncidenceBounded C δ B`** :  `∀ u, #{ γ : mcaEvent C δ (u 0) (u 1) γ } ≤ B`.

i.e. "the worst-case far-line incidence `I(δ)` is at most the budget `B = ⌊q·ε*⌋ ≈ n`".  This is
*exactly* the recognized-open explicit-`μ_n` list-decoding statement: at the window radius
`δ* = 1 − ρ − H(ρ)/(β log n)` (beyond Johnson, below capacity), is the far-line incidence over a
smooth multiplicative subgroup still `≤ q·ε* ≈ n`?  No technique in the literature bridges this
Johnson→capacity gap for explicit fixed Reed–Solomon codes; it is the prize core.

## What is proven here (the conditional pin — axiom-clean, no `sorry`)

* **`epsMCA_le_of_worstCaseIncidence`** — `WorstCaseIncidenceBounded C δ B ⟹ ε_mca(C, δ) ≤ B/q`.
  Pure supremum + the exact per-stack probability identity.

* **`worstCaseIncidence_pin`** — THE CONDITIONAL PIN: if the open core `Prop` holds with a budget
  `B` whose normalized value `B/q ≤ ε*`, and `δ ≤ 1`, then `δ ≤ mcaDeltaStar C ε*`.  This routes
  the open `Prop` through `le_mcaDeltaStar_of_good` to bracket the governing-law threshold.

* **`worstCaseIncidence_pin_budget`** — the budget specialization: with `ε* = E/q` for a natural
  budget `E` (the prize's `q·ε* ≈ n`), the open core `I(δ) ≤ E` alone implies `δ ≤ δ*`.

* **`worstCaseIncidenceBounded_of_orbitCount`** — the ORBIT-COUNT face at the open-core layer:
  the axiom-clean Action–Orbit crossing law (`OrbitCountCrossingLaw.crossing_law`) turns a
  per-stack factorization `I_u = N_u·S` plus the orbit-count test `N_u ≤ d`, `S·d = n`, into the
  incidence bound `WorstCaseIncidenceBounded C δ n`.

* **`worstCaseIncidence_pin_of_orbitCount`** — the same certificate composed with
  `worstCaseIncidence_pin`: supplying the per-stack orbit-count test plus `n/q ≤ ε*` pins
  `δ ≤ δ*`.

## Honest scope

* The `Prop` `WorstCaseIncidenceBounded C δ B` at the window radius **is** the recognized open
  problem (the prize core).  It is stated, NOT proved.  Best known unconditional incidence bounds
  are `n^{1-o(1)}` (BGK/Paley short-character-sum cancellation), which is vacuous at the budget
  `≈ n` in the window interior.  Nothing here closes it.
* The conditional implication `Prop ⟹ δ ≥ window-radius` **is** proved, axiom-clean.  This makes
  the prize's remaining open content a single explicit, precisely-stated `Prop` with everything
  else proven around it — the honest "closed conditional conjecture".
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger Code

namespace ProximityGap.OpenCoreConditionalPin

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The single open core `Prop` -/

open Classical in
/-- **THE SINGLE OPEN CORE, stated as one explicit `Prop`.**

`WorstCaseIncidenceBounded C δ B` says: for **every** stack `u = (u₀, u₁)`, the number of *bad*
scalars `γ` — those for which the affine line `u₀ + γ·u₁` triggers `mcaEvent` at radius `δ` — is at
most `B`.

This is the worst-case far-line incidence `I(δ) ≤ B` of the governing law: the bad-scalar count
`#{γ : mcaEvent ...}` is, for a monomial pencil over a smooth `μ_n` domain, exactly the line–
syndrome-ball incidence `#{α : xᵃ + α xᵇ is δ-close to RS[k]}`.  At the window radius
`δ* = 1 − ρ − H(ρ)/(β log n)` and budget `B ≈ q·ε* ≈ n`, this is the recognized-open prize core.

It is **not** proven here; it is the explicit hypothesis that the conditional pin consumes. -/
def WorstCaseIncidenceBounded (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ B

/-! ## The exact per-stack probability identity ⟹ supremum bound -/

open Classical in
/-- **From the open core to the MCA error bound.**  If the worst-case far-line incidence is at
most `B` at radius `δ`, then `ε_mca(C, δ) ≤ B / q`.  Uses the exact per-stack probability identity
`Pr_γ[mcaEvent] = (#bad-scalars)/q` (`prob_uniform_eq_card_filter_div_card`) and takes the
supremum over stacks. -/
theorem epsMCA_le_of_worstCaseIncidence (C : Set (ι → A)) (δ : ℝ≥0) {B : ℕ}
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ B) :
    epsMCA (F := F) (A := A) C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast hI u

/-! ## THE CONDITIONAL `δ*` PIN -/

/-- **THE CONDITIONAL `δ*` PIN (#407).**

If the single open core `Prop` `WorstCaseIncidenceBounded C δ B` holds at the window radius `δ`,
with a budget `B` whose normalized value `B/q ≤ ε*`, and `δ ≤ 1`, then the governing-law threshold
satisfies `δ ≤ mcaDeltaStar C ε*`.

This is the honest closed *conditional* conjecture: the entire open content of the prize is the
single hypothesis `hI`; the implication to the `δ*` lower pin is fully proven (axiom-clean). -/
theorem worstCaseIncidence_pin (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar := by
  refine le_mcaDeltaStar_of_good (F := F) (A := A) C εstar hδ ?_
  exact le_trans (epsMCA_le_of_worstCaseIncidence (F := F) (A := A) C δ hI) hbudget

/-- **Budget specialization of the conditional pin (the prize's `q·ε* ≈ n` form).**

When the target error is itself a budget ratio `ε* = E/q` for a natural number `E` (the prize has
`E = ⌊q·ε*⌋ ≈ n`), the single open core `I(δ) ≤ E` *alone* (no further side condition) implies the
`δ*` lower pin `δ ≤ mcaDeltaStar C (E/q)`. -/
theorem worstCaseIncidence_pin_budget (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ}
    (hδ : δ ≤ 1)
    (hI : WorstCaseIncidenceBounded (F := F) (A := A) C δ E) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  worstCaseIncidence_pin (F := F) (A := A) C _ hδ hI le_rfl

/-! ## The orbit-count face of the conditional pin -/

open Classical in
/-- **The orbit-count face of the open core (Action–Orbit reformulation).**

The governing-law budget test `I(δ) ≤ n` is, by the axiom-clean crossing law
`OrbitCountCrossingLaw.crossing_law`, equivalent to the orbit-count test
`N_pencil(δ) ≤ gcd(b−a, n)`.  Concretely: if for every stack `u` the bad-scalar count factors as
`N_u · S` (constant orbit size `S > 0`, `S · d = n`) with the **orbit-count test** `N_u ≤ d`, then
the open core `I(δ) ≤ n` holds.

This is the standalone interface the R4 coset-rigidity route must feed: prove the orbit-count
certificate, and the raw incidence hypothesis is discharged. -/
theorem worstCaseIncidenceBounded_of_orbitCount
    (C : Set (ι → A)) {δ : ℝ≥0} {S d n : ℕ}
    (hS : 0 < S) (hsupply : S * d = n)
    (horbit : ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S
        ∧ N ≤ d) :
    WorstCaseIncidenceBounded (F := F) (A := A) C δ n := by
  intro u
  obtain ⟨N, hid, hNd⟩ := horbit u
  exact (ArkLib.ProximityGap.OrbitCountCrossingLaw.crossing_law hS hsupply hid).2 hNd

open Classical in
/-- **The orbit-count face of the conditional pin.**

The standalone orbit-count certificate gives `WorstCaseIncidenceBounded C δ n`; if the normalized
budget `n/q` is at most `ε*`, the governing-law threshold reaches `δ`. -/
theorem worstCaseIncidence_pin_of_orbitCount
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {S d n : ℕ}
    (hδ : δ ≤ 1) (hS : 0 < S) (hsupply : S * d = n)
    (horbit : ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S
        ∧ N ≤ d)
    (hbudget : (n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar :=
  worstCaseIncidence_pin (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_orbitCount (F := F) (A := A) C hS hsupply horbit)
    hbudget

/-- **Budget-specialized orbit-count pin.**

If the target error is exactly the natural budget ratio `n/q`, the per-stack orbit-count
certificate pins `δ ≤ mcaDeltaStar C (n/q)` with no separate budget side condition. -/
open Classical in
theorem worstCaseIncidence_pin_budget_of_orbitCount
    (C : Set (ι → A)) {δ : ℝ≥0} {S d n : ℕ}
    (hδ : δ ≤ 1) (hS : 0 < S) (hsupply : S * d = n)
    (horbit : ∀ u : WordStack A (Fin 2) ι,
      ∃ N : ℕ,
        (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card = N * S
        ∧ N ≤ d) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C
      ((n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  worstCaseIncidence_pin_budget (F := F) (A := A) C hδ
    (worstCaseIncidenceBounded_of_orbitCount (F := F) (A := A) C hS hsupply horbit)

end ProximityGap.OpenCoreConditionalPin

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.OpenCoreConditionalPin.epsMCA_le_of_worstCaseIncidence
#print axioms ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin
#print axioms ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin_budget
#print axioms ProximityGap.OpenCoreConditionalPin.worstCaseIncidenceBounded_of_orbitCount
#print axioms ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin_of_orbitCount
#print axioms ProximityGap.OpenCoreConditionalPin.worstCaseIncidence_pin_budget_of_orbitCount
