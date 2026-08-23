/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidenceDeviationCharSum
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
import ArkLib.Data.Probability.Instances

/-!
# A conditional `δ*` lower bound from a uniform Gauss-period bound (TRUE but VACUOUS at the
  prize budget) — #407

This file assembles the proven substrate into one axiom-clean **conditional**:

  > **IF** every nonzero subgroup Gauss period is small, `∀ b ≠ 0, ‖η_b‖ ≤ B`,
  > **AND** the resulting *naive* worst-case incidence sits below the budget, `|G| + q·B ≤ q·ε*`,
  > **THEN** the MCA threshold reaches that radius, `δ ≤ mcaDeltaStar C ε*`.

The theorems below (`le_mcaDeltaStar_of_uniformCharSumBound`,
`le_mcaDeltaStar_of_charSumBound`) are **true conditionals**, proved axiom-clean.  But the reader
must understand **two things the earlier docstring overstated** (corrected per the adversarial
refutation in workflow `wf_9db879bc`):

### (1) The incidence bound is the NAIVE `(#frequencies)·B`, not a per-frequency `≲ B`.

The chain runs through `IncidenceDeviationCharSum.lineIncidence_le_mean_add`, which proves

  > `I(s₀,s₁) ≤ |G| + (#deviationSupport s₁)·B ≤ |G| + q·B`.

The `q·B` is the **triangle-summed naive bound**: `B` is paid once for *each* of the up-to-`q`
annihilating frequencies, with **no cancellation between distinct frequencies**.  It is NOT the
claim that "char-sum bound `B` feeds far-line incidence linearly with no √-loss"; the full factor
`q` on `B` is exactly the absence of √-cancellation.  (It does avoid the energy lane's separate
`√` from `T² ≤ |G|·E`, but it pays a worse `q` instead.)

### (2) The conditional is VACUOUS at the prize budget for any nonzero `B`.

The budget hypothesis is `(|G| + q·B)/q ≤ ε*`, i.e. `|G|/q + B ≤ ε*`.  At the prize regime the
budget is `q·ε* ≈ n` (so `ε* ≈ n/q`) and the smooth subgroup has `|G| ≈ n` (so `|G|/q ≈ n/q ≈ ε*`).
Substituting gives `B ≤ ε* − |G|/q ≈ 0`, i.e. the hypothesis demands `q·B ≤ 0`, i.e. **`B = 0`**.
Any nonzero power-saving bound `B = n^{1−c}` overshoots the prize budget by a factor `≈ q·B / n ≈
n^{1−c}` (on the order of `1e47` at the prize point), so it does **NOT** satisfy `hBudget`.  The
conditional is therefore VACUOUS at the prize budget — it is satisfiable only away from the prize
budget (small `q`, or `ε*` not at the window value), where it carries no prize content.

### (3) What is actually needed (and is NOT supplied here).

Reaching the prize budget `q·ε* ≈ n` requires the **per-frequency square-root cancellation**
`∑_{b·s₁=0} conj(η_b)ψ(b·s₀) ≲ √q · B` over the hyperplane — i.e. the genuine oscillatory
cancellation that the naive triangle bound throws away.  That is the **open Paley-graph /
BCHKS Conjecture 1.12 square-root**, the recognised prize floor.  This brick does NOT supply it
and makes NO progress on it; it only packages the naive count into a (vacuous-at-prize) conditional.

## The chain (each step a proven in-tree theorem)

1. `epsMCA_le_of_forall_badCount_le` (built here): a uniform per-stack bad-scalar count bound
   `≤ M` gives `epsMCA ≤ M/q`.
2. `FarCosetExplosion.badScalars_eq_explainable`: for far directions the bad-scalar set IS the
   line-explainability (incidence) set (threaded as the structural hypothesis `hStruct`).
3. `IncidenceDeviationCharSum.lineIncidence_le_mean_add`: the **naive** `I ≤ |G| + q·B` from
   `‖η_b‖ ≤ B` (the `q·B`, not √q·B — no inter-frequency cancellation).
4. `MCAThresholdLedger.le_mcaDeltaStar_of_good`: `epsMCA ≤ ε*` gives `δ ≤ δ*`.

The structural step 2 is threaded as the explicit named hypothesis `hStruct`/`hBadCount` so no
analytic content is laundered; the analytic input is the parameter `B`.  The conditional is honest
(nothing open is silently discharged) — but, per (2), its budget hypothesis is unsatisfiable at the
prize budget for nonzero `B`, so it does not by itself yield the prize lower bound.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #407.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ProximityGap Code
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge
open ArkLib.ProximityGap.IncidenceDeviationCharSum

namespace ArkLib.ProximityGap.CharSumDeltaStarBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Step 1: the general per-stack bad-count upper bound on `epsMCA` -/

open Classical in
/-- **`epsMCA ≤ M/q` from a uniform per-stack bad-scalar count bound.** If, for *every* word
stack `u`, the number of bad scalars `γ` (those firing `mcaEvent`) is at most `M`, then the MCA
error is at most `M/|F|`.  This is the general upper-bound consumer the bridge needs: it turns a
*combinatorial* bound on the worst-case bad count (the far-line incidence) into a *probabilistic*
bound on `ε_mca`.  Pure `iSup`-monotonicity plus the uniform-probability count identity. -/
theorem epsMCA_le_of_forall_badCount_le (C : Set (ι → A)) (δ : ℝ≥0) (M : ℕ)
    (hM : ∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ M) :
    epsMCA (F := F) (A := A) C δ ≤ (M : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast hM u

/-! ### Step 2+3: the worst-case incidence bound from the char-sum bound (the NAIVE
`(#freq)·B = |G| + q·B` triangle bound over the deviation-support hyperplane — NOT per-frequency
`B`; this is VACUOUS at the prize budget `q·ε* ≈ n`, which needs the open per-frequency
√-cancellation `∑_{b·s₁=0} conj(η_b)ψ(b·s₀) ≲ √q·B` = Paley / BCHKS Conj 1.12, not supplied here) -/

/-- **Worst-case far-line incidence below the NAIVE budget `|G| + q·B`, from the uniform char-sum
bound.** For the syndrome-field geometry `V = F` (where `IncidencePeriodBridge` proves
`I = ∑_{b·s₁=0} conj(η_b) ψ(b·s₀)` term-by-term), a uniform bound `‖η_b‖ ≤ B` on nonzero
frequencies triangle-bounds every far-line incidence by `|G| + q·B`.

WARNING: the `q·B` is the **naive `(#frequencies)·B` count** — `B` paid once per annihilating
frequency, NO cancellation between distinct frequencies — NOT a square-root-cancelled `√q·B`.  At
the prize budget `q·ε* ≈ n` (with `|G| ≈ n`) this budget meets `q·ε*` only for `B ≈ 0`; a nonzero
power-saving `B` overshoots.  Reaching `q·ε*` for nonzero `B` needs the open per-frequency
square-root cancellation (Paley/BCHKS-1.12), which this does NOT supply. -/
theorem worstCase_incidence_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) (s₀ s₁ : F) :
    (lineIncidence G s₀ s₁ : ℝ)
      ≤ (G.card : ℝ) + (Fintype.card F : ℝ) * B :=
  lineIncidence_le_mean_add hψ G s₀ s₁ hB0 hB

/-! ### The bridge theorem -/

open Classical in
/-- **A `δ*` lower-bound conditional from a uniform bad-count bound `M` (TRUE; VACUOUS at the
prize budget).**

For a code `C`, radius `δ`, target `ε*`, and a uniform per-stack bad-count bound `M`:

* **(`hBadCount`)** every word stack's bad-scalar count is `≤ M` (downstream, `M = ⌈|G| + q·B⌉`,
  the **naive** char-sum incidence budget — see `le_mcaDeltaStar_of_charSumBound`);
* **(`hBudget`)** the budget meets the target: `(M : ℝ≥0∞)/q ≤ ε*`;
* **(`hδ1`)** `δ ≤ 1`.

**Then** `δ ≤ mcaDeltaStar C ε*` — the threshold reaches this radius.

This is a true, axiom-clean conditional.  WARNING (do not over-read): when `M = ⌈|G| + q·B⌉` is the
naive char-sum budget, `hBudget` reads `(|G| + q·B)/q ≤ ε*`, i.e. `|G|/q + B ≤ ε*`.  At the prize
budget `q·ε* ≈ n` with `|G| ≈ n` this forces `B ≈ 0`, so the conditional is VACUOUS at the prize
budget for any nonzero `B`.  Di Benedetto's PROVEN power-saving `B ≤ n^{1−31/2880}` does NOT satisfy
`hBudget` at the window level (it overshoots `q·ε* ≈ n` by `≈ q·B/n = n^{1−31/2880}`).  The genuine
prize lower bound needs the open per-frequency square-root cancellation (`∑_b ≲ √q·B`,
Paley/BCHKS-1.12), which is NOT in this chain. -/
theorem le_mcaDeltaStar_of_uniformCharSumBound
    (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ : ℝ≥0) {M : ℕ}
    (hBadCount : ∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ M)
    (hBudget : (M : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar := by
  have hgood : epsMCA (F := F) (A := A) C δ ≤ εstar :=
    le_trans (epsMCA_le_of_forall_badCount_le C δ M hBadCount) hBudget
  exact ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good
    (F := F) (A := A) C εstar hδ1 hgood

/-! ### The calibration witness: the worst-case incidence count IS the bridge's `M` -/

/-- **The bridge's `M` from the char-sum bound, made explicit.** The natural-number budget the
bridge consumes is the ceiling of the **naive** worst-case incidence `|G| + q·B` (the
`(#frequencies)·B` triangle count, no inter-frequency cancellation).  This records
`M = ⌈|G| + q·B⌉` so that `hBudget` reads `(⌈|G|+q·B⌉)/q ≤ ε*`.

WARNING: at the prize budget `q·ε* ≈ n` with `|G| ≈ n`, the requirement `(|G| + q·B)/q ≤ ε*`
forces `B ≈ 0`; a power-saving `B = n^{1−c}` makes `⌈|G|+q·B⌉ ≈ q·n^{1−c} ≫ q·ε* ≈ n`, so it does
NOT clear the budget.  The naive `q·B` is the obstruction; clearing it at the prize budget needs the
open √q·B cancellation (Paley/BCHKS-1.12). -/
noncomputable def charSumIncidenceBudget (G : Finset F) (B : ℝ) : ℕ :=
  ⌈(G.card : ℝ) + (Fintype.card F : ℝ) * B⌉₊

/-- The analytic worst-case incidence is below its ceiling budget — the trivial half tying
`worstCase_incidence_le` to `charSumIncidenceBudget`. -/
theorem lineIncidence_le_charSumIncidenceBudget {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) (s₀ s₁ : F) :
    lineIncidence G s₀ s₁ ≤ charSumIncidenceBudget (F := F) G B := by
  have hle := lineIncidence_le_mean_add hψ G s₀ s₁ hB0 hB
  unfold charSumIncidenceBudget
  have hceil : (G.card : ℝ) + (Fintype.card F : ℝ) * B
      ≤ (⌈(G.card : ℝ) + (Fintype.card F : ℝ) * B⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast le_trans hle hceil

/-! ### The end-to-end capstone: `δ*` lower bound from the char-sum bound `B` ONLY -/

open Classical in
/-- **End-to-end `δ*` lower-bound conditional from the char-sum bound `B` (TRUE; VACUOUS at the
prize budget).**

This is a true, axiom-clean conditional with the analytic input isolated to the single object `B`
(the uniform Gauss-period bound).  For a code `C`, radius `δ`, target `ε*`, smooth subgroup
`G = μ_n`, primitive character `ψ`, and uniform char-sum bound `B`:

* **(`hB`)** the **char-sum bound** `‖η_b‖ ≤ B` for all `b ≠ 0`;
* **(`hStruct`)** the **in-tree far-coset structural law** — every word stack's bad-scalar count
  is at most some far-line incidence `lineIncidence G (s₀ u) (s₁ u)` of the syndrome geometry
  (`FarCosetExplosion.badScalars_eq_explainable`; structural plumbing, NOT analytic content);
* **(`hBudget`)** the budget hypothesis `(charSumIncidenceBudget G B : ℝ≥0∞) / q ≤ ε*`, i.e.
  `(|G| + q·B)/q ≤ ε*` with the **naive** incidence `|G| + q·B`;
* **(`hδ1`)** `δ ≤ 1`.

**Then** `δ ≤ mcaDeltaStar C ε*`.

WARNING — this conditional does NOT by itself give the prize lower bound, and the budget hypothesis
is VACUOUS at the prize budget (corrected per the adversarial refutation `wf_9db879bc`):

* The deviation brick `lineIncidence_le_mean_add` supplies only the **naive `I ≤ |G| + q·B`** —
  `B` paid once per annihilating frequency over the up-to-`q`-size hyperplane, **no cancellation
  between distinct frequencies**.  The `q·B` is NOT a square-root-cancelled `√q·B`.
* Hence `hBudget` reads `|G|/q + B ≤ ε*`.  At the prize budget `q·ε* ≈ n` with `|G| ≈ n` this is
  `B ≤ ε* − |G|/q ≈ 0`, i.e. it requires `q·B ≤ 0`, i.e. **`B = 0`**.  Any nonzero power-saving
  `B = n^{1−c}` (Di Benedetto `B ≤ n^{1−31/2880}` is PROVEN) overshoots the prize budget by
  `≈ q·B/n = n^{1−c}` (`≈ 1e47` at the prize point), so it does NOT satisfy `hBudget`.
* Reaching the prize budget for nonzero `B` requires the **per-frequency square-root cancellation**
  `∑_{b·s₁=0} conj(η_b)ψ(b·s₀) ≲ √q·B`, the open **Paley-graph / BCHKS Conjecture 1.12** floor.
  This brick does NOT supply it.  The conditional is honest and reusable, but its prize-budget
  instantiation is empty for nonzero `B`. -/
theorem le_mcaDeltaStar_of_charSumBound
    (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ : ℝ≥0)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B)
    (s₀ s₁ : WordStack A (Fin 2) ι → F)
    (hStruct : ∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
        ≤ lineIncidence G (s₀ u) (s₁ u))
    (hBudget : (charSumIncidenceBudget (F := F) G B : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar := by
  -- Each stack's bad count ≤ its far-line incidence ≤ the analytic budget ⌈|G|+q·B⌉.
  have hM : ∀ u : WordStack A (Fin 2) ι,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card
        ≤ charSumIncidenceBudget (F := F) G B := fun u =>
    le_trans (hStruct u)
      (lineIncidence_le_charSumIncidenceBudget hψ G hB0 hB (s₀ u) (s₁ u))
  exact le_mcaDeltaStar_of_uniformCharSumBound C εstar δ hM hBudget hδ1

/-! ### Non-vacuity: the char-sum hypothesis is satisfiable -/

/-- **The char-sum hypothesis `hB` is satisfiable: it always holds at `B = |G|`.** The subgroup
Gauss period is a sum of `|G|` unit-modulus terms, so `‖η_b‖ ≤ |G|` for every `b`, including
`b ≠ 0`.  Hence the hypothesis `hB` is consistent — never contradictory — for any `B ≥ |G|`.

NOTE on scope: this certifies only that `hB` is non-contradictory.  It does NOT certify that the
*budget* hypothesis `hBudget` is satisfiable at the prize budget — it is not (see
`le_mcaDeltaStar_of_charSumBound`: `hBudget` at `q·ε* ≈ n` forces `B ≈ 0`, so even the PROVEN
power-saving `B = n^{1−31/2880}` fails the budget).  The conditional's prize-budget instantiation is
empty for nonzero `B`; closing it needs the open √q·B cancellation (Paley/BCHKS-1.12). -/
theorem charSumBound_satisfiable_trivial {ψ : AddChar F ℂ} (G : Finset F) :
    ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ (G.card : ℝ) := by
  intro b _
  calc ‖eta ψ G b‖ = ‖∑ y ∈ G, ψ (b * y)‖ := rfl
    _ ≤ ∑ y ∈ G, ‖ψ (b * y)‖ := norm_sum_le _ _
    _ = ∑ _y ∈ G, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun y _ => ?_); exact norm_addChar_apply ψ (b * y)
    _ = (G.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The char-sum bound `B` exists (the hypothesis set `hB` is consistent).** There is a `B ≥ 0`
with `‖η_b‖ ≤ B` for all `b ≠ 0` — namely `B = |G|`.  This packages
`charSumBound_satisfiable_trivial` as the explicit witness that the char-sum premise of
`le_mcaDeltaStar_of_charSumBound` is not contradictory.

This is ONLY about consistency of `hB`; it says nothing about the *budget* hypothesis `hBudget`,
which is the part that fails at the prize budget (it forces `B ≈ 0`, while the trivial witness has
`B = |G| ≈ n`).  See `le_mcaDeltaStar_of_charSumBound` for why the conditional is vacuous at the
prize budget for nonzero `B`. -/
theorem charSumBound_consistent {ψ : AddChar F ℂ} (G : Finset F) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :=
  ⟨(G.card : ℝ), by positivity, charSumBound_satisfiable_trivial G⟩

end ArkLib.ProximityGap.CharSumDeltaStarBridge

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms
  ArkLib.ProximityGap.CharSumDeltaStarBridge.epsMCA_le_of_forall_badCount_le
#print axioms ArkLib.ProximityGap.CharSumDeltaStarBridge.worstCase_incidence_le
#print axioms
  ArkLib.ProximityGap.CharSumDeltaStarBridge.le_mcaDeltaStar_of_uniformCharSumBound
#print axioms
  ArkLib.ProximityGap.CharSumDeltaStarBridge.lineIncidence_le_charSumIncidenceBudget
#print axioms
  ArkLib.ProximityGap.CharSumDeltaStarBridge.le_mcaDeltaStar_of_charSumBound
#print axioms
  ArkLib.ProximityGap.CharSumDeltaStarBridge.charSumBound_satisfiable_trivial
#print axioms ArkLib.ProximityGap.CharSumDeltaStarBridge.charSumBound_consistent
