/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# FRI query-round soundness: probability-measure form (issue #14)

The Batched FRI security file (`ArkLib/ProofSystem/BatchedFri/Security.lean`) proves the
**counting** form of the query-round acceptance bound:

  `|{ q : Fin t → ι | ∀ j, q j ∈ G }| / N ^ t ≤ (1 - δ) ^ t`,

where `G` is the "good" (corruption-missing) set of evaluation points, `N = |ι|` is the domain
size, and `t` is the number of independent query repetitions.

That counting ratio is exactly the **probability**, under `t` *independent uniform* queries, that
every query lands in `G` — i.e. the probability that a `δ`-far word slips through the entire
query phase undetected. This module makes that bridge precise and self-contained (it imports only
`Mathlib`, so it is verifiable independently of the FRI dependency cone, which is currently not
fully built in the shared checkout).

## Main results

* `prob_allQueriesIn_eq` : under the independent-uniform product PMF on `Fin t → ι`, the
  probability of the event `{ q | ∀ j, q j ∈ G }` equals `(|G| / N) ^ t`.
* `prob_allQueriesIn_le` : that probability is `≤ (1 - δ) ^ t` whenever the good set has
  density `|G| / N ≤ 1 - δ` (the soundness-error bound consumed by Claim 8.2).
* `prob_someQueryOut_ge` : the complementary detection probability is
  `≥ 1 - (1 - δ) ^ t` — the honest "the verifier catches a far word" statement.

All results are `[propext, Classical.choice, Quot.sound]` only.
-/

namespace ArkLib.Fri.QueryRoundProb

open scoped NNReal ENNReal BigOperators
open PMF

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The independent-uniform product distribution on length-`t` query tuples: each of the `t`
coordinates is sampled uniformly and independently from the domain `ι`. -/
noncomputable def uniformQueries (t : ℕ) [Nonempty ι] : PMF (Fin t → ι) :=
  PMF.uniformOfFintype (Fin t → ι)

/-- Complement identity for the uniform PMF outer measure on a `Fintype`: since the total mass is
`1`, the probability of `sᶜ` is `1 - P(s)`. (All sets are measurable for the discrete σ-algebra on
a finite type, so this follows from `measure_compl` on the associated probability measure.) -/
theorem prob_compl_eq (β : Type) [Fintype β] [Nonempty β] (s : Set β) :
    (PMF.uniformOfFintype β).toOuterMeasure sᶜ
      = 1 - (PMF.uniformOfFintype β).toOuterMeasure s := by
  classical
  letI : MeasurableSpace β := ⊤
  haveI : MeasurableSingletonClass β :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : MeasureTheory.IsProbabilityMeasure (PMF.uniformOfFintype β).toMeasure :=
    ⟨by simp⟩
  have hms : ∀ A : Set β, MeasurableSet A := fun _ => MeasurableSpace.measurableSet_top
  have hcompl : ((PMF.uniformOfFintype β).toMeasure) sᶜ
      = 1 - ((PMF.uniformOfFintype β).toMeasure) s :=
    MeasureTheory.prob_compl_eq_one_sub (hms s)
  rwa [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (hms _),
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (hms _)] at hcompl

omit [DecidableEq ι] in
/-- A single uniform query lands in the good set `G` with probability `|G| / N`. -/
theorem prob_singleQueryIn (G : Finset ι) [Nonempty ι] :
    (PMF.uniformOfFintype ι).toOuterMeasure G = (G.card : ℝ≥0∞) / Fintype.card ι := by
  classical
  rw [PMF.toOuterMeasure_apply_finset]
  have hval : ∀ a ∈ G, (PMF.uniformOfFintype ι) a = (Fintype.card ι : ℝ≥0∞)⁻¹ := by
    intro a _; exact PMF.uniformOfFintype_apply a
  rw [Finset.sum_congr rfl hval]
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.div_eq_inv_mul]
  ring

omit [DecidableEq ι] in
/-- **Query-round acceptance probability (exact form).** Under `t` independent uniform queries,
the probability that *every* query lands in the good set `G` equals `(|G| / N) ^ t`.

This is the probability-measure incarnation of the proved counting identity
`|{ q | ∀ j, q j ∈ G }| = |G| ^ t` from `BatchedFri/Security.lean`. -/
theorem prob_allQueriesIn_eq (G : Finset ι) (t : ℕ) [Nonempty ι] :
    (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
        {q : Fin t → ι | ∀ j, q j ∈ G}
      = ((G.card : ℝ≥0∞) / Fintype.card ι) ^ t := by
  classical
  -- The event as a `Finset` (pi finset over `G` in each coordinate).
  have hset : {q : Fin t → ι | ∀ j, q j ∈ G}
      = (Fintype.piFinset (fun _ : Fin t => G) : Finset (Fin t → ι)) := by
    ext q; simp
  rw [hset, PMF.toOuterMeasure_apply_finset]
  -- Each tuple has probability `1 / |Fin t → ι| = (1/N)^t`; count = `|G|^t`.
  have hval : ∀ a ∈ Fintype.piFinset (fun _ : Fin t => G),
      (PMF.uniformOfFintype (Fin t → ι)) a
        = (Fintype.card (Fin t → ι) : ℝ≥0∞)⁻¹ := by
    intro a _; exact PMF.uniformOfFintype_apply a
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Fintype.card_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Goal: `↑(G.card ^ t) * (↑(card ι ^ t))⁻¹ = (↑G.card / ↑(card ι)) ^ t`
  rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]
  push_cast
  ring

omit [DecidableEq ι] in
/-- **Query-round soundness error (probability form).** If the good set has density
`|G| / N ≤ 1 - δ`, then the probability that all `t` independent uniform queries land in `G`
(the soundness-failure event) is at most `(1 - δ) ^ t`.

This is the probability-space statement of the FRI/Batched-FRI Claim 8.2 query-round error. -/
theorem prob_allQueriesIn_le (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) [Nonempty ι]
    (h_density : (G.card : ℝ≥0∞) / Fintype.card ι ≤ 1 - δ) :
    (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
        {q : Fin t → ι | ∀ j, q j ∈ G}
      ≤ (1 - δ) ^ t := by
  rw [prob_allQueriesIn_eq G t]
  exact pow_le_pow_left' h_density t

omit [DecidableEq ι] in
/-- **Detection probability lower bound.** The probability that *some* query lands outside the
good set `G` (the verifier's "reject a far word" event) is at least `1 - (1 - δ) ^ t`.

This is the honest soundness guarantee: a `δ`-far word is rejected by the query phase except with
probability `(1 - δ) ^ t`. -/
theorem prob_someQueryOut_ge (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) [Nonempty ι]
    (h_density : (G.card : ℝ≥0∞) / Fintype.card ι ≤ 1 - δ) :
    1 - (1 - δ) ^ t
      ≤ (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
          {q : Fin t → ι | ¬ (∀ j, q j ∈ G)} := by
  classical
  -- Complement: P(¬E) = 1 - P(E) for a PMF outer measure, then monotone in P(E) bound.
  have hev : {q : Fin t → ι | ¬ (∀ j, q j ∈ G)}
      = {q : Fin t → ι | ∀ j, q j ∈ G}ᶜ := by
    ext q; simp [Set.mem_compl_iff]
  rw [hev, prob_compl_eq]
  exact tsub_le_tsub_left (prob_allQueriesIn_le G δ t h_density) 1

/-! ### Query-round detection amplification (issue #14)

The detection lower bound `1 - (1 - δ) ^ t` from `prob_someQueryOut_ge` is monotone in the number
of queries `t` and, for `t ≥ 1`, dominates the single-query rejection probability `δ`. These
arithmetic facts turn a single-query rejection guarantee — in particular the BCIKS20 RS
affine-line proximity threshold `ε := errorBound δ deg domain`, which lower-bounds the
single-query detection of a `δ`-far word — into a `t`-round rejection guarantee. -/

/-- `(1 - δ) ^ t` is antitone in `t`, since `1 - δ ≤ 1`: more queries can only shrink the
joint-acceptance probability of a far word. -/
theorem accProb_antitone (δ : ℝ≥0∞) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    (1 - δ) ^ t₂ ≤ (1 - δ) ^ t₁ :=
  pow_le_pow_of_le_one (by simp) tsub_le_self h

/-- The per-round detection lower bound `1 - (1 - δ) ^ t` is monotone in the number of queries
`t`: more queries can only increase the rejection guarantee. -/
theorem detectBound_monotone (δ : ℝ≥0∞) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    (1 : ℝ≥0∞) - (1 - δ) ^ t₁ ≤ 1 - (1 - δ) ^ t₂ :=
  tsub_le_tsub_left (accProb_antitone δ h) 1

/-- With a single query the detection lower bound is exactly `δ`: a `δ`-far word is rejected with
probability `≥ 1 - (1 - δ) ^ 1 = δ`. -/
theorem detectBound_one (δ : ℝ≥0∞) (hδ : δ ≤ 1) :
    (1 : ℝ≥0∞) - (1 - δ) ^ 1 = δ := by
  rw [pow_one, ENNReal.sub_sub_cancel ENNReal.one_ne_top hδ]

/-- For at least one query, the `t`-round detection lower bound dominates the single-query
rejection probability `δ`. -/
theorem detectBound_ge_delta (δ : ℝ≥0∞) (hδ : δ ≤ 1) {t : ℕ} (ht : 1 ≤ t) :
    δ ≤ (1 : ℝ≥0∞) - (1 - δ) ^ t := by
  calc
    δ = (1 : ℝ≥0∞) - (1 - δ) ^ 1 := (detectBound_one δ hδ).symm
    _ ≤ (1 : ℝ≥0∞) - (1 - δ) ^ t := detectBound_monotone δ ht

omit [DecidableEq ι] in
/-- **A query round rejects a far word with probability ≥ the proximity bound.** If a proximity
error threshold `ε` (e.g. the BCIKS20 RS affine-line `errorBound δ deg domain`) lower-bounds the
single-query rejection probability `δ` of a `δ`-far word, then the `t`-query round (`t ≥ 1`)
rejects that word — `some query lands outside the good set` — with probability at least `ε`.

This is the arithmetic bridge from the single-round RS affine-line proximity rejection to the
amplified `t`-round query phase: increasing the query count never decreases the guarantee. -/
theorem prob_someQueryOut_ge_proximity
    (G : Finset ι) (δ ε : ℝ≥0∞) (t : ℕ) [Nonempty ι]
    (h_detection : ε ≤ (1 : ℝ≥0∞) - (1 - δ) ^ t)
    (h_density : (G.card : ℝ≥0∞) / Fintype.card ι ≤ 1 - δ) :
    ε ≤ (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
          {q : Fin t → ι | ¬ (∀ j, q j ∈ G)} :=
  le_trans h_detection (prob_someQueryOut_ge G δ t h_density)

/-! ### Axiom audit (issue #14 query-round probability brick) -/

#print axioms prob_singleQueryIn
#print axioms prob_allQueriesIn_eq
#print axioms prob_allQueriesIn_le
#print axioms prob_someQueryOut_ge
#print axioms prob_compl_eq
#print axioms accProb_antitone
#print axioms detectBound_monotone
#print axioms detectBound_one
#print axioms detectBound_ge_delta
#print axioms prob_someQueryOut_ge_proximity

end ArkLib.Fri.QueryRoundProb
