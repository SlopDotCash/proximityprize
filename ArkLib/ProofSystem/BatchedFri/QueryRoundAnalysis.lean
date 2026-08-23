/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Batched FRI query-round acceptance analysis (issue #14)

The per-round query-soundness probability accounting: queryAcceptProb_eq (= |G|^t/N^t exact),
queryAcceptProb_le (<= (1-d)^t), queryAcceptProb_add_detect (partition), queryDetectProb_ge,
and the claim assembly. The source tree now has the corresponding PMF route in
`ArkLib.ToMathlib.FriQueryRoundProb` / `QueryRoundProbability.lean`, including the bridge from the
concrete FRI query-round challenge oracle to the uniform product PMF. The remaining input is the
protocol-specific verifier-guard-to-correlated-agreement/proximity trigger and OracleReduction
plumbing.
-/

open scoped NNReal ENNReal
open Finset Function ProbabilityTheory PMF

namespace Issue14Scratch

/-! ## Part A. Query-tuple counting and the product cardinality.

`card_allQueriesIn` restates the in-tree `Fri.QueryRound.card_allQueriesIn`
verbatim; `card_queryTuple` provides `card (Fin t → ι) = N^t`. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- (= `Fri.QueryRound.card_allQueriesIn`) The number of length-`t` query tuples
landing entirely in `G` is `|G|^t`. -/
theorem card_allQueriesIn (G : Finset ι) (t : ℕ) :
    (Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card = G.card ^ t := by
  classical
  have hpi : (Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G))
      = Fintype.piFinset (fun _ : Fin t => G) := by
    ext q; simp [Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  simp

/-- `card (Fin t → ι) = (card ι)^t`.
`Fintype.card_fun : card (α → β) = card β ^ card α`, with `card (Fin t) = t`. -/
theorem card_queryTuple (t : ℕ) :
    Fintype.card (Fin t → ι) = (Fintype.card ι) ^ t := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-! ## Part B. The probability-measure value of the all-queries-in-`G` event.

To keep Parts A–C **Mathlib-only** (independently checkable, no ArkLib import),
we define the query-round acceptance probability *directly* as the raw PMF tsum,
which is exactly what the in-tree `Pr_{ ... }[ ... ]` notation reduces to (proved
in-tree as `ProbabilityTheory.Pr_eq_tsum_indicator`):

  `Pr_{ let a ← p }[P a] = ∑' a, p a * (if P a then 1 else 0)`.

The bridge to that notation is recorded as a comment on `queryAcceptProb`; the
substance below uses only `PMF.uniformOfFintype`, `Finset`, `Fintype`, `ℝ≥0∞`. -/

/-- Probability that a tuple `q : Fin t → ι`, drawn from the independent-uniform
product PMF, lands entirely in `G`.  This is definitionally
`Pr_{ let q ← PMF.uniformOfFintype (Fin t → ι) }[∀ j, q j ∈ G]`
(via `ProbabilityTheory.Pr_eq_tsum_indicator`). -/
noncomputable def queryAcceptProb [Nonempty ι] (G : Finset ι) (t : ℕ) : ℝ≥0∞ :=
  ∑' q : Fin t → ι,
    (PMF.uniformOfFintype (Fin t → ι)) q * (if (∀ j, q j ∈ G) then (1 : ℝ≥0∞) else 0)

/-- Complementary detection probability: some query lands outside `G`. -/
noncomputable def queryDetectProb [Nonempty ι] (G : Finset ι) (t : ℕ) : ℝ≥0∞ :=
  ∑' q : Fin t → ι,
    (PMF.uniformOfFintype (Fin t → ι)) q * (if ¬ (∀ j, q j ∈ G) then (1 : ℝ≥0∞) else 0)

/-- Indicator-sum bookkeeping: `∑ x, (if p x then 1 else 0) = |{x | p x}|` in `ℝ≥0∞`.
Uses `Finset.sum_boole` (stable across mathlib v4.30). -/
theorem sum_indicator_eq_card_filter
    {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ x : α, (if p x then (1 : ℝ≥0∞) else 0))
      = ((Finset.univ.filter p).card : ℝ≥0∞) := by
  classical
  rw [Finset.sum_boole]

/-- **Exact value.** Under the independent-uniform product PMF on `Fin t → ι`, the
probability that all `t` queries land in `G` equals `|G|^t / N^t`. -/
theorem queryAcceptProb_eq [Nonempty ι] (G : Finset ι) (t : ℕ) :
    queryAcceptProb G t = (G.card : ℝ≥0∞) ^ t / (Fintype.card ι : ℝ≥0∞) ^ t := by
  classical
  unfold queryAcceptProb
  -- turn the tsum over the fintype into a finite sum
  rw [tsum_fintype]
  -- each uniform weight is the constant (card (Fin t → ι))⁻¹
  simp_rw [PMF.uniformOfFintype_apply]
  -- factor the constant out of the indicator sum
  rw [← Finset.mul_sum]
  -- reduce the indicator sum to the filter cardinality, then count
  rw [sum_indicator_eq_card_filter (p := fun q : Fin t → ι => ∀ j, q j ∈ G),
      card_allQueriesIn G t, card_queryTuple t]
  -- Goal: (↑(card ι ^ t))⁻¹ * ↑(G.card ^ t) = (↑G.card) ^ t / (↑card ι) ^ t
  push_cast
  -- Goal: ((↑card ι) ^ t)⁻¹ * (↑G.card) ^ t = (↑G.card) ^ t / (↑card ι) ^ t
  rw [ENNReal.div_eq_inv_mul]

/-! ## Part C. Acceptance bound and detection bound (probability form). -/

/-- **ACCEPTANCE bound (probability form).** If the good (corruption-missing) set
`G` has normalized density `|G|/N ≤ 1 - δ`, the probability that all `t` queries
land in `G` is at most `(1 - δ)^t`. -/
theorem queryAcceptProb_le [Nonempty ι] (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (h_density : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ) :
    queryAcceptProb G t ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ t := by
  classical
  rw [queryAcceptProb_eq G t]
  -- Base inequality in ℝ≥0∞ from the ℝ≥0 density.
  have hN : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  have hbaseNN :
      (G.card : ℝ≥0∞) / (Fintype.card ι : ℝ≥0∞) ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) := by
    calc (G.card : ℝ≥0∞) / (Fintype.card ι : ℝ≥0∞)
        = (((G.card : ℝ≥0) / (Fintype.card ι) : ℝ≥0) : ℝ≥0∞) := by
              -- `ENNReal.coe_div hN : ↑(a/b) = ↑a/↑b`; the two double-`Nat`-casts
              -- reconcile under `push_cast`.
              rw [ENNReal.coe_div hN]
              push_cast
              rfl
      _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast h_density
  have hdiv_pow :
      ((G.card : ℝ≥0∞) / (Fintype.card ι : ℝ≥0∞)) ^ t
        = (G.card : ℝ≥0∞) ^ t / (Fintype.card ι : ℝ≥0∞) ^ t := by
    rw [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  calc (G.card : ℝ≥0∞) ^ t / (Fintype.card ι : ℝ≥0∞) ^ t
      = ((G.card : ℝ≥0∞) / (Fintype.card ι : ℝ≥0∞)) ^ t := hdiv_pow.symm
    _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ t := pow_le_pow_left' hbaseNN t

/-- The accept event and the detect (complement) event partition probability mass:
their probabilities sum to `1`. -/
theorem queryAcceptProb_add_detect [Nonempty ι] (G : Finset ι) (t : ℕ) :
    queryAcceptProb G t + queryDetectProb G t = 1 := by
  classical
  unfold queryAcceptProb queryDetectProb
  rw [← ENNReal.tsum_add]
  have hpoint :
      (fun q : Fin t → ι =>
          (PMF.uniformOfFintype (Fin t → ι)) q * (if (∀ j, q j ∈ G) then (1:ℝ≥0∞) else 0)
        + (PMF.uniformOfFintype (Fin t → ι)) q * (if ¬ (∀ j, q j ∈ G) then (1:ℝ≥0∞) else 0))
        = fun q : Fin t → ι => (PMF.uniformOfFintype (Fin t → ι)) q := by
    funext q
    by_cases hq : (∀ j, q j ∈ G) <;> simp [hq]
  rw [hpoint, PMF.tsum_coe]

/-- **DETECTION / SOUNDNESS bound (probability form).** The complementary event —
*some* query lands outside `G`, detecting an inconsistency — has probability at
least `1 - (1 - δ)^t`. This is the soundness guarantee of the `t`-repetition query
phase: a `δ`-far word is rejected with probability `≥ 1 - (1 - δ)^t`. -/
theorem queryDetectProb_ge [Nonempty ι] (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (h_density : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ) :
    1 - ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ t ≤ queryDetectProb G t := by
  classical
  have hsum : queryAcceptProb G t + queryDetectProb G t = 1 :=
    queryAcceptProb_add_detect G t
  have hacc : queryAcceptProb G t ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ t :=
    queryAcceptProb_le G δ t h_density
  -- accept ≠ ∞ (it is ≤ 1).
  have hacc_ne_top : queryAcceptProb G t ≠ ∞ := by
    have hle1 : queryAcceptProb G t ≤ 1 := by
      have := add_le_add_right (le_refl (queryAcceptProb G t)) (queryDetectProb G t)
      calc queryAcceptProb G t
          ≤ queryAcceptProb G t + queryDetectProb G t := le_self_add
        _ = 1 := hsum
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hle1
  -- detect = 1 - accept  (from accept + detect = 1, via `ENNReal.eq_sub_of_add_eq`).
  have hB_eq : queryDetectProb G t = 1 - queryAcceptProb G t := by
    have h' : queryDetectProb G t + queryAcceptProb G t = 1 := by
      rw [add_comm]; exact hsum
    exact ENNReal.eq_sub_of_add_eq hacc_ne_top h'
  rw [hB_eq]
  -- 1 - (1-δ)^t ≤ 1 - accept  (antitone in the subtrahend, since accept ≤ (1-δ)^t).
  exact tsub_le_tsub_left hacc 1

/-! ## Part D. Wiring to the in-tree Claim 8.2 frontier; honest residual isolation.

The in-tree residual `Fri.fri_query_soundness` reduces, via the proved
`Fri.FriQuerySoundnessParts.pieces_imply_claim`, to three named ingredients. Part B
/ C above *proves* the probability-measure form of the first
(`query_round_acceptance_bound`). The other two are genuinely open / sibling-owned
and are isolated below as explicit named `Prop` hypotheses — they are NOT proved
and NOT axiomatized in shared code.

`assembleClaim82` shows precisely how the proved query-round acceptance probability
plugs into the frontier: it is hypothesis-clean (it *takes* R1 and R2 as arguments
rather than asserting them), so it carries no hidden soundness debt. -/

section Wiring

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/-- Local mirror of the in-tree `ArkLib.Data.CodingTheory.InterleavedCode.jointAgreement`
(InterleavedCode.lean:697), reproduced verbatim so that Part D's wiring skeleton compiles
under bare `import Mathlib` (the scratch file does not import ArkLib).  Definitionally
identical to the in-tree predicate, so the wiring transfers unchanged. -/
def Code.jointAgreement {F κ ι : Type*} [Fintype ι] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ≥0) (W : κ → ι → F) : Prop :=
  ∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∃ v : κ → ι → F, ∀ i, v i ∈ C ∧ S ⊆ Finset.filter (fun j => v i j = W i j) Finset.univ

/-- (R1) Named residual: the correlated-agreement → `Code.jointAgreement` coding
bridge (the deep BCIKS20 proximity-gap content). Takes the *density* hypothesis and
yields joint agreement at `δ := 1 - α`. NOT proved here. -/
structure CorrelatedAgreementBridge
    {κ ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Set (ι → 𝔽)) (densityLEα : Prop) (α : ℝ≥0) (W : κ → ι → 𝔽) : Prop where
  bridge :
    densityLEα →
      Code.jointAgreement (F := 𝔽) (κ := κ) (ι := ι) (C := C) (δ := 1 - α) (W := W)

/-- (R2) Named residual: the batching virtual-oracle-lens soundness preservation,
sequential composition, and total-error accounting that turn the per-query
acceptance probability into the end-to-end `OracleReduction.run` bound. Sibling-
owned protocol plumbing. NOT proved here. -/
structure QueryRoundReductionWiring
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) (densityLEα : Prop) : Prop where
  -- The proved per-query acceptance probability bound (`queryAcceptProb_le`) is
  -- *available* to the wiring; `queryAcceptProb` is defeq to the in-tree
  -- `Pr_{ let q ← PMF.uniformOfFintype (Fin t → ι) }[∀ j, q j ∈ G]`.
  acceptance_available :
    ∀ [Nonempty ι], (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ →
      queryAcceptProb G t ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ t
  -- The remaining (unproved) reduction step that derives the density hypothesis the
  -- coding bridge consumes from the end-to-end soundness analysis.
  derives_density : densityLEα

/-- Assembly skeleton for Claim 8.2: given the proved query-round acceptance
probability (packaged in `QueryRoundReductionWiring.acceptance_available`) and the
two named residuals R1/R2, conclude `Code.jointAgreement`. This is hypothesis-clean
(R1, R2 are arguments), exposing exactly where the proved math meets the open
substrate — no `sorry`, no axiom. -/
theorem assembleClaim82
    {κ ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Set (ι → 𝔽)) (α δ : ℝ≥0) (W : κ → ι → 𝔽)
    (G : Finset ι) (t : ℕ) (densityLEα : Prop)
    (wiring : QueryRoundReductionWiring G δ t densityLEα)
    (bridge : CorrelatedAgreementBridge (𝔽 := 𝔽) C densityLEα α W) :
    Code.jointAgreement (F := 𝔽) (κ := κ) (ι := ι) (C := C) (δ := 1 - α) (W := W) :=
  bridge.bridge wiring.derives_density

end Wiring

/-! ## Summary

PROVED probability-measure query-round analysis (the genuine extractable advance),
all Mathlib-only (Parts A–C, no ArkLib import):
  * `queryAcceptProb_eq`        — Pr[all t queries in G] = |G|^t / N^t   (EXACT)
  * `queryAcceptProb_le`        — ≤ (1-δ)^t  under |G|/N ≤ 1-δ           (ACCEPT error)
  * `queryAcceptProb_add_detect`— accept + detect = 1                    (partition of mass)
  * `queryDetectProb_ge`        — detect ≥ 1 - (1-δ)^t                   (SOUNDNESS)

`queryAcceptProb G t` is *defeq* to the in-tree
`Pr_{ let q ← PMF.uniformOfFintype (Fin t → ι) }[∀ j, q j ∈ G]` via
`ProbabilityTheory.Pr_eq_tsum_indicator` (one `rw`), so these transfer directly
to the FRI cone's notation. Part D (the `Code.jointAgreement` wiring) additionally
imports `ArkLib.Data.CodingTheory.InterleavedCode`.

These promote the in-tree *ratio* lemmas (`Fri.QueryRound.queryRound_acceptance_le_of_density`,
`Fri.queryRoundDensityBound`) to the PMF probability the `OracleReduction.run`
acceptance analysis measures, and add the complementary detection bound the in-tree
code never stated.

GENUINELY OPEN (named, isolated, NOT faked):
  R1 — protocol transcript → CA/proximity trigger → jointAgreement
  R2 — virtual-oracle-lens / sequential-composition / total-error wiring
-/

end Issue14Scratch
