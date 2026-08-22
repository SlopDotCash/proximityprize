/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilHarvestCap

/-!
# Dimension deficit: forced coincidence mass, the Bezout escape class, and the
# conditional three-pencil `StallResidual` composition

Issue #466, P1 rate-quarter — executes the "formalize the dimension count" round on
top of `_P1RateQuarterPencilHarvestCap.lean`.

**Probe** (`scripts/probes/probe_rate_quarter_p1_dimension_deficit.py`, exact):

* **The pure degree argument is NOT universal.**  A fully-aligned pencil triple needs
  nonzero polys `a + b = c` (deg `< k`) with `roots ⊇ (ov₁₂, ov₂₃, ov₁₃)` — a Bezout
  identity `z_X·α + z_Y·β = z_Z·γ`.  Coefficient counting kills it generically when
  `Σ|ov| ≥ 2k`, but an explicit toy escape exists (`k = 3, q = 17`: solution dim 1 at
  `Σ = 2k`).  So "dimension deficit ⟹ no triple" cannot be a kernel theorem without
  excluding the escape class; this file does NOT pretend otherwise.
* **The natural escapes fail at μ_256 by exact squeezes**: multiplicative-coset
  configurations (`x^64 − s` splitting over `F₂₅₇`) overshoot the degree budget by
  exactly one (`64 = k`), while order-32 cosets undershoot the coverage floor
  (`96 < 167`); exact solution dimension is 0 in every admissible configuration.
* At the prize shape the escape would need `≥ 167772161` common roots per overlap
  inside the window `[0, 2^30) ⊂ F_P` from deg `< k` polynomial triples — a
  BGK/Paley-type nonexistence, open.

**What IS kernel-checked here** (prize shape):

* `bonferroni_three` — three-set inclusion-exclusion lower bound in `Fin N`.
* `fullyAligned_triple_pairwise_overlap_ge` — **the forced-coincidence theorem**: any
  pairwise-distinct pencil triple with all alignments `≥ T − 1` forces EVERY pairwise
  aligned-overlap to carry `≥ 167772161` coordinates — two distinct codeword pairs
  agreeing simultaneously with the stack on `≥ 1.67·10⁸` common points.  This is the
  structure any escape must realize.
* `symmetric_escape_excluded` — the equal-overlap escape (all three overlaps the same
  set) is IMPOSSIBLE: it would force `3(T−1) ≤ N + 2(k−1)`, false by
  `167772161 > 0`-scale margins.  First unconditional exclusion inside the escape
  class.
* `FullyAlignedTripleFree` — the named residual (margin form of the dimension
  deficit): every pairwise-distinct pencil triple has some pencil 5-under-aligned.
  Probe-pinned generically (forced margin `≈ 5.6·10⁷ ≫ 5`); NOT a tautology (toy
  escape); open exactly on the Bezout-coincidence class over the prize window.
* `stall_budget_of_three_pencil_cover_of_tripleFree` — **the composition**:
  `FullyAlignedTripleFree dom u₀ u₁` implies every bad family covered by three
  pairwise-distinct pencils obeys the `StallResidual` budget `#bad ≤ N`.
* `generic_alignment_threshold` — the exact shortfall at which the generic dimension
  turns positive (`t = 55924054`), and `mu256_coset_squeeze` — the μ_256 squeeze
  arithmetic.

**Honesty**: the coordinator's route "pure degree argument forces `ρ=σ=τ=0`" is
REFUTED as a universal statement (toy escape).  `FullyAlignedTripleFree` is the
honest residual carrying exactly the open content; `StallResidual` itself remains
open (also: cover-by-few-pencils is unproven).  No δ* movement; the bracket
`3/8 ≤ δ* ≤ 43/96 + ε` is untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterDimensionDeficit

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

local instance localInstance_P1RateQuarterDimensionDeficit_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterDimensionDeficit_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Inclusion-exclusion bookkeeping -/

/-- **Bonferroni for three sets in `Fin N`**: total mass is at most `N` plus the
pairwise overlap mass. -/
theorem bonferroni_three (A₁ A₂ A₃ : Finset (Fin N)) :
    A₁.card + A₂.card + A₃.card ≤
      N + (A₁ ∩ A₂).card + (A₁ ∩ A₃).card + (A₂ ∩ A₃).card := by
  classical
  have h12 := Finset.card_union_add_card_inter A₁ A₂
  have h123 := Finset.card_union_add_card_inter (A₁ ∪ A₂) A₃
  have hdist : (A₁ ∪ A₂) ∩ A₃ = (A₁ ∩ A₃) ∪ (A₂ ∩ A₃) :=
    Finset.union_inter_distrib_right ..
  have hle : ((A₁ ∩ A₃) ∪ (A₂ ∩ A₃)).card ≤ (A₁ ∩ A₃).card + (A₂ ∩ A₃).card :=
    Finset.card_union_le _ _
  have hN : (A₁ ∪ A₂ ∪ A₃).card ≤ N := by
    have h := Finset.card_le_univ (A₁ ∪ A₂ ∪ A₃)
    simpa [Finset.card_univ, Fintype.card_fin] using h
  rw [hdist] at h123
  omega

/-! ## The forced-coincidence theorem -/

section Triple

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable {wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ : Fin N → F}

/-- **Forced coincidence**: a pairwise-distinct pencil triple with all alignments
`≥ T − 1` forces the `(a,b)`-overlap to carry at least
`3(T−1) − N − 2(k−1) = 167772161` coordinates (and symmetrically for the other two
pairs) — two distinct codeword pairs agreeing simultaneously with the stack on
`≥ 1.67·10⁸` common points.  Any escape from the dimension deficit must realize this
coincidence mass inside the evaluation window. -/
theorem fullyAligned_triple_pairwise_overlap_ge
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hwc₀ : wc₀ ∈ predecessorCode dom) (hwc₁ : wc₁ ∈ predecessorCode dom)
    (hac : (wa₀, wa₁) ≠ (wc₀, wc₁)) (hbc : (wb₀, wb₁) ≠ (wc₀, wc₁))
    (hA₁ : predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ wa₀ wa₁).card)
    (hA₂ : predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ wb₀ wb₁).card)
    (hA₃ : predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ wc₀ wc₁).card) :
    167772161 ≤
      (alignedSet u₀ u₁ wa₀ wa₁ ∩ alignedSet u₀ u₁ wb₀ wb₁).card := by
  classical
  have hbon := bonferroni_three (alignedSet u₀ u₁ wa₀ wa₁)
    (alignedSet u₀ u₁ wb₀ wb₁) (alignedSet u₀ u₁ wc₀ wc₁)
  have hac' : (alignedSet u₀ u₁ wa₀ wa₁ ∩ alignedSet u₀ u₁ wc₀ wc₁).card ≤ k - 1 :=
    alignedSet_inter_card_lt_k dom u₀ u₁ hwa₀ hwa₁ hwc₀ hwc₁ hac
  have hbc' : (alignedSet u₀ u₁ wb₀ wb₁ ∩ alignedSet u₀ u₁ wc₀ wc₁).card ≤ k - 1 :=
    alignedSet_inter_card_lt_k dom u₀ u₁ hwb₀ hwb₁ hwc₀ hwc₁ hbc
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hk : k = 268435456 := by norm_num [k]
  omega

/-- **The symmetric escape is excluded**: no fully-aligned pairwise-distinct triple
has all three pairwise overlaps EQUAL as sets — it would force
`3(T−1) ≤ N + 2(k−1) = 1610612734 < 1778384895`. -/
theorem symmetric_escape_excluded
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hab : (wa₀, wa₁) ≠ (wb₀, wb₁))
    (hA₁ : predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ wa₀ wa₁).card)
    (hA₂ : predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ wb₀ wb₁).card)
    (hA₃ : predecessorThreshold - 1 ≤ (alignedSet u₀ u₁ wc₀ wc₁).card)
    (h12eq13 : alignedSet u₀ u₁ wa₀ wa₁ ∩ alignedSet u₀ u₁ wb₀ wb₁ =
      alignedSet u₀ u₁ wa₀ wa₁ ∩ alignedSet u₀ u₁ wc₀ wc₁)
    (h12eq23 : alignedSet u₀ u₁ wa₀ wa₁ ∩ alignedSet u₀ u₁ wb₀ wb₁ =
      alignedSet u₀ u₁ wb₀ wb₁ ∩ alignedSet u₀ u₁ wc₀ wc₁) :
    False := by
  classical
  set A₁ := alignedSet u₀ u₁ wa₀ wa₁
  set A₂ := alignedSet u₀ u₁ wb₀ wb₁
  set A₃ := alignedSet u₀ u₁ wc₀ wc₁
  have h12 := Finset.card_union_add_card_inter A₁ A₂
  have h123 := Finset.card_union_add_card_inter (A₁ ∪ A₂) A₃
  have hdist : (A₁ ∪ A₂) ∩ A₃ = (A₁ ∩ A₃) ∪ (A₂ ∩ A₃) :=
    Finset.union_inter_distrib_right ..
  have hself : (A₁ ∩ A₃) ∪ (A₂ ∩ A₃) = A₁ ∩ A₂ := by
    rw [← h12eq13, ← h12eq23, Finset.union_self]
  have hcardeq : ((A₁ ∪ A₂) ∩ A₃).card = (A₁ ∩ A₂).card := by
    rw [hdist, hself]
  have hS : (A₁ ∩ A₂).card ≤ k - 1 :=
    alignedSet_inter_card_lt_k dom u₀ u₁ hwa₀ hwa₁ hwb₀ hwb₁ hab
  have hN' : (A₁ ∪ A₂ ∪ A₃).card ≤ N := by
    have h := Finset.card_le_univ (A₁ ∪ A₂ ∪ A₃)
    simpa [Finset.card_univ, Fintype.card_fin] using h
  have hT := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  have hk : k = 268435456 := by norm_num [k]
  omega

end Triple

/-! ## The named residual and the composition -/

/-- **Named residual (OPEN): the margin form of the dimension deficit.**  Every
pairwise-distinct triple of codeword pencils has some pencil 5-under-aligned.  The
probe pins this at generic rank with forced margin `≈ 5.6·10⁷ ≫ 5`; it is NOT a
tautology — the Bezout escape class (`z₁₂ρ + z₂₃σ = z₁₃τ` with huge split root sets
inside the window `[0, 2^30) ⊂ F_P`) is the exact open content
(realized at toy scale; excluded in its symmetric form by
`symmetric_escape_excluded`; BGK/Paley-type at the prize window). -/
def FullyAlignedTripleFree (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) : Prop :=
  ∀ wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ : Fin N → F,
    wa₀ ∈ predecessorCode dom → wa₁ ∈ predecessorCode dom →
    wb₀ ∈ predecessorCode dom → wb₁ ∈ predecessorCode dom →
    wc₀ ∈ predecessorCode dom → wc₁ ∈ predecessorCode dom →
    (wa₀, wa₁) ≠ (wb₀, wb₁) → (wa₀, wa₁) ≠ (wc₀, wc₁) →
    (wb₀, wb₁) ≠ (wc₀, wc₁) →
    (alignedSet u₀ u₁ wc₀ wc₁).card + 5 ≤ predecessorThreshold ∨
    (alignedSet u₀ u₁ wb₀ wb₁).card + 5 ≤ predecessorThreshold ∨
    (alignedSet u₀ u₁ wa₀ wa₁).card + 5 ≤ predecessorThreshold

section Composition

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- **The composition**: under `FullyAlignedTripleFree`, every bad family covered by
three pairwise-distinct pencils obeys the `StallResidual` budget `#bad ≤ N` — the
margin hypothesis of `stall_budget_of_three_pencil_cover` is discharged by the
residual, whichever pencil carries the margin. -/
theorem stall_budget_of_three_pencil_cover_of_tripleFree
    (hfree : FullyAlignedTripleFree dom u₀ u₁)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hwc₀ : wc₀ ∈ predecessorCode dom) (hwc₁ : wc₁ ∈ predecessorCode dom)
    (hab : (wa₀, wa₁) ≠ (wb₀, wb₁)) (hac : (wa₀, wa₁) ≠ (wc₀, wc₁))
    (hbc : (wb₀, wb₁) ≠ (wc₀, wc₁))
    (hcover : ∀ γ ∈ G, pf γ = wa₀ + γ • wa₁ ∨ pf γ = wb₀ + γ • wb₁ ∨
      pf γ = wc₀ + γ • wc₁) :
    G.card ≤ N := by
  classical
  rcases hfree wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ hwa₀ hwa₁ hwb₀ hwb₁ hwc₀ hwc₁
    hab hac hbc with hc | hb | ha
  · exact stall_budget_of_three_pencil_cover dom u₀ u₁ G Sf pf hdata
      hwa₀ hwa₁ hwb₀ hwb₁ hcover hc
  · refine stall_budget_of_three_pencil_cover dom u₀ u₁ G Sf pf hdata
      hwa₀ hwa₁ hwc₀ hwc₁ (fun γ hγ => ?_) hb
    rcases hcover γ hγ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · refine stall_budget_of_three_pencil_cover dom u₀ u₁ G Sf pf hdata
      hwb₀ hwb₁ hwc₀ hwc₁ (fun γ hγ => ?_) ha
    rcases hcover γ hγ with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end Composition

/-! ## Threshold and squeeze arithmetic (kernel-pinned probe cross-checks) -/

/-- The exact alignment shortfall at which the generic solution dimension turns
positive: `3(T−1−t) − N ≤ 2k − 1` iff `t ≥ 55924054`.  Below it (in particular at
full alignment `t = 0`) the generic dimension is 0 and only Bezout escapes remain. -/
theorem generic_alignment_threshold :
    3 * (predecessorThreshold - 1 - 55924054) - N ≤ 2 * k - 1 ∧
    2 * k - 1 < 3 * (predecessorThreshold - 1 - 55924053) - N := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

/-- The μ_256 coset-escape squeeze (probe section B): order-32 cosets undershoot the
coverage floor (`3·32 = 96 < 167 = 3·141 − 256`), while the floor stays within the
MDS budget (`167 ≤ 3·63`) — the escape window at μ_256 is pinched between the two,
and the order-64 coset polynomial has degree exactly `k` (one too high). -/
theorem mu256_coset_squeeze :
    3 * 32 < 3 * (142 - 1) - 256 ∧ 3 * (142 - 1) - 256 ≤ 3 * 63 ∧ ¬ (64 < 64) := by
  norm_num

/-- Prize-scale forced coincidence ledger: `3(T−1) − N − 2(k−1) = 167772161`, and the
symmetric-escape bound `3(T−1) > N + 2(k−1)` (by margin `167772161`). -/
theorem forced_coincidence_ledger :
    3 * (predecessorThreshold - 1) - N - 2 * (k - 1) = 167772161 ∧
    N + 2 * (k - 1) + 167772161 = 3 * (predecessorThreshold - 1) := by
  constructor <;> norm_num [predecessorThreshold_eq, N, k]

end ArkLib.ProximityGap.Frontier.P1RateQuarterDimensionDeficit

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterDimensionDeficit

#print axioms bonferroni_three
#print axioms fullyAligned_triple_pairwise_overlap_ge
#print axioms symmetric_escape_excluded
#print axioms stall_budget_of_three_pencil_cover_of_tripleFree
#print axioms generic_alignment_threshold
#print axioms mu256_coset_squeeze
#print axioms forced_coincidence_ledger
