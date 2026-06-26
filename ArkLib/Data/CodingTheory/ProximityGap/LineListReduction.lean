/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CodewordHeavyScalar

/-!
# The line-list reduction: bad scalars ≤ (affine-line list size) · ⌊n/a⌋

Issue #389, the positive direction. The bipartite incidence skeleton
(`CodewordHeavyScalar.lean`: each codeword feeds `≤ ⌊n/a⌋` scalars; `LineCorePartition.lean`:
each core belongs to one scalar) yields a clean **reduction of the per-scalar MCA count to a
single line list size**:

> **`badScalar_card_le_lineList_mul`** — with `a = k+m+1` and nonvanishing direction `u₁`,
> the scalars `γ` for which some codeword agrees with `w_γ = u₀ + γ·u₁` on `≥ a` points
> number at most `Λ · ⌊n/a⌋`, where `Λ` is the **affine-line list size** — the number of
> codewords that come within agreement `a` of *some* word on the line.

This is structurally better than the per-word list-decoding the supply naively asks for: it
replaces the worst-case-over-`q`-words list size with **one** list — the codewords near the whole
affine line `{u₀ + γ·u₁}`. The wall now reads "bound the line list sub-trivially"; that list is at
most `q` times the worst per-word list, but it can be far smaller.  For `u₁ = xᵏ` far from the
code, the line is a genuinely 1-parameter family whose list size is the natural object of
affine-subspace list decoding (Guruswami–Xing and successors). It is the cleanest positive-side
target the incidence skeleton produces.

## References

* Issue #389; `CodewordHeavyScalar.lean` (`codeword_heavy_scalar_card_le`),
  `LineCorePartition.lean`, `ExplainableCoreExactCount.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The scalars whose line word `u₀ + γ • u₁` is agreed with by some codeword on at least
`a` coordinates.  This is the line-list bad-scalar set used by
`badScalar_card_le_lineList_mul`. -/
noncomputable def lineBadScalars (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    Finset F :=
  (Finset.univ : Finset F).filter
    (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- The codewords that appear somewhere along the affine line `u₀ + γ • u₁` with agreement
at least `a`.  Bounding this finite set is the line-list-size input left after the per-codeword
heavy-scalar bound. -/
noncomputable def lineAppearingCodewords (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    Finset (Fin n → F) :=
  (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

/-- A budgeted line list: at most `L` codewords appear with agreement `a` somewhere on the line. -/
def LineListBudgeted (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (L : ℕ) : Prop :=
  (lineAppearingCodewords dom k a u₀ u₁).card ≤ L

/-- A line is safe from zero-direction saturation when no codeword already agrees with the offset
on `a` zero-direction coordinates.  Without this condition, the bad-scalar set can be the entire
field independently of the moving support. -/
def ZeroDirectionSafeLine (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : Prop :=
  ∀ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) →
    (directionZeroAgreementSet c u₀ u₁).card < a

/-- Uniform zero-direction safety over all affine lines.  This is a necessary side condition for
any production bad-scalar budget below the full field size. -/
def UniformZeroDirectionSafe (dom : Fin n ↪ F) (k a : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ZeroDirectionSafeLine dom k a u₀ u₁

/-- A uniform bad-scalar budget over every affine line in the named-set model. -/
def UniformLineBadScalarsBudgeted (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, (lineBadScalars dom k a u₀ u₁).card ≤ B

/-- A line direction is eligible for the support-aware line-list bound when its zero-coordinate set
is smaller than the agreement threshold.  If the zero set already has size at least `a`, then a
single fixed agreement on those coordinates can make every scalar look heavy and the fiber argument
has no useful denominator. -/
def SupportEligibleLineDirection (a : ℕ) (u₁ : Fin n → F) : Prop :=
  (directionZeroSet u₁).card < a

/-- A uniform support-aware line-list budget: every affine line whose direction has fewer than `a`
zero coordinates has at most `L` appearing codewords.  This is the family-level production
obligation left after the per-codeword ratio-census argument. -/
def UniformSupportLineListBudgeted (dom : Fin n ↪ F) (k a L : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, SupportEligibleLineDirection a u₁ →
    LineListBudgeted dom k a u₀ u₁ L

/-- The family-level bad-scalar budget obtained from a support-aware line-list bound.  The budget is
adjusted direction-by-direction by the moving support size and the zero-coordinate loss. -/
def SupportAdjustedLineBadScalarsBudgeted (dom : Fin n ↪ F) (k a L : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, (hz : SupportEligibleLineDirection a u₁) →
    (lineBadScalars dom k a u₀ u₁).card
      ≤ L * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card))

/-- The support-adjusted line-list budget fits inside a uniform target `B` on every eligible
direction.  This is the arithmetic side condition needed to turn the direction-dependent bound into
a production budget. -/
def SupportAdjustedBudgetFits (a L B : ℕ) : Prop :=
  ∀ u₁ : Fin n → F, SupportEligibleLineDirection a u₁ →
    L * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card)) ≤ B

/-- The residual large-zero safe branch: directions whose zero set already has size at least `a`
but which do not saturate by a codeword-zero-agreement witness.  The support-fiber denominator no
longer helps here, so this branch must be handled by a separate theorem. -/
def LargeZeroSafeLineBadScalarsBudgeted (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      (lineBadScalars dom k a u₀ u₁).card ≤ B

open Classical in
/-- Appearing codewords with exactly `t` zero-direction agreements with the offset. -/
noncomputable def zeroAgreementStratum
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (t : ℕ) :
    Finset (Fin n → F) :=
  (lineAppearingCodewords dom k a u₀ u₁).filter
    (fun c => (directionZeroAgreementSet c u₀ u₁).card = t)

open Classical in
/-- The punctured zero-stratified weight of a line: sum over appearing codewords of the moving
support budget with denominator corrected by that codeword's zero-direction agreement count.  This
is meaningful in the large-zero branch because zero-direction safety gives
`#zeroAgreement(c,u₀,u₁) < a` for every appearing codeword. -/
noncomputable def puncturedZeroStratifiedLineWeight
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : ℕ :=
  ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
    (directionSupportSet u₁).card / (a - (directionZeroAgreementSet c u₀ u₁).card)

/-- A single line has punctured zero-stratified budget `B` when the punctured weight is at most
`B`.  This is the proposed replacement for a naive line-list bound in the large-zero safe branch. -/
def PuncturedZeroStratifiedLineBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (B : ℕ) : Prop :=
  puncturedZeroStratifiedLineWeight dom k a u₀ u₁ ≤ B

/-- Uniform punctured zero-stratified budget on the large-zero safe branch. -/
def UniformPuncturedZeroStratifiedLineBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B

/-- A per-line cardinality budget for every zero-agreement stratum.  The function `N` is the
candidate upper bound for the number of appearing codewords with exactly `t` zero-direction
agreements. -/
def ZeroAgreementStrataCardBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (N : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → (zeroAgreementStratum dom k a u₀ u₁ t).card ≤ N t

/-- Arithmetic fit condition for a proposed zero-agreement stratum cardinality budget. -/
def ZeroAgreementStrataBudgetFits (a B : ℕ) (u₁ : Fin n → F) (N : ℕ → ℕ) : Prop :=
  ∑ t ∈ Finset.range a,
    N t * ((directionSupportSet u₁).card / (a - t)) ≤ B

/-- Uniform stratum-cardinality budget on the large-zero safe branch. -/
def UniformLargeZeroSafeZeroAgreementStrataCardBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (N : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N

/-- Uniform arithmetic fit for a zero-agreement stratum budget on large-zero directions. -/
def UniformLargeZeroSafeZeroAgreementStrataBudgetFits
    (a B : ℕ) (N : ℕ → ℕ) : Prop :=
  ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroAgreementStrataBudgetFits (F := F) (n := n) a B u₁ N

open Classical in
/-- **The line-list reduction.** With nonvanishing direction `u₁`, the scalars whose line
word `w_γ` is agreed with by some codeword on `≥ a` points are covered by the appearing
codewords, each contributing `≤ ⌊n/a⌋` of them: `#badScalars ≤ Λ · ⌊n/a⌋`. -/
theorem badScalar_card_le_lineList_mul (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) :
    ((Finset.univ : Finset F).filter
        (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
            ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card
        * (n / a) := by
  classical
  set badΓ : Finset F := (Finset.univ : Finset F).filter
    (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) with hbadΓ
  set appC : Finset (Fin n → F) := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) with happC
  -- bad scalars are covered by the per-codeword heavy-scalar sets of appearing codewords
  have hcover : badΓ ⊆ appC.biUnion (fun c =>
      (Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)) := by
    intro γ hγ
    obtain ⟨-, c, hc, hca⟩ := Finset.mem_filter.mp hγ
    refine Finset.mem_biUnion.mpr ⟨c, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, γ, hca⟩
  calc badΓ.card
      ≤ (appC.biUnion (fun c => (Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ c ∈ appC, ((Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ appC, (n / a) :=
        Finset.sum_le_sum fun c _ => codeword_heavy_scalar_card_le a ha c u₀ u₁ hu₁
    _ = appC.card * (n / a) := by rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- Named-set form of `badScalar_card_le_lineList_mul`. -/
theorem lineBadScalars_card_le_lineAppearingCodewords_card_mul
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card * (n / a) := by
  simpa [lineBadScalars, lineAppearingCodewords]
    using badScalar_card_le_lineList_mul dom k a ha u₀ u₁ hu₁

open Classical in
/-- Support-aware line-list reduction.  If the zero set of `u₁` has size `z < a`, then each
appearing codeword contributes at most `support(u₁)/(a-z)` heavy scalars, so the line's bad
scalars are bounded by the line-list size times that corrected per-codeword budget. -/
theorem lineBadScalars_card_le_lineAppearingCodewords_card_mul_support_div_sub_zero
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (hz : (directionZeroSet u₁).card < a) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card *
        ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card)) := by
  classical
  set badΓ : Finset F := lineBadScalars dom k a u₀ u₁ with hbadΓ
  set appC : Finset (Fin n → F) := lineAppearingCodewords dom k a u₀ u₁ with happC
  have hcover : badΓ ⊆ appC.biUnion (fun c =>
      (Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)) := by
    intro γ hγ
    rw [hbadΓ, lineBadScalars] at hγ
    obtain ⟨-, c, hc, hca⟩ := Finset.mem_filter.mp hγ
    refine Finset.mem_biUnion.mpr ⟨c, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩⟩
    rw [happC, lineAppearingCodewords]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, γ, hca⟩
  calc badΓ.card
      ≤ (appC.biUnion (fun c => (Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ c ∈ appC, ((Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ appC,
          ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card)) :=
        Finset.sum_le_sum fun c _ =>
          codeword_heavy_scalar_card_le_support_div_sub_zero a c u₀ u₁ hz
    _ = appC.card * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card)) := by
        rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- Budgeted line-list consumer: if the line has at most `L` appearing codewords, then its
bad-scalar set is bounded by `L * ⌊n/a⌋`.  This isolates the remaining positive-side obligation
as a line-list-size theorem. -/
theorem lineBadScalars_card_le_of_lineListBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) {L : ℕ}
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (lineBadScalars dom k a u₀ u₁).card ≤ L * (n / a) := by
  exact le_trans
    (lineBadScalars_card_le_lineAppearingCodewords_card_mul dom k a ha u₀ u₁ hu₁)
    (Nat.mul_le_mul_right (n / a) hL)

open Classical in
/-- Support-aware budgeted line-list consumer.  This removes the artificial nowhere-zero direction
condition from the positive line-list route; only the zero set size must be below the agreement
threshold. -/
theorem lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (hz : (directionZeroSet u₁).card < a) {L : ℕ}
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ L * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card)) := by
  exact le_trans
    (lineBadScalars_card_le_lineAppearingCodewords_card_mul_support_div_sub_zero
      dom k a u₀ u₁ hz)
    (Nat.mul_le_mul_right
      ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card)) hL)

open Classical in
/-- Punctured zero-stratified line reduction.  For a zero-safe line, the bad scalars are bounded
by the sum over appearing codewords of the corrected moving-support budget using the denominator
`a - #zeroAgreement(c,u₀,u₁)`.  Unlike the support-eligible theorem, this still works when the
full zero set of `u₁` has size at least `a`. -/
theorem lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ := by
  classical
  set badΓ : Finset F := lineBadScalars dom k a u₀ u₁ with hbadΓ
  set appC : Finset (Fin n → F) := lineAppearingCodewords dom k a u₀ u₁ with happC
  have hcover : badΓ ⊆ appC.biUnion (fun c =>
      (Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)) := by
    intro γ hγ
    rw [hbadΓ, lineBadScalars] at hγ
    obtain ⟨-, c, hc, hca⟩ := Finset.mem_filter.mp hγ
    refine Finset.mem_biUnion.mpr ⟨c, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩⟩
    rw [happC, lineAppearingCodewords]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, γ, hca⟩
  calc badΓ.card
      ≤ (appC.biUnion (fun c => (Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ c ∈ appC, ((Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ c ∈ appC,
          (directionSupportSet u₁).card /
            (a - (directionZeroAgreementSet c u₀ u₁).card) := by
        refine Finset.sum_le_sum ?_
        intro c hcApp
        have hcLine : c ∈ lineAppearingCodewords dom k a u₀ u₁ := by
          simpa [happC] using hcApp
        have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
          have hcFilter :
              c ∈ (Finset.univ : Finset (Fin n → F)).filter
                (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
                  ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) := by
            simpa [lineAppearingCodewords] using hcLine
          exact (Finset.mem_filter.mp hcFilter).2.1
        exact codeword_heavy_scalar_card_le_support_div_sub_zeroAgreement
          a c u₀ u₁ (hsafe c hcCode)
    _ = puncturedZeroStratifiedLineWeight dom k a u₀ u₁ := by
        rw [puncturedZeroStratifiedLineWeight, happC]

open Classical in
/-- Exact `t`-stratum form of the punctured line weight.  Under zero-direction safety, every
appearing codeword has zero-agreement count `t < a`, so the codeword-weighted definition regroups
over the finite strata `0 ≤ t < a`. -/
theorem puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    puncturedZeroStratifiedLineWeight dom k a u₀ u₁
      = ∑ t ∈ Finset.range a,
        (zeroAgreementStratum dom k a u₀ u₁ t).card *
          ((directionSupportSet u₁).card / (a - t)) := by
  classical
  set appC : Finset (Fin n → F) := lineAppearingCodewords dom k a u₀ u₁ with happC
  have hmaps :
      ∀ c ∈ appC, (directionZeroAgreementSet c u₀ u₁).card ∈ Finset.range a := by
    intro c hcApp
    have hcLine : c ∈ lineAppearingCodewords dom k a u₀ u₁ := by
      simpa [happC] using hcApp
    have hcFilter :
        c ∈ (Finset.univ : Finset (Fin n → F)).filter
          (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
            ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) := by
      simpa [lineAppearingCodewords] using hcLine
    exact Finset.mem_range.mpr (hsafe c (Finset.mem_filter.mp hcFilter).2.1)
  rw [puncturedZeroStratifiedLineWeight, ← happC]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun c => (directionSupportSet u₁).card /
      (a - (directionZeroAgreementSet c u₀ u₁).card))]
  refine Finset.sum_congr rfl fun t _ht => ?_
  rw [zeroAgreementStratum, ← happC]
  calc
    ∑ c ∈ appC.filter (fun c => (directionZeroAgreementSet c u₀ u₁).card = t),
        ((directionSupportSet u₁).card /
          (a - (directionZeroAgreementSet c u₀ u₁).card))
      = ∑ _c ∈ appC.filter (fun c => (directionZeroAgreementSet c u₀ u₁).card = t),
          ((directionSupportSet u₁).card / (a - t)) := by
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [(Finset.mem_filter.mp hc).2]
    _ = (appC.filter (fun c => (directionZeroAgreementSet c u₀ u₁).card = t)).card *
        ((directionSupportSet u₁).card / (a - t)) := by
          rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- A stratum-cardinality budget bounds the punctured line weight by the corresponding weighted
budget sum. -/
theorem puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (N : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hStrata : ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N) :
    puncturedZeroStratifiedLineWeight dom k a u₀ u₁
      ≤ ∑ t ∈ Finset.range a,
        N t * ((directionSupportSet u₁).card / (a - t)) := by
  rw [puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata dom k a u₀ u₁ hsafe]
  exact Finset.sum_le_sum fun t ht =>
    Nat.mul_le_mul_right
      ((directionSupportSet u₁).card / (a - t))
      (hStrata t (Finset.mem_range.mp ht))

/-- A stratum-cardinality budget plus the arithmetic fit condition gives the punctured line
budget. -/
theorem puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ)
    (u₀ u₁ : Fin n → F) (N : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hStrata : ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N)
    (hFits : ZeroAgreementStrataBudgetFits (F := F) (n := n) a B u₁ N) :
    PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B :=
  le_trans
    (puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
      dom k a u₀ u₁ N hsafe hStrata)
    hFits

/-- Uniform stratum-cardinality bounds plus their fit condition discharge the punctured
large-zero safe budget. -/
theorem uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) (N : ℕ → ℕ)
    (hStrata : UniformLargeZeroSafeZeroAgreementStrataCardBudgeted dom k a N)
    (hFits :
      UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N) :
    UniformPuncturedZeroStratifiedLineBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
    dom k a B u₀ u₁ N hsafe
    (hStrata u₀ u₁ hnotEligible hsafe)
    (hFits u₁ hnotEligible)

/-- Consumer form of the punctured zero-stratified line reduction. -/
theorem lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) {B : ℕ}
    (hB : PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  le_trans
    (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight dom k a u₀ u₁ hsafe)
    hB

/-- A uniform punctured zero-stratified budget discharges the large-zero safe residual. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hPunctured : UniformPuncturedZeroStratifiedLineBudgeted dom k a B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
    dom k a u₀ u₁ hsafe (hPunctured u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Zero-direction saturation: if a codeword already agrees with the offset on at least `a`
zero-direction coordinates, then every scalar is bad for the line. -/
theorem lineBadScalars_eq_univ_of_codeword_directionZeroAgreement_ge
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) {c : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hzero : a ≤ (directionZeroAgreementSet c u₀ u₁).card) :
    lineBadScalars dom k a u₀ u₁ = Finset.univ := by
  ext γ
  constructor
  · intro _; exact Finset.mem_univ γ
  · intro _
    rw [lineBadScalars, Finset.mem_filter]
    exact ⟨Finset.mem_univ γ, c, hc,
      le_trans hzero (directionZeroAgreementSet_card_le_agreeSet_line c u₀ u₁ γ)⟩

open Classical in
/-- Cardinal form of zero-direction saturation for a line. -/
theorem lineBadScalars_card_eq_field_card_of_codeword_directionZeroAgreement_ge
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) {c : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hzero : a ≤ (directionZeroAgreementSet c u₀ u₁).card) :
    (lineBadScalars dom k a u₀ u₁).card = Fintype.card F := by
  rw [lineBadScalars_eq_univ_of_codeword_directionZeroAgreement_ge
    dom k a u₀ u₁ hc hzero, Finset.card_univ]

open Classical in
/-- Any nontrivial upper bound on the line's bad scalars rules out codewords that already meet the
threshold on the zero-direction coordinates. -/
theorem directionZeroAgreement_lt_of_lineBadScalars_card_lt_field_card
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F)
    (hsmall : (lineBadScalars dom k a u₀ u₁).card < Fintype.card F) :
    ∀ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) →
      (directionZeroAgreementSet c u₀ u₁).card < a := by
  intro c hc
  by_contra hnot
  have hzero : a ≤ (directionZeroAgreementSet c u₀ u₁).card := Nat.le_of_not_gt hnot
  have hcard := lineBadScalars_card_eq_field_card_of_codeword_directionZeroAgreement_ge
    dom k a u₀ u₁ hc hzero
  rw [hcard] at hsmall
  exact (Nat.lt_irrefl (Fintype.card F)) hsmall

omit [Fintype F] in
/-- Failure of zero-direction safety is exactly a codeword that already reaches the agreement
threshold on the zero-direction coordinates. -/
theorem not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (¬ ZeroDirectionSafeLine dom k a u₀ u₁) ↔
      ∃ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro c hc
    by_contra hlt
    exact hnone ⟨c, hc, Nat.le_of_not_gt hlt⟩
  · rintro ⟨c, hc, hge⟩ hsafe
    exact (not_lt_of_ge hge) (hsafe c hc)

open Classical in
/-- A zero-direction safety failure saturates the whole scalar field. -/
theorem lineBadScalars_eq_univ_of_not_zeroDirectionSafeLine
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hunsafe : ¬ ZeroDirectionSafeLine dom k a u₀ u₁) :
    lineBadScalars dom k a u₀ u₁ = Finset.univ := by
  rcases (not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
    dom k a u₀ u₁).mp hunsafe with ⟨c, hc, hzero⟩
  exact lineBadScalars_eq_univ_of_codeword_directionZeroAgreement_ge
    dom k a u₀ u₁ hc hzero

open Classical in
/-- Cardinal form: an unsafe zero-direction line has field-size bad-scalar count. -/
theorem lineBadScalars_card_eq_field_card_of_not_zeroDirectionSafeLine
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hunsafe : ¬ ZeroDirectionSafeLine dom k a u₀ u₁) :
    (lineBadScalars dom k a u₀ u₁).card = Fintype.card F := by
  rw [lineBadScalars_eq_univ_of_not_zeroDirectionSafeLine dom k a u₀ u₁ hunsafe,
    Finset.card_univ]

open Classical in
/-- Any subfield-size bad-scalar bound for one line forces zero-direction safety on that line. -/
theorem zeroDirectionSafeLine_of_lineBadScalars_budget_lt_field
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {B : ℕ}
    (hbudget : (lineBadScalars dom k a u₀ u₁).card ≤ B)
    (hB : B < Fintype.card F) :
    ZeroDirectionSafeLine dom k a u₀ u₁ :=
  directionZeroAgreement_lt_of_lineBadScalars_card_lt_field_card
    dom k a u₀ u₁ (lt_of_le_of_lt hbudget hB)

open Classical in
/-- A uniform bad-scalar budget below field size forces zero-direction safety for every line. -/
theorem uniformZeroDirectionSafe_of_uniformLineBadScalarsBudgeted_lt_field
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hbudget : UniformLineBadScalarsBudgeted dom k a B)
    (hB : B < Fintype.card F) :
    UniformZeroDirectionSafe dom k a := by
  intro u₀ u₁
  exact zeroDirectionSafeLine_of_lineBadScalars_budget_lt_field
    dom k a u₀ u₁ (hbudget u₀ u₁) hB

omit [Fintype F] in
/-- Exact family failure form for zero-direction safety. -/
theorem not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
    (dom : Fin n ↪ F) (k a : ℕ) :
    (¬ UniformZeroDirectionSafe dom k a) ↔
      ∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ c hc
    by_contra hlt
    exact hnone ⟨u₀, u₁, c, hc, Nat.le_of_not_gt hlt⟩
  · rintro ⟨u₀, u₁, c, hc, hge⟩ hsafe
    exact (not_lt_of_ge hge) (hsafe u₀ u₁ c hc)

open Classical in
/-- If zero-direction safety fails anywhere, no uniform bad-scalar budget below field size can
hold. -/
theorem not_uniformLineBadScalarsBudgeted_of_not_uniformZeroDirectionSafe_lt_field
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hB : B < Fintype.card F)
    (hunsafe : ¬ UniformZeroDirectionSafe dom k a) :
    ¬ UniformLineBadScalarsBudgeted dom k a B := by
  intro hbudget
  exact hunsafe
    (uniformZeroDirectionSafe_of_uniformLineBadScalarsBudgeted_lt_field
      dom k a B hbudget hB)

open Classical in
/-- Exact failure form for a uniform bad-scalar budget in the named-set model. -/
theorem not_uniformLineBadScalarsBudgeted_iff_exists_lineBadScalars_gt
    (dom : Fin n ↪ F) (k a B : ℕ) :
    (¬ UniformLineBadScalarsBudgeted dom k a B) ↔
      ∃ u₀ u₁ : Fin n → F, B < (lineBadScalars dom k a u₀ u₁).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁
    exact le_of_not_gt (fun hgt => hnone ⟨u₀, u₁, hgt⟩)
  · rintro ⟨u₀, u₁, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁)) hgt

open Classical in
/-- Exact failure form for the large-zero safe residual. -/
theorem not_largeZeroSafeLineBadScalarsBudgeted_iff_exists_largeZero_safe_lineBadScalars_gt
    (dom : Fin n ↪ F) (k a B : ℕ) :
    (¬ LargeZeroSafeLineBadScalarsBudgeted dom k a B) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          B < (lineBadScalars dom k a u₀ u₁).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩ hlarge
    exact (not_lt_of_ge (hlarge u₀ u₁ hnotEligible hsafe)) hgt

open Classical in
/-- Exact failure form for a single punctured zero-stratified line budget. -/
theorem not_puncturedZeroStratifiedLineBudgeted_iff_weight_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (B : ℕ) :
    (¬ PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B) ↔
      B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁ := by
  rw [PuncturedZeroStratifiedLineBudgeted]
  exact not_le

open Classical in
/-- Exact failure form for the uniform punctured zero-stratified budget. -/
theorem not_uniformPuncturedZeroStratifiedLineBudgeted_iff_exists_largeZero_safe_weight_gt
    (dom : Fin n ↪ F) (k a B : ℕ) :
    (¬ UniformPuncturedZeroStratifiedLineBudgeted dom k a B) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁ := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe)) hgt

open Classical in
/-- Any over-budget large-zero safe line also overbudgets the punctured zero-stratified weight. -/
theorem puncturedZeroStratifiedLineWeight_gt_of_lineBadScalars_card_gt
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hgt : B < (lineBadScalars dom k a u₀ u₁).card) :
    B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁ :=
  lt_of_lt_of_le hgt
    (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight dom k a u₀ u₁ hsafe)

open Classical in
/-- If the large-zero safe residual fails, then the stronger punctured zero-stratified budget fails
with an explicit weighted-cost witness. -/
theorem not_uniformPuncturedZeroStratifiedLineBudgeted_of_not_largeZeroSafeLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hnot : ¬ LargeZeroSafeLineBadScalarsBudgeted dom k a B) :
    ¬ UniformPuncturedZeroStratifiedLineBudgeted dom k a B := by
  rcases (not_largeZeroSafeLineBadScalarsBudgeted_iff_exists_largeZero_safe_lineBadScalars_gt
    dom k a B).mp hnot with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
  exact
    (not_uniformPuncturedZeroStratifiedLineBudgeted_iff_exists_largeZero_safe_weight_gt
      dom k a B).mpr
      ⟨u₀, u₁, hnotEligible, hsafe,
        puncturedZeroStratifiedLineWeight_gt_of_lineBadScalars_card_gt
          dom k a B u₀ u₁ hsafe hgt⟩

open Classical in
/-- Exact failure form for one line's zero-agreement stratum cardinality budget. -/
theorem not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (N : ℕ → ℕ) :
    (¬ ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N) ↔
      ∃ t : ℕ, t < a ∧ N t < (zeroAgreementStratum dom k a u₀ u₁ t).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht
    exact le_of_not_gt
      (fun hgt => hnone ⟨t, ht, hgt⟩)
  · rintro ⟨t, ht, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget t ht)) hgt

open Classical in
/-- Exact failure form for the uniform large-zero safe stratum-cardinality budget. -/
theorem not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
    (dom : Fin n ↪ F) (k a : ℕ) (N : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeZeroAgreementStrataCardBudgeted dom k a N) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ N t < (zeroAgreementStratum dom k a u₀ u₁ t).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe t ht
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe t ht)) hgt

omit [Fintype F] in
/-- Exact failure form for one line's arithmetic stratum-budget fit. -/
theorem not_zeroAgreementStrataBudgetFits_iff_sum_gt
    (a B : ℕ) (u₁ : Fin n → F) (N : ℕ → ℕ) :
    (¬ ZeroAgreementStrataBudgetFits (F := F) (n := n) a B u₁ N) ↔
      B < ∑ t ∈ Finset.range a,
        N t * ((directionSupportSet u₁).card / (a - t)) := by
  rw [ZeroAgreementStrataBudgetFits]
  exact not_le

omit [Fintype F] in
/-- Exact failure form for the uniform large-zero arithmetic stratum-budget fit. -/
theorem not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
    (a B : ℕ) (N : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N) ↔
      ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        B < ∑ t ∈ Finset.range a,
          N t * ((directionSupportSet u₁).card / (a - t)) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₁ hnotEligible
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₁, hnotEligible, hgt⟩)
  · rintro ⟨u₁, hnotEligible, hgt⟩ hfits
    exact (not_lt_of_ge (hfits u₁ hnotEligible)) hgt

open Classical in
/-- If a proposed stratum budget fits arithmetically, any punctured-budget failure must come from
an overfull zero-agreement stratum. -/
theorem not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
    (dom : Fin n ↪ F) (k a B : ℕ) (N : ℕ → ℕ)
    (hFits :
      UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N)
    (hnot : ¬ UniformPuncturedZeroStratifiedLineBudgeted dom k a B) :
    ¬ UniformLargeZeroSafeZeroAgreementStrataCardBudgeted dom k a N := by
  intro hStrata
  exact hnot
    (uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
      dom k a B N hStrata hFits)

open Classical in
/-- Exact subfield-budget failure trichotomy for the line-list route.  If the target budget is
below field size, then a uniform bad-scalar budget fails for exactly one of three scanner-visible
reasons: an eligible direction is over budget; a zero-direction saturation witness exists; or the
large-zero safe residual is over budget. -/
theorem not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hB : B < Fintype.card F) :
    (¬ UniformLineBadScalarsBudgeted dom k a B) ↔
      (∃ u₀ u₁ : Fin n → F, SupportEligibleLineDirection a u₁ ∧
        B < (lineBadScalars dom k a u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          B < (lineBadScalars dom k a u₀ u₁).card) := by
  constructor
  · intro hnot
    rcases (not_uniformLineBadScalarsBudgeted_iff_exists_lineBadScalars_gt
      dom k a B).mp hnot with ⟨u₀, u₁, hgt⟩
    by_cases heligible : SupportEligibleLineDirection a u₁
    · exact Or.inl ⟨u₀, u₁, heligible, hgt⟩
    · by_cases hsafe : ZeroDirectionSafeLine dom k a u₀ u₁
      · exact Or.inr <| Or.inr ⟨u₀, u₁, heligible, hsafe, hgt⟩
      · exact Or.inr <| Or.inl ⟨u₀, u₁, hsafe⟩
  · rintro (hEligible | hRest)
    · rcases hEligible with ⟨u₀, u₁, _heligible, hgt⟩
      exact (not_uniformLineBadScalarsBudgeted_iff_exists_lineBadScalars_gt
        dom k a B).mpr ⟨u₀, u₁, hgt⟩
    · rcases hRest with hUnsafe | hLarge
      · rcases hUnsafe with ⟨u₀, u₁, hunsafe⟩
        have hcard :
            (lineBadScalars dom k a u₀ u₁).card = Fintype.card F :=
          lineBadScalars_card_eq_field_card_of_not_zeroDirectionSafeLine
            dom k a u₀ u₁ hunsafe
        exact (not_uniformLineBadScalarsBudgeted_iff_exists_lineBadScalars_gt
          dom k a B).mpr ⟨u₀, u₁, by simpa [hcard] using hB⟩
      · rcases hLarge with ⟨u₀, u₁, _hnotEligible, _hsafe, hgt⟩
        exact (not_uniformLineBadScalarsBudgeted_iff_exists_lineBadScalars_gt
          dom k a B).mpr ⟨u₀, u₁, hgt⟩

open Classical in
/-- Uniform support-aware line-list control gives the corresponding support-adjusted bad-scalar
budget for every eligible affine-line direction. -/
theorem supportAdjustedLineBadScalarsBudgeted_of_uniformSupportLineListBudgeted
    (dom : Fin n ↪ F) (k a L : ℕ)
    (hL : UniformSupportLineListBudgeted dom k a L) :
    SupportAdjustedLineBadScalarsBudgeted dom k a L := by
  intro u₀ u₁ hz
  exact lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
    dom k a u₀ u₁ hz (hL u₀ u₁ hz)

open Classical in
/-- The complete support/large-zero decomposition for the named-set line-list model.  A uniform
bad-scalar budget follows from: a uniform line-list budget on support-eligible directions; an
arithmetic check that the support-adjusted bound fits under `B`; zero-direction safety; and a
separate bound for the large-zero safe residual. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLarge : LargeZeroSafeLineBadScalarsBudgeted dom k a B) :
    UniformLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁
  by_cases heligible : SupportEligibleLineDirection a u₁
  · exact le_trans
      ((supportAdjustedLineBadScalarsBudgeted_of_uniformSupportLineListBudgeted
        dom k a L hSupport) u₀ u₁ heligible)
      (hFits u₁ heligible)
  · exact hLarge u₀ u₁ heligible (hZeroSafe u₀ u₁)

/-- Production wrapper using the new punctured zero-stratified theorem for the large-zero safe
branch. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hPunctured : UniformPuncturedZeroStratifiedLineBudgeted dom k a B) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
      dom k a B hPunctured)

/-- Production wrapper using explicit zero-agreement stratum cardinality budgets for the
large-zero safe branch. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_zeroAgreementStrata
    (dom : Fin n ↪ F) (k a L B : ℕ) (N : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hStrata : UniformLargeZeroSafeZeroAgreementStrataCardBudgeted dom k a N)
    (hStrataFits :
      UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
    dom k a L B hSupport hFits hZeroSafe
    (uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
      dom k a B N hStrata hStrataFits)

open Classical in
/-- Exact failure form for the uniform support-aware line-list budget: it fails precisely when some
eligible affine line has more than `L` appearing codewords. -/
theorem not_uniformSupportLineListBudgeted_iff_exists_eligible_lineAppearing_gt
    (dom : Fin n ↪ F) (k a L : ℕ) :
    (¬ UniformSupportLineListBudgeted dom k a L) ↔
      ∃ u₀ u₁ : Fin n → F, SupportEligibleLineDirection a u₁ ∧
        L < (lineAppearingCodewords dom k a u₀ u₁).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hz
    unfold LineListBudgeted
    by_contra hle
    exact hnone ⟨u₀, u₁, hz, Nat.lt_of_not_ge hle⟩
  · rintro ⟨u₀, u₁, hz, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hz)) hgt

open Classical in
/-- Exact failure form for the support-adjusted bad-scalar family budget: it fails precisely when
some eligible affine line has too many bad scalars for its adjusted support budget. -/
theorem not_supportAdjustedLineBadScalarsBudgeted_iff_exists_eligible_lineBadScalars_gt
    (dom : Fin n ↪ F) (k a L : ℕ) :
    (¬ SupportAdjustedLineBadScalarsBudgeted dom k a L) ↔
      ∃ u₀ u₁ : Fin n → F, SupportEligibleLineDirection a u₁ ∧
        L * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card))
          < (lineBadScalars dom k a u₀ u₁).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hz
    by_contra hle
    exact hnone ⟨u₀, u₁, hz, Nat.lt_of_not_ge hle⟩
  · rintro ⟨u₀, u₁, hz, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hz)) hgt

open Classical in
/-- A support-adjusted bad-scalar counterexample refutes the uniform line-list budget.  This is the
family-level version of the per-line contrapositive. -/
theorem not_uniformSupportLineListBudgeted_of_exists_eligible_lineBadScalars_gt
    (dom : Fin n ↪ F) (k a L : ℕ)
    (hgt :
      ∃ u₀ u₁ : Fin n → F, SupportEligibleLineDirection a u₁ ∧
        L * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card))
          < (lineBadScalars dom k a u₀ u₁).card) :
    ¬ UniformSupportLineListBudgeted dom k a L := by
  intro hL
  exact
    ((not_supportAdjustedLineBadScalarsBudgeted_iff_exists_eligible_lineBadScalars_gt
        dom k a L).mpr hgt)
      (supportAdjustedLineBadScalarsBudgeted_of_uniformSupportLineListBudgeted dom k a L hL)

open Classical in
/-- Support-aware contrapositive: an over-budget bad-scalar count refutes the proposed line-list
budget even when the direction has zeros, provided the zero set is smaller than the threshold. -/
theorem not_lineListBudgeted_of_lineBadScalars_card_gt_support_div_sub_zero
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (hz : (directionZeroSet u₁).card < a) {L : ℕ}
    (hgt :
      L * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card))
        < (lineBadScalars dom k a u₀ u₁).card) :
    ¬ LineListBudgeted dom k a u₀ u₁ L := by
  intro hL
  exact (not_lt_of_ge
    (lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
      dom k a u₀ u₁ hz hL)) hgt

open Classical in
/-- Numeric witness form of the support-aware contrapositive. -/
theorem lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt_support_div_sub_zero
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (hz : (directionZeroSet u₁).card < a) {L : ℕ}
    (hgt :
      L * ((directionSupportSet u₁).card / (a - (directionZeroSet u₁).card))
        < (lineBadScalars dom k a u₀ u₁).card) :
    L < (lineAppearingCodewords dom k a u₀ u₁).card := by
  exact lt_of_not_ge
    (not_lineListBudgeted_of_lineBadScalars_card_gt_support_div_sub_zero
      dom k a u₀ u₁ hz hgt)

open Classical in
/-- Scanner-facing contrapositive: if a line has more bad scalars than `L * ⌊n/a⌋`, then the
line-list budget `L` is false.  The per-codeword ratio-census layer cannot be blamed; the
obstruction is an oversized appearing-codeword list. -/
theorem not_lineListBudgeted_of_lineBadScalars_card_gt
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) {L : ℕ}
    (hgt : L * (n / a) < (lineBadScalars dom k a u₀ u₁).card) :
    ¬ LineListBudgeted dom k a u₀ u₁ L := by
  intro hL
  exact (not_lt_of_ge
    (lineBadScalars_card_le_of_lineListBudgeted dom k a ha u₀ u₁ hu₁ hL)) hgt

open Classical in
/-- Equivalent numeric witness form of the previous theorem: an over-budget bad-scalar count
forces the appearing-codeword list itself to have more than `L` members. -/
theorem lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) {L : ℕ}
    (hgt : L * (n / a) < (lineBadScalars dom k a u₀ u₁).card) :
    L < (lineAppearingCodewords dom k a u₀ u₁).card := by
  exact lt_of_not_ge
    (not_lineListBudgeted_of_lineBadScalars_card_gt dom k a ha u₀ u₁ hu₁ hgt)

/-! ## Source audit -/

#print axioms badScalar_card_le_lineList_mul
#print axioms lineBadScalars_card_le_lineAppearingCodewords_card_mul
#print axioms lineBadScalars_card_le_lineAppearingCodewords_card_mul_support_div_sub_zero
#print axioms lineBadScalars_card_le_of_lineListBudgeted
#print axioms lineBadScalars_card_le_of_lineListBudgeted_support_div_sub_zero
#print axioms zeroAgreementStratum
#print axioms puncturedZeroStratifiedLineWeight
#print axioms PuncturedZeroStratifiedLineBudgeted
#print axioms UniformPuncturedZeroStratifiedLineBudgeted
#print axioms ZeroAgreementStrataCardBudgeted
#print axioms ZeroAgreementStrataBudgetFits
#print axioms UniformLargeZeroSafeZeroAgreementStrataCardBudgeted
#print axioms UniformLargeZeroSafeZeroAgreementStrataBudgetFits
#print axioms lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
#print axioms puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
#print axioms puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
#print axioms puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
#print axioms
  uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
#print axioms lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
#print axioms lineBadScalars_eq_univ_of_codeword_directionZeroAgreement_ge
#print axioms lineBadScalars_card_eq_field_card_of_codeword_directionZeroAgreement_ge
#print axioms directionZeroAgreement_lt_of_lineBadScalars_card_lt_field_card
#print axioms not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
#print axioms lineBadScalars_eq_univ_of_not_zeroDirectionSafeLine
#print axioms lineBadScalars_card_eq_field_card_of_not_zeroDirectionSafeLine
#print axioms zeroDirectionSafeLine_of_lineBadScalars_budget_lt_field
#print axioms uniformZeroDirectionSafe_of_uniformLineBadScalarsBudgeted_lt_field
#print axioms not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
#print axioms not_uniformLineBadScalarsBudgeted_of_not_uniformZeroDirectionSafe_lt_field
#print axioms not_uniformLineBadScalarsBudgeted_iff_exists_lineBadScalars_gt
#print axioms not_largeZeroSafeLineBadScalarsBudgeted_iff_exists_largeZero_safe_lineBadScalars_gt
#print axioms not_puncturedZeroStratifiedLineBudgeted_iff_weight_gt
#print axioms not_uniformPuncturedZeroStratifiedLineBudgeted_iff_exists_largeZero_safe_weight_gt
#print axioms puncturedZeroStratifiedLineWeight_gt_of_lineBadScalars_card_gt
#print axioms
  not_uniformPuncturedZeroStratifiedLineBudgeted_of_not_largeZeroSafeLineBadScalarsBudgeted
#print axioms not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
#print axioms not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
#print axioms not_zeroAgreementStrataBudgetFits_iff_sum_gt
#print axioms
  not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
#print axioms
  not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
#print axioms not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe
#print axioms supportAdjustedLineBadScalarsBudgeted_of_uniformSupportLineListBudgeted
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_zeroAgreementStrata
#print axioms not_uniformSupportLineListBudgeted_iff_exists_eligible_lineAppearing_gt
#print axioms not_supportAdjustedLineBadScalarsBudgeted_iff_exists_eligible_lineBadScalars_gt
#print axioms not_uniformSupportLineListBudgeted_of_exists_eligible_lineBadScalars_gt
#print axioms not_lineListBudgeted_of_lineBadScalars_card_gt
#print axioms lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt
#print axioms not_lineListBudgeted_of_lineBadScalars_card_gt_support_div_sub_zero
#print axioms lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt_support_div_sub_zero

end ProximityGap.Ownership
