/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CodewordHeavyScalar
import ArkLib.Data.CodingTheory.RSWeightEnumerator

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
affine line `{u₀ + γ·u₁}`. The wall now reads "bound the line list sub-trivially"; the list is
at most `q` times the worst per-word list, but it can be far smaller.  For directions far from
the code, the line is a genuinely 1-parameter family whose list size is the natural object of
affine-subspace list decoding (Guruswami–Xing and successors). It is the cleanest positive-side
target the incidence skeleton produces.

## References

* Issue #389; `CodewordHeavyScalar.lean` (`codeword_heavy_scalar_card_le`),
  `LineCorePartition.lean`, `ExplainableCoreExactCount.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 1900

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

open Classical in
/-- Codewords agreeing with a fixed offset word `u₀` on every coordinate of `S`.  This is the
coordinate-fiber object below a zero-agreement stratum: a `t`-stratum is covered by these fibers
over all `t`-subsets of the zero direction. -/
noncomputable def coordinateAgreementFiber
    (dom : Fin n ↪ F) (k : ℕ) (u₀ : Fin n → F) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧ ∀ i ∈ S, c i = u₀ i)

/-- A per-line coordinate-fiber budget: for every `t < a`, every `t`-subset of the zero-direction
coordinates has at most `M t` codewords agreeing with the offset on that subset. -/
def ZeroCoordinateAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (coordinateAgreementFiber dom k u₀ S).card ≤ M t

/-- Uniform coordinate-fiber budget on the large-zero safe branch. -/
def UniformLargeZeroSafeCoordinateAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroCoordinateAgreementFiberBudgeted dom k a u₀ u₁ M

/-- Arithmetic fit for a coordinate-fiber budget.  The `t`-stratum is covered by the
`choose(#zeroSet(u₁), t)` coordinate fibers of size at most `M t`. -/
def ZeroCoordinateAgreementFiberBudgetFits
    (a B : ℕ) (u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∑ t ∈ Finset.range a,
    ((directionZeroSet u₁).card.choose t * M t) *
      ((directionSupportSet u₁).card / (a - t)) ≤ B

/-- Uniform arithmetic fit for coordinate-fiber budgets on large-zero directions. -/
def UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits
    (a B : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ M

open Classical in
/-- An RS coordinate fiber over at least `k` coordinates contains at most one codeword. -/
theorem coordinateAgreementFiber_card_le_one_of_k_le
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (u₀ : Fin n → F)
    {S : Finset (Fin n)} (hS : k ≤ S.card) :
    (coordinateAgreementFiber dom k u₀ S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro c hc c' hc'
  by_contra hne
  rw [coordinateAgreementFiber, Finset.mem_filter] at hc hc'
  have hsub : S ⊆ agreeSet c c' := by
    intro i hi
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hc.2.2 i hi).trans (hc'.2.2 i hi).symm⟩
  have hlarge : k ≤ (agreeSet c c').card :=
    le_trans hS (Finset.card_le_card hsub)
  have hsmall : (agreeSet c c').card ≤ k - 1 :=
    rsCode_pairwise_agreeSet_card_le dom hk hc.2.1 hc'.2.1 hne
  omega

open Classical in
/-- Quantitative MDS bound for a coordinate-agreement fiber.  Prescribing the values on `S`
leaves at most `|F|^(k - #S)` degree-`< k` RS codewords.  For `#S >= k` this recovers the
rigidity endpoint `<= 1`; for smaller `S` it exposes the exact interpolation-scale envelope needed
by the zero-agreement stratum budget. -/
theorem coordinateAgreementFiber_card_le_field_pow_sub_card
    (dom : Fin n ↪ F) (k : ℕ) (u₀ : Fin n → F) (S : Finset (Fin n)) :
    (coordinateAgreementFiber dom k u₀ S).card ≤ Fintype.card F ^ (k - S.card) := by
  classical
  haveI : Fintype (Polynomial.degreeLT F k) :=
    Fintype.ofEquiv (Fin k → F) (Polynomial.degreeLTEquiv F k).symm.toEquiv
  let polyFiber : Finset (Polynomial.degreeLT F k) :=
    (Finset.univ : Finset (Polynomial.degreeLT F k)).filter
      (fun P : Polynomial.degreeLT F k => ∀ i ∈ S, (P : Polynomial F).eval (dom i) = u₀ i)
  have hcover :
      coordinateAgreementFiber dom k u₀ S ⊆
        polyFiber.image (fun P : Polynomial.degreeLT F k =>
          fun i : Fin n => (P : Polynomial F).eval (dom i)) := by
    intro c hc
    rw [coordinateAgreementFiber, Finset.mem_filter] at hc
    rcases hc.2.1 with ⟨P, hPdeg, hc_eq⟩
    let Pdeg : Polynomial.degreeLT F k := ⟨P, Polynomial.mem_degreeLT.mpr hPdeg⟩
    refine Finset.mem_image.mpr ⟨Pdeg, ?_, ?_⟩
    · change Pdeg ∈ (Finset.univ : Finset (Polynomial.degreeLT F k)).filter
        (fun P : Polynomial.degreeLT F k =>
          ∀ i ∈ S, (P : Polynomial F).eval (dom i) = u₀ i)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i hi
      exact (congrFun hc_eq i).symm.trans (hc.2.2 i hi)
    · exact hc_eq.symm
  have hpoly :
      polyFiber.card ≤ Fintype.card F ^ (k - S.card) := by
    by_cases hnonempty : polyFiber.Nonempty
    · rcases hnonempty with ⟨P₀, hP₀⟩
      haveI : Fintype (LinearMap.ker (ArkLib.CS25.evalOnS dom k S)) := Fintype.ofFinite _
      let kerFiber : Finset (Polynomial.degreeLT F k) :=
        (Finset.univ : Finset (Polynomial.degreeLT F k)).filter
          (fun P : Polynomial.degreeLT F k =>
            P ∈ LinearMap.ker (ArkLib.CS25.evalOnS dom k S))
      let shifted : Finset (Polynomial.degreeLT F k) :=
        polyFiber.image (fun P : Polynomial.degreeLT F k => P - P₀)
      have hshift_card : shifted.card = polyFiber.card := by
        change (polyFiber.image (fun P : Polynomial.degreeLT F k => P - P₀)).card =
          polyFiber.card
        exact Finset.card_image_of_injOn
          (fun P hP Q hQ heq => by
            have h := congrArg (fun R : Polynomial.degreeLT F k => R + P₀) heq
            simpa [sub_add_cancel] using h)
      have hshift_subset : shifted ⊆ kerFiber := by
        intro Q hQ
        change Q ∈ polyFiber.image (fun P : Polynomial.degreeLT F k => P - P₀) at hQ
        rw [Finset.mem_image] at hQ
        rcases hQ with ⟨P, hP, rfl⟩
        change P - P₀ ∈ (Finset.univ : Finset (Polynomial.degreeLT F k)).filter
          (fun P : Polynomial.degreeLT F k =>
            P ∈ LinearMap.ker (ArkLib.CS25.evalOnS dom k S))
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [LinearMap.mem_ker]
        ext i
        have hP' := (Finset.mem_filter.mp hP).2 i i.2
        have hP₀' := (Finset.mem_filter.mp hP₀).2 i i.2
        change ((P : Polynomial F) - (P₀ : Polynomial F)).eval (dom (i : Fin n)) = 0
        rw [Polynomial.eval_sub, hP', hP₀', sub_self]
      have hker_card :
          kerFiber.card = Fintype.card F ^ (k - S.card) := by
        have hker_card' :
            kerFiber.card =
              Fintype.card (LinearMap.ker (ArkLib.CS25.evalOnS dom k S)) := by
          change ((Finset.univ : Finset (Polynomial.degreeLT F k)).filter
            (fun P : Polynomial.degreeLT F k =>
              P ∈ LinearMap.ker (ArkLib.CS25.evalOnS dom k S))).card =
              Fintype.card (LinearMap.ker (ArkLib.CS25.evalOnS dom k S))
          rw [← Fintype.card_subtype]
        rw [hker_card', ← Nat.card_eq_fintype_card,
          ArkLib.CS25.natCard_ker_evalOnS_general]
      rw [← hshift_card]
      exact le_trans (Finset.card_le_card hshift_subset) (le_of_eq hker_card)
    · exact le_trans (by simp [Finset.not_nonempty_iff_eq_empty.mp hnonempty]) (Nat.zero_le _)
  exact le_trans (le_trans (Finset.card_le_card hcover) Finset.card_image_le) hpoly

open Classical in
/-- The MDS interpolation envelope supplies a coordinate-fiber budget with
`M t = |F|^(k - t)` on every line. -/
theorem zeroCoordinateAgreementFiberBudgeted_field_pow_sub_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    ZeroCoordinateAgreementFiberBudgeted dom k a u₀ u₁
      (fun t => Fintype.card F ^ (k - t)) := by
  intro t _ht S hS
  have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
  simpa [hScard] using coordinateAgreementFiber_card_le_field_pow_sub_card dom k u₀ S

open Classical in
/-- Uniform large-zero-safe coordinate-fiber budget from the MDS interpolation envelope. -/
theorem uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_field_pow_sub_card
    (dom : Fin n ↪ F) (k a : ℕ) :
    UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a
      (fun t => Fintype.card F ^ (k - t)) := by
  intro u₀ u₁ _hnotEligible _hsafe
  exact zeroCoordinateAgreementFiberBudgeted_field_pow_sub_card dom k a u₀ u₁

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
/-- A `t`-stratum is covered by coordinate-agreement fibers over the `t`-subsets of the
zero-direction coordinates.  The covering map sends a codeword to its exact zero-agreement set. -/
theorem zeroAgreementStratum_subset_coordinateAgreementFiber_biUnion
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t : ℕ) :
    zeroAgreementStratum dom k a u₀ u₁ t ⊆
      ((directionZeroSet u₁).powersetCard t).biUnion
        (fun S => coordinateAgreementFiber dom k u₀ S) := by
  intro c hc
  rw [zeroAgreementStratum, Finset.mem_filter] at hc
  let S : Finset (Fin n) := directionZeroAgreementSet c u₀ u₁
  have hSsub : S ⊆ directionZeroSet u₁ := by
    intro i hi
    change i ∈ directionZeroAgreementSet c u₀ u₁ at hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hi
    exact hi.1
  have hScard : S.card = t := by
    simpa [S] using hc.2
  refine Finset.mem_biUnion.mpr ⟨S, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨hSsub, hScard⟩
  · rw [coordinateAgreementFiber, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    constructor
    · have hcApp := hc.1
      rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
      exact hcApp.2.1
    · intro i hi
      change i ∈ directionZeroAgreementSet c u₀ u₁ at hi
      rw [directionZeroAgreementSet, Finset.mem_filter] at hi
      exact hi.2

open Classical in
/-- Cardinal form of `zeroAgreementStratum_subset_coordinateAgreementFiber_biUnion`. -/
theorem zeroAgreementStratum_card_le_sum_coordinateAgreementFibers
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t : ℕ) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      ≤ ∑ S ∈ (directionZeroSet u₁).powersetCard t,
        (coordinateAgreementFiber dom k u₀ S).card := by
  calc
    (zeroAgreementStratum dom k a u₀ u₁ t).card
        ≤ (((directionZeroSet u₁).powersetCard t).biUnion
            (fun S => coordinateAgreementFiber dom k u₀ S)).card :=
          Finset.card_le_card
            (zeroAgreementStratum_subset_coordinateAgreementFiber_biUnion
              dom k a u₀ u₁ t)
    _ ≤ ∑ S ∈ (directionZeroSet u₁).powersetCard t,
          (coordinateAgreementFiber dom k u₀ S).card :=
        Finset.card_biUnion_le

open Classical in
/-- If every coordinate-agreement fiber over a `t`-subset of the zero direction has size at most
`M`, then the whole `t`-stratum has size at most `choose(#zeroSet(u₁), t) * M`. -/
theorem zeroAgreementStratum_card_le_choose_mul_coordinateAgreementFiberBound
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t M : ℕ)
    (hM : ∀ S ∈ (directionZeroSet u₁).powersetCard t,
      (coordinateAgreementFiber dom k u₀ S).card ≤ M) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      ≤ (directionZeroSet u₁).card.choose t * M := by
  calc
    (zeroAgreementStratum dom k a u₀ u₁ t).card
        ≤ ∑ S ∈ (directionZeroSet u₁).powersetCard t,
          (coordinateAgreementFiber dom k u₀ S).card :=
          zeroAgreementStratum_card_le_sum_coordinateAgreementFibers dom k a u₀ u₁ t
    _ ≤ ∑ _S ∈ (directionZeroSet u₁).powersetCard t, M :=
        Finset.sum_le_sum hM
    _ = ((directionZeroSet u₁).powersetCard t).card * M := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (directionZeroSet u₁).card.choose t * M := by
        rw [Finset.card_powersetCard]

open Classical in
/-- High zero-agreement strata are automatically binomially bounded.  Once `k ≤ t`, each fixed
`t`-subset of zero coordinates determines at most one RS codeword, so the whole exact
zero-agreement stratum has size at most the number of such subsets. -/
theorem zeroAgreementStratum_card_le_choose_of_k_le_t
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) {t : ℕ} (hkt : k ≤ t) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      ≤ (directionZeroSet u₁).card.choose t := by
  calc
    (zeroAgreementStratum dom k a u₀ u₁ t).card
        ≤ (directionZeroSet u₁).card.choose t * 1 :=
          zeroAgreementStratum_card_le_choose_mul_coordinateAgreementFiberBound
            dom k a u₀ u₁ t 1 (by
              intro S hS
              have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
              exact coordinateAgreementFiber_card_le_one_of_k_le dom hk u₀
                (by rw [hScard]; exact hkt))
    _ = (directionZeroSet u₁).card.choose t := by rw [Nat.mul_one]

open Classical in
/-- Coordinate-fiber budgets imply the corresponding zero-agreement stratum-cardinality budgets. -/
theorem zeroAgreementStrataCardBudgeted_of_coordinateAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (M N : ℕ → ℕ)
    (hFiber : ZeroCoordinateAgreementFiberBudgeted dom k a u₀ u₁ M)
    (hN : ∀ t : ℕ, t < a → (directionZeroSet u₁).card.choose t * M t ≤ N t) :
    ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N := by
  intro t ht
  exact le_trans
    (zeroAgreementStratum_card_le_choose_mul_coordinateAgreementFiberBound
      dom k a u₀ u₁ t (M t) (hFiber t ht))
    (hN t ht)

open Classical in
/-- A mixed low/high stratum budget: low strata are supplied directly, while strata with `t ≥ k`
use the singleton coordinate-fiber envelope. -/
theorem zeroAgreementStrataCardBudgeted_of_lowStrata_and_highChoose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (N : ℕ → ℕ)
    (hlow : ∀ t : ℕ, t < a → t < k →
      (zeroAgreementStratum dom k a u₀ u₁ t).card ≤ N t)
    (hhigh : ∀ t : ℕ, t < a → k ≤ t → (directionZeroSet u₁).card.choose t ≤ N t) :
    ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N := by
  intro t ht
  by_cases htk : t < k
  · exact hlow t ht htk
  · exact le_trans
      (zeroAgreementStratum_card_le_choose_of_k_le_t dom hk a u₀ u₁ (Nat.le_of_not_gt htk))
      (hhigh t ht (Nat.le_of_not_gt htk))

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

open Classical in
/-- A coordinate-fiber budget plus its arithmetic fit gives the punctured line budget. -/
theorem puncturedZeroStratifiedLineBudgeted_of_coordinateAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hFiber : ZeroCoordinateAgreementFiberBudgeted dom k a u₀ u₁ M)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ M) :
    PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B := by
  refine puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
    dom k a B u₀ u₁ (fun t => (directionZeroSet u₁).card.choose t * M t)
    hsafe ?_ ?_
  · exact zeroAgreementStrataCardBudgeted_of_coordinateAgreementFiberBudgeted
      dom k a u₀ u₁ M (fun t => (directionZeroSet u₁).card.choose t * M t)
      hFiber (fun _t _ht => le_rfl)
  · simpa [ZeroCoordinateAgreementFiberBudgetFits, ZeroAgreementStrataBudgetFits] using hFits

open Classical in
/-- Uniform coordinate-fiber bounds plus their fit condition discharge the punctured large-zero
safe budget. -/
theorem uniformPuncturedZeroStratifiedLineBudgeted_of_uniformCoordinateAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) (M : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a M)
    (hFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M) :
    UniformPuncturedZeroStratifiedLineBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact puncturedZeroStratifiedLineBudgeted_of_coordinateAgreementFiberBudgeted
    dom k a B u₀ u₁ M hsafe
    (hFiber u₀ u₁ hnotEligible hsafe)
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
/-- If `N` already dominates the automatic binomial ceiling in every high stratum `k ≤ t`, then
any overfull zero-agreement stratum must lie in the low interpolation range `t < k`. -/
theorem exists_low_zeroAgreementStratum_gt_of_exists_stratum_gt_and_high_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (N : ℕ → ℕ)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → (directionZeroSet u₁).card.choose t ≤ N t)
    (hgt : ∃ t : ℕ, t < a ∧ N t < (zeroAgreementStratum dom k a u₀ u₁ t).card) :
    ∃ t : ℕ, t < a ∧ t < k ∧ N t < (zeroAgreementStratum dom k a u₀ u₁ t).card := by
  rcases hgt with ⟨t, ht, hgt⟩
  by_cases hlow : t < k
  · exact ⟨t, ht, hlow, hgt⟩
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hstratum :
        (zeroAgreementStratum dom k a u₀ u₁ t).card ≤ N t :=
      le_trans
        (zeroAgreementStratum_card_le_choose_of_k_le_t dom hk a u₀ u₁ hkt)
        (hHigh t ht hkt)
    exact False.elim ((not_lt_of_ge hstratum) hgt)

open Classical in
/-- Failure form of a single stratum-cardinality budget, with high strata discharged by the
automatic binomial ceiling. -/
theorem not_zeroAgreementStrataCardBudgeted_iff_exists_low_stratum_gt_of_high_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (N : ℕ → ℕ)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → (directionZeroSet u₁).card.choose t ≤ N t) :
    (¬ ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧
        N t < (zeroAgreementStratum dom k a u₀ u₁ t).card := by
  constructor
  · intro hnot
    exact exists_low_zeroAgreementStratum_gt_of_exists_stratum_gt_and_high_choose
      dom hk a u₀ u₁ N hHigh
      ((not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
        dom k a u₀ u₁ N).mp hnot)
  · rintro ⟨t, ht, _hlt, hgt⟩ hbudget
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
/-- Exact failure form for one line's coordinate-fiber budget. -/
theorem not_zeroCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroCoordinateAgreementFiberBudgeted dom k a u₀ u₁ M) ↔
      ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < (coordinateAgreementFiber dom k u₀ S).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht S hS
    exact le_of_not_gt (fun hgt => hnone ⟨t, ht, S, hS, hgt⟩)
  · rintro ⟨t, ht, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget t ht S hS)) hgt

open Classical in
/-- Exact failure form for the uniform large-zero safe coordinate-fiber budget. -/
theorem not_uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a M) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (coordinateAgreementFiber dom k u₀ S).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe t ht S hS)) hgt

omit [Fintype F] in
/-- Exact failure form for one line's coordinate-fiber arithmetic fit. -/
theorem not_zeroCoordinateAgreementFiberBudgetFits_iff_sum_gt
    (a B : ℕ) (u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ M) ↔
      B < ∑ t ∈ Finset.range a,
        ((directionZeroSet u₁).card.choose t * M t) *
          ((directionSupportSet u₁).card / (a - t)) := by
  rw [ZeroCoordinateAgreementFiberBudgetFits]
  exact not_le

omit [Fintype F] in
/-- Exact failure form for the uniform large-zero coordinate-fiber arithmetic fit. -/
theorem not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_iff_exists_sum_gt
    (a B : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M) ↔
      ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        B < ∑ t ∈ Finset.range a,
          ((directionZeroSet u₁).card.choose t * M t) *
            ((directionSupportSet u₁).card / (a - t)) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₁ hnotEligible
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₁, hnotEligible, hgt⟩)
  · rintro ⟨u₁, hnotEligible, hgt⟩ hfits
    exact (not_lt_of_ge (hfits u₁ hnotEligible)) hgt

omit [Fintype F] in
/-- The coordinate-fiber arithmetic fit contains its `t = 0` summand.  This exposes the first
arithmetic obstruction before any higher-stratum information is used. -/
theorem zeroCoordinateAgreementFiberBudgetFits_zeroTerm_le
    (a B : ℕ) (u₁ : Fin n → F) (M : ℕ → ℕ) (ha : 0 < a)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ M) :
    M 0 * ((directionSupportSet u₁).card / a) ≤ B := by
  have hmem : 0 ∈ Finset.range a := Finset.mem_range.mpr ha
  have hterm :
      ((directionZeroSet u₁).card.choose 0 * M 0) *
          ((directionSupportSet u₁).card / (a - 0)) ≤
        ∑ t ∈ Finset.range a,
          ((directionZeroSet u₁).card.choose t * M t) *
            ((directionSupportSet u₁).card / (a - t)) := by
    exact Finset.single_le_sum
      (f := fun t =>
        ((directionZeroSet u₁).card.choose t * M t) *
          ((directionSupportSet u₁).card / (a - t)))
      (fun _ _ => Nat.zero_le _) hmem
  exact le_trans (by simpa using hterm) hFits

/-- For the raw MDS field-power envelope, the `t = 0` term alone forces
`|F|^k * support(u₁)/a ≤ B`. -/
theorem fieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
    (k a B : ℕ) (u₁ : Fin n → F) (ha : 0 < a)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁
      (fun t => Fintype.card F ^ (k - t))) :
    Fintype.card F ^ k * ((directionSupportSet u₁).card / a) ≤ B := by
  simpa using
    (zeroCoordinateAgreementFiberBudgetFits_zeroTerm_le
      (F := F) (n := n) a B u₁ (fun t => Fintype.card F ^ (k - t)) ha hFits)

/-- Uniform version of the field-power zero-term obstruction on large-zero directions. -/
theorem uniformFieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
    (k a B : ℕ) (ha : 0 < a)
    (hFits : UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F ^ (k - t))) :
    ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      Fintype.card F ^ k * ((directionSupportSet u₁).card / a) ≤ B := by
  intro u₁ hnotEligible
  exact fieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
    (F := F) (n := n) k a B u₁ ha (hFits u₁ hnotEligible)

/-- A single large-zero direction whose `t = 0` field-power term exceeds `B` refutes the raw
field-power coordinate-fiber fit. -/
theorem not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_zeroTerm_gt
    (k a B : ℕ) (ha : 0 < a)
    (hgt : ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      B < Fintype.card F ^ k * ((directionSupportSet u₁).card / a)) :
    ¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F ^ (k - t)) := by
  intro hFits
  rcases hgt with ⟨u₁, hnotEligible, hgt⟩
  exact (not_lt_of_ge
    (uniformFieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
      (F := F) (n := n) k a B ha hFits u₁ hnotEligible)) hgt

/-- If the direction support has size at least `a`, the field-power fit already forces the full
`|F|^k` term under budget. -/
theorem fieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_support_ge
    (k a B : ℕ) (u₁ : Fin n → F) (ha : 0 < a)
    (hsupport : a ≤ (directionSupportSet u₁).card)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁
      (fun t => Fintype.card F ^ (k - t))) :
    Fintype.card F ^ k ≤ B := by
  have hzero :=
    fieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
      (F := F) (n := n) k a B u₁ ha hFits
  have hdiv : 1 ≤ (directionSupportSet u₁).card / a :=
    Nat.div_pos hsupport ha
  have hterm : Fintype.card F ^ k
      ≤ Fintype.card F ^ k * ((directionSupportSet u₁).card / a) := by
    exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one hdiv)
  exact le_trans hterm hzero

/-- Uniform field-power fit on a large-zero direction with support at least `a` forces
`|F|^k ≤ B`. -/
theorem uniformFieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_exists_support_ge
    (k a B : ℕ) (ha : 0 < a)
    (hwitness : ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      a ≤ (directionSupportSet u₁).card)
    (hFits : UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F ^ (k - t))) :
    Fintype.card F ^ k ≤ B := by
  rcases hwitness with ⟨u₁, hnotEligible, hsupport⟩
  exact fieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_support_ge
    (F := F) (n := n) k a B u₁ ha hsupport (hFits u₁ hnotEligible)

/-- If `B < |F|^k` and there is a large-zero direction with support at least `a`, the raw
field-power coordinate-fiber arithmetic fit is impossible. -/
theorem not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_support_ge
    (k a B : ℕ) (ha : 0 < a)
    (hB : B < Fintype.card F ^ k)
    (hwitness : ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      a ≤ (directionSupportSet u₁).card) :
    ¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F ^ (k - t)) := by
  intro hFits
  exact (not_lt_of_ge
    (uniformFieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_exists_support_ge
      (F := F) (n := n) k a B ha hwitness hFits)) hB

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
/-- If a proposed coordinate-fiber budget fits arithmetically, any punctured-budget failure must
come from an overfull coordinate-agreement fiber. -/
theorem not_uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_of_not_uniformPunctured
    (dom : Fin n ↪ F) (k a B : ℕ) (M : ℕ → ℕ)
    (hFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M)
    (hnot : ¬ UniformPuncturedZeroStratifiedLineBudgeted dom k a B) :
    ¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a M := by
  intro hFiber
  exact hnot
    (uniformPuncturedZeroStratifiedLineBudgeted_of_uniformCoordinateAgreementFiberBudgeted
      dom k a B M hFiber hFits)

open Classical in
/-- Direct scanner witness: if the coordinate-fiber arithmetic fit is fixed, any failed punctured
budget produces an explicit overfull fiber in the large-zero safe branch. -/
theorem exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformPunctured
    (dom : Fin n ↪ F) (k a B : ℕ) (M : ℕ → ℕ)
    (hFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M)
    (hnot : ¬ UniformPuncturedZeroStratifiedLineBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          M t < (coordinateAgreementFiber dom k u₀ S).card :=
  (not_uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt
    dom k a M).mp
    (not_uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_of_not_uniformPunctured
      dom k a B M hFits hnot)

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
/-- Scanner-facing refinement of the subfield-budget failure trichotomy using a proposed
zero-agreement stratum envelope.  If the large-zero arithmetic fit for `N` is fixed, then the
large-zero residual can only survive by producing an overfull `t`-stratum. -/
theorem exists_eligible_or_unsafe_or_largeZero_stratum_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) (N : ℕ → ℕ)
    (hB : B < Fintype.card F)
    (hStrataFits :
      UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
      (∃ u₀ u₁ : Fin n → F, SupportEligibleLineDirection a u₁ ∧
        B < (lineBadScalars dom k a u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ N t < (zeroAgreementStratum dom k a u₀ u₁ t).card) := by
  rcases (not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe
    dom k a B hB).mp hnot with hEligible | hRest
  · exact Or.inl hEligible
  · rcases hRest with hUnsafe | hLarge
    · exact Or.inr <| Or.inl hUnsafe
    · rcases hLarge with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
      refine Or.inr <| Or.inr ⟨u₀, u₁, hnotEligible, hsafe, ?_⟩
      by_contra hnone
      have hStrata : ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N := by
        intro t ht
        exact le_of_not_gt (fun htgt => hnone ⟨t, ht, htgt⟩)
      have hPunctured : PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B :=
        puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
          dom k a B u₀ u₁ N hsafe hStrata (hStrataFits u₁ hnotEligible)
      exact (not_lt_of_ge
        (lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
          dom k a u₀ u₁ hsafe hPunctured)) hgt

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

/-- Production wrapper using coordinate-agreement fiber budgets for the large-zero safe branch. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiber : UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a M)
    (hFiberFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
    dom k a L B hSupport hFits hZeroSafe
    (uniformPuncturedZeroStratifiedLineBudgeted_of_uniformCoordinateAgreementFiberBudgeted
      dom k a B M hFiber hFiberFits)

/-- Production wrapper using the explicit MDS coordinate-fiber envelope
`M t = |F|^(k - t)`.  The remaining obligation is purely arithmetic: this envelope must fit the
large-zero weighted budget. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_fieldPowCoordinateFibers
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
        (fun t => Fintype.card F ^ (k - t))) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
    dom k a L B (fun t => Fintype.card F ^ (k - t))
    hSupport hFits hZeroSafe
    (uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_field_pow_sub_card dom k a)
    hFiberFits

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
/-- If the support-eligible line-list route, support arithmetic, uniform zero-direction safety, and
large-zero arithmetic stratum fit are all fixed, then any failure of the uniform bad-scalar budget
must exhibit a concrete overfull zero-agreement stratum in the large-zero safe branch. -/
theorem exists_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (N : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hStrataFits :
      UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ N t < (zeroAgreementStratum dom k a u₀ u₁ t).card := by
  by_contra hnone
  have hStrata : UniformLargeZeroSafeZeroAgreementStrataCardBudgeted dom k a N := by
    intro u₀ u₁ hnotEligible hsafe t ht
    exact le_of_not_gt (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_zeroAgreementStrata
      dom k a L B N hSupport hFits hZeroSafe hStrata hStrataFits)

open Classical in
/-- Scanner-facing full failure split for the stratum-envelope production route.  Without assuming
zero-direction safety in advance, a failed uniform bad-scalar budget must expose either a saturating
zero-direction codeword or a concrete overfull zero-agreement stratum in the large-zero safe branch.
-/
theorem unsafe_or_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (N : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hStrataFits :
      UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ N t < (zeroAgreementStratum dom k a u₀ u₁ t).card) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (exists_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B N hSupport hFits hZeroSafe hStrataFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

open Classical in
/-- Scanner-facing full failure split with high zero-agreement strata discharged by their
automatic binomial ceiling.  Once `N` dominates `choose(#zeroSet(u₁), t)` for every high
`k ≤ t < a`, a failed uniform bad-scalar budget must expose either zero-direction saturation or a
large-zero safe **low** stratum `t < k`. -/
theorem unsafe_or_largeZero_safe_low_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (N : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hStrataFits :
      UniformLargeZeroSafeZeroAgreementStrataBudgetFits (F := F) (n := n) a B N)
    (hHigh :
      ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ∀ t : ℕ, t < a → k ≤ t → (directionZeroSet u₁).card.choose t ≤ N t)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧
            N t < (zeroAgreementStratum dom k a u₀ u₁ t).card) := by
  rcases (unsafe_or_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
      dom k a L B N hSupport hFits hStrataFits hnot) with hUnsafe | hStratum
  · exact Or.inl hUnsafe
  · rcases hStratum with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
    exact Or.inr ⟨u₀, u₁, hnotEligible, hsafe,
      exists_low_zeroAgreementStratum_gt_of_exists_stratum_gt_and_high_choose
        dom hk a u₀ u₁ N (hHigh u₁ hnotEligible) hgt⟩

open Classical in
/-- If `M` is at least one in every high range `k ≤ t < a`, then any overfull
coordinate-agreement fiber must lie in the low interpolation range `t < k`. -/
theorem exists_low_coordinateAgreementFiber_gt_of_exists_fiber_gt_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hgt : ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (coordinateAgreementFiber dom k u₀ S).card) :
    ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (coordinateAgreementFiber dom k u₀ S).card := by
  rcases hgt with ⟨t, ht, S, hS, hgt⟩
  by_cases hlow : t < k
  · exact ⟨t, ht, hlow, S, hS, hgt⟩
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hfiber :
        (coordinateAgreementFiber dom k u₀ S).card ≤ 1 :=
      coordinateAgreementFiber_card_le_one_of_k_le dom hk u₀
        (by rw [hScard]; exact hkt)
    have hle : (coordinateAgreementFiber dom k u₀ S).card ≤ M t :=
      le_trans hfiber (hHigh t ht hkt)
    exact False.elim ((not_lt_of_ge hle) hgt)

open Classical in
/-- If the support-eligible line-list route, support arithmetic, zero-direction safety, and
coordinate-fiber arithmetic fit are fixed, then any failed uniform bad-scalar budget must exhibit a
large-zero safe coordinate-agreement fiber whose size exceeds the proposed `M t`. -/
theorem exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          M t < (coordinateAgreementFiber dom k u₀ S).card := by
  by_contra hnone
  have hFiber : UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
      dom k a L B M hSupport hFits hZeroSafe hFiber hFiberFits)

open Classical in
/-- Scanner-facing full failure split for the coordinate-fiber production route.  Without assuming
zero-direction safety in advance, a failed uniform bad-scalar budget must expose either a saturating
zero-direction codeword or an overfull coordinate-agreement fiber in the large-zero safe branch. -/
theorem unsafe_or_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hFiberFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (coordinateAgreementFiber dom k u₀ S).card) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B M hSupport hFits hZeroSafe hFiberFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

open Classical in
/-- With the explicit MDS coordinate-fiber envelope `M t = |F|^(k - t)` and its arithmetic fit,
the only possible failure of the uniform bad-scalar budget is zero-direction saturation. -/
theorem unsafe_of_not_uniformLineBadScalarsBudgeted_with_fieldPowCoordinateFibers
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hFiberFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B
        (fun t => Fintype.card F ^ (k - t)))
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
      a ≤ (directionZeroAgreementSet c u₀ u₁).card := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact False.elim
      (hnot
        (uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_fieldPowCoordinateFibers
          dom k a L B hSupport hFits hZeroSafe hFiberFits))
  · exact (not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
      dom k a).mp hZeroSafe

open Classical in
/-- Scanner-facing full failure split with high coordinate fibers discharged by RS uniqueness.
Once `M t ≥ 1` for every high `k ≤ t < a`, a failed uniform bad-scalar budget must expose either
zero-direction saturation or a large-zero safe **low** coordinate fiber `t < k`. -/
theorem
    unsafe_or_largeZero_safe_low_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hFiberFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (coordinateAgreementFiber dom k u₀ S).card) := by
  rcases (unsafe_or_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
      dom k a L B M hSupport hFits hFiberFits hnot) with hUnsafe | hFiber
  · exact Or.inl hUnsafe
  · rcases hFiber with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
    exact Or.inr ⟨u₀, u₁, hnotEligible, hsafe,
      exists_low_coordinateAgreementFiber_gt_of_exists_fiber_gt_and_high_one
        dom hk a u₀ u₁ M hHigh hgt⟩

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
#print axioms coordinateAgreementFiber
#print axioms ZeroCoordinateAgreementFiberBudgeted
#print axioms UniformLargeZeroSafeCoordinateAgreementFiberBudgeted
#print axioms ZeroCoordinateAgreementFiberBudgetFits
#print axioms UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits
#print axioms coordinateAgreementFiber_card_le_one_of_k_le
#print axioms coordinateAgreementFiber_card_le_field_pow_sub_card
#print axioms zeroCoordinateAgreementFiberBudgeted_field_pow_sub_card
#print axioms uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_field_pow_sub_card
#print axioms puncturedZeroStratifiedLineWeight
#print axioms PuncturedZeroStratifiedLineBudgeted
#print axioms UniformPuncturedZeroStratifiedLineBudgeted
#print axioms ZeroAgreementStrataCardBudgeted
#print axioms ZeroAgreementStrataBudgetFits
#print axioms UniformLargeZeroSafeZeroAgreementStrataCardBudgeted
#print axioms UniformLargeZeroSafeZeroAgreementStrataBudgetFits
#print axioms lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
#print axioms puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
#print axioms zeroAgreementStratum_subset_coordinateAgreementFiber_biUnion
#print axioms zeroAgreementStratum_card_le_sum_coordinateAgreementFibers
#print axioms zeroAgreementStratum_card_le_choose_mul_coordinateAgreementFiberBound
#print axioms zeroAgreementStratum_card_le_choose_of_k_le_t
#print axioms zeroAgreementStrataCardBudgeted_of_coordinateAgreementFiberBudgeted
#print axioms zeroAgreementStrataCardBudgeted_of_lowStrata_and_highChoose
#print axioms puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
#print axioms puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
#print axioms puncturedZeroStratifiedLineBudgeted_of_coordinateAgreementFiberBudgeted
#print axioms
  uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
#print axioms
  uniformPuncturedZeroStratifiedLineBudgeted_of_uniformCoordinateAgreementFiberBudgeted
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
#print axioms exists_low_zeroAgreementStratum_gt_of_exists_stratum_gt_and_high_choose
#print axioms not_zeroAgreementStrataCardBudgeted_iff_exists_low_stratum_gt_of_high_choose
#print axioms not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
#print axioms not_zeroAgreementStrataBudgetFits_iff_sum_gt
#print axioms not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
#print axioms not_zeroCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt
#print axioms
  not_uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt
#print axioms not_zeroCoordinateAgreementFiberBudgetFits_iff_sum_gt
#print axioms
  not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_iff_exists_sum_gt
#print axioms zeroCoordinateAgreementFiberBudgetFits_zeroTerm_le
#print axioms fieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
#print axioms uniformFieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
#print axioms
  not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_zeroTerm_gt
#print axioms fieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_support_ge
#print axioms uniformFieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_exists_support_ge
#print axioms
  not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_support_ge
#print axioms
  not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
#print axioms
  not_uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_of_not_uniformPunctured
#print axioms exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformPunctured
#print axioms not_uniformLineBadScalarsBudgeted_iff_eligible_or_unsafe_or_largeZero_safe
#print axioms exists_eligible_or_unsafe_or_largeZero_stratum_of_not_uniformLineBadScalarsBudgeted
#print axioms supportAdjustedLineBadScalarsBudgeted_of_uniformSupportLineListBudgeted
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_fieldPowCoordinateFibers
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_zeroAgreementStrata
#print axioms exists_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms unsafe_or_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_low_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms exists_low_coordinateAgreementFiber_gt_of_exists_fiber_gt_and_high_one
#print axioms exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms unsafe_of_not_uniformLineBadScalarsBudgeted_with_fieldPowCoordinateFibers
#print axioms
  unsafe_or_largeZero_safe_low_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms not_uniformSupportLineListBudgeted_iff_exists_eligible_lineAppearing_gt
#print axioms not_supportAdjustedLineBadScalarsBudgeted_iff_exists_eligible_lineBadScalars_gt
#print axioms not_uniformSupportLineListBudgeted_of_exists_eligible_lineBadScalars_gt
#print axioms not_lineListBudgeted_of_lineBadScalars_card_gt
#print axioms lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt
#print axioms not_lineListBudgeted_of_lineBadScalars_card_gt_support_div_sub_zero
#print axioms lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt_support_div_sub_zero

end ProximityGap.Ownership
