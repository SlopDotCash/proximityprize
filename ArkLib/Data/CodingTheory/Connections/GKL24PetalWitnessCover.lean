/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment

/-!
# GKL24 petal-witness-cover false surface + reduction (issue #67)

Historical atomic max-domain surface `GKL24MaxDomainWitnessCoverFalseAsStated` plus the proven
reduction to the in-tree petal-disjointness cover. The original residual form was intentionally
retired from the strict census after the #363 audit found isolated-bad-scalar stacks where the
per-carrier maximal-domain clause is unsatisfiable.

The useful live content of this file is the conditional reduction: if a future theorem supplies
this stronger certificate under repaired side conditions, it still tightens the ABF26 T5.1
first-moment residual to the atomic GKL24 maximal-agree-domain count.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap
namespace Issue67Scratch

open NNReal Code Finset

section
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## 0. Proved helper: strict extension from a strict size inequality.

The in-tree petal-nonemptiness lemma `linePetal_nonempty_of_ssubset_lineAgreeSet` wants
`D ⊂ lineAgreeSet …`. We reduce the strict-subset obligation to `D ⊆ line` ∧ `|D| < |line|`,
which is the natural quantitative form (for the decoded codeword, `|line| ≥ (1-δ)·n`, so this is
`|D| < (1-δ)·n`). Pure Finset fact. -/
theorem strict_of_subset_of_card_lt
    {D E : Finset ι} (hsub : D ⊆ E) (hlt : D.card < E.card) : D ⊂ E := by
  have hne : D ≠ E := fun h => by rw [h] at hlt; exact (lt_irrefl _ hlt)
  -- `⊂` is the strict order `<` on `Finset`; `⊆` is `≤` (`Finset.le_iff_subset`).
  exact lt_of_le_of_ne (Finset.le_iff_subset.mpr hsub) hne

/-- Specialization to a line-agreement set. -/
theorem lineAgreeSet_strict_of_card_lt
    {D : Finset ι} {u₀ u₁ w : ι → F} {γ : F}
    (hsub : D ⊆ lineAgreeSet u₀ u₁ w γ)
    (hlt : D.card < (lineAgreeSet u₀ u₁ w γ).card) :
    D ⊂ lineAgreeSet u₀ u₁ w γ :=
  strict_of_subset_of_card_lt hsub hlt

/-! ## 1. The false-as-stated atomic maximal-domain witness-cover surface.

Per stack: a close-codeword carrier `T u` covering the bad scalars, and for every `w ∈ T u`, the
GKL24 maximal-domain data for `Γ_w := mcaBadWitness w`: a max domain `D`, per-γ codeword `wOf`,
inclusions, strict expansions, and the pairwise large-intersection bound (the genuine GKL24
Lemma 1 content). All fields are `Prop`; this is the retired over-strong surface. The radius `p`
is `ℝ≥0`
(matching `maxCorrAgreeDomain` and the in-tree `linePetal_pairwise_disjoint_of_maxCorrAgreeDomain`
intersection bound), with the petal-counting consumer using `(p:ℝ)`. -/
def GKL24MaxDomainWitnessCoverFalseAsStated
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (B_T : ℝ) (p : ℝ≥0) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
      mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
        T.biUnion (fun w =>
          mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
      (T.card : ℝ) ≤ B_T ∧
      ∀ w ∈ T,
        ∃ D : Finset ι, ∃ wOf : F → ι → F,
          maxCorrAgreeDomain MC p (u 0) (u 1) D ∧
          ((1 - (p : ℝ)) * (Fintype.card ι : ℝ) ≤ (D.card : ℝ)) ∧
          (∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
            wOf γ ∈ (MC : Set (ι → F))) ∧
          (∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
            D ⊂ lineAgreeSet (u 0) (u 1) (wOf γ) γ) ∧
          (∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
            ∀ γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w, γ ≠ γ' →
              ((1 - p) * Fintype.card ι : ℝ≥0) ≤
                (((lineAgreeSet (u 0) (u 1) (wOf γ) γ ∩
                    lineAgreeSet (u 0) (u 1) (wOf γ') γ').card : ℕ) : ℝ≥0))

/-! ## 2. PROOF: the atomic false surface ⇒ the in-tree petal witness-cover hypothesis.

We derive the disjoint petals from the certificate via the in-tree
`linePetal_pairwise_disjoint_of_maxCorrAgreeDomain` (per-γ `wOf` form), plus petal nonemptiness
and subset-of-complement. The petal function we exhibit is `petal γ := linePetal D (wOf γ) γ`. -/
theorem gkl24PetalWitnessCoverHypothesis_of_maxDomainWitnessCover
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T : ℝ} {p : ℝ≥0}
    (hres : GKL24MaxDomainWitnessCoverFalseAsStated MC δ B_T p) :
    GKL24PetalWitnessCoverHypothesis MC δ B_T (p : ℝ) := by
  classical
  intro u
  obtain ⟨T, hTsub, hcover, hcard, hTcert⟩ := hres u
  refine ⟨T, hTsub, hcover, hcard, ?_⟩
  intro w hw
  obtain ⟨D, wOf, hDmax, hDlarge, hwMem, hDstrict, hIlarge⟩ := hTcert w hw
  refine ⟨D, fun γ => linePetal D (u 0) (u 1) (wOf γ) γ, hDlarge, ?_, ?_, ?_⟩
  · -- pairwise disjointness via the in-tree per-γ maximal-domain disjointness lemma.
    exact linePetal_pairwise_disjoint_of_maxCorrAgreeDomain
      MC p D (u 0) (u 1) wOf
      (mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w)
      hDmax
      (fun γ hγ => (hDstrict γ hγ).1)
      (fun γ hγ γ' hγ' hne => hIlarge γ hγ γ' hγ' hne)
      hwMem
  · -- nonemptiness from strict expansion.
    intro γ hγ
    exact Nat.succ_le_iff.mpr
      (Finset.card_pos.mpr (linePetal_nonempty_of_ssubset_lineAgreeSet (hDstrict γ hγ)))
  · -- petal ⊆ univ \ D.
    intro γ _hγ
    exact linePetal_subset_compl D (u 0) (u 1) (wOf γ) γ

/-! ## 3. Front doors: atomic false surface ⇒ sharp T5.1 first-moment `b = p·n`.

Composing §2 with the proven in-tree consumers gives the `B_T · (p·n)` count and `ε_mca` bound.
With `B_T := L²`, `p := δ_list` this is exactly the `L²·δ_list·n` first-moment summand of ABF26
T5.1; adding `GCXK25SecondMoment.card_lt_one_div_of_second_moment_rs` (`1/η`) closes the RHS. -/

/-- **Sharp per-stack first-moment count from the atomic maximal-domain surface.** -/
theorem mcaBad_card_le_t51_firstMoment_of_maxDomainWitnessCover
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T : ℝ} {p : ℝ≥0}
    (hres : GKL24MaxDomainWitnessCoverFalseAsStated MC δ B_T p)
    (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤
      B_T * ((p : ℝ) * (Fintype.card ι : ℝ)) :=
  mcaBad_card_le_of_gkl24_petal_witnessCover_hypothesis MC δ (p.coe_nonneg)
    (gkl24PetalWitnessCoverHypothesis_of_maxDomainWitnessCover MC δ hres) u

/-- **Sharp `ε_mca` first-moment bound from the atomic maximal-domain surface.** -/
theorem epsMCA_le_ofReal_t51_firstMoment_of_maxDomainWitnessCover
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T : ℝ} {p : ℝ≥0}
    (hres : GKL24MaxDomainWitnessCoverFalseAsStated MC δ B_T p) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal ((B_T * ((p : ℝ) * (Fintype.card ι : ℝ))) / Fintype.card F) :=
  epsMCA_le_ofReal_of_gkl24_petal_witnessCover_hypothesis MC δ (p.coe_nonneg)
    (gkl24PetalWitnessCoverHypothesis_of_maxDomainWitnessCover MC δ hres)

/-! ## 4. Regression sanity: the in-tree relaxed carrier plumbing is still reachable.

We re-derive that the trivially-relaxed setting is consistent: a single-codeword carrier still
satisfies the COVER and MEMBERSHIP halves of the atomic surface (the certificate fields are the
genuine GKL24 content and are NOT claimed here). This documents that the only new obligation over
the in-tree state is the maximal-domain certificate, not the carrier plumbing. -/
theorem maxDomainWitnessCover_carrier_cover_inTree
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u : WordStack F (Fin 2) ι) :
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
      mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
        T.biUnion (fun w =>
          mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) := by
  classical
  let T : Finset (ι → F) := Finset.univ.filter (fun w : ι → F => w ∈ (MC : Set (ι → F)))
  refine ⟨T, ?_, ?_⟩
  · intro w hw
    simpa [T] using hw
  · refine mcaBad_subset_biUnion_mcaBadWitness (MC : Set (ι → F)) δ (u 0) (u 1) T ?_
    intro w hw
    simpa [T, hw]

end

end Issue67Scratch
end ProximityGap
