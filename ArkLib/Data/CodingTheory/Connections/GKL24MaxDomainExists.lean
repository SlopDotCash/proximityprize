/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment
import ArkLib.Data.CodingTheory.Connections.GCXK25SecondMoment

set_option autoImplicit false

/-!
# Existence of the maximal correlated-agreement domain (GKL24 building block)

The GKL24 first-moment argument (`GKL24MaxCorrWitnessCoverHypothesis`) requires, per codeword, a
*maximal* correlated-agreement domain `D` (`maxCorrAgreeDomain`).  This file proves the underlying
existence fact: whenever *some* correlated-agreement domain exists, a maximal one exists — a finite
poset has a maximal element.  This is the first verified component of the GKL24
maximal-correlated-agreement-domain residual; the remaining geometric properties (strict containment
in the bad line-agreement sets, the `(1−p)·n` pairwise intersection) are the genuine GKL24
Lemma 1 / Cor 1 content.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Maximal correlated-agreement domain exists (when any domain does).**  If some `D₀` is a
correlated-agreement domain, then a *maximal* one exists.  Proof: the correlated-agreement domains
form a nonempty finite family of `Finset ι`s; a maximal-cardinality member is maximal under
inclusion (any larger domain containing it has equal cardinality, hence equals it). -/
theorem exists_maxCorrAgreeDomain_of_nonempty
    (MC : Submodule F (ι → F)) (p : ℝ≥0) (u₀ u₁ : ι → F)
    (h : ∃ D₀ : Finset ι, corrAgreeDomain MC p u₀ u₁ D₀) :
    ∃ D : Finset ι, maxCorrAgreeDomain MC p u₀ u₁ D := by
  classical
  obtain ⟨D₀, hD₀⟩ := h
  set 𝒮 : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powerset.filter (fun D => corrAgreeDomain MC p u₀ u₁ D) with h𝒮
  have hD₀mem : D₀ ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hD₀⟩
  obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image 𝒮 Finset.card ⟨D₀, hD₀mem⟩
  refine ⟨D, (Finset.mem_filter.mp hDmem).2, ?_⟩
  intro E hDE hE
  have hEmem : E ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hE⟩
  exact (Finset.eq_of_subset_of_card_le hDE (hDmax E hEmem)).ge

/-- **Pairwise intersection of two line-agreement sets (distinct combiners).**  For `γ ≠ γ'`, the
coordinates where `w` agrees with both `u₀ + γ·u₁` and `u₀ + γ'·u₁` are exactly those where `u₁`
vanishes and `w = u₀`: on the overlap, `(γ − γ')·u₁ᵢ = 0` forces `u₁ᵢ = 0`, hence `wᵢ = u₀ᵢ`.  This
is the structural core of the GKL24 residual's `(1−p)·n` pairwise-intersection requirement — once a
maximal domain `D ⊆ lineAgreeSet γ` is in hand, `D` lands inside this common set, so `(1−p)·n ≤ |D|`
transfers to the intersection. -/
theorem lineAgreeSet_inter_eq (u₀ u₁ w : ι → F) {γ γ' : F} (hγ : γ ≠ γ') :
    lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ'
      = Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) := by
  ext i
  simp only [Finset.mem_inter, mem_lineAgreeSet_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    have heq : γ • u₁ i = γ' • u₁ i :=
      add_left_cancel (a := u₀ i) (by rw [← h1, ← h2])
    have hu1 : u₁ i = 0 := by
      by_contra hne
      rw [smul_eq_mul, smul_eq_mul] at heq
      exact hγ (mul_right_cancel₀ hne heq)
    exact ⟨hu1, by rw [h1, hu1, smul_zero, add_zero]⟩
  · rintro ⟨hu1, hw⟩
    refine ⟨?_, ?_⟩ <;> rw [hw, hu1, smul_zero, add_zero]

/-- **Reduction of the residual's pairwise-intersection bound to domain containment.**  If `D` is a
correlated-agreement domain (so `(1−p)·n ≤ |D|`) contained in both `lineAgreeSet γ` and
`lineAgreeSet γ'`, then `(1−p)·n ≤ |lineAgreeSet γ ∩ lineAgreeSet γ'|`.  Combined with
`exists_maxCorrAgreeDomain_of_nonempty`, this discharges the `(1−p)·n` pairwise-intersection clause
of `GKL24MaxCorrWitnessCoverHypothesis` from the single remaining GKL24 kernel property: that the
maximal domain is contained in each bad witness's line-agreement set (`D ⊆ lineAgreeSet γ`). -/
theorem corrAgreeDomain_subset_inter_card
    {MC : Submodule F (ι → F)} {p : ℝ≥0} {u₀ u₁ w : ι → F} {γ γ' : F} {D : Finset ι}
    (hD : corrAgreeDomain MC p u₀ u₁ D)
    (hγ : D ⊆ lineAgreeSet u₀ u₁ w γ) (hγ' : D ⊆ lineAgreeSet u₀ u₁ w γ') :
    ((1 - p) * Fintype.card ι : ℝ≥0)
      ≤ ((lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ').card : ℝ≥0) :=
  le_trans hD.1 (by exact_mod_cast Finset.card_le_card (Finset.subset_inter hγ hγ'))

/-- **Line-agreement petals are pairwise disjoint above a domain absorbing their intersection.**
If `D` contains `lineAgreeSet γ ∩ lineAgreeSet γ'`, the petals `lineAgreeSet γ \ D` and
`lineAgreeSet γ' \ D` are disjoint: their overlap lies in the intersection, which `D` removes.
This is the GKL24 / GCXK25 sunflower-petal disjointness step. -/
theorem linePetal_disjoint_of_inter_subset (D : Finset ι) (u₀ u₁ w : ι → F) {γ γ' : F}
    (h : lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ' ⊆ D) :
    Disjoint (linePetal D u₀ u₁ w γ) (linePetal D u₀ u₁ w γ') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [linePetal, Finset.mem_sdiff] at hi
  rw [linePetal, Finset.mem_sdiff] at hi'
  exact hi.2 (h (Finset.mem_inter.mpr ⟨hi.1, hi'.1⟩))

/-- **Sunflower petals for distinct bad combiners are disjoint above a domain containing the common
zero-agreement set.**  Specialising `linePetal_disjoint_of_inter_subset` via `lineAgreeSet_inter_eq`:
for `γ ≠ γ'`, if `D ⊇ {i : u₁ᵢ = 0 ∧ wᵢ = u₀ᵢ}` then the two petals are disjoint.  Together with
`corrAgreeDomain_subset_inter_card` and `exists_maxCorrAgreeDomain_of_nonempty`, this assembles the
sunflower structure of the GKL24 residual around a maximal domain. -/
theorem linePetal_disjoint_of_common_subset (D : Finset ι) (u₀ u₁ w : ι → F) {γ γ' : F}
    (hγ : γ ≠ γ')
    (h : Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) ⊆ D) :
    Disjoint (linePetal D u₀ u₁ w γ) (linePetal D u₀ u₁ w γ') :=
  linePetal_disjoint_of_inter_subset D u₀ u₁ w (by rw [lineAgreeSet_inter_eq u₀ u₁ w hγ]; exact h)

/-- **Petal-counting: pairwise-disjoint large petals bound the number of combiners.**  If the petals
`P γ` (`γ ∈ B`) are pairwise disjoint, each contained in `U`, and each of size `≥ L`, then
`|B|·L ≤ |U|`.  Proof: the disjoint petals tile a subset of `U`, so `∑|P γ| = |⋃ P γ| ≤ |U|`, while
`∑|P γ| ≥ |B|·L`.  This is the cardinality consumer for the GKL24 sunflower step. -/
theorem card_mul_le_of_disjoint_petals {B : Finset F} {P : F → Finset ι} {U : Finset ι} {L : ℕ}
    (hdisj : ∀ γ ∈ B, ∀ γ' ∈ B, γ ≠ γ' → Disjoint (P γ) (P γ'))
    (hsub : ∀ γ ∈ B, P γ ⊆ U) (hL : ∀ γ ∈ B, L ≤ (P γ).card) :
    B.card * L ≤ U.card :=
  calc B.card * L = ∑ _γ ∈ B, L := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ γ ∈ B, (P γ).card := Finset.sum_le_sum hL
    _ = (B.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ U.card := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

/-- **Petal lower bound under domain containment.**  When the maximal domain `D` is contained in a
bad witness's line-agreement set, the petal `lineAgreeSet γ \ D` has size `≥ |lineAgreeSet γ| − |D|`,
hence `≥ (large agreement) − |D|`.  Combined with `card_mul_le_of_disjoint_petals` and the petal
disjointness, this delivers the GKL24 first-moment count `|B| · (agreement − |D|) ≤ n − |D|`. -/
theorem card_linePetal_ge (D : Finset ι) (u₀ u₁ w : ι → F) (γ : F) :
    (lineAgreeSet u₀ u₁ w γ).card - D.card ≤ (linePetal D u₀ u₁ w γ).card := by
  rw [linePetal]
  have h := Finset.card_sdiff_add_card_inter (lineAgreeSet u₀ u₁ w γ) D
  have hi : (lineAgreeSet u₀ u₁ w γ ∩ D).card ≤ D.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- **GKL24 first-moment count (sunflower assembly).**  Let `D` absorb the common zero-agreement set
`{i : u₁ᵢ = 0 ∧ wᵢ = u₀ᵢ}`, and let every combiner `γ ∈ B` have line-agreement of size `≥ A`.  Then
`|B| · (A − |D|) ≤ n − |D|`.  This assembles the whole sunflower argument — petal disjointness
(`linePetal_disjoint_of_common_subset`), the petal lower bound (`card_linePetal_ge`), and the
counting consumer (`card_mul_le_of_disjoint_petals`) — into the GKL24 first-moment bound on the
number of bad combiners.  Instantiated with `A = (1−δ)·n` (the bad-witness agreement) this is GKL24's
`|Bad¹|`-style count; the sole remaining input is that `D` absorbs the common set. -/
theorem badCombiner_count {D : Finset ι} {u₀ u₁ w : ι → F} {B : Finset F} {A : ℕ}
    (hcommon : Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) ⊆ D)
    (hA : ∀ γ ∈ B, A ≤ (lineAgreeSet u₀ u₁ w γ).card) :
    B.card * (A - D.card) ≤ Fintype.card ι - D.card := by
  have hU : (Finset.univ \ D).card = Fintype.card ι - D.card := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset ι) D
    rw [Finset.univ_inter, Finset.card_univ] at h
    omega
  rw [← hU]
  refine card_mul_le_of_disjoint_petals (fun γ _ γ' _ hne =>
    linePetal_disjoint_of_common_subset D u₀ u₁ w hne hcommon) (fun γ _ => ?_) (fun γ hγ => ?_)
  · rw [linePetal]
    exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl D)
  · exact le_trans (Nat.sub_le_sub_right (hA γ hγ) D.card) (card_linePetal_ge D u₀ u₁ w γ)

/-- **Bad-witness combiners have large line-agreement.**  Every `γ ∈ mcaBadWitness C δ u₀ u₁ w` has
`|lineAgreeSet γ| ≥ (1−δ)·n`: the witnessing set `S` (size `≥ (1−δ)n` on which `w` agrees with the
line) is contained in `lineAgreeSet γ`.  This supplies the agreement input `A = (1−δ)n` of
`badCombiner_count`, connecting the sunflower count to the actual residual. -/
theorem card_lineAgreeSet_ge_of_mem_mcaBadWitness
    {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ w : ι → F} {γ : F}
    (hγ : γ ∈ mcaBadWitness (MC : Set (ι → F)) δ u₀ u₁ w) :
    ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ ((lineAgreeSet u₀ u₁ w γ).card : ℝ≥0) := by
  classical
  simp only [mcaBadWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  obtain ⟨S, hScard, hSagree, -⟩ := hγ
  have hSsub : S ⊆ lineAgreeSet u₀ u₁ w γ := fun i hi => by
    rw [mem_lineAgreeSet_iff]; exact hSagree i hi
  exact le_trans hScard (by exact_mod_cast Finset.card_le_card hSsub)

/-- **The common zero-agreement set jointly agrees (via `(w, 0)`).**  On `{i : u₁ᵢ = 0 ∧ wᵢ = u₀ᵢ}`
the codeword pair `(w, 0)` witnesses joint agreement: `w = u₀` there and `0 = u₁` there.  Hence,
once this set is large enough, it is a correlated-agreement domain. -/
theorem pairJointAgreesOn_common {MC : Submodule F (ι → F)} {u₀ u₁ w : ι → F} (hw : w ∈ MC) :
    pairJointAgreesOn (MC : Set (ι → F))
      (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)) u₀ u₁ := by
  refine ⟨w, hw, 0, MC.zero_mem, fun i hi => ?_⟩
  rw [Finset.mem_filter] at hi
  exact ⟨hi.2.2, by rw [Pi.zero_apply]; exact hi.2.1.symm⟩

/-- **A maximal correlated-agreement domain containing a given one exists.**  Strengthening
`exists_maxCorrAgreeDomain_of_nonempty`: from a correlated-agreement domain `D₀`, a *maximal* domain
`D ⊇ D₀` exists.  Combined with `pairJointAgreesOn_common`, taking `D₀ = {i : u₁ᵢ=0 ∧ wᵢ=u₀ᵢ}` (when
large) yields a maximal domain that **absorbs the common zero-agreement set** — the precise input
`hcommon` that `badCombiner_count` and the petal disjointness require. -/
theorem exists_maxCorrAgreeDomain_containing
    (MC : Submodule F (ι → F)) (p : ℝ≥0) (u₀ u₁ : ι → F) (D₀ : Finset ι)
    (hD₀ : corrAgreeDomain MC p u₀ u₁ D₀) :
    ∃ D : Finset ι, D₀ ⊆ D ∧ maxCorrAgreeDomain MC p u₀ u₁ D := by
  classical
  set 𝒮 : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powerset.filter
      (fun D => corrAgreeDomain MC p u₀ u₁ D ∧ D₀ ⊆ D) with h𝒮
  have hD₀mem : D₀ ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hD₀, Finset.Subset.refl _⟩
  obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image 𝒮 Finset.card ⟨D₀, hD₀mem⟩
  obtain ⟨hDcorr, hD₀D⟩ := (Finset.mem_filter.mp hDmem).2
  refine ⟨D, hD₀D, hDcorr, fun E hDE hE => ?_⟩
  have hEmem : E ∈ 𝒮 :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hE, Finset.Subset.trans hD₀D hDE⟩
  exact (Finset.eq_of_subset_of_card_le hDE (hDmax E hEmem)).ge

/-- **GKL24 first-moment count for `mcaBadWitness` (full assembly).**  If the maximal domain `D`
absorbs the common zero-agreement set, then the number of bad combiners witnessed by `w` obeys
`|mcaBadWitness w| · (⌊(1−δ)·n⌋ − |D|) ≤ n − |D|`.  This is GKL24's `|Bad¹|` first-moment bound,
assembled end-to-end: the agreement input `⌊(1−δ)n⌋` comes from
`card_lineAgreeSet_ge_of_mem_mcaBadWitness` (via `Nat.floor`), fed into `badCombiner_count`.  Combined
with `pairJointAgreesOn_common` + `exists_maxCorrAgreeDomain_containing` (which build a `D` absorbing
the common set whenever it is large), this is the complete formalized GKL24 first-moment argument. -/
theorem mcaBadWitness_card_first_moment {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ w : ι → F}
    {D : Finset ι}
    (hcommon : Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) ⊆ D) :
    (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card
        * (⌊((1 - δ) * Fintype.card ι : ℝ≥0)⌋₊ - D.card)
      ≤ Fintype.card ι - D.card := by
  refine badCombiner_count hcommon (fun γ hγ => ?_)
  calc ⌊((1 - δ) * Fintype.card ι : ℝ≥0)⌋₊
      ≤ ⌊((lineAgreeSet u₀ u₁ w γ).card : ℝ≥0)⌋₊ :=
        Nat.floor_mono (card_lineAgreeSet_ge_of_mem_mcaBadWitness (MC := MC) hγ)
    _ = (lineAgreeSet u₀ u₁ w γ).card := Nat.floor_natCast _

/-- **GKL24 first-moment count, raw form: `|mcaBadWitness w| ≤ n − |common|`.**  Taking the absorbing
domain to be the common zero-agreement set itself, whenever it is smaller than the bad-witness radius
`⌊(1−δ)n⌋`, the bad-combiner count is at most the number of non-common coordinates.  No correlated-
agreement rate `p` is needed — this is the most fundamental form of the count, from which the sharp
`p·n` bound follows by `|D| ≥ (1−p)n`. -/
theorem mcaBadWitness_card_le_of_radius {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ w : ι → F}
    (hub : (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)).card
      < ⌊((1 - δ) * Fintype.card ι : ℝ≥0)⌋₊) :
    (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card
      ≤ Fintype.card ι - (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)).card := by
  have hcount := mcaBadWitness_card_first_moment (MC := MC) (δ := δ) (u₀ := u₀) (u₁ := u₁) (w := w)
    (D := Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)) (Finset.Subset.refl _)
  exact le_trans (Nat.le_mul_of_pos_right _ (by omega)) hcount

/-- **GKL24 first-moment bound, unconditional: `|mcaBadWitness w| ≤ n − |common|`.**  For *every*
stack (with `w` a codeword), the number of bad combiners is at most the number of non-common
coordinates.  Each bad combiner's petal `lineAgreeSet γ \ common` is nonempty — the `¬pairJointAgrees`
clause forces the witnessing set outside the common set (otherwise `(w, 0)` would witness joint
agreement via `pairJointAgreesOn_common`) — and distinct petals are disjoint, so the bad combiners
inject into `univ \ common`.  This is the cleanest, hypothesis-free form of GKL24's first moment. -/
theorem mcaBadWitness_card_le_compl_common {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ w : ι → F}
    (hw : w ∈ MC) :
    (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card
      ≤ Fintype.card ι - (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)).card := by
  classical
  set C₀ := Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) with hC₀
  have hU : (Finset.univ \ C₀).card = Fintype.card ι - C₀.card := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset ι) C₀
    rw [Finset.univ_inter, Finset.card_univ] at h; omega
  rw [← hU, ← mul_one (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card]
  refine card_mul_le_of_disjoint_petals (P := linePetal C₀ u₀ u₁ w)
    (fun γ _ γ' _ hne => linePetal_disjoint_of_common_subset C₀ u₀ u₁ w hne (Finset.Subset.refl _))
    (fun γ _ => by
      rw [linePetal]
      exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _))
    (fun γ hγ => ?_)
  rw [Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
  simp only [mcaBadWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  obtain ⟨S, _, hSagree, hSnopair⟩ := hγ
  have hSnotsub : ¬ S ⊆ C₀ := by
    intro hsub
    refine hSnopair ⟨w, hw, 0, MC.zero_mem, fun i hi => ?_⟩
    have hiC := hsub hi
    rw [hC₀, Finset.mem_filter] at hiC
    exact ⟨hiC.2.2, by rw [Pi.zero_apply]; exact hiC.2.1.symm⟩
  obtain ⟨i, hiS, hiC⟩ := Finset.not_subset.mp hSnotsub
  exact ⟨i, by rw [linePetal, Finset.mem_sdiff, mem_lineAgreeSet_iff]; exact ⟨hSagree i hiS, hiC⟩⟩

/-- **Inclusion–exclusion for two line-agreement sets.**  For `γ ≠ γ'`,
`|lineAgreeSet γ| + |lineAgreeSet γ'| ≤ |common| + n`: the two sets overlap exactly in the common
zero-agreement set (`lineAgreeSet_inter_eq`), and their union fits in `univ`.  When both agreements
are large (`≥ (1−δ)n`, as for bad combiners), this forces `|common| ≥ (1−2δ)n` — the structural
reason `|mcaBadWitness w| ≤ 2δn` once two bad combiners exist. -/
theorem lineAgreeSet_card_add_le (u₀ u₁ w : ι → F) {γ γ' : F} (hγ : γ ≠ γ') :
    (lineAgreeSet u₀ u₁ w γ).card + (lineAgreeSet u₀ u₁ w γ').card
      ≤ (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)).card + Fintype.card ι := by
  have h := Finset.card_union_add_card_inter (lineAgreeSet u₀ u₁ w γ) (lineAgreeSet u₀ u₁ w γ')
  rw [lineAgreeSet_inter_eq u₀ u₁ w hγ] at h
  have hunion : (lineAgreeSet u₀ u₁ w γ ∪ lineAgreeSet u₀ u₁ w γ').card ≤ Fintype.card ι := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-- **GKL24 sharp first-moment bound `|Bad¹| ≤ p·n`.**  If a correlated-agreement domain `D` at rate
`p` (so `(1−p)·n ≤ |D|`) absorbs the common zero-agreement set, and the bad-witness radius is smaller
(`|D| < ⌊(1−δ)·n⌋`, i.e. `δ < p`), then `|mcaBadWitness w| ≤ p·n`.  This is GKL24's sharp
first-moment count — the genuine external residual blocking the GCXK25 list-decoding→MCA chain: from
the sunflower count `|B|·(⌊(1−δ)n⌋−|D|) ≤ n−|D|` with `⌊(1−δ)n⌋ > |D|` we get `|B| ≤ n−|D|`, and
`|D| ≥ (1−p)n` gives `n−|D| ≤ p·n`. -/
theorem mcaBadWitness_card_le_pn {MC : Submodule F (ι → F)} {δ p : ℝ≥0} {u₀ u₁ w : ι → F}
    {D : Finset ι} (hp : p ≤ 1)
    (hcommon : Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) ⊆ D)
    (hDcard : (1 - p) * Fintype.card ι ≤ (D.card : ℝ≥0))
    (hlt : D.card < ⌊((1 - δ) * Fintype.card ι : ℝ≥0)⌋₊) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ≥0)
      ≤ p * Fintype.card ι := by
  have hcount := mcaBadWitness_card_first_moment (MC := MC) (δ := δ) hcommon
  have hk : 0 < ⌊((1 - δ) * Fintype.card ι : ℝ≥0)⌋₊ - D.card := by omega
  have hBnat : (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card
      ≤ Fintype.card ι - D.card := le_trans (Nat.le_mul_of_pos_right _ hk) hcount
  have hDle : D.card ≤ Fintype.card ι := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  -- `n − |D| ≤ p·n` in `ℝ≥0` without group subtraction
  have hsum : (↑(Fintype.card ι - D.card) : ℝ≥0) + ↑D.card = ↑(Fintype.card ι) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hDle]
  have hn : (↑(Fintype.card ι) : ℝ≥0) = p * Fintype.card ι + (1 - p) * Fintype.card ι := by
    rw [← add_mul, add_tsub_cancel_of_le hp, one_mul]
  have key : (↑(Fintype.card ι - D.card) : ℝ≥0) ≤ p * Fintype.card ι := by
    have h1 : (↑(Fintype.card ι - D.card) : ℝ≥0) + (1 - p) * Fintype.card ι
        ≤ p * Fintype.card ι + (1 - p) * Fintype.card ι := by
      calc (↑(Fintype.card ι - D.card) : ℝ≥0) + (1 - p) * Fintype.card ι
          ≤ (↑(Fintype.card ι - D.card) : ℝ≥0) + ↑D.card := add_le_add le_rfl hDcard
        _ = ↑(Fintype.card ι) := hsum
        _ = p * Fintype.card ι + (1 - p) * Fintype.card ι := hn
    exact le_of_add_le_add_right h1
  exact le_trans (by exact_mod_cast hBnat) key

/-- **GKL24 sharp first-moment via the common set directly.**  Taking the absorbing domain to be the
common zero-agreement set itself: if `(1−p)·n ≤ |{i : u₁ᵢ=0 ∧ wᵢ=u₀ᵢ}| < ⌊(1−δ)·n⌋`, then
`|mcaBadWitness w| ≤ p·n`.  This is the self-contained form of GKL24's `|Bad¹| ≤ p·n`: no auxiliary
domain is needed, only that the common agreement set is sized between the two radii. -/
theorem mcaBadWitness_card_le_pn_of_common {MC : Submodule F (ι → F)} {δ p : ℝ≥0}
    {u₀ u₁ w : ι → F} (hp : p ≤ 1)
    (hlb : (1 - p) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)).card : ℝ≥0))
    (hub : (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)).card
      < ⌊((1 - δ) * Fintype.card ι : ℝ≥0)⌋₊) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ≥0) ≤ p * Fintype.card ι :=
  mcaBadWitness_card_le_pn hp (Finset.Subset.refl _) hlb hub

/-- **Per-stack bad count from the witness cover.**  The per-stack bad-combiner set `mcaBad` is
covered by the per-codeword witness sets over any carrier `T ⊇ C` (`mcaBad_subset_biUnion_…`), so
`|mcaBad| ≤ ∑_{w ∈ T} |mcaBadWitness w|`.  Combined with the per-codeword first-moment bounds
(`mcaBadWitness_card_le_compl_common` etc.), this lifts the GKL24 first moment from individual
codewords to the per-stack count that the GCXK25 list-decoding→MCA reduction consumes. -/
theorem mcaBad_card_le_sum_mcaBadWitness {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ : ι → F}
    (T : Finset (ι → F)) (hT : ∀ w ∈ (MC : Set (ι → F)), w ∈ T) :
    (mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card
      ≤ ∑ w ∈ T, (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card :=
  le_trans (Finset.card_le_card (mcaBad_subset_biUnion_mcaBadWitness _ δ u₀ u₁ T hT))
    Finset.card_biUnion_le

/-- **Per-stack first-moment bound `|mcaBad| ≤ |T|·max(1, 2δn)`.**  Combining the witness cover
(`mcaBad_card_le_sum_mcaBadWitness`) with the per-codeword bound
(`mcaBadWitness_card_le_two_delta_mul_card`) over a codeword carrier `T`: the per-stack bad set has
size at most `|T|` times the per-codeword radius `max(1, 2δn)`.  With `|T|` the list size `L`, this is
the per-stack first-moment input of the GCXK25 list-decoding→MCA reduction (here at the in-tree `2δn`
radius). -/
theorem mcaBad_card_le_carrier_two_delta {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ : ι → F}
    (T : Finset (ι → F)) (hT : ∀ w ∈ (MC : Set (ι → F)), w ∈ T)
    (hTsub : ∀ w ∈ T, w ∈ (MC : Set (ι → F))) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ)
      ≤ T.card * max 1 (2 * (δ : ℝ) * Fintype.card ι) := by
  have h1 : ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ)
      ≤ ∑ w ∈ T, ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) := by
    have h := mcaBad_card_le_sum_mcaBadWitness (MC := MC) (δ := δ) (u₀ := u₀) (u₁ := u₁) T hT
    rw [← Nat.cast_sum]; exact_mod_cast h
  refine le_trans h1 ?_
  calc ∑ w ∈ T, ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ)
      ≤ ∑ _w ∈ T, max 1 (2 * (δ : ℝ) * Fintype.card ι) :=
        Finset.sum_le_sum fun w hw =>
          mcaBadWitness_card_le_two_delta_mul_card MC δ u₀ u₁ w (hTsub w hw)
    _ = T.card * max 1 (2 * (δ : ℝ) * Fintype.card ι) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **`ε_mca` bound from a codeword carrier (GKL24 first moment → MCA error).**  For any carrier `T`
covering the code, `ε_mca(C, δ) ≤ |T|·max(1, 2δn) / |F|`.  This is the end-to-end bridge: the entire
GKL24 first-moment chain (sunflower count → per-codeword `2δn` → per-stack carrier bound) feeds the
`ε_mca` glue (`epsMCA_le_ofReal_of_forall_mcaBad_card_le`).  The bound is parameterized by `|T|`, so
a sharper cover (the `L` close codewords) plugs straight in to give the list-size-scaled MCA error. -/
theorem epsMCA_le_two_delta_of_carrier {MC : Submodule F (ι → F)} {δ : ℝ≥0}
    (T : Finset (ι → F)) (hT : ∀ w ∈ (MC : Set (ι → F)), w ∈ T)
    (hTsub : ∀ w ∈ T, w ∈ (MC : Set (ι → F))) :
    epsMCA (F := F) (A := F) ((MC : Set (ι → F))) δ
      ≤ ENNReal.ofReal ((T.card : ℝ) * max 1 (2 * (δ : ℝ) * Fintype.card ι) / Fintype.card F) :=
  epsMCA_le_ofReal_of_forall_mcaBad_card_le _ δ
    (fun _ => mcaBad_card_le_carrier_two_delta T hT hTsub)

/-- **GKL24/GCXK25 second-moment bound `|Bad²| < 1/ε`.**  In the regime where the common
zero-agreement set is *small* (`|common| ≤ (1−p)n`) and each bad combiner's line-agreement is large
(`≥ √(1−p+ε)·n`), the bad-witness count satisfies `|mcaBadWitness w|·ε < 1`.  This applies the
in-tree Cauchy–Schwarz second-moment count (`GCXK25SecondMoment.card_lt_inv_of_second_moment_rs`) to
the line-agreement sets `A_γ = lineAgreeSet γ`: their pairwise intersections all equal the common
set (`lineAgreeSet_inter_eq`), so the small-`|common|` hypothesis supplies exactly the required
small-pairwise-intersection bound.  Complements the first-moment `|Bad¹| ≤ p·n` (large-`|common|`
regime): together they give the GCXK25 `p·n + 1/ε` per-codeword count. -/
theorem mcaBadWitness_card_lt_inv_of_second_moment {MC : Submodule F (ι → F)} {δ : ℝ≥0}
    {u₀ u₁ w : ι → F} (p ε : ℝ) (hε : 0 < ε) (hεp : ε ≤ p) (hp1 : p < 1)
    (hn : 0 < Fintype.card ι)
    (hSle : ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
        (1 - p + ε) ^ ((1 : ℝ) / 2) * (Fintype.card ι : ℝ)
          ≤ ((lineAgreeSet u₀ u₁ w γ).card : ℝ))
    (hcommon : ((Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)).card : ℝ)
        ≤ (1 - p) * (Fintype.card ι : ℝ)) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) * ε < 1 := by
  rcases Finset.eq_empty_or_nonempty
      (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w) with he | hne
  · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]; exact one_pos
  · exact GCXK25SecondMoment.card_lt_inv_of_second_moment_rs _
      (fun γ => lineAgreeSet u₀ u₁ w γ) hne p ε hε hεp hp1 hn hSle
      (fun γ _ γ' _ hne' => by rw [lineAgreeSet_inter_eq u₀ u₁ w hne']; exact hcommon)

end ProximityGap
