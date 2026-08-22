/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The witness-spread structure of MCA lower bounds (Proximity Prize, ABF26 #232)

The Grand MCA Challenge needs a **lower** bound `ε_mca(C, δ) > ε*` for `δ` above the
threshold `δ*`. The state-of-the-art near-capacity lower bound is `ε_mca ≥ n^{Ω(1)}/|F|`
([BCHKS25],[KK25],[CGHLL26]); the file `MCAGeneralLowerBound.lean` proves the unconditional
`ε_mca ≥ 1/|F|` up to capacity for every proper linear code. To beat `1/|F|`, one must make
`mcaEvent` fire for **many** scalars `γ` on a single line.

This file isolates *exactly* what such a construction must look like, and proves a sharp
structural obstruction:

* `pairJointAgreesOn_iff_split` — **rowwise split.** The MCA joint-pair predicate is exactly
  the conjunction of independent row explanations on the same witness set. This makes row-level
  non-explainability a reusable route to `¬ pairJointAgreesOn`.

* `epsMCA_ge_card_div_of_mcaEvent_set` — **multi-`γ` lower bound.** If a fixed stack `u`
  admits a whole finite set `G ⊆ F` of bad scalars (`mcaEvent` fires at each), then
  `ε_mca(C, δ) ≥ |G|/|F|`. This is the lower-bound engine the prize needs: producing
  `|G| = n^{Ω(1)}` bad scalars yields the near-capacity bound. (Generalizes the single-scalar
  `epsMCA_ge_inv_card_of_mcaEvent`, which is the `|G| = 1` case.)

* `unique_bad_gamma_common_witness` — **the obstruction.** For *any* linear code `C`, if two
  bad scalars `γ₁, γ₂` are witnessed by the **same** coordinate set `S` (the same `S` carries
  the line-closeness for both *and* the joint-disagreement), then `γ₁ = γ₂`. Reason: from
  `w₁ = u₀ + γ₁·u₁` and `w₂ = u₀ + γ₂·u₁` on `S`, the linear combinations
  `v₁ := (γ₁-γ₂)⁻¹(w₁-w₂)` and `v₀ := w₁ - γ₁·v₁` are codewords agreeing with `(u₀,u₁)` on
  `S` — exactly the `pairJointAgreesOn` that `mcaEvent` forbids.

* `common_witness_badGamma_card_le_one` / `epsMCA_common_witness_le_inv_card` — **consequence.**
  A single common witness set yields at most `1/|F|`. Hence **the prize's lower bound
  provably requires the witness sets `S_γ` to vary with `γ`** — i.e. the list-decoding
  geometry (different codewords, hence different agreement sets, near the line). This is the
  precise reason the near-capacity lower bound is genuinely hard, and it delineates the open
  core honestly: the open content is *not* positivity (`1/|F|`, done) but producing a line
  whose `δ`-close points are witnessed by a *spread* of distinct coordinate sets.

* `badScalar_card_le_one_of_forced_univ` / `epsMCA_le_inv_card_of_forced_univ` — **forced
  universal witness barrier.** If the radius is so small that every legal `mcaEvent` witness set
  must be all coordinates, then every bad scalar shares the same witness set `univ`; the common
  witness obstruction collapses the bad set to size at most one. This turns the exact F5
  `δ*` pin and the zero-code endpoint into instances of the same structural phenomenon.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open ProximityGap Code

namespace ProximityGap.MCAWitnessSpread

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The joint-pair clause splits rowwise.** `pairJointAgreesOn C S u₀ u₁` packages two
independent row explanations over the same coordinate set `S`: one codeword agrees with `u₀`
on `S`, and one codeword agrees with `u₁` on `S`. This is often the cleanest way to refute
joint agreement, since failure of either row explanation is enough. -/
theorem pairJointAgreesOn_iff_split (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) :
    pairJointAgreesOn C S u₀ u₁ ↔
      (∃ v₀ ∈ C, ∀ i ∈ S, v₀ i = u₀ i) ∧ (∃ v₁ ∈ C, ∀ i ∈ S, v₁ i = u₁ i) := by
  constructor
  · rintro ⟨v₀, h₀, v₁, h₁, h⟩
    exact ⟨⟨v₀, h₀, fun i hi => (h i hi).1⟩, ⟨v₁, h₁, fun i hi => (h i hi).2⟩⟩
  · rintro ⟨⟨v₀, h₀, e₀⟩, ⟨v₁, h₁, e₁⟩⟩
    exact ⟨v₀, h₀, v₁, h₁, fun i hi => ⟨e₀ i hi, e₁ i hi⟩⟩

open Classical in
/-- **Multi-scalar MCA lower bound.** If a fixed stack `u` admits a whole finite set `G ⊆ F`
of bad scalars — `mcaEvent C δ (u 0) (u 1) γ` fires for every `γ ∈ G` — then
`ε_mca(C, δ) ≥ |G|/|F|`.

This is the lower-bound engine for the Grand MCA Challenge: the near-capacity bound
`ε_mca ≥ n^{Ω(1)}/|F|` is exactly this lemma instantiated with a line carrying
`|G| = n^{Ω(1)}` bad scalars. Generalizes `epsMCA_ge_inv_card_of_mcaEvent` (`|G| = 1`). -/
theorem epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent C δ (u 0) (u 1) γ) :
    (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (A := A) C δ := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := A) C δ u)
  rw [prob_uniform_eq_card_filter_div_card]
  have hsub : G ⊆ Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hG γ hγ
  have hcard : G.card
      ≤ (Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card :=
    Finset.card_le_card hsub
  simp only [ENNReal.coe_natCast]
  gcongr

/-- **At most one bad scalar per witness set (linear codes).** For any linear code `C` and any
coordinate set `S` on which `(u₀, u₁)` has *no* joint codeword pair, at most one scalar `γ` can
have the line `u₀ + γ·u₁` agree with a codeword on all of `S`.

Proof: if `w₁ = u₀ + γ₁·u₁` and `w₂ = u₀ + γ₂·u₁` on `S` with `γ₁ ≠ γ₂`, then
`v₁ := (γ₁-γ₂)⁻¹(w₁-w₂)` and `v₀ := w₁ - γ₁·v₁` are codewords (linearity) with `v₀ = u₀`,
`v₁ = u₁` on `S` — a `pairJointAgreesOn` witness, contradicting the hypothesis. -/
theorem unique_bad_gamma_common_witness
    (C : Submodule F (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) {γ₁ γ₂ : F}
    (hno : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁)
    (h₁ : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₂ • u₁ i) :
    γ₁ = γ₂ := by
  by_contra hne
  obtain ⟨w₁, hw₁C, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂C, hw₂⟩ := h₂
  have hd : (γ₁ - γ₂) ≠ 0 := sub_ne_zero.mpr hne
  set v₁ : ι → A := (γ₁ - γ₂)⁻¹ • (w₁ - w₂) with hv₁def
  set v₀ : ι → A := w₁ - γ₁ • v₁ with hv₀def
  have hv₁mem : v₁ ∈ C := C.smul_mem _ (C.sub_mem hw₁C hw₂C)
  have hv₀mem : v₀ ∈ C := C.sub_mem hw₁C (C.smul_mem _ hv₁mem)
  apply hno
  refine ⟨v₀, hv₀mem, v₁, hv₁mem, ?_⟩
  intro i hi
  have hv₁i : v₁ i = u₁ i := by
    simp only [hv₁def, Pi.smul_apply, Pi.sub_apply, hw₁ i hi, hw₂ i hi]
    rw [show (u₀ i + γ₁ • u₁ i) - (u₀ i + γ₂ • u₁ i) = (γ₁ - γ₂) • u₁ i from by
      rw [sub_smul]; abel]
    rw [inv_smul_smul₀ hd]
  have hv₀i : v₀ i = u₀ i := by
    simp only [hv₀def, Pi.sub_apply, Pi.smul_apply, hw₁ i hi, hv₁i]
    abel
  exact ⟨hv₀i, hv₁i⟩

/-- **Two line witnesses determine a slope codeword.** If two distinct scalars have line
explainers `c, c'` on witness sets `S, S'`, then the divided difference
`(γ - γ')⁻¹ • (c - c')` is a codeword and it agrees with the direction row `u₁` on
`S ∩ S'`.

This is the algebraic core behind the UDR-edge polynomial-pencil route: once witness
overlaps are large, the explainer map has codeword-valued secant slopes. -/
theorem line_slope_codeword_of_two_witnesses
    (C : Submodule F (ι → A)) {S S' : Finset ι} {u₀ u₁ c c' : ι → A} {γ γ' : F}
    (hne : γ ≠ γ') (hc : c ∈ C) (hc' : c' ∈ C)
    (hS : ∀ i ∈ S, c i = u₀ i + γ • u₁ i)
    (hS' : ∀ i ∈ S', c' i = u₀ i + γ' • u₁ i) :
    (γ - γ')⁻¹ • (c - c') ∈ C ∧
      ∀ i ∈ S ∩ S', ((γ - γ')⁻¹ • (c - c')) i = u₁ i := by
  constructor
  · exact C.smul_mem _ (C.sub_mem hc hc')
  · intro i hi
    obtain ⟨hiS, hiS'⟩ := Finset.mem_inter.mp hi
    have hd : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
    simp only [Pi.smul_apply, Pi.sub_apply, hS i hiS, hS' i hiS']
    rw [show (u₀ i + γ • u₁ i) - (u₀ i + γ' • u₁ i) = (γ - γ') • u₁ i from by
      rw [sub_smul]
      abel]
    rw [inv_smul_smul₀ hd]

/-- **Edge-band witness overlap.** If two witness sets both have size at least `n-w`
inside an `n`-point domain and `2w+k+1 ≤ n`, then they overlap in at least `k+1`
coordinates. -/
theorem edge_witness_inter_card_ge {S S' : Finset ι} {n k w : ℕ}
    (hcard : Fintype.card ι = n) (hS : n - w ≤ S.card) (hS' : n - w ≤ S'.card)
    (hband : 2 * w + k + 1 ≤ n) :
    k + 1 ≤ (S ∩ S').card := by
  have hU : (S ∪ S').card ≤ n := by
    calc (S ∪ S').card ≤ (Finset.univ : Finset ι).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card ι := Finset.card_univ
      _ = n := hcard
  have hie : (S ∪ S').card + (S ∩ S').card = S.card + S'.card :=
    Finset.card_union_add_card_inter S S'
  have hmain : 2 * (n - w) ≤ n + (S ∩ S').card := by
    calc 2 * (n - w) ≤ S.card + S'.card := by omega
      _ = (S ∪ S').card + (S ∩ S').card := hie.symm
      _ ≤ n + (S ∩ S').card := Nat.add_le_add_right hU _
  omega

/-- **UDR-edge slope bridge.** In the edge band, any two distinct line witnesses produce
a codeword-valued secant slope that agrees with the direction row on at least `k+1`
coordinates.  This is the formal first step toward the slope-collapse/polynomial-pencil
count: all pairwise explainer slopes are genuine nearby codewords for `u₁`. -/
theorem edge_slope_codeword_of_two_line_witnesses
    (C : Submodule F (ι → A)) {n k w : ℕ} (hcard : Fintype.card ι = n)
    (hband : 2 * w + k + 1 ≤ n)
    {S S' : Finset ι} {u₀ u₁ c c' : ι → A} {γ γ' : F}
    (hne : γ ≠ γ') (hSsz : n - w ≤ S.card) (hS'sz : n - w ≤ S'.card)
    (hc : c ∈ C) (hc' : c' ∈ C)
    (hS : ∀ i ∈ S, c i = u₀ i + γ • u₁ i)
    (hS' : ∀ i ∈ S', c' i = u₀ i + γ' • u₁ i) :
    ∃ v ∈ C, v = (γ - γ')⁻¹ • (c - c') ∧
      k + 1 ≤ (S ∩ S').card ∧ ∀ i ∈ S ∩ S', v i = u₁ i := by
  have hslope := line_slope_codeword_of_two_witnesses C hne hc hc' hS hS'
  refine ⟨(γ - γ')⁻¹ • (c - c'), hslope.1, rfl,
    edge_witness_inter_card_ge hcard hSsz hS'sz hband, hslope.2⟩

open Classical in
/-- **The common-witness bad-scalar set is a subsingleton (linear codes).** Restating
`unique_bad_gamma_common_witness`: with a single coordinate set `S` on which `(u₀, u₁)` has no
joint codeword pair, the set of scalars whose line agrees with a codeword on all of `S` has at
most one element. -/
theorem common_witness_badGamma_card_le_one
    (C : Submodule F (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A)
    (hno : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁) :
    (Finset.univ.filter
      (fun γ : F => ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ₁ h₁ γ₂ h₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  exact unique_bad_gamma_common_witness C S u₀ u₁ hno h₁ h₂

open Classical in
/-- **A single common witness set yields at most `1/|F|`.** If *every* bad scalar in a finite
set `G` is witnessed by the **same** coordinate set `S` (same `S` carries both the
line-closeness and the joint-disagreement, as in `mcaEvent`), then `|G| ≤ 1`. Consequently the
common-witness route never beats the unconditional `ε_mca ≥ 1/|F|`.

Hence the prize's near-capacity lower bound `ε_mca ≥ n^{Ω(1)}/|F|` provably **requires the
witness sets to vary with `γ`** — the list-decoding spread of distinct agreement sets around
the line. This pins down precisely what is open on the lower-bound side. -/
theorem common_witness_badGamma_set_card_le_one
    (C : Submodule F (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) (G : Finset F)
    (hno : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁)
    (hG : ∀ γ ∈ G, ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    G.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ₁ hmem₁ γ₂ hmem₂
  exact unique_bad_gamma_common_witness C S u₀ u₁ hno (hG γ₁ hmem₁) (hG γ₂ hmem₂)

open Classical in
/-- **Forced-universal-witness barrier.** If the radius/cardinality side condition forces every
legal `mcaEvent` witness set to be `Finset.univ`, then every stack has at most one bad scalar.

Mathematically, this is the endpoint version of the witness-spread obstruction: when geometry
leaves no room for the witness sets to vary, all bad scalars share the common witness `univ`, so
`unique_bad_gamma_common_witness` collapses them. -/
theorem badScalar_card_le_one_of_forced_univ
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) → T = Finset.univ)
    (u : WordStack A (Fin 2) ι) :
    (Finset.filter
      (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  obtain ⟨S, hS, hclose, hno⟩ := hγ.2
  obtain ⟨S', hS', hclose', _⟩ := hγ'.2
  rw [hforce S hS] at hclose hno
  rw [hforce S' hS'] at hclose'
  exact unique_bad_gamma_common_witness C Finset.univ (u 0) (u 1) hno hclose hclose'

open Classical in
/-- **Forced codimension-one witness barrier.** If the radius/cardinality side condition forces
every legal `mcaEvent` witness set to be either all coordinates or all coordinates except one,
then every stack has at most `|ι|` bad scalars.

Each bad scalar chooses one legal witness set.  Universal witnesses collapse the whole bad set to
one scalar by `unique_bad_gamma_common_witness`; otherwise, an all-but-one witness is charged to
its omitted coordinate.  Two scalars charged to the same omitted coordinate share the same witness
set, so the common-witness uniqueness lemma identifies them. -/
theorem badScalar_card_le_card_of_forced_codimOne
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) →
        T = Finset.univ ∨ ∃ i : ι, T = Finset.univ.erase i)
    (u : WordStack A (Fin 2) ι) :
    (Finset.filter
      (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ Fintype.card ι := by
  let B : Finset F :=
    Finset.filter
      (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let event : B → Prop := fun γ =>
    mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) (γ : F)
  have event_spec : ∀ γ : B, event γ := by
    intro γ
    exact (Finset.mem_filter.mp γ.property).2
  let S : B → Finset ι := fun γ => Classical.choose (event_spec γ)
  have S_spec : ∀ γ : B,
      (S γ).card ≥ ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ∧
      (∃ w ∈ C, ∀ i ∈ S γ, w i = u 0 i + (γ : F) • u 1 i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) (S γ) (u 0) (u 1) := by
    intro γ
    exact Classical.choose_spec (event_spec γ)
  have key_exists : ∀ γ : B, ∃ i : ι, S γ = Finset.univ ∨ S γ = Finset.univ.erase i := by
    intro γ
    rcases hforce (S γ) (S_spec γ).1 with h | ⟨i, hi⟩
    · exact ⟨i₀, Or.inl h⟩
    · exact ⟨i, Or.inr hi⟩
  let key : B → ι := fun γ =>
    Classical.choose (key_exists γ)
  have key_spec : ∀ γ : B, S γ = Finset.univ ∨ S γ = Finset.univ.erase (key γ) := by
    intro γ
    exact Classical.choose_spec (key_exists γ)
  have key_inj : Function.Injective key := by
    intro γ γ' hkey
    apply Subtype.ext
    rcases key_spec γ with hγuniv | hγerase
    · rcases key_spec γ' with hγ'univ | hγ'erase
      · have hcloseγ : ∃ w ∈ C, ∀ i ∈ Finset.univ, w i = u 0 i + (γ : F) • u 1 i := by
          obtain ⟨w, hwC, hw⟩ := (S_spec γ).2.1
          exact ⟨w, hwC, fun i hi => hw i (by simp [hγuniv])⟩
        have hcloseγ' : ∃ w ∈ C, ∀ i ∈ Finset.univ, w i = u 0 i + (γ' : F) • u 1 i := by
          obtain ⟨w, hwC, hw⟩ := (S_spec γ').2.1
          exact ⟨w, hwC, fun i hi => hw i (by simp [hγ'univ])⟩
        exact unique_bad_gamma_common_witness C Finset.univ (u 0) (u 1)
          (by simpa [hγuniv] using (S_spec γ).2.2) hcloseγ hcloseγ'
      · have hcloseγ : ∃ w ∈ C, ∀ i ∈ S γ', w i = u 0 i + (γ : F) • u 1 i := by
          obtain ⟨w, hwC, hw⟩ := (S_spec γ).2.1
          exact ⟨w, hwC, fun i hi => hw i (by rw [hγuniv]; exact Finset.mem_univ i)⟩
        exact unique_bad_gamma_common_witness C (S γ') (u 0) (u 1)
          (S_spec γ').2.2 hcloseγ (S_spec γ').2.1
    · rcases key_spec γ' with hγ'univ | hγ'erase
      · have hcloseγ' : ∃ w ∈ C, ∀ i ∈ S γ, w i = u 0 i + (γ' : F) • u 1 i := by
          obtain ⟨w, hwC, hw⟩ := (S_spec γ').2.1
          exact ⟨w, hwC, fun i hi => hw i (by rw [hγ'univ]; exact Finset.mem_univ i)⟩
        exact unique_bad_gamma_common_witness C (S γ) (u 0) (u 1)
          (S_spec γ).2.2 (S_spec γ).2.1 hcloseγ'
      · have hSsame : S γ' = S γ := by
          rw [hγ'erase, hγerase, hkey]
        have hcloseγ' : ∃ w ∈ C, ∀ i ∈ S γ, w i = u 0 i + (γ' : F) • u 1 i := by
          obtain ⟨w, hwC, hw⟩ := (S_spec γ').2.1
          exact ⟨w, hwC, fun i hi => hw i (by simpa [hSsame] using hi)⟩
        exact unique_bad_gamma_common_witness C (S γ) (u 0) (u 1)
          (S_spec γ).2.2 (S_spec γ).2.1 hcloseγ'
  have hcard := Fintype.card_le_of_injective key key_inj
  rw [← Fintype.card_coe B]
  exact hcard

open Classical in
/-- **General forced-predicate witness barrier.** If the radius/cardinality side condition forces
every legal `mcaEvent` witness set to have cardinality at least `m`, then every stack has at most
as many bad scalars as there are coordinate subsets of size `≥ m`.

This strictly generalizes `badScalar_card_le_card_of_forced_codimOne` (which is the special case
`m = |ι| − 1`, where the `≥ m` subsets are exactly `univ` and the `|ι|` all-but-one sets, with the
sharper bound `|ι|`).  The proof is the clean injection `γ ↦ S_γ`: a bad scalar's chosen witness
set has size `≥ m` by `hforce`, and two bad scalars sharing a witness set are identified by
`unique_bad_gamma_common_witness`.  Use it for the higher granularity bands where the codimension is
larger than one and the omitted-coordinate charging of the codim-one proof no longer applies. -/
theorem badScalar_card_le_largeSubsets_of_forced_pred
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (m : ℕ)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) → m ≤ T.card)
    (u : WordStack A (Fin 2) ι) :
    (Finset.filter
      (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ).card
      ≤ (Finset.univ.filter (fun S : Finset ι => m ≤ S.card)).card := by
  classical
  set B : Finset F :=
    Finset.filter (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ with hBdef
  set T : Finset (Finset ι) :=
    Finset.univ.filter (fun S : Finset ι => m ≤ S.card) with hTdef
  let f : F → Finset ι := fun γ =>
    if h : mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ then Classical.choose h else ∅
  have f_spec : ∀ γ ∈ B,
      ((f γ).card : ℝ≥0) ≥ ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ∧
      (∃ w ∈ C, ∀ i ∈ f γ, w i = u 0 i + γ • u 1 i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) (f γ) (u 0) (u 1) := by
    intro γ hγ
    have hev : mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ :=
      (Finset.mem_filter.mp hγ).2
    have hfeq : f γ = Classical.choose hev := by simp only [f, hev, dif_pos]
    rw [hfeq]
    exact Classical.choose_spec hev
  have hmaps : ∀ γ ∈ B, f γ ∈ T := by
    intro γ hγ
    rw [hTdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hforce (f γ) (f_spec γ hγ).1⟩
  have hinj : Set.InjOn f ↑B := by
    intro γ hγ γ' hγ' hff
    have hγB : γ ∈ B := Finset.mem_coe.mp hγ
    have hγ'B : γ' ∈ B := Finset.mem_coe.mp hγ'
    have hno := (f_spec γ hγB).2.2
    have hclose := (f_spec γ hγB).2.1
    have hclose' : ∃ w ∈ C, ∀ i ∈ f γ, w i = u 0 i + γ' • u 1 i := by
      have h := (f_spec γ' hγ'B).2.1
      rwa [← hff] at h
    exact unique_bad_gamma_common_witness C (f γ) (u 0) (u 1) hno hclose hclose'
  exact Finset.card_le_card_of_injOn f hmaps hinj

open Classical in
/-- **Probability form of the general forced-predicate witness barrier.** If every legal
`mcaEvent` witness set is forced to have size at least `m`, then `ε_mca ≤ N_m/|F|`, where `N_m`
is the number of coordinate subsets of size at least `m`.  This is the good-side upper bound for
the deeper granularity bands beyond the first jump. -/
theorem epsMCA_le_largeSubsets_div_of_forced_pred
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (m : ℕ)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) → m ≤ T.card) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ ((Finset.univ.filter (fun S : Finset ι => m ≤ S.card)).card : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_largeSubsets_of_forced_pred C δ m hforce u

open Classical in
/-- A finite subset of a nonempty finite type with cardinality at least `n - 1` is either the
whole type or the complement of one point. This is the pure combinatorial classifier behind the
codimension-one witness barrier. -/
theorem eq_univ_or_eq_univ_erase_of_pred_le (T : Finset ι)
    (hT : Fintype.card ι - 1 ≤ T.card) :
    T = Finset.univ ∨ ∃ i : ι, T = Finset.univ.erase i := by
  have hcard_le : T.card ≤ Fintype.card ι := Finset.card_le_univ T
  rcases lt_or_eq_of_le hcard_le with hlt | hcard_eq
  · right
    have hcard : T.card = Fintype.card ι - 1 := by omega
    have hcompl_card : Tᶜ.card = 1 := by
      rw [Finset.card_compl, hcard]
      omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl_card
    refine ⟨i, ?_⟩
    have hT : T = ({i} : Finset ι)ᶜ := by
      calc
        T = Tᶜᶜ := by simp
        _ = ({i} : Finset ι)ᶜ := by rw [hi]
    rw [hT, Finset.compl_singleton]
  · left
    exact Finset.eq_univ_of_card T hcard_eq

open Classical in
/-- Cardinal-threshold form of `badScalar_card_le_card_of_forced_codimOne`. It is enough to
know that every legal witness has size at least `|ι| - 1`; the finite-set classifier turns that
into the universal/all-but-one dichotomy. -/
theorem badScalar_card_le_card_of_forced_pred
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) →
        Fintype.card ι - 1 ≤ T.card)
    (u : WordStack A (Fin 2) ι) :
    (Finset.filter
      (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ Fintype.card ι :=
  badScalar_card_le_card_of_forced_codimOne C δ
    (fun T hT => eq_univ_or_eq_univ_erase_of_pred_le T (hforce T hT)) u

open Classical in
/-- **Probability form of the forced-universal-witness barrier.** If every legal `mcaEvent`
witness set is forced to be all coordinates, then the MCA error is at most the unconditional
floor `1/|F|` for any linear code. The only way to exceed this floor is therefore a genuine
spread of distinct witness sets. -/
theorem epsMCA_le_inv_card_of_forced_univ
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) → T = Finset.univ) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ 1 / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_one_of_forced_univ C δ hforce u

open Classical in
/-- **Probability form of the forced codimension-one witness barrier.** If every legal
`mcaEvent` witness set is forced to be either all coordinates or all-but-one coordinate, then
the MCA error is at most `|ι|/|F|`. This is the abstract upper-bound half of the second
granularity band. -/
theorem epsMCA_le_card_div_of_forced_codimOne
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) →
        T = Finset.univ ∨ ∃ i : ι, T = Finset.univ.erase i) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_card_of_forced_codimOne C δ hforce u

open Classical in
/-- Cardinal-threshold form of `epsMCA_le_card_div_of_forced_codimOne`: if every legal witness
has size at least `|ι| - 1`, then `ε_mca ≤ |ι| / |F|`. -/
theorem epsMCA_le_card_div_of_forced_pred
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) →
        Fintype.card ι - 1 ≤ T.card) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_card_div_of_forced_codimOne C δ
    (fun T hT => eq_univ_or_eq_univ_erase_of_pred_le T (hforce T hT))

open Classical in
/-- At the first granularity radius, the MCA witness-size clause is exactly `|S| ≥ |ι| - 1`.
This is the arithmetic specialization behind the first-jump witness-count upper bound. -/
theorem granularity_card_clause :
    ((1 : ℝ≥0) - 1 / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0)
      = ((Fintype.card ι - 1 : ℕ) : ℝ≥0) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hne : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hinv : (1 / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0) = 1 := by
    rw [one_div, inv_mul_cancel₀ hne]
  have hpred : ((Fintype.card ι - 1 : ℕ) : ℝ≥0) + 1 =
      (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Nat.succ_pred_eq_of_pos hn
  rw [tsub_mul, one_mul, hinv, ← hpred, add_tsub_cancel_right]

open Classical in
/-- **First-granularity bad-count upper bound.** At radius `δ = 1/|ι|`, every legal witness
has size at least `|ι| - 1`, so the codimension-one witness barrier gives at most `|ι|` bad
scalars for any stack and any linear code. -/
theorem badScalar_card_le_card_of_granularity_radius
    (C : Submodule F (ι → A)) (u : WordStack A (Fin 2) ι) :
    (Finset.filter
      (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A))
          (1 / (Fintype.card ι : ℝ≥0)) (u 0) (u 1) γ)
      Finset.univ).card ≤ Fintype.card ι :=
  badScalar_card_le_card_of_forced_pred C (1 / (Fintype.card ι : ℝ≥0))
    (fun T hT => by
      rw [granularity_card_clause] at hT
      exact_mod_cast hT) u

open Classical in
/-- **First-granularity MCA upper bound.** For any linear code,
`ε_mca(C, 1/|ι|) ≤ |ι|/|F|`. This is the generic upper half expected at the first jump:
proving a matching stack with `|ι|` bad scalars is now the only remaining code-specific work. -/
theorem epsMCA_le_card_div_of_granularity_radius (C : Submodule F (ι → A)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A))
        (1 / (Fintype.card ι : ℝ≥0))
      ≤ (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_card_div_of_forced_pred C (1 / (Fintype.card ι : ℝ≥0))
    (fun T hT => by
      rw [granularity_card_clause] at hT
      exact_mod_cast hT)

#print axioms pairJointAgreesOn_iff_split
#print axioms epsMCA_ge_card_div_of_mcaEvent_set
#print axioms unique_bad_gamma_common_witness
#print axioms line_slope_codeword_of_two_witnesses
#print axioms edge_witness_inter_card_ge
#print axioms edge_slope_codeword_of_two_line_witnesses
#print axioms common_witness_badGamma_card_le_one
#print axioms common_witness_badGamma_set_card_le_one
#print axioms badScalar_card_le_one_of_forced_univ
#print axioms badScalar_card_le_largeSubsets_of_forced_pred
#print axioms epsMCA_le_largeSubsets_div_of_forced_pred
#print axioms badScalar_card_le_card_of_forced_codimOne
#print axioms eq_univ_or_eq_univ_erase_of_pred_le
#print axioms badScalar_card_le_card_of_forced_pred
#print axioms epsMCA_le_inv_card_of_forced_univ
#print axioms epsMCA_le_card_div_of_forced_codimOne
#print axioms epsMCA_le_card_div_of_forced_pred
#print axioms granularity_card_clause
#print axioms badScalar_card_le_card_of_granularity_radius
#print axioms epsMCA_le_card_div_of_granularity_radius

end ProximityGap.MCAWitnessSpread
