/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LadderSpectrumFusionValue

/-!
# The full-band ladder law (#371): the spectrum mass bounds EVERY radius

The boundary-slice exact law used its upper radius bound `(1−δ)n ≤ k+1` only
for the CONVERSE inclusion (constructing a `(k+1)`-point witness).  The forward
inclusion — every bad scalar is a residual ratio of some injective
`(k+1)`-tuple — needs only `k < (1−δ)n`, i.e. it holds at EVERY radius below
capacity (`badSet_subset_ratio_image`).

Specializing to the ladder stack over an antipodally closed power domain and
chaining through the Schur reduction and the spectrum fusion:

  **`#badSet(x^{k+1}, x^k, δ) ≤ ∑_{a ∈ A(h,k+1)} 2^a · C(h,a)`
     for EVERY `δ` with `k < (1−δ)n`** — the whole band from `0` to capacity,

with EQUALITY in the top band `k < (1−δ)n ≤ k+1`
(`boundary_slice_ladder_badSet_card`).  The ladder-stack bad-count curve is
therefore pinned: monotone below the spectrum mass everywhere, exactly the
spectrum mass at the deepest band before capacity.  Conditional only on the
in-tree signed-sum injectivity.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The all-radii forward inclusion**: at every radius below capacity
(`k < (1−δ)n`), for strongly far directions, every bad scalar is the residual
ratio of an injective `(k+1)`-tuple.  (The boundary-slice exact law's `⊆` half,
freed from its upper radius bound.) -/
theorem badSet_subset_ratio_image (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
      ⊆ (Finset.univ.filter
          (fun t : Fin (k+1) → Fin n => Function.Injective t)).image
        (fun t => -(residual dom k t u₀) / residual dom k t u₁) := by
  have hallres : ∀ t : Fin (k+1) → Fin n, Function.Injective t →
      residual dom k t u₁ ≠ 0 := by
    intro t htinj hres
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
    have hsub : Finset.univ.image t ⊆ agreeSet c u₁ := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcag a⟩
    have hcard : k + 1 ≤ (agreeSet c u₁).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ c hcC
    omega
  intro γ hγ
  obtain ⟨S, hsz, ⟨c, hcC, hag⟩, -⟩ := (Finset.mem_filter.mp hγ).2
  have hScard : k + 1 ≤ S.card := by
    have h1 : ((k : ℝ≥0)) < (S.card : ℝ≥0) := lt_of_lt_of_le hlo hsz
    have h2 : k < S.card := by exact_mod_cast h1
    omega
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hScard
  set t : Fin (k+1) → Fin n :=
    fun a => (S'.equivFin.symm (Fin.cast hS'card.symm a) : Fin n) with ht
  have htinj : Function.Injective t := by
    intro a b hab
    have h1 : (S'.equivFin.symm (Fin.cast hS'card.symm a))
        = S'.equivFin.symm (Fin.cast hS'card.symm b) := Subtype.ext hab
    have h2 := S'.equivFin.symm.injective h1
    exact Fin.cast_injective _ h2
  have htmem : ∀ a, t a ∈ S := fun a =>
    hS'sub (S'.equivFin.symm (Fin.cast hS'card.symm a)).2
  obtain ⟨P, hPdeg, rfl⟩ := hcC
  have hPdeg' : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0
      simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  have hlinezero : residual dom k t (fun i => u₀ i + γ * u₁ i) = 0 := by
    refine residual_eq_zero_of_extends dom k t hPdeg' fun a => ?_
    have := hag (t a) (htmem a)
    simpa [smul_eq_mul] using this.symm
  rw [residual_line] at hlinezero
  refine Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, htinj⟩, ?_⟩
  exact (gamma_eq_of_owned dom k t (hallres t htinj) hlinezero).symm

open ArkLib.ProximityGap.KKH26 in
open Classical in
/-- **THE FULL-BAND LADDER LAW**: at EVERY radius below capacity
(`k < (1−δ)n`), over the antipodally closed power domain, the ladder-stack bad
count is bounded by the spectrum mass — with equality in the top band
(`boundary_slice_ladder_badSet_card`).  Conditional only on the in-tree
signed-sum injectivity. -/
theorem ladder_badSet_card_le_spectrum_all_radii (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {g : F} {h : ℕ} (hn : n = 2 * h) (hh : g ^ h = -1)
    (hdom : ∀ i : Fin n, dom i = g ^ (i : ℕ))
    (hinj : Set.InjOn (spectrumVal g)
      (spectrumData h (validWeights h (k + 1)))) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)).card
      ≤ ∑ a ∈ validWeights h (k + 1), 2 ^ a * h.choose a := by
  -- the direction column has degree exactly k: farness is free
  have hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k := by
    have h := agreeSet_card_le_of_natDegree_eq dom hk
      (Q := X ^ k) (natDegree_X_pow k)
    simpa using h
  -- the tuple-level farness for the ratio rewriting
  have hallres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      residual dom k t (fun i => (dom i) ^ k) ≠ 0 := by
    intro t htinj hres
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
    have hsub : Finset.univ.image t ⊆ agreeSet c (fun i => (dom i) ^ k) := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcag a⟩
    have hcard : k + 1 ≤ (agreeSet c (fun i => (dom i) ^ k)).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ c hcC
    omega
  -- the ratio image is the negated subset-sum image (Schur reduction)
  have himg : (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
      (fun t => -(residual dom k t (fun i => (dom i) ^ (k + 1)))
        / residual dom k t (fun i => (dom i) ^ k))
      = (Finset.univ.powersetCard (k + 1)).image
        (fun S : Finset (Fin n) => -∑ i ∈ S, dom i) := by
    have h1 : (Finset.univ.filter
          (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
        (fun t => -(residual dom k t (fun i => (dom i) ^ (k + 1)))
          / residual dom k t (fun i => (dom i) ^ k))
        = (Finset.univ.filter
          (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
        (fun t => ∑ a, (fun i => -(dom i)) (t a)) := by
      refine Finset.image_congr fun t ht => ?_
      have htinj : Function.Injective t := by
        have := Finset.mem_coe.mp ht
        exact (Finset.mem_filter.mp this).2
      rw [ladder_ratio_eq dom hk t (hallres t htinj)]
      simp
    rw [h1, injTuple_image_sum_eq (fun i => -(dom i)) k]
    refine Finset.image_congr fun S _ => ?_
    simp
  -- chain: badSet ⊆ ratio image = negated-sum image, whose card is the mass
  calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)).card
      ≤ ((Finset.univ.filter
          (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
        (fun t => -(residual dom k t (fun i => (dom i) ^ (k + 1)))
          / residual dom k t (fun i => (dom i) ^ k))).card :=
        Finset.card_le_card (badSet_subset_ratio_image dom hk hlo hμ)
    _ = ((Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) => -∑ i ∈ S, dom i)).card := by rw [himg]
    _ = ∑ a ∈ validWeights h (k + 1), 2 ^ a * h.choose a := by
        -- the fusion count (negation absorption + exponent reindexing)
        have hneg : (Finset.univ.powersetCard (k + 1)).image
              (fun S : Finset (Fin n) => -∑ i ∈ S, dom i)
            = ((Finset.univ.powersetCard (k + 1)).image
              (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)).image
                (fun x => -x) := by
          rw [Finset.image_image]
          rfl
        rw [hneg, Finset.card_image_of_injective _ neg_injective]
        have himg2 : (Finset.univ.powersetCard (k + 1)).image
              (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)
            = ((range (2 * h)).powersetCard (k + 1)).image
              (fun S => ∑ j ∈ S, g ^ j) := by
          ext x
          simp only [Finset.mem_image, Finset.mem_powersetCard]
          constructor
          · rintro ⟨S, ⟨-, hcard⟩, rfl⟩
            refine ⟨S.image (fun i : Fin n => (i : ℕ)), ⟨?_, ?_⟩, ?_⟩
            · intro j hj
              obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
              rw [Finset.mem_range]
              have := i.2
              omega
            · rw [Finset.card_image_of_injective _ Fin.val_injective, hcard]
            · rw [Finset.sum_image fun i _ j _ hij => Fin.val_injective hij]
              exact (Finset.sum_congr rfl fun i _ => hdom i).symm
          · rintro ⟨T, ⟨hTsub, hTcard⟩, rfl⟩
            have hTn : ∀ m ∈ T, m < n := fun m hm => by
              have := Finset.mem_range.mp (hTsub hm)
              omega
            refine ⟨T.attachFin hTn, ⟨Finset.subset_univ _, ?_⟩, ?_⟩
            · rw [Finset.card_attachFin, hTcard]
            · have himgval : (T.attachFin hTn).image
                  (fun i : Fin n => (i : ℕ)) = T := by
                ext j
                simp only [Finset.mem_image]
                constructor
                · rintro ⟨i, hi, rfl⟩
                  exact (Finset.mem_attachFin hTn).mp hi
                · intro hj
                  exact ⟨⟨j, hTn j hj⟩, (Finset.mem_attachFin hTn).mpr hj, rfl⟩
              calc ∑ i ∈ T.attachFin hTn, dom i
                  = ∑ i ∈ T.attachFin hTn, g ^ (i : ℕ) :=
                    Finset.sum_congr rfl fun i _ => hdom i
                _ = ∑ j ∈ (T.attachFin hTn).image
                      (fun i : Fin n => (i : ℕ)), g ^ j :=
                    (Finset.sum_image
                      fun i _ j _ hij => Fin.val_injective hij).symm
                _ = ∑ j ∈ T, g ^ j := by rw [himgval]
        rw [himg2]
        exact subsetSum_image_card_eq g hh (k + 1) hinj

open ArkLib.ProximityGap.KKH26 in
open Classical in
omit [DecidableEq F] in
/-- Probability form of `ladder_badSet_card_le_spectrum_all_radii`: at every
radius below capacity, the ladder stack's `mcaEvent` probability is bounded by
the spectrum mass divided by the field size. -/
theorem ladder_mcaEvent_prob_le_spectrum_all_radii (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {g : F} {h : ℕ} (hn : n = 2 * h) (hh : g ^ h = -1)
    (hdom : ∀ i : Fin n, dom i = g ^ (i : ℕ))
    (hinj : Set.InjOn (spectrumVal g)
      (spectrumData h (validWeights h (k + 1)))) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ]
      ≤ (((∑ a ∈ validWeights h (k + 1), 2 ^ a * h.choose a : ℕ) : ℝ≥0) :
            ℝ≥0∞)
          / (((Fintype.card F : ℕ) : ℝ≥0) : ℝ≥0∞) := by
  rw [prob_uniform_eq_card_filter_div_card]
  gcongr
  exact ladder_badSet_card_le_spectrum_all_radii dom hk hlo hn hh hdom hinj

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.badSet_subset_ratio_image
#print axioms ProximityGap.Ownership.ladder_badSet_card_le_spectrum_all_radii
#print axioms ProximityGap.Ownership.ladder_mcaEvent_prob_le_spectrum_all_radii
