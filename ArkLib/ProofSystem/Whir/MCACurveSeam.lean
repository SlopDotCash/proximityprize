/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCACurveEvent
import ArkLib.ProofSystem.Whir.MCAPairSeam

/-!
# The ℓ-ary curve seam: `hasMutualCorrAgreement` for the power generator from `ε_mcaCurve`

`MCAPairSeam.lean` closes the WHIR seam for the pair case (`parℓ = Fin 2`, affine-line
combiner `(1, γ)`). This file is the **ℓ-ary extension** (`parℓ = Fin L`, any `L ≥ 2`) for
the power generator `r ↦ (r^0, r^1, ..., r^{L−1})` — the "powers of z" general combination
the Hab25 paper (ePrint 2025/2110) notes can be proven similarly:

* `proximityCondition_imp_mcaEventCurve` — predicate bridge: WHIR's per-row
  `proximityCondition` at the power combiner `(γ^0, ..., γ^{L−1})` implies the ℓ-ary curve
  MCA event `mcaEventCurve` at the same scalar — the witness set transfers, and a per-row
  unmatched row kills any joint codeword stack;
* `Pr_proximityCondition_le_epsMCACurve` — its probability-level corollary against
  `epsMCACurve`;
* `hasMutualCorrAgreement_genRSC_of_epsMCACurve_le` — **the seam**: for the power generator
  `genRSC (Fin L) φ m exp` with `exp j = j`, any bound `ε_mcaCurve(C, L, δ) ≤ errStar δ` on
  the admissible range yields `hasMutualCorrAgreement (genRSC (Fin L) φ m exp) B* errStar`.
  Sampling the generator is parameter sampling (`pr_uniform_subtype_image`; the power map is
  injective via its `j = 1` coordinate, which needs `L ≥ 2`), and the stack-sup lands on
  `ε_mcaCurve`.

At `L = 2` this subsumes the pair seam: `epsMCACurve_two_eq_epsMCA` identifies the
hypothesis with the pair one (`hasMutualCorrAgreement_genRSC_pair_of_epsMCACurve_le`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι]

omit [Fintype F] [DecidableEq F] in
/-- **One-way bridge: WHIR `proximityCondition` ⟹ ℓ-ary curve `mcaEventCurve`.**

When `parℓ = Fin L` and the combiner is the power tuple `(γ^0, γ^1, ..., γ^{L−1})`, the
WHIR per-row event implies the ℓ-ary curve MCA event at the same scalar: the witness set
`S` and the codeword matching the combination transfer verbatim, and the per-row clause
(some row `f i` unmatched by *any* codeword on `S`) refutes any joint codeword stack —
its `i`-th row would be such a codeword. The ℓ-ary generalization of
`proximityCondition_imp_mcaEvent_affineLine`; as there, `δ < 1` keeps the witness set
nonempty so the per-row clause can be extracted. -/
lemma proximityCondition_imp_mcaEventCurve
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1) {L : ℕ}
    (f : Fin L → ι → F) (γ : F)
    (h : proximityCondition (parℓ := Fin L) f δ (fun j => γ ^ (j : ℕ)) C) :
    ProximityGap.mcaEventCurve (F := F) (A := F) ((C : Set (ι → F))) δ f γ := by
  obtain ⟨S, hS_card, u, hu_mem, h_inner⟩ := h
  -- `S` is nonempty: `S.card ≥ (1-δ)·n` with `δ < 1` and `n > 0`.
  have hn_pos : (0 : ℝ≥0) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h_pos : (0 : ℝ≥0) < (1 - δ) * Fintype.card ι :=
    mul_pos (tsub_pos_of_lt hδ) hn_pos
  have hS_nonempty : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hempty | hne
    · subst hempty
      simp only [Finset.card_empty, Nat.cast_zero] at hS_card
      exact absurd hS_card (not_le.mpr h_pos)
    · exact hne
  obtain ⟨s₀, hs₀⟩ := hS_nonempty
  obtain ⟨_, i, h_unmatched⟩ := h_inner s₀ hs₀
  refine ⟨S, hS_card, ⟨u, hu_mem, fun s hs => ?_⟩, ?_⟩
  · -- Clause (ii): `u s = ∑ j, γ^j • f j s` from `u s = ∑ j, γ^j * f j s`.
    obtain ⟨hu_eq, _⟩ := h_inner s hs
    simpa [smul_eq_mul] using hu_eq
  · -- Clause (iii): no joint codeword stack, because row `i` is unmatched.
    rintro ⟨v, hv_mem, hv_agree⟩
    obtain ⟨s, hs, hne⟩ := h_unmatched (v i) (hv_mem i)
    exact hne (hv_agree s hs i)

omit [DecidableEq F] in
/-- **Probability-level corollary of the ℓ-ary predicate bridge.** For any `L`-row stack
`f`, the probability over `γ ←$ᵖ F` of WHIR's `proximityCondition` with the power combiner
`(γ^0, ..., γ^{L−1})` is bounded by the ℓ-ary curve MCA error `epsMCACurve C L δ`. The
`Fin L` analogue of `Pr_proximityCondition_le_epsMCA`. -/
lemma Pr_proximityCondition_le_epsMCACurve
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1) {L : ℕ}
    (f : Fin L → ι → F) :
    Pr_{let γ ←$ᵖ F}[proximityCondition (parℓ := Fin L) f δ
        (fun j => γ ^ (j : ℕ)) C]
      ≤ ProximityGap.epsMCACurve (F := F) (A := F) ((C : Set (ι → F))) L δ := by
  refine le_trans ?_ (le_iSup
    (fun u : Code.WordStack F (Fin L) ι =>
      Pr_{let γ ←$ᵖ F}[ProximityGap.mcaEventCurve (F := F) (A := F)
        ((C : Set (ι → F))) δ u γ]) f)
  exact Pr_le_Pr_of_implies _ _ _
    (fun γ h => proximityCondition_imp_mcaEventCurve hδ f γ h)

open Classical in
/-- **The ℓ-ary curve seam.** For the power generator (`parℓ = Fin L`, `L ≥ 2`, exponents
`exp j = j`, combiner `(γ^0, ..., γ^{L−1})` with `γ` uniform), an `ε_mcaCurve`-bound on the
underlying smooth Reed–Solomon code yields `hasMutualCorrAgreement`:

  `ε_mcaCurve(C, L, δ) ≤ errStar δ` for `0 < δ < 1 − B*`
    ⟹ the generator has MCA `(B*, errStar)`.

Sampling the generator is parameter sampling (`pr_uniform_subtype_image`; injectivity of
`r ↦ (r^0, ..., r^{L−1})` reads off the `j = 1` coordinate, hence `L ≥ 2`), the per-row
event implies the ℓ-ary curve MCA event at the same scalar
(`proximityCondition_imp_mcaEventCurve`), and the stack sup is `ε_mcaCurve`. The ℓ-ary
extension of `hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le`. -/
theorem hasMutualCorrAgreement_genRSC_of_epsMCACurve_le
    {L : ℕ} (hL : 1 < L)
    (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin L ↪ ℕ)
    (hexp : ∀ j : Fin L, exp j = (j : ℕ))
    (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal)
    (heps : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      ProximityGap.epsMCACurve (F := F) (A := F)
        (((RSGenerator.genRSC (Fin L) φ m exp).C : Set (ι → F))) L δ ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin L) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin L) φ m exp).hℓ
    hasMutualCorrAgreement (RSGenerator.genRSC (Fin L) φ m exp) BStar errStar := by
  intro f δ hδ
  -- work at the literal `Fin L`; everything transfers by definitional unfolding of `genRSC`
  let fL : Fin L → ι → F := f
  let C : LinearCode ι F := smoothCode φ m
  -- the radius is below 1
  have hδ1 : δ < 1 := by
    have h2 := hδ.2
    have : (δ : ℝ) < 1 := lt_of_lt_of_le h2 (by linarith)
    exact_mod_cast this
  -- the power map and its injectivity (via the `j = 1` coordinate)
  set g : F → (Fin L → F) := fun r => fun j => r ^ (exp j) with hg_def
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := congrFun hab ⟨1, hL⟩
    have he : exp (⟨1, hL⟩ : Fin L) = 1 := hexp ⟨1, hL⟩
    simpa [hg_def, he] using h1
  haveI : Nonempty ↥(Finset.univ.image g) :=
    Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  -- sampling the generator is sampling the parameter
  have hpr := pr_uniform_subtype_image g hginj
    (fun r => proximityCondition fL δ r C)
  -- the sampled combiner is the power tuple
  have hcomb : ∀ γ : F, g γ = (fun j : Fin L => γ ^ (j : ℕ)) := by
    intro γ
    funext j
    simp [hg_def, hexp j]
  -- the per-scalar event implies the ℓ-ary curve MCA event
  have himp : ∀ γ : F, proximityCondition fL δ (g γ) C →
      ProximityGap.mcaEventCurve (F := F) (A := F)
        ((C : Set (ι → F))) δ fL γ := by
    intro γ h
    refine proximityCondition_imp_mcaEventCurve hδ1 fL γ ?_
    rwa [hcomb γ] at h
  have hmain : (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[
      proximityCondition fL δ (↑r) C]) ≤ errStar δ :=
    calc (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[proximityCondition fL δ (↑r) C])
        = Pr_{let γ ←$ᵖ F}[proximityCondition fL δ (g γ) C] := hpr
      _ ≤ Pr_{let γ ←$ᵖ F}[ProximityGap.mcaEventCurve (F := F) (A := F)
            ((C : Set (ι → F))) δ fL γ] :=
          Pr_le_Pr_of_implies _ _ _ himp
      _ ≤ ProximityGap.epsMCACurve (F := F) (A := F) ((C : Set (ι → F))) L δ :=
          le_iSup (fun u : Code.WordStack F (Fin L) ι =>
            Pr_{let γ ←$ᵖ F}[ProximityGap.mcaEventCurve (F := F) (A := F)
              ((C : Set (ι → F))) δ u γ]) fL
      _ ≤ errStar δ := heps δ hδ.1 hδ.2
  exact hmain

open Classical in
/-- **Consistency at `L = 2`: the curve seam subsumes the pair seam.** The pair-generator
MCA follows from an `ε_mcaCurve(C, 2, ·)`-bound via `epsMCACurve_two_eq_epsMCA` — the same
conclusion as `hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le`, with the curve-side
hypothesis. -/
theorem hasMutualCorrAgreement_genRSC_pair_of_epsMCACurve_le
    (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp : ∀ j : Fin 2, exp j = (j : ℕ))
    (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal)
    (heps : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      ProximityGap.epsMCACurve (F := F) (A := F)
        (((RSGenerator.genRSC (Fin 2) φ m exp).C : Set (ι → F))) 2 δ ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin 2) φ m exp).hℓ
    hasMutualCorrAgreement (RSGenerator.genRSC (Fin 2) φ m exp) BStar errStar :=
  hasMutualCorrAgreement_genRSC_of_epsMCACurve_le (by norm_num) φ m exp hexp
    BStar hB errStar heps

end MutualCorrAgreement

/-! ## Axiom audit — all kernel-clean. -/
#print axioms MutualCorrAgreement.proximityCondition_imp_mcaEventCurve
#print axioms MutualCorrAgreement.Pr_proximityCondition_le_epsMCACurve
#print axioms MutualCorrAgreement.hasMutualCorrAgreement_genRSC_of_epsMCACurve_le
#print axioms MutualCorrAgreement.hasMutualCorrAgreement_genRSC_pair_of_epsMCACurve_le
