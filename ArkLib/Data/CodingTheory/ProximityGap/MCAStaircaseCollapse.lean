/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCASmoothJumpUnconditional
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.RadiusOne

/-!
# The staircase collapse law (#357 round 3): dead witnesses and the complete threshold

The round-3 probe measured that the high-rate bad count does **not** grow past the first
staircase rung: at `δ = 2/n` the maximum is still exactly `n` (F₇ and F₁₁, same maximizer
stack), far below the naive antichain ceiling. This file proves the mechanism and its
consequence — the **complete MCA landscape of the high-rate family at every radius and
every error target**.

## The dead-witness lemma (code-general)

`pairJointAgreesOn_of_card_le` — for ANY pair of words and ANY witness set with
`|S| ≤ k`, the joint-explanation clause holds automatically: each row separately admits a
degree-`< k` interpolant through its `≤ k` prescribed values (`Lagrange.interpolate`).
Hence `mcaEvent` can only fire with witnesses of size **≥ k+1**
(`witness_card_of_mcaEvent`): the δ-dependence of `ε_mca` freezes once the agreement floor
reaches `k+1`. Structurally, this is *why* the open window sits where it does: the live
radii are exactly those whose agreement floors lie strictly between `k+1` and Johnson.

## The high-rate collapse

For `k = n−2` the only live witnesses anywhere are the `n` erasures and `univ` — at every
radius. The antichain argument of `MCAAntichainEngine` therefore applies verbatim with no
radius hypothesis (`badScalar_card_le_card_high_rate`), giving
`ε_mca(RS[F,D,n−2], δ) ≤ n/q` for ALL `δ`; monotonicity from the exact jump value pins the
plateau (`epsMCA_rs_highRate_plateau`):

  `ε_mca(RS[F, μ_n, n−2], δ) = n/q for every δ ∈ [1/n, 1]`.

## The complete threshold function

* `ε* ∈ [1/q, n/q)` — `δ* = 1/n` (`mcaDeltaStar_rs_smooth_full_band`, landed);
* `ε* ≥ n/q` — every radius is good, so `δ* = 1` (`mcaDeltaStar_rs_highRate_top`).

`RS[F, μ_n, n−2]` is the **first code family whose MCA threshold function is determined at
every `(δ, ε*)`**, machine-checked. This also retro-explains the R1 probe's pure step
function (`epsMCA_rs_highRate_subgranularity`: `1/q` below the first rung, then `n/q`,
nothing else, all the way to `δ = 1`).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-3 staircase-collapse comment, probe data); `MCAAntichainEngine.lean`,
  `MCASmoothJumpUnconditional.lean`.
-/

set_option linter.unusedSectionVars false

open Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code ProximityGap.MCAThresholdLedger
open ProximityGap.MCAWitnessSpread ProximityGap.MCADeltaStarHighRateFamily
open ProximityGap.MCAAntichainEngine ProximityGap.MCASmoothJumpUnconditional
open ProximityGap.MCADeltaStarExactPoint

namespace ProximityGap.MCAStaircaseCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The dead-witness lemma -/

/-- Any word admits a codeword agreeing with it on any `≤ k` coordinates (Lagrange). -/
theorem exists_codeword_agreeing (domain : ι ↪ F) {k : ℕ} {S : Finset ι}
    (hS : S.card ≤ k) (u : ι → F) :
    ∃ w ∈ ReedSolomon.code domain k, ∀ i ∈ S, w i = u i := by
  classical
  have hinj : Set.InjOn domain ↑S := fun x _ y _ h => domain.injective h
  refine ⟨ReedSolomon.evalOnPoints domain (Lagrange.interpolate S domain u), ?_, ?_⟩
  · rw [ReedSolomon.mem_code_iff_exists_polynomial]
    refine ⟨Lagrange.interpolate S domain u, ?_, rfl⟩
    exact lt_of_lt_of_le (Lagrange.degree_interpolate_lt (r := u) hinj)
      (by exact_mod_cast hS)
  · intro i hi
    show (Lagrange.interpolate S domain u).eval (domain i) = u i
    exact Lagrange.eval_interpolate_at_node (r := u) hinj hi

/-- **The dead-witness lemma.** On any coordinate set of size `≤ k`, every pair of words
is jointly explainable — row-wise Lagrange interpolation. Code-general (RS of degree
bound `k`), radius-free. -/
theorem pairJointAgreesOn_of_card_le (domain : ι ↪ F) {k : ℕ} {S : Finset ι}
    (hS : S.card ≤ k) (u₀ u₁ : ι → F) :
    pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁ := by
  obtain ⟨v₀, hv₀, hag₀⟩ := exists_codeword_agreeing domain hS u₀
  obtain ⟨v₁, hv₁, hag₁⟩ := exists_codeword_agreeing domain hS u₁
  exact ⟨v₀, hv₀, v₁, hv₁, fun i hi => ⟨hag₀ i hi, hag₁ i hi⟩⟩

/-- **Witness floor.** `mcaEvent` witnesses always have `≥ k+1` coordinates: smaller sets
are dead (their `¬pairJointAgreesOn` clause is unsatisfiable). -/
theorem witness_card_of_mcaEvent (domain : ι ↪ F) {k : ℕ} {δ : ℝ≥0} {u₀ u₁ : ι → F}
    {S : Finset ι}
    (hno : ¬ pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁) :
    k + 1 ≤ S.card := by
  by_contra h
  exact hno (pairJointAgreesOn_of_card_le domain (by omega) u₀ u₁)

/-! ## The high-rate all-radii cap -/

open Classical in
/-- **The all-radii antichain cap.** For `k = n−2` the live witnesses at *every* radius
have `≥ n−1` coordinates, so the granularity antichain argument applies verbatim: at most
`n` bad scalars per stack, for every `δ`. -/
theorem badScalar_card_le_card_high_rate (domain : ι ↪ F) (hn : 3 ≤ Fintype.card ι)
    (u : WordStack F (Fin 2) ι) (δ : ℝ≥0) :
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F)
          (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) δ
          (u 0) (u 1) γ)).card
      ≤ Fintype.card ι := by
  classical
  set C := ReedSolomon.code domain (Fintype.card ι - 2) with hC
  set G := Finset.univ.filter
    (fun γ : F => mcaEvent (F := F) (C : Set (ι → F)) δ (u 0) (u 1) γ) with hG
  by_cases hu : ∃ γ ∈ G, ∃ w ∈ C, ∀ i, w i = u 0 i + γ • u 1 i
  · obtain ⟨γu, hγu, hwu⟩ := hu
    have hsub : G ⊆ {γu} := by
      intro γ hγ
      rw [Finset.mem_singleton]
      rw [hG, Finset.mem_filter] at hγ
      obtain ⟨-, S, hcard, hline, hno⟩ := hγ
      obtain ⟨w', hw', hag'⟩ := hwu
      exact bad_scalar_eq_of_witness_subset C (Finset.subset_univ S) hline hno
        ⟨w', hw', fun i _ => hag' i⟩
    calc G.card ≤ ({γu} : Finset F).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton γu
      _ ≤ Fintype.card ι := Fintype.card_pos
  · push Not at hu
    apply Finset.card_le_card_of_injOn (fun γ =>
      if h : mcaEvent (F := F) (C : Set (ι → F)) δ (u 0) (u 1) γ
      then (if hfull : h.choose = Finset.univ then Classical.arbitrary ι
        else (exists_notMem_of_ne_univ hfull).choose)
      else Classical.arbitrary ι)
    · intro γ _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro γ hγ γ' hγ' heq
      rw [Finset.mem_coe, hG, Finset.mem_filter] at hγ hγ'
      obtain ⟨-, hev⟩ := hγ
      obtain ⟨-, hev'⟩ := hγ'
      have hnu : hev.choose ≠ Finset.univ := by
        intro hfull
        obtain ⟨-, hline, -⟩ := hev.choose_spec
        rw [hfull] at hline
        obtain ⟨w, hw, hag⟩ := hline
        obtain ⟨i, hi⟩ := hu γ
          (by rw [hG, Finset.mem_filter]; exact ⟨Finset.mem_univ γ, hev⟩) w hw
        exact hi (hag i (Finset.mem_univ i))
      have hnu' : hev'.choose ≠ Finset.univ := by
        intro hfull
        obtain ⟨-, hline', -⟩ := hev'.choose_spec
        rw [hfull] at hline'
        obtain ⟨w, hw, hag⟩ := hline'
        obtain ⟨i, hi⟩ := hu γ'
          (by rw [hG, Finset.mem_filter]; exact ⟨Finset.mem_univ γ', hev'⟩) w hw
        exact hi (hag i (Finset.mem_univ i))
      simp only [dif_pos hev, dif_pos hev', dif_neg hnu, dif_neg hnu'] at heq
      set j := (exists_notMem_of_ne_univ hnu).choose with hjdef
      have hj : j ∉ hev.choose := (exists_notMem_of_ne_univ hnu).choose_spec
      have hj' : (exists_notMem_of_ne_univ hnu').choose ∉ hev'.choose :=
        (exists_notMem_of_ne_univ hnu').choose_spec
      rw [← heq] at hj'
      -- the dead-witness floor replaces the radius hypothesis
      have hsize : ∀ (S : Finset ι), j ∉ S →
          ¬ pairJointAgreesOn (C : Set (ι → F)) S (u 0) (u 1) →
          S = Finset.univ.erase j := by
        intro S hjS hnoS
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          exact Finset.mem_erase.mpr ⟨fun hxj => hjS (hxj ▸ hx), Finset.mem_univ x⟩
        · rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
          have hfloor := witness_card_of_mcaEvent (k := Fintype.card ι - 2)
            (δ := δ) domain hnoS
          omega
      have hS : hev.choose = Finset.univ.erase j :=
        hsize hev.choose hj hev.choose_spec.2.2
      have hS' : hev'.choose = Finset.univ.erase j :=
        hsize hev'.choose hj' hev'.choose_spec.2.2
      obtain ⟨-, hline, hno⟩ := hev.choose_spec
      obtain ⟨-, hline', -⟩ := hev'.choose_spec
      rw [hS] at hline hno
      rw [hS'] at hline'
      exact unique_bad_gamma_common_witness C (Finset.univ.erase j) (u 0) (u 1)
        hno hline hline'

open Classical in
/-- `ε_mca(RS[F,D,n−2], δ) ≤ n/q` at **every** radius. -/
theorem epsMCA_rs_highRate_le_all (domain : ι ↪ F) (hn : 3 ≤ Fintype.card ι) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) δ
      ≤ ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_card_high_rate domain hn u δ

/-! ## The plateau and the complete threshold function -/

omit [DecidableEq ι] [DecidableEq F] in
/-- **The sub-granularity branch:** for high-rate RS codes with `n ≥ 4`, every radius
strictly below the first lattice point has exactly the universal floor `1/q`.

Together with `epsMCA_rs_highRate_plateau`, this is the theorem form of the pure
high-rate step function: `1/q` below `1/n`, `n/q` from `1/n` onward (in the smooth-domain
setting of the plateau theorem). -/
theorem epsMCA_rs_highRate_subgranularity (domain : ι ↪ F) (hn : 4 ≤ Fintype.card ι)
    {δ : ℝ≥0} (hδ : δ < 1 / (Fintype.card ι : ℝ≥0)) :
    epsMCA (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) δ
      = 1 / (Fintype.card F : ℝ≥0∞) := by
  classical
  have hnpos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hδn : δ * (Fintype.card ι : ℝ≥0) < 1 := by
    have h := mul_lt_mul_of_pos_right hδ hnpos
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hnpos)] at h
  have hproper :
      (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) ≠ Set.univ :=
    rsCode_ne_univ domain (by omega) (by omega)
  exact epsMCA_eq_inv_card_of_small_radius
    (ReedSolomon.code domain (Fintype.card ι - 2)) hδn hproper

/-- **The plateau:** `ε_mca(RS[F, μ_n, n−2], δ) = n/q` for every `δ ≥ 1/n` (smooth domain,
antipodal pair, odd characteristic). -/
theorem epsMCA_rs_highRate_plateau (domain : ι ↪ F)
    (himg : Finset.univ.image domain = nthRootsFinset (Fintype.card ι) (1 : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ (Fintype.card ι))
    (hn : 4 ≤ Fintype.card ι)
    (hnF : ((Fintype.card ι : ℕ) : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) (hanti : domain b₂ = -domain b₁)
    {δ : ℝ≥0} (hδ : 1 / (Fintype.card ι : ℝ≥0) ≤ δ) :
    epsMCA (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) δ
      = ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm (epsMCA_rs_highRate_le_all domain (by omega) δ) ?_
  rw [← epsMCA_rs_smooth_jump_eq domain himg hζ hn hnF h2 hb hanti]
  exact epsMCA_mono _ hδ

/-- **The top branch of the threshold function:** for `ε* ≥ n/q` every radius is good, so
`δ* = 1`. -/
theorem mcaDeltaStar_rs_highRate_top (domain : ι ↪ F) (hn : 3 ≤ Fintype.card ι)
    {εstar : ℝ≥0∞}
    (hε : ((Fintype.card ι : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) εstar = 1 := by
  apply le_antisymm
  · exact csSup_le' (fun δ hδ => hδ.1)
  · apply le_csSup (mcaGoodRadii_bddAbove _ _)
    exact ⟨le_rfl, le_trans (epsMCA_rs_highRate_le_all domain hn 1) hε⟩

/-! ## Source audit -/

#print axioms exists_codeword_agreeing
#print axioms pairJointAgreesOn_of_card_le
#print axioms witness_card_of_mcaEvent
#print axioms badScalar_card_le_card_high_rate
#print axioms epsMCA_rs_highRate_le_all
#print axioms epsMCA_rs_highRate_subgranularity
#print axioms epsMCA_rs_highRate_plateau
#print axioms mcaDeltaStar_rs_highRate_top

end ProximityGap.MCAStaircaseCollapse
