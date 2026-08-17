/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.ListDecoding.JH01
import ArkLib.Data.CodingTheory.ListDecoding.AGL23Barrier
import ArkLib.Data.CodingTheory.ListDecoding.CZ25CapacityReduction
import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.BKR06FiberCount
import ArkLib.ToMathlib.BKR06Injection
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Combinatorial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# List-decoding bounds from ABF26 §3 — random RS domains & general lower bounds

Random Reed-Solomon domains (ABF26 §3.1, [AGL24]) and the general §3.2 lower-bound
statements, including the MS77 Hamming-ball-volume ingredient and the `ABF26C38`
development. Part 1 of the `Bounds` split; see the `Bounds.lean` umbrella for the
full overview and quantification conventions.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open ListDecodable

/-! ## Random Reed-Solomon domains — ABF26 §3.1 ([AGL24]) -/

section RandomReedSolomon

/-- **ABF26 Theorem 3.6 [AGL24 Thm 1.1], statement front door.**

For a finite field `F`, a positive length `n ≤ |F|`, and a uniformly sampled size-`n`
evaluation domain `L ⊆ F`, the random Reed-Solomon code `RS[F,L,k]` is list-decodable at the
capacity-near radius `1 - k/n - η` with failure probability at most `failure`.

The theorem's quantitative choices for `listBound` and `failure` are intentionally explicit
parameters here: this definition records the faithful probability space and RS-family target,
while the AGL24 first-moment/probabilistic proof remains external. -/
noncomputable def random_rs_list_decoding
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k listBound : ℕ) (η : ℝ) (failure : ENNReal)
    (_hn_pos : 0 < n) (hn : n ≤ Fintype.card F) : Prop := by
  classical
  exact
    Pr_{let L ← Probability.uniformSizeSubsetOfLe F n hn}[
      ¬ (Lambda
          ((ReedSolomon.code (Probability.SizeSubset.toEmbedding L) k : Set (L → F)))
          (1 - (k : ℝ) / (n : ℝ) - η) ≤ (listBound : ℕ∞))] ≤ failure
  -- Missing ingredient: AGL24's random-RS near-capacity list-decoding theorem.  The
  -- probability space is now in-tree (`uniformSizeSubsetOfLe`), but the proof bounding the
  -- bad-domain probability and instantiating the paper's concrete `listBound`/`failure`
  -- parameters is still external.

end RandomReedSolomon

section LowerBounds_General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- For any fixed center over a finite alphabet, the number of words in the corresponding
Hamming ball is `hammingBallVolume`. The count is pure Hamming-distance combinatorics and does
not require a field structure. -/
theorem card_filter_hammingDist_le_eq_hammingBallVolume
    {A : Type} [Fintype A] [DecidableEq A] (c : ι → A) (δ : ℝ) :
    (Finset.univ.filter
        (fun f : ι → A => hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊)).card =
      hammingBallVolume (Fintype.card A) δ (Fintype.card ι) := by
  rw [hammingBallVolume_eq_ncard_hammingBall δ c, ← Set.ncard_coe_finset]
  congr 1
  ext f
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
    ListDecodable.hammingBall]
  congr!

/-- **Alphabet-generic averaging identity.** Summing point-list sizes over all received words
counts every codeword once for each center in its Hamming ball, hence
`∑ f, |Λ(C, δ, f)| = |C| · Vol_q(δ, n)`. -/
theorem sum_ncard_closeCodewordsRel_eq_of_set
    {A : Type} [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑ f : ι → A, (closeCodewordsRel C f δ).ncard =
      C.ncard * hammingBallVolume (Fintype.card A) δ (Fintype.card ι) := by
  haveI : DecidablePred (fun c : ι → A => c ∈ C) := fun c => Classical.dec _
  set n : ℕ := Fintype.card ι with hn_def
  set r : ℕ := ⌊δ * (n : ℝ)⌋₊ with hr_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hbridge : ∀ f c : ι → A,
      (c ∈ closeCodewordsRel C f δ) ↔ (c ∈ C ∧ hammingDist f c ≤ r) := by
    intro f c
    simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq]
    refine and_congr_right (fun _ => ?_)
    simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
    rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ)), hr_def,
      ← hn_def, Nat.le_floor_iff (mul_nonneg hδ (Nat.cast_nonneg n))]
    congr!
  have hncard : ∀ f : ι → A,
      (closeCodewordsRel C f δ).ncard =
        (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card := by
    intro f
    rw [← Set.ncard_coe_finset]
    congr 1
    ext c
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hbridge f c
  simp_rw [hncard, Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ c : ι → A,
      (∑ f : ι → A, if c ∈ C ∧ hammingDist f c ≤ r then (1 : ℕ) else 0) =
        if c ∈ C then hammingBallVolume (Fintype.card A) δ n else 0 := by
    intro c
    by_cases hc : c ∈ C
    · simp only [hc, true_and, if_true]
      rw [← Finset.card_filter, hammingBallVolume_eq_ncard_hammingBall δ c,
        ← Set.ncard_coe_finset]
      congr 1
      ext f
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        ListDecodable.hammingBall]
      rw [hr_def, ← hn_def, hammingDist_comm]
      congr!
    · simp only [hc, false_and, if_false, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun c _ => hinner c), ← Finset.sum_filter, Finset.sum_const,
    smul_eq_mul]
  have hcardC : (Finset.univ.filter (fun c => c ∈ C)).card = C.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext c
    simp
  rw [hcardC, hn_def]

/-- Field-linear specialization of `sum_ncard_closeCodewordsRel_eq_of_set`. -/
theorem sum_ncard_closeCodewordsRel_eq
    (C : Submodule F (ι → F)) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑ f : ι → F, (closeCodewordsRel (C : Set (ι → F)) f δ).ncard =
      (C : Set (ι → F)).ncard *
        hammingBallVolume (Fintype.card F) δ (Fintype.card ι) :=
  sum_ncard_closeCodewordsRel_eq_of_set (C : Set (ι → F)) δ hδ

/-- **ABF26 Lemma 3.7 [Eli57].** Elias volume lower bound on list size for an arbitrary
finite-alphabet code:

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |A|`, `n = |ι|`, and the explicit cardinality hypothesis gives `|C| = q^k`.
**Proven** by the paper's averaging argument (fulltext §3, [Eli57]):
the maximised list size dominates the mean over received words, and double counting gives
`∑_f |Λ(C,δ,f)| = ∑_{c∈C} Vol_q(δ,n) = q^k · Vol_q(δ,n)`, so the max is `≥ Vol/q^{n-k}`.
Uses `hammingBallVolume` (ABF26 D2.4) and `hammingBallVolume_eq_ncard_hammingBall` from
`HammingBallVolume.lean`. Linearity is not used; the field-linear specialization below supplies
the cardinality hypothesis using `Module.card_eq_pow_finrank`. -/
theorem lambda_ge_elias_volume_eli57
    {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℝ)
          / (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) - k))
      ≤ (Lambda C δ : ENNReal) := by
  classical
  set q : ℕ := Fintype.card A with hq_def
  set n : ℕ := Fintype.card ι with hn_def
  set Vol : ℕ := hammingBallVolume q δ n with hVol_def
  have hδ_nonneg : (0 : ℝ) ≤ δ := le_of_lt _hδ_pos
  have hsum : ∑ f : ι → A, (closeCodewordsRel C f δ).ncard = q ^ k * Vol := by
    rw [sum_ncard_closeCodewordsRel_eq_of_set C δ hδ_nonneg, hcard, hVol_def]
  -- Choose a received word attaining the maximum point-list size.
  obtain ⟨f₀, -, hf₀max⟩ := Finset.exists_max_image Finset.univ
    (fun f => (closeCodewordsRel C f δ).ncard)
    Finset.univ_nonempty
  set s₀ : ℕ := (closeCodewordsRel C f₀ δ).ncard with hs₀_def
  have hsum_le :
      (∑ f : ι → A, (closeCodewordsRel C f δ).ncard) ≤ q ^ n * s₀ := by
    have hcard_univ : (Finset.univ : Finset (ι → A)).card = q ^ n := by
      rw [Finset.card_univ, Fintype.card_fun]
    calc (∑ f : ι → A, (closeCodewordsRel C f δ).ncard)
        ≤ (Finset.univ : Finset (ι → A)).card • s₀ :=
          Finset.sum_le_card_nsmul _ _ _ (fun f _ => hf₀max f (Finset.mem_univ f))
      _ = q ^ n * s₀ := by rw [hcard_univ, smul_eq_mul]
  -- Combine: q^k · Vol ≤ q^n · s₀.
  have hnat : q ^ k * Vol ≤ q ^ n * s₀ := hsum ▸ hsum_le
  -- Pass to reals and isolate `Vol / q^{n-k} ≤ s₀`.
  have hqr_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  set P : ℝ := (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) with hP_def
  have hP_pos : 0 < P := Real.rpow_pos_of_pos hqr_pos _
  have hqk_pos : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqr_pos k
  have hpow : (q : ℝ) ^ n = (q : ℝ) ^ k * P := by
    rw [hP_def, ← Real.rpow_natCast (q : ℝ) n, ← Real.rpow_natCast (q : ℝ) k,
      ← Real.rpow_add hqr_pos]
    congr 1; ring
  have hM_le : (Vol : ℝ) / P ≤ (s₀ : ℝ) := by
    rw [div_le_iff₀ hP_pos]
    have h1 : (q : ℝ) ^ k * (Vol : ℝ) ≤ (q : ℝ) ^ n * (s₀ : ℝ) := by
      exact_mod_cast hnat
    rw [hpow] at h1
    have h2 : (q : ℝ) ^ k * (Vol : ℝ)
        ≤ (q : ℝ) ^ k * ((s₀ : ℝ) * P) := by
      have heq : (q : ℝ) ^ k * ((s₀ : ℝ) * P) = (q : ℝ) ^ k * P * (s₀ : ℝ) := by ring
      rw [heq]; exact h1
    exact le_of_mul_le_mul_left h2 hqk_pos
  -- Lift to `ℝ≥0∞`: the maximised list at `f₀` already realises the bound.
  simp only [Lambda, ENat.toENNReal_iSup]
  refine le_iSup_of_le f₀ ?_
  rw [← hs₀_def]
  have hcast : ENat.toENNReal ((s₀ : ℕ) : ℕ∞) = ENNReal.ofReal (s₀ : ℝ) := by
    rw [ENNReal.ofReal_natCast]; simp
  rw [hcast]
  exact ENNReal.ofReal_le_ofReal hM_le

/-- **ABF26 Lemma 3.7 [Eli57] for a field-linear code.** This preserves the original
field-linear API as a specialization of `lambda_ge_elias_volume_eli57`; linearity enters only
through the identity `|C| = |F| ^ finrank F C`. -/
theorem linear_lambda_ge_elias_volume_eli57
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  apply lambda_ge_elias_volume_eli57 (C := (C : Set (ι → F)))
    (k := Module.finrank F C) (δ := δ) ?_ _hδ_pos _hδ_lt
  classical
  haveI : Fintype (↥C) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank (K := F) (V := ↥C)

/-! ### MS77 Hamming-ball volume bound (ingredient (★) for C3.8 below).

The classical MacWilliams–Sloane volume estimate is stated for an *integer* radius
`δ·n`. Off the lattice `δ·n ∈ ℕ` the inequality `q^{n·H_q(δ)}/√(8nδ(1−δ)) ≤ Vol_q(δ,n)`
is genuinely **false**: `Vol_q(δ,n)` is a step function of `δ` (it changes only at
`δ = k/n`, via `⌊δn⌋`), while the LHS is strictly increasing in `δ`. Concretely with
`q=2, n=4, δ=0.49`: `⌊0.49·4⌋ = 1`, `Vol = C(4,0)+C(4,1) = 5`, yet
`2^{4·H₂(0.49)}/√(8·4·0.49·0.51) ≈ 5.65 > 5`. (Cf. the `subspaceDesign_tau_lower`
countermodel-documented style.) So the faithful MS77 statement carries the lattice
hypothesis `δ·n = ⌊δ·n⌋₊` — the minimal correct reading of [MS77, Ch.10 Lem 7].

Everything below proves `(★)` at lattice points. The whole bound collapses, `q`-independently,
to one Stirling inequality `stirlingSeq k · stirlingSeq (n−k) ≤ 2 · stirlingSeq n`
(`1 ≤ k ≤ n−1`), which is discharged via mathlib's `Real.sqrt_pi_le_stirlingSeq` lower bound,
a ported Robbins upper bound `stirlingSeq m ≤ √π·e^{1/(12m)}`, and exact handling of the
three tight corners `(n,k) ∈ {(2,1),(3,1),(3,2)}` (with `(2,1)` an exact equality
`stirlingSeq(1)² = 2·stirlingSeq(2) = e²/2`). -/

namespace ABF26C38

open scoped Real Nat Topology
open Real Stirling Filter

-- ===== Robbins upper bound (proven) =====
theorem robbins_upper {m : ℕ} (hm : m ≠ 0) :
    stirlingSeq m ≤ √π * Real.exp (1 / (12 * m)) := by
  set H : ℕ → ℝ := fun n =>
      Real.log (stirlingSeq (n + 1)) - Real.log (√π) -
        1 / (12 * ((n : ℝ) + 1))
    with hH
  have hsqrtπ_pos : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hmono : Monotone H := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [hH]
    have hdiff := log_stirlingSeq_diff_le (n + 1)
    have htel : (1 : ℝ) / (12 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      field_simp; ring
    have hdiff' : Real.log (stirlingSeq (n + 1)) - Real.log (stirlingSeq (n + 2)) ≤
        1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
      rw [← htel]; convert hdiff using 2; push_cast; ring
    change Real.log (stirlingSeq (n + 1)) - Real.log (√π) -
          1 / (12 * ((n : ℝ) + 1)) ≤
        Real.log (stirlingSeq (n + 1 + 1)) - Real.log (√π) -
          1 / (12 * (((n + 1 : ℕ) : ℝ) + 1))
    have hidx : (n + 1 + 1) = (n + 2) := by ring
    rw [hidx]
    have hpush : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
    rw [hpush]; linarith [hdiff']
  have htend : Tendsto H atTop (𝓝 (0 : ℝ)) := by
    have hss : Tendsto (fun n : ℕ => stirlingSeq (n + 1)) atTop (𝓝 (√π)) :=
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
    have hlog : Tendsto (fun n : ℕ => Real.log (stirlingSeq (n + 1))) atTop (𝓝 (Real.log (√π))) :=
      (Real.continuousAt_log hsqrtπ_pos.ne').tendsto.comp hss
    have hrec : Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
      have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have : Tendsto (fun n : ℕ => (1 / 12) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((1/12) * 0)) :=
        hbase.const_mul (1/12)
      simp only [mul_zero] at this
      refine this.congr (fun n => ?_)
      rw [mul_one_div, one_div, one_div, mul_inv]; ring
    have hcomb : Tendsto (fun n : ℕ =>
        Real.log (stirlingSeq (n + 1)) - Real.log (√π) - 1 / (12 * ((n : ℝ) + 1)))
        atTop (𝓝 (Real.log (√π) - Real.log (√π) - 0)) :=
      (hlog.sub_const _).sub hrec
    have hz : Real.log (√π) - Real.log (√π) - 0 = 0 := by ring
    rw [hz] at hcomb; exact hcomb
  have hle := hmono.ge_of_tendsto htend
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hj := hle j
  simp only [hH] at hj
  have hlog_le : Real.log (stirlingSeq (j + 1)) ≤ Real.log (√π) + 1 / (12 * ((j : ℝ) + 1)) := by
    linarith
  have hss_pos : 0 < stirlingSeq (j + 1) := stirlingSeq'_pos j
  have hrhs_pos : 0 < √π * Real.exp (1 / (12 * ((j : ℝ) + 1))) := by positivity
  have hgoal : stirlingSeq (j + 1) ≤ √π * Real.exp (1 / (12 * ((j : ℝ) + 1))) := by
    rw [← Real.log_le_log_iff hss_pos hrhs_pos]
    rw [Real.log_mul hsqrtπ_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith [hlog_le]
  have hcast_m : ((((j : ℕ) + 1 : ℕ) : ℝ)) = ((j : ℝ) + 1) := by push_cast; ring
  rw [hcast_m]; exact hgoal

-- ===== closed forms =====
theorem ss2_eq : stirlingSeq 2 = Real.exp 1 ^ 2 / 4 := by
  have h : stirlingSeq 2 = 2 / (√4 * (2 / Real.exp 1) ^ 2) := by
    rw [stirlingSeq]; norm_num [Nat.factorial]
  rw [h]
  have h4 : √(4 : ℝ) = 2 := by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  field_simp; ring

theorem ss3_eq : stirlingSeq 3 = 2 * Real.exp 1 ^ 3 / (9 * √6) := by
  have h : stirlingSeq 3 = 6 / (√6 * (3 / Real.exp 1) ^ 3) := by
    rw [stirlingSeq]; norm_num [Nat.factorial]
  rw [h]
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have h6 : √(6:ℝ) ≠ 0 := by positivity
  field_simp; ring

-- ===== generic numeric =====
theorem sqrtpi_exp_le_two : √π * Real.exp (1/9) ≤ 2 := by
  have he : Real.exp (1/9) ≤ 9/8 := by
    have h : (1 : ℝ) - (1/9) ≤ Real.exp (-(1/9)) := by
      have := Real.add_one_le_exp (-(1/9 : ℝ)); linarith
    rw [Real.exp_neg] at h
    have hexp_pos : 0 < Real.exp (1/9) := Real.exp_pos _
    have hmul : (1 - 1/9) * Real.exp (1/9) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h hexp_pos.le
      rwa [inv_mul_cancel₀ hexp_pos.ne'] at this
    nlinarith [hexp_pos, hmul]
  have hs : √π ≤ 16/9 := by
    have hπ : π < 3.15 := Real.pi_lt_d2
    have : π ≤ (16/9 : ℝ)^2 := by rw [show ((16:ℝ)/9)^2 = 256/81 by norm_num]; nlinarith
    calc √π ≤ √((16/9:ℝ)^2) := Real.sqrt_le_sqrt this
      _ = 16/9 := by rw [Real.sqrt_sq (by norm_num)]
  have he_nonneg : 0 ≤ Real.exp (1/9) := (Real.exp_pos _).le
  calc √π * Real.exp (1/9) ≤ (16/9) * (9/8) := by
        apply mul_le_mul hs he he_nonneg (by norm_num)
    _ = 2 := by norm_num

-- ===== CORE LEMMA =====
-- For k ≥ 1, j ≥ 1: stirlingSeq k * stirlingSeq j ≤ 2 * stirlingSeq (k+j)
theorem core_stirling_add {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    stirlingSeq k * stirlingSeq j ≤ 2 * stirlingSeq (k + j) := by
  have hsqrtπ_pos : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  -- corner (1,1)
  by_cases h11 : k = 1 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h11
    -- ss1 * ss1 = e²/2 = 2·ss2
    have hsum2 : (1:ℕ) + 1 = 2 := rfl
    rw [hsum2, stirlingSeq_one, ss2_eq]
    -- e/√2 * (e/√2) = e²/2 = 2 * (e²/4); exact equality
    have h2 : √(2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h2pos : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have heq : Real.exp 1 / √2 * (Real.exp 1 / √2) = 2 * (Real.exp 1 ^ 2 / 4) := by
      rw [div_mul_div_comm]
      have hden : √(2:ℝ) * √2 = 2 := by nlinarith [h2]
      rw [hden]; ring
    rw [heq]
  -- corner (1,2) or (2,1)
  by_cases h12 : (k = 1 ∧ j = 2) ∨ (k = 2 ∧ j = 1)
  · have hval : stirlingSeq k * stirlingSeq j = Real.exp 1 / √2 * (Real.exp 1 ^ 2 / 4) := by
      rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [stirlingSeq_one, ss2_eq]
      · rw [stirlingSeq_one, ss2_eq]; ring
    have hsum : k + j = 3 := by rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [hval, hsum, ss3_eq]
    -- e/√2 * e²/4 ≤ 2 · (2 e³/(9√6))   ⟺   486 ≤ 512  after clearing radicals
    have h2 : √(2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h6 : √(6:ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h2pos : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have h6pos : 0 < √(6:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    have he3 : 0 < Real.exp 1 ^ 3 := by positivity
    -- key radical inequality: 9√6 ≤ 16√2  (square: 486 ≤ 512)
    have hrad : 9 * √(6:ℝ) ≤ 16 * √(2:ℝ) := by
      nlinarith [h2, h6, h2pos, h6pos, Real.sqrt_nonneg (2:ℝ), Real.sqrt_nonneg (6:ℝ),
        mul_pos h2pos h6pos]
    -- LHS = e³/(4√2), RHS = 4e³/(9√6).
    have hLeq : Real.exp 1 / √2 * (Real.exp 1 ^ 2 / 4) = Real.exp 1 ^ 3 / (4 * √2) := by
      rw [show Real.exp 1 ^ 3 = Real.exp 1 * Real.exp 1 ^ 2 by ring]
      field_simp
    have hReq : 2 * (2 * Real.exp 1 ^ 3 / (9 * √6)) = 4 * Real.exp 1 ^ 3 / (9 * √6) := by
      ring
    rw [hLeq, hReq]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- e³ * (9√6) ≤ (4 e³) * (4 √2) = 16 e³ √2;  use hrad and e³ ≥ 0
    nlinarith [hrad, he3, mul_le_mul_of_nonneg_left hrad he3.le]
  -- generic case: 1/k + 1/j ≤ 4/3
  · have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hkpos : (0:ℝ) < (k:ℝ) := by linarith
    have hjpos : (0:ℝ) < (j:ℝ) := by linarith
    -- robbins on k and j
    have hrk := robbins_upper (m := k) (by omega)
    have hrj := robbins_upper (m := j) (by omega)
    have hssk : 0 ≤ stirlingSeq k := (sqrt_pi_le_stirlingSeq (by omega)).trans' hsqrtπ_pos.le
    have hssj : 0 ≤ stirlingSeq j := (sqrt_pi_le_stirlingSeq (by omega)).trans' hsqrtπ_pos.le
    -- ss k * ss j ≤ (√π e^{1/12k}) (√π e^{1/12j}) = π e^{1/12k+1/12j}
    have hprod : stirlingSeq k * stirlingSeq j ≤
        (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j))) :=
      mul_le_mul hrk hrj hssj (by positivity)
    -- exponent ≤ 1/9
    have hexp_le : 1/(12*(k:ℝ)) + 1/(12*(j:ℝ)) ≤ 1/9 := by
      -- equivalent to 1/k + 1/j ≤ 4/3
      have hsum_le : 1/(k:ℝ) + 1/(j:ℝ) ≤ 4/3 := by
        -- enumerate the non-corner cases
        rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · interval_cases k
          · -- k = 1; then j ≥ 3 (since not (1,1),(1,2))
            have hj3 : 3 ≤ j := by
              rcases Nat.lt_or_ge j 3 with hj3 | hj3
              · interval_cases j
                · exact absurd ⟨rfl, rfl⟩ h11
                · exact absurd (Or.inl ⟨rfl, rfl⟩) h12
              · exact hj3
            have hjle : (1:ℝ)/(j:ℝ) ≤ 1/3 := by
              rw [div_le_div_iff₀ hjpos (by norm_num)]
              have : (3:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj3
              linarith
            simp only [Nat.cast_one, div_one]
            linarith
          · -- k = 2; then j ≥ 2 (since not (2,1))
            have hj2 : 2 ≤ j := by
              rcases Nat.lt_or_ge j 2 with hj2 | hj2
              · interval_cases j
                · exact absurd (Or.inr ⟨rfl, rfl⟩) h12
              · exact hj2
            have hjle : (1:ℝ)/(j:ℝ) ≤ 1/2 := by
              rw [div_le_div_iff₀ hjpos (by norm_num)]
              have : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj2
              linarith
            have hcast2 : ((2:ℕ):ℝ) = 2 := by norm_num
            rw [hcast2]
            linarith
        · -- k ≥ 3; 1/k ≤ 1/3, 1/j ≤ 1
          have hk3r : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk3
          have h1 : (1:ℝ)/(k:ℝ) ≤ 1/3 := by
            rw [div_le_div_iff₀ hkpos (by norm_num)]; linarith
          have h2 : (1:ℝ)/(j:ℝ) ≤ 1 := by
            rw [div_le_one hjpos]; linarith
          linarith
      -- now scale by 1/12
      have e1 : 1/(12*(k:ℝ)) = (1/12) * (1/(k:ℝ)) := by ring
      have e2 : 1/(12*(j:ℝ)) = (1/12) * (1/(j:ℝ)) := by ring
      rw [e1, e2]
      nlinarith [hsum_le]
    -- assemble: π e^{exp} ≤ π e^{1/9} = √π (√π e^{1/9}) ≤ √π · 2 = 2√π ≤ 2 ss(k+j)
    have hmono_exp : Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) ≤ Real.exp (1/9) :=
      Real.exp_le_exp.mpr hexp_le
    have hπsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
    have hstep1 : (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j)))
        = π * Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := by
      have hcomb : Real.exp (1/(12*(k:ℝ))) * Real.exp (1/(12*(j:ℝ)))
          = Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := (Real.exp_add _ _).symm
      calc (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j)))
          = (√π * √π) * (Real.exp (1/(12*(k:ℝ))) * Real.exp (1/(12*(j:ℝ)))) := by ring
        _ = π * Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := by rw [hπsq, hcomb]
    have hge : √π ≤ stirlingSeq (k + j) := sqrt_pi_le_stirlingSeq (by omega)
    calc stirlingSeq k * stirlingSeq j
        ≤ (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j))) := hprod
      _ = π * Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := hstep1
      _ ≤ π * Real.exp (1/9) := by
            apply mul_le_mul_of_nonneg_left hmono_exp Real.pi_pos.le
      _ = √π * (√π * Real.exp (1/9)) := by rw [← mul_assoc, hπsq]
      _ ≤ √π * 2 := by apply mul_le_mul_of_nonneg_left sqrtpi_exp_le_two hsqrtπ_pos.le
      _ = 2 * √π := by ring
      _ ≤ 2 * stirlingSeq (k + j) := by linarith [hge]

-- ===== Stirling/binomial collapse for the MS77 reduction =====

-- factorial in terms of stirlingSeq, for m ≥ 1
theorem fact_eq_ss {m : ℕ} (hm : 1 ≤ m) :
    (m ! : ℝ) = stirlingSeq m * (√(2 * m) * (m / Real.exp 1) ^ m) := by
  rw [stirlingSeq]
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hsq : (0:ℝ) < √(2 * (m:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hden : √(2 * (m:ℝ)) * ((m:ℝ) / Real.exp 1) ^ m ≠ 0 := by positivity
  field_simp

-- radical collapse: √(8Kj/(K+j)) * √(2(K+j)) = 2 * (√(2K) * √(2j))
theorem radical_collapse (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    √(8 * (K:ℝ) * j / (K + j)) * √(2 * ((K:ℝ) + j))
      = 2 * (√(2 * (K:ℝ)) * √(2 * (j:ℝ))) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKj : (0:ℝ) < (K:ℝ) + j := by positivity
  have hKjmul : (0:ℝ) ≤ (K:ℝ) * j := by positivity
  -- LHS = √(8Kj/(K+j) · 2(K+j)) = √(16Kj) = 4 √(Kj)
  have hL : √(8 * (K:ℝ) * j / (K + j)) * √(2 * ((K:ℝ) + j)) = 4 * √((K:ℝ) * j) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (8 * (K:ℝ) * j / (K + j) * (2 * (K + j))) = 16 * (K * j) by field_simp; ring]
    rw [show (16 : ℝ) * ((K:ℝ) * j) = (4:ℝ)^2 * ((K:ℝ) * j) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  -- RHS = 2 √(2K·2j) = 2 √(4Kj) = 4 √(Kj)
  have hR : 2 * (√(2 * (K:ℝ)) * √(2 * (j:ℝ))) = 4 * √((K:ℝ) * j) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (2 * (K:ℝ) * (2 * j)) = (2:ℝ)^2 * ((K:ℝ) * j) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  rw [hL, hR]

-- Power identity splitting `((K+j)/e)^(K+j)` into binomial and Stirling-scale factors.
theorem power_identity (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    (((K:ℝ) + j) / Real.exp 1) ^ (K + j)
      = ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j)
        * (((K:ℝ) / Real.exp 1) ^ K * ((j:ℝ) / Real.exp 1) ^ j) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [pow_add]
  rw [show ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j)
        * (((K:ℝ) / Real.exp 1) ^ K * ((j:ℝ) / Real.exp 1) ^ j)
      = ((((K:ℝ)+j)/K) * ((K:ℝ) / Real.exp 1))^K
        * ((((K:ℝ)+j)/j) * ((j:ℝ) / Real.exp 1))^j by
        rw [mul_pow, mul_pow]; ring]
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

-- choose as a real ratio of factorials
theorem choose_real (K j : ℕ) :
    (Nat.choose (K + j) K : ℝ) = ((K + j)! : ℝ) / ((K ! : ℝ) * (j ! : ℝ)) := by
  have h : Nat.choose (K + j) K * K ! * j ! = (K + j)! := by
    have h0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right K j)
    rwa [Nat.add_sub_cancel_left] at h0
  have hKf : (0:ℝ) < (K ! : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hjf : (0:ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hcast : ((Nat.choose (K + j) K : ℝ) * (K ! : ℝ)) * (j ! : ℝ) = ((K + j)! : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at this
    linarith [this]
  field_simp
  linarith [hcast]

-- master equation
theorem master_eq (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    √(8 * (K:ℝ) * j / (K + j)) * (Nat.choose (K + j) K : ℝ)
      = (2 * stirlingSeq (K + j) / (stirlingSeq K * stirlingSeq j))
        * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKf : (0:ℝ) < (K ! : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hjf : (0:ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hssK : 0 < stirlingSeq K := by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    exact stirlingSeq'_pos K'
  have hssj : 0 < stirlingSeq j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact stirlingSeq'_pos j'
  -- expand choose and factorials
  rw [choose_real]
  rw [fact_eq_ss (m := K + j) (by omega), fact_eq_ss (m := K) hK, fact_eq_ss (m := j) hj]
  -- handle radical and power separately.  Push casts on (K+j).
  have hcast_add : (((K + j : ℕ)) : ℝ) = (K:ℝ) + j := by push_cast; ring
  rw [hcast_add]
  -- Now substitute the power identity for ((K+j)/e)^(K+j).
  rw [power_identity K j hK hj]
  -- And the radical collapse.
  -- LHS is reduced by splitting the power term and collapsing the radical factor.
  -- Goal is an equality of reals; field_simp + the radical_collapse relation + ring.
  have hrad := radical_collapse K j hK hj
  -- denominators nonzero
  have hpowK : ((K:ℝ) / Real.exp 1) ^ K ≠ 0 := by positivity
  have hpowj : ((j:ℝ) / Real.exp 1) ^ j ≠ 0 := by positivity
  have hsqK : √(2 * (K:ℝ)) ≠ 0 := by positivity
  have hsqj : √(2 * (j:ℝ)) ≠ 0 := by positivity
  -- generalize the radicals AND the power terms so field_simp can't distribute inside them
  set a := √(2 * (K:ℝ)) with ha
  set b := √(2 * (j:ℝ)) with hb
  set c := √(2 * ((K:ℝ) + j)) with hc
  set d := √(8 * (K:ℝ) * j / (K + j)) with hd
  set P : ℝ := (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j with hP
  set eK : ℝ := ((K:ℝ) / Real.exp 1) ^ K with heK
  set ej : ℝ := ((j:ℝ) / Real.exp 1) ^ j with hej
  -- now LHS = d * (ss(K+j) * (c * (P * (eK * ej))) / (ss K * (a * eK) * (ss j * (b * ej))))
  -- RHS = 2 ss(K+j)/(ss K ss j) * P; hrad : d * c = 2*(a*b)
  have heK_ne : eK ≠ 0 := by rw [heK]; positivity
  have hej_ne : ej ≠ 0 := by rw [hej]; positivity
  -- field_simp clears the (now-opaque) factors; relation hrad : d*c = 2*(a*b)
  field_simp
  linear_combination (stirlingSeq (K + j) * P) * hrad

-- B_eq: exp((K+j)·(-δ log δ - (1-δ) log(1-δ))) = ((K+j)/K)^K · ((K+j)/j)^j, δ = K/(K+j)
theorem B_eq (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    Real.exp (((K + j : ℕ) : ℝ) * (-( (K:ℝ)/(K+j)) * Real.log ((K:ℝ)/(K+j))
        - (1 - (K:ℝ)/(K+j)) * Real.log (1 - (K:ℝ)/(K+j))))
      = (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKj : (0:ℝ) < (K:ℝ) + j := by positivity
  have hcast : (((K + j : ℕ) : ℝ)) = (K:ℝ) + j := by push_cast; ring
  rw [hcast]
  -- 1 - K/(K+j) = j/(K+j)
  have h1d : (1 : ℝ) - (K:ℝ)/(K+j) = (j:ℝ)/(K+j) := by field_simp; ring
  rw [h1d]
  -- the exponent = K·log((K+j)/K) + j·log((K+j)/j)
  have hlogK : Real.log ((K:ℝ)/(K+j)) = - Real.log (((K:ℝ)+j)/K) := by
    rw [← Real.log_inv]; congr 1; field_simp
  have hlogj : Real.log ((j:ℝ)/(K+j)) = - Real.log (((K:ℝ)+j)/j) := by
    rw [← Real.log_inv]; congr 1; field_simp
  rw [hlogK, hlogj]
  -- exponent: (K+j)·(-(K/(K+j))·(-log((K+j)/K)) - (j/(K+j))·(-log((K+j)/j)))
  --         = K·log((K+j)/K) + j·log((K+j)/j)
  have hexp_simp : ((K:ℝ) + j) * (-((K:ℝ)/(K+j)) * (-Real.log (((K:ℝ)+j)/K))
      - (j:ℝ)/(K+j) * (-Real.log (((K:ℝ)+j)/j)))
      = (K:ℝ) * Real.log (((K:ℝ)+j)/K) + (j:ℝ) * Real.log (((K:ℝ)+j)/j) := by
    field_simp; ring
  rw [hexp_simp, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by positivity), Real.exp_log (by positivity)]

-- ===== core lemma (proven separately, restate signature for use) =====

-- ===== entropy identity =====

-- ===== entropy/power identity =====
theorem qpow_eq_exp (q : ℕ) (n : ℕ) (δ : ℝ) (hq : 2 ≤ q) :
    (q:ℝ) ^ ((n:ℝ) * qEntropy q δ)
      = Real.exp ((n:ℝ) * (δ * Real.log ((q:ℝ)-1) - δ * Real.log δ - (1-δ) * Real.log (1-δ))) := by
  have hqpos : (0:ℝ) < q := by positivity
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log q ≠ 0 := by have := Real.log_pos hq1; linarith
  rw [Real.rpow_def_of_pos hqpos]
  congr 1
  rw [qEntropy]
  simp only [Real.logb]
  field_simp

-- ===== FINAL: MS77 lattice bound (★) =====
-- For q ≥ 2, 0 < δ < 1, n ≥ 1, lattice δ*n = ⌊δ*n⌋₊:
--   q^{n·qEntropy q δ} / √(8nδ(1-δ)) ≤ hammingBallVolume q δ n
theorem ms77_lattice (q n : ℕ) (δ : ℝ)
    (hq : 2 ≤ q) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hlat : δ * n = (⌊δ * n⌋₊ : ℝ)) :
    (q:ℝ) ^ ((n:ℝ) * qEntropy q δ) / (8 * (n:ℝ) * δ * (1 - δ)) ^ ((1:ℝ)/2)
      ≤ (hammingBallVolume q δ n : ℝ) := by
  classical
  set K : ℕ := ⌊δ * n⌋₊ with hKdef
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  -- δ*n = K, so K = δ*n ∈ (0, n)
  have hKr : (K:ℝ) = δ * n := hlat.symm
  have hKpos_r : (0:ℝ) < (K:ℝ) := by rw [hKr]; positivity
  have hK1 : 1 ≤ K := by
    have : 0 < K := by exact_mod_cast hKpos_r
    omega
  -- K < n
  have hKlt_r : (K:ℝ) < (n:ℝ) := by
    rw [hKr]
    calc δ * n < 1 * n := by apply mul_lt_mul_of_pos_right hδ1 hnpos
      _ = n := by ring
  have hKltn : K < n := by exact_mod_cast hKlt_r
  -- set j = n - K ≥ 1, n = K + j
  set j : ℕ := n - K with hjdef
  have hj1 : 1 ≤ j := by omega
  have hnKj : n = K + j := by omega
  have hjpos_r : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
  -- δ = K/n, 1-δ = j/n
  have hδeq : δ = (K:ℝ) / n := by rw [hKr]; field_simp
  have h1δeq : 1 - δ = (j:ℝ) / n := by
    rw [hδeq, hnKj]; push_cast; field_simp; ring
  -- positivity facts
  have hqr1 : (1:ℝ) ≤ (q:ℝ) - 1 := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hqr1pos : (0:ℝ) < (q:ℝ) - 1 := by linarith
  -- S = √(8nδ(1-δ)) = √(8Kj/(K+j))
  have hSval : (8 * (n:ℝ) * δ * (1 - δ)) ^ ((1:ℝ)/2) = √(8 * (K:ℝ) * j / (K + j)) := by
    rw [← Real.sqrt_eq_rpow]
    congr 1
    rw [h1δeq, hδeq, hnKj]
    push_cast
    field_simp
  -- entropy/power identity, then split off (q-1)^K
  have hqpow := qpow_eq_exp q n δ hq
  -- exp(n·δ·log(q-1)) = (q-1)^K
  have hsplit : (q:ℝ) ^ ((n:ℝ) * qEntropy q δ)
      = ((q:ℝ) - 1) ^ K
        * Real.exp ((n:ℝ) * (- δ * Real.log δ - (1-δ) * Real.log (1-δ))) := by
    rw [hqpow]
    rw [show (n:ℝ) * (δ * Real.log ((q:ℝ)-1) - δ * Real.log δ - (1-δ) * Real.log (1-δ))
        = (n:ℝ) * δ * Real.log ((q:ℝ)-1)
          + (n:ℝ) * (- δ * Real.log δ - (1-δ) * Real.log (1-δ)) by ring]
    rw [Real.exp_add]
    congr 1
    -- exp(n·δ·log(q-1)) = (q-1)^K, since n·δ = K
    have hnδ : (n:ℝ) * δ = (K:ℝ) := by rw [hKr]; ring
    rw [show (n:ℝ) * δ * Real.log ((q:ℝ)-1) = (K:ℝ) * Real.log ((q:ℝ)-1) by rw [hnδ]]
    rw [Real.exp_nat_mul, Real.exp_log hqr1pos]
  -- Bform via B_eq (with δ = K/(K+j))
  have hBform : Real.exp ((n:ℝ) * (- δ * Real.log δ - (1-δ) * Real.log (1-δ)))
      = (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j := by
    rw [← B_eq K j hK1 hj1]
    congr 1
    -- n·(-δ log δ - (1-δ)log(1-δ)) = (K+j)·(-(K/(K+j))log(K/(K+j)) - (1-K/(K+j))log(1-K/(K+j)))
    have hcast_add : (((K + j : ℕ)) : ℝ) = (K:ℝ) + j := by push_cast; ring
    rw [hcast_add]
    have hδeq' : δ = (K:ℝ) / ((K:ℝ) + j) := by rw [hδeq, hnKj]; push_cast; ring
    have hnr : (n:ℝ) = (K:ℝ) + j := by rw [hnKj]; push_cast; ring
    rw [hδeq', hnr]
  -- Single largest term: hammingBallVolume ≥ C(n,K)·(q-1)^K
  have hsingle : ((Nat.choose n K) * ((q - 1) ^ K) : ℝ) ≤ (hammingBallVolume q δ n : ℝ) := by
    rw [hammingBallVolume]
    have hmem : K ∈ Finset.range (⌊δ * n⌋₊ + 1) := by
      rw [← hKdef]; simp
    have hterm : (Nat.choose n K * (q - 1) ^ K : ℕ)
        ≤ ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i := by
      apply Finset.single_le_sum (f := fun i => Nat.choose n i * (q - 1) ^ i)
        (fun i _ => Nat.zero_le _) hmem
    have hcast := (Nat.cast_le (α := ℝ)).mpr hterm
    have hqsub : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
      have h1q : 1 ≤ q := by omega
      rw [Nat.cast_sub h1q]; push_cast; ring
    push_cast [hqsub] at hcast ⊢
    convert hcast using 2
  -- master eq: S·C(n,K) = (2 ss(K+j)/(ss K ss j)) · Bform
  have hmaster : √(8 * (K:ℝ) * j / (K + j)) * (Nat.choose n K : ℝ)
      = (2 * stirlingSeq (K + j) / (stirlingSeq K * stirlingSeq j))
        * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) := by
    rw [hnKj]; exact master_eq K j hK1 hj1
  -- core lemma ⇒ Bform ≤ S·C(n,K)
  have hsqrtπ_pos : (0:ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hssK : 0 < stirlingSeq K :=
    lt_of_lt_of_le hsqrtπ_pos (sqrt_pi_le_stirlingSeq (by omega))
  have hssj : 0 < stirlingSeq j :=
    lt_of_lt_of_le hsqrtπ_pos (sqrt_pi_le_stirlingSeq (by omega))
  have hcore : stirlingSeq K * stirlingSeq j ≤ 2 * stirlingSeq (K + j) :=
    core_stirling_add hK1 hj1
  have hBpos : 0 ≤ (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j := by positivity
  have hSpos : (0:ℝ) < √(8 * (K:ℝ) * j / (K + j)) := by
    apply Real.sqrt_pos.mpr; positivity
  -- Bform ≤ S·C(n,K)
  have hBle : (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j
      ≤ √(8 * (K:ℝ) * j / (K + j)) * (Nat.choose n K : ℝ) := by
    rw [hmaster]
    -- ratio ≥ 1: 2 ss(K+j)/(ss K ss j) ≥ 1
    have hratio : (1:ℝ) ≤ 2 * stirlingSeq (K + j) / (stirlingSeq K * stirlingSeq j) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hcore]
    nlinarith [hBpos, hratio]
  -- assemble: q^{nH}/S = (q-1)^K · Bform / S ≤ (q-1)^K · C(n,K) ≤ Vol
  rw [hSval, hsplit, hBform]
  -- goal: ((q-1)^K · Bform) / √(...) ≤ Vol
  have hqK_pos : (0:ℝ) ≤ ((q:ℝ) - 1) ^ K := by positivity
  calc ((q:ℝ) - 1) ^ K * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) / √(8 * (K:ℝ) * j / (K + j))
      = ((q:ℝ) - 1) ^ K * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j / √(8 * (K:ℝ) * j / (K + j))) := by
        rw [mul_div_assoc]
    _ ≤ ((q:ℝ) - 1) ^ K * (Nat.choose n K : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hqK_pos
        rw [div_le_iff₀ hSpos, mul_comm (Nat.choose n K : ℝ)]
        exact hBle
    _ = ((Nat.choose n K) * ((q - 1) ^ K) : ℝ) := by
        ring
    _ ≤ (hammingBallVolume q δ n : ℝ) := hsingle


end ABF26C38


/-- **ABF26 Corollary 3.8.** Volume-based lower bound on list size for an arbitrary code over a
nontrivial finite alphabet, using the MS77 volume estimate
`Vol_q(δ, n) ≥ q^{n·H_q(δ)} / √(8·n·δ·(1-δ))`. With `ρ := k/n`:

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`

Uses `qEntropy` (ABF26 D2.2). **FULLY PROVEN** (axioms ⊆ {propext, Classical.choice,
Quot.sound}); no `sorry`, under the lattice hypothesis `hlat` documented next.
The stronger `[Nontrivial A]` assumption is load-bearing here because `qEntropy` divides by
`Real.log q`; the Elias core above needs only `[Nonempty A]` and therefore permits `q = 1`.

**Lattice hypothesis (documented statement repair).** The MS77 estimate `(★)` below is a
classical lemma for an **integer** radius `δ·n`. As literally stated for arbitrary
`0 < δ < 1` it is **false**: `Vol_q(δ,n)` is a step function of `δ` (it changes only at the
lattice points `δ = k/n`, via the floor `⌊δn⌋`), while the LHS `q^{n·H_q(δ)}/√(8nδ(1-δ))` is
strictly increasing in `δ`; between lattice points the LHS overtakes the frozen volume.
Countermodel `q=2, n=4, δ=0.49`: `⌊0.49·4⌋ = 1`, so `Vol = C(4,0)+C(4,1) = 5`, yet
`2^{4·H₂(0.49)}/√(8·4·0.49·0.51) ≈ 5.65 > 5`. The faithful reading of
[MS77, Ch.10 Lem 7] therefore carries the minimal hypothesis `hlat : δ·n = ⌊δ·n⌋₊`
(equivalently `δ = ⌊δn⌋/n`). This mirrors the documented-countermodel house style of
`subspaceDesign_tau_lower` / the `RationalFunctions` statement-bug class. At lattice points
the bound is TRUE (numerically verified, zero failures over `q ∈ {2,7,101,1009,65537}`,
`n ≤ 160`) and is proven below.

**Proof architecture.** Since L3.7 (`lambda_ge_elias_volume_eli57`, PROVEN in-tree)
gives `Vol_q(δ,n) / q^{n-k} ≤ |Λ(C,δ)|`, this corollary follows by transitivity from the
single real inequality

  `q^{n·H_q(δ)} / √(8·n·δ·(1-δ)) ≤ Vol_q(δ, n)`         (★)

The reduction `(★) ⟹ C3.8` (with `n ≠ 0`): `ρ = k/n ⟹ n·ρ = k`, so the C3.8 numerator
exponent `n·(ρ-1+H_q) = k - n + n·H_q`, giving `q^{n(ρ-1+H_q)} = q^{n·H_q} / q^{n-k}`; hence
the C3.8 real RHS `= (q^{n·H_q}/√(8nδ(1-δ))) / q^{n-k} ≤ Vol / q^{n-k}` by (★), which is
exactly the L3.7 real bound, and `ENNReal.ofReal` is monotone.

Inequality (★) at the lattice point is `ABF26C38.ms77_lattice` (proven above). It collapses,
`q`-independently, to one Stirling inequality: the single largest term gives
`Vol ≥ C(n,K)(q-1)^K` (`K = ⌊δn⌋ = δn`); the entropy/power identity cancels the `(q-1)^K`
exactly against `q^{n·H_q}`; the radical constant `√(8nδ(1-δ))` collapses to give the
*exact* equation `√(8K(n−K)/n)·C(n,K) = (2·stirlingSeq n / (stirlingSeq K·stirlingSeq(n−K)))
·exp(n·H_bin(K/n))`; whence (★) ⟺ `stirlingSeq K·stirlingSeq(n−K) ≤ 2·stirlingSeq n`
(`ABF26C38.core_stirling_add`), discharged via mathlib's `Real.sqrt_pi_le_stirlingSeq`, a
ported Robbins upper bound `stirlingSeq m ≤ √π·e^{1/(12m)}` (`ABF26C38.robbins_upper`,
telescoped from `Stirling.log_stirlingSeq_diff_le`), and exact treatment of the three tight
corners `{(2,1),(3,1),(3,2)}` (with `(2,1)` an exact equality `stirlingSeq(1)² = e²/2`).
[MS77, MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 10, Lemma 7]. -/
theorem lambda_ge_entropy_volume
    {A : Type} [Fintype A] [Nontrivial A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ)) :
    let q : ℕ := Fintype.card A
    let n : ℕ := Fintype.card ι
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda C δ : ENNReal) := by
  -- ABF26-C3.8: VERIFIED reduction to the single external MS77 ingredient (★).
  intro q n ρ
  -- Abbreviations matching L3.7's real bound.
  set S : ℝ := (8 * (n : ℝ) * δ * (1 - δ)) ^ ((1 : ℝ) / 2) with hS_def
  set Vol : ℝ := (hammingBallVolume q δ n : ℝ) with hVol_def
  set P : ℝ := (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) with hP_def
  -- Basic positivity facts.
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have hqr_pos : (0 : ℝ) < (q : ℝ) := by
    have : 1 < q := Fintype.one_lt_card
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  have hP_pos : 0 < P := Real.rpow_pos_of_pos hqr_pos _
  -- MS77 Stirling volume estimate (★), PROVEN at lattice points (see `ABF26C38.ms77_lattice`).
  have hq2 : 2 ≤ q := Fintype.one_lt_card (α := A)
  have hn1 : 1 ≤ n := hn_pos
  -- (Fintype.one_lt_card gives `1 < q`, hence `2 ≤ q`.)
  -- the lattice hypothesis, with `n = Fintype.card ι`.
  have hlat' : δ * (n : ℝ) = (⌊δ * (n : ℝ)⌋₊ : ℝ) := hlat
  have hMS77 : (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / S ≤ Vol := by
    rw [hS_def, hVol_def]
    exact ABF26C38.ms77_lattice q n δ hq2 _hδ_pos _hδ_lt hn1 hlat'
  -- Algebra: rewrite the C3.8 numerator exponent via `n·ρ = k`.
  have hnρ : (n : ℝ) * ρ = (k : ℝ) := by
    simp only [ρ]; field_simp
  have hexp : (n : ℝ) * (ρ - 1 + qEntropy q δ)
      = ((n : ℝ) * qEntropy q δ) - ((n : ℝ) - (k : ℝ)) := by
    have : (n : ℝ) * (ρ - 1 + qEntropy q δ)
        = (n : ℝ) * ρ - (n : ℝ) + (n : ℝ) * qEntropy q δ := by ring
    rw [this, hnρ]; ring
  -- `q^{n(ρ-1+H_q)} = q^{n·H_q} / q^{n-k}`.
  have hnum : (q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
      = (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / P := by
    rw [hexp, Real.rpow_sub hqr_pos, hP_def]
  -- The real-side reduction: C3.8 RHS ≤ Vol / P (= L3.7 real bound).
  have hreduce :
      (q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ)) / S ≤ Vol / P := by
    -- `(q^{nH}/P)/S = (q^{nH}/S)/P ≤ Vol/P` by (★) and `P > 0`.
    rw [hnum]
    have hcomm : ((q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / P) / S
        = ((q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / S) / P := by
      rw [div_div, div_div, mul_comm P S]
    rw [hcomm]
    -- divide both sides of (★) by `P > 0`.
    gcongr
  -- Chain through L3.7 (PROVEN): ofReal(Vol/P) ≤ Λ.
  have hL37 := lambda_ge_elias_volume_eli57 (ι := ι) C k hcard δ _hδ_pos _hδ_lt
  -- L3.7's RHS real expression is `Vol / P`; rewrite to our `set` names.
  refine le_trans (ENNReal.ofReal_le_ofReal hreduce) ?_
  -- now: ofReal (Vol / P) ≤ Λ, matching L3.7.
  convert hL37 using 2

/-- **ABF26 Corollary 3.8 for a field-linear code.** This preserves the original API as a
specialization of `lambda_ge_entropy_volume`, with the code cardinality supplied by
`Module.card_eq_pow_finrank`. -/
theorem linear_lambda_ge_entropy_volume
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ)) :
    let q : ℕ := Fintype.card F
    let n : ℕ := Fintype.card ι
    let k : ℕ := Module.finrank F C
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  apply lambda_ge_entropy_volume (C := (C : Set (ι → F)))
    (k := Module.finrank F C) (δ := δ) ?_ _hδ_pos _hδ_lt hlat
  classical
  haveI : Fintype (↥C) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank (K := F) (V := ↥C)

/-- **ST20 plurality-center averaging core (in-tree, fully proven).**
Given `ℓ + 1` words `c₀, …, c_ℓ : ι → F`, the *plurality center* `z`, obtained by choosing at
each coordinate a value attained by at least one of the `cⱼ` (e.g. the most frequent one),
satisfies the aggregate-distance bound

  `∑ⱼ d_H(z, cⱼ) ≤ ℓ · n`,    where `n = |ι|`.

This is the genuinely-combinatorial half of [ST20 Thm 1.2] and is self-contained from mathlib:
at each coordinate `i`, since `z i` equals `cⱼ₀ i` for some `j₀`, at most `ℓ` of the `ℓ + 1`
words can disagree with `z` there, so `#{j | z i ≠ cⱼ i} ≤ ℓ`; summing the Hamming distances by
swapping the order of summation (`∑ⱼ #{i | z i ≠ cⱼ i} = ∑ᵢ #{j | z i ≠ cⱼ i} ≤ ∑ᵢ ℓ = ℓ·n`)
gives the bound. The statement is phrased for any per-coordinate *representative* center
`hz : ∀ i, ∃ j, z i = c j i` (plurality is the canonical ST20 choice; the aggregate bound is the
same for any representative). The existence of such a `z` (take `z = c 0`) is immediate.

This proves the *averaging* ingredient (b) of T3.9's reduction. It does NOT close T3.9: the ST20
list-decoding bound additionally needs the ℓ-fold-agreement pigeonhole (ingredient (a)) that
selects `ℓ + 1` codewords pairwise agreeing on a *common* `≥ n − s` coordinate set, so that the
center is within relative distance `δ` of ALL of them simultaneously — see the T3.9 docstring and
`research/proximity-prize/dispositions/pc-w2-ST20-core.md`. That pigeonhole is a linear-algebra
dimension count absent from mathlib and in-tree, and is the remaining genuine wall. -/
theorem exists_representative_center_sum_hammingDist_le
    (ℓ : ℕ) (c : Fin (ℓ + 1) → (ι → F)) :
    ∃ z : ι → F, (∑ j, hammingDist z (c j)) ≤ ℓ * Fintype.card ι := by
  -- Representative center: `z = c 0`. (Plurality is the optimal such representative; the
  -- aggregate `≤ ℓ·n` bound holds for any per-coordinate representative, so we use the
  -- simplest one to keep the existence witness explicit.)
  refine ⟨c 0, ?_⟩
  -- The center is a representative at every coordinate.
  have hz : ∀ i : ι, ∃ j : Fin (ℓ + 1), (c 0) i = c j i := fun i => ⟨0, rfl⟩
  -- Rewrite each Hamming distance as a coordinate-filter cardinality and turn it into a sum.
  have hdist : ∀ j, hammingDist (c 0) (c j)
      = ∑ i : ι, ite ((c 0) i ≠ c j i) 1 0 := by
    intro j
    rw [hammingDist]
    exact Finset.card_filter (fun i => (c 0) i ≠ c j i) Finset.univ
  rw [Finset.sum_congr rfl (fun j _ => hdist j)]
  -- Swap the order of summation: `∑ⱼ ∑ᵢ … = ∑ᵢ ∑ⱼ …`.
  rw [Finset.sum_comm]
  -- Per-coordinate bound: `∑ⱼ ite (c 0 i ≠ c j i) 1 0 = #{j | c 0 i ≠ c j i} ≤ ℓ`,
  -- because `j = 0` is excluded (`c 0 i = c 0 i`).
  have hinner : ∀ i : ι, (∑ j, ite ((c 0) i ≠ c j i) 1 0) ≤ ℓ := by
    intro i
    rw [← Finset.card_filter (fun j => (c 0) i ≠ c j i) Finset.univ]
    have hsub : {j ∈ (Finset.univ : Finset (Fin (ℓ + 1))) | (c 0) i ≠ c j i}
        ⊆ (Finset.univ : Finset (Fin (ℓ + 1))).erase 0 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hj.2 rfl
    calc {j ∈ (Finset.univ : Finset (Fin (ℓ + 1))) | (c 0) i ≠ c j i}.card
        ≤ ((Finset.univ : Finset (Fin (ℓ + 1))).erase 0).card := Finset.card_le_card hsub
      _ = Fintype.card (Fin (ℓ + 1)) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      _ = ℓ := by rw [Fintype.card_fin]; omega
  -- Aggregate: `∑ᵢ (inner) ≤ ∑ᵢ ℓ = ℓ · |ι|`.
  calc (∑ i : ι, ∑ j, ite ((c 0) i ≠ c j i) 1 0)
      ≤ ∑ _i : ι, ℓ := Finset.sum_le_sum (fun i _ => hinner i)
    _ = ℓ * Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

-- ===== ST20 (T3.9) helper 1: range fiber lower bound =====
private theorem st20_range_fiber_ge (a m i : ℕ) (hm : 0 < m) (hi : i < m) :
    a / m ≤ (Finset.range a |>.filter (fun t => t % m = i)).card := by
  have hsub : (Finset.range (a / m)).image (fun s => s * m + i)
      ⊆ (Finset.range a |>.filter (fun t => t % m = i)) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have hstep : s * m + m ≤ (a / m) * m := by
        have hs1 : s + 1 ≤ a / m := hs
        calc s * m + m = (s + 1) * m := by ring
          _ ≤ (a/m) * m := Nat.mul_le_mul_right m hs1
      have hdm : (a/m) * m ≤ a := Nat.div_mul_le_self a m
      omega
    · have : (s * m + i) % m = i % m := Nat.mul_add_mod' s m i
      rw [this, Nat.mod_eq_of_lt hi]
  calc a / m = (Finset.range (a / m)).card := by rw [Finset.card_range]
    _ = ((Finset.range (a / m)).image (fun s => s * m + i)).card := by
        rw [Finset.card_image_of_injOn]
        intro x _ y _ h; simp only at h
        have : x * m = y * m := by omega
        exact Nat.eq_of_mul_eq_mul_right hm this
    _ ≤ _ := Finset.card_le_card hsub

-- ===== ST20 (T3.9) helper 2: fiber lower bound transported to attach =====
private theorem st20_attach_fiber_ge (Sc : Finset ι) (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < m)
    (e : {x // x ∈ Sc} ≃ Fin Sc.card) :
    Sc.card / m ≤ (Sc.attach.filter (fun x => (e x).val % m = j)).card := by
  have hbij : (Sc.attach.filter (fun x => (e x).val % m = j)).card
      = (Finset.univ.filter (fun t : Fin Sc.card => t.val % m = j)).card := by
    apply Finset.card_bij (fun x _ => e x)
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_filter] at hx; exact hx.2
    · intro x _ y _ h; exact e.injective h
    · intro t ht
      refine ⟨e.symm t, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_attach, true_and, Equiv.apply_symm_apply]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht; exact ht
      · simp [Equiv.apply_symm_apply]
  rw [hbij]
  have hrange : (Finset.univ.filter (fun t : Fin Sc.card => t.val % m = j)).card
      = (Finset.range Sc.card |>.filter (fun t => t % m = j)).card := by
    apply Finset.card_bij (fun (t : Fin Sc.card) _ => t.val)
    · intro t ht; simp only [Finset.mem_filter, Finset.mem_range]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ⟨t.isLt, ht⟩
    · intro x _ y _ h; exact Fin.ext h
    · intro v hv; simp only [Finset.mem_filter, Finset.mem_range] at hv
      exact ⟨⟨v, hv.1⟩, by simp [Finset.mem_filter, hv.2], rfl⟩
  rw [hrange]
  exact st20_range_fiber_ge _ _ _ hm hj

-- ===== ST20 (T3.9) helper 3: pure-nat arithmetic inequality (lattice form) =====
private theorem st20_nat_ineq (ℓ r₀ : ℕ) (hℓ : 1 ≤ ℓ) :
    ((ℓ+1)*r₀/ℓ) - ((ℓ+1)*r₀/ℓ)/(ℓ+1) ≤ r₀ := by
  set a := (ℓ+1)*r₀/ℓ with ha
  have hAl : a * ℓ ≤ (ℓ+1)*r₀ := Nat.div_mul_le_self _ _
  obtain ⟨s, hs_le, hs_eq⟩ : ∃ s, s ≤ ℓ ∧ a = (ℓ+1) * (a/(ℓ+1)) + s := by
    refine ⟨a % (ℓ+1), ?_, ?_⟩
    · have := Nat.mod_lt a (show 0 < ℓ+1 by omega); omega
    · have := Nat.div_add_mod a (ℓ+1); omega
  set b := a/(ℓ+1) with hb
  rw [Nat.sub_le_iff_le_add, hs_eq]
  have hcore : ℓ*b + s ≤ r₀ := by
    have key : ((ℓ+1)*b + s) * ℓ ≤ (ℓ+1)*r₀ := by rw [← hs_eq]; exact hAl
    nlinarith [key, hs_le, hℓ, Nat.zero_le b, Nat.zero_le s, Nat.zero_le r₀,
               Nat.mul_le_mul_right ℓ hs_le]
  have hexp : (ℓ+1)*b = ℓ*b + b := by ring
  rw [hexp]; omega

-- ===== ST20 (T3.9) helper 4: kernel extraction =====
private theorem st20_kernel_extract (C : Submodule F (ι → F)) (S : Finset ι) (ℓ : ℕ)
    (hdim : S.card < Module.finrank F C) (hq : ℓ + 1 ≤ Fintype.card F) :
    ∃ cf : Fin (ℓ + 1) → (ι → F), Function.Injective cf ∧
      (∀ j, cf j ∈ C) ∧ (∀ j, ∀ i ∈ S, cf j i = 0) := by
  classical
  let ρ : (ι → F) →ₗ[F] (S → F) := LinearMap.funLeft F F (fun i : S => (i : ι))
  let g : C →ₗ[F] (S → F) := ρ.comp C.subtype
  haveI : FiniteDimensional F C := inferInstance
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hrange : Module.finrank F (LinearMap.range g) ≤ S.card := by
    have h1 : Module.finrank F (LinearMap.range g) ≤ Module.finrank F (S → F) :=
      Submodule.finrank_le _
    have h2 : Module.finrank F (S → F) = S.card := by rw [Module.finrank_pi]; simp
    omega
  have hker : 1 ≤ Module.finrank F (LinearMap.ker g) := by omega
  haveI : Fintype (LinearMap.ker g) := Fintype.ofFinite _
  have hcard_ker : Fintype.card (LinearMap.ker g)
      = Fintype.card F ^ Module.finrank F (LinearMap.ker g) :=
    Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker g)
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hge : Fintype.card F ≤ Fintype.card (LinearMap.ker g) := by
    rw [hcard_ker]
    calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (le_of_lt hq1) hker
  have hle : ℓ + 1 ≤ Fintype.card (LinearMap.ker g) := le_trans hq hge
  obtain ⟨emb⟩ : Nonempty (Fin (ℓ+1) ↪ (LinearMap.ker g)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hle)
  refine ⟨fun j => (((emb j : C) : ι → F)), ?_, ?_, ?_⟩
  · intro a b hab
    apply emb.injective
    have h2 : (emb a : C) = (emb b : C) := Subtype.ext hab
    exact Subtype.ext h2
  · intro j; exact (emb j : C).2
  · intro j i hi
    have hmem : (emb j : C) ∈ LinearMap.ker g := (emb j).2
    rw [LinearMap.mem_ker] at hmem
    have hcf := congr_fun hmem ⟨i, hi⟩
    have hgval : (g (emb j)) ⟨i, hi⟩ = (((emb j : C) : ι → F)) i := rfl
    rw [hgval] at hcf
    simpa using hcf

-- ===== ST20 (T3.9) helper 5: distance bound for constructed y =====
private theorem st20_dist_bound (S : Finset ι) (ℓ : ℕ)
    (cf : Fin (ℓ + 1) → (ι → F))
    (hcfC0 : ∀ j, ∀ i, i ∈ S → cf j i = 0) :
    ∃ y : ι → F, ∀ j : Fin (ℓ+1),
      hammingDist y (cf j) ≤ Sᶜ.card - Sᶜ.card / (ℓ+1) := by
  classical
  set Sc : Finset ι := Sᶜ with hSc
  set e : {x // x ∈ Sc} ≃ Fin Sc.card := Sc.equivFin with he
  set partN : {x // x ∈ Sc} → Fin (ℓ+1) :=
    fun x => ⟨(e x).val % (ℓ+1), Nat.mod_lt _ (by omega)⟩ with hpartN
  set y : ι → F := fun i => if hi : i ∈ Sc then cf (partN ⟨i, hi⟩) i else 0 with hy
  refine ⟨y, fun j => ?_⟩
  rw [hammingDist]
  have hsub : (Finset.univ.filter (fun i => y i ≠ cf j i)) ⊆
      (Sc.attach.filter (fun x => partN x ≠ j)).image Subtype.val := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hiSc : i ∈ Sc
    · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
      refine ⟨⟨i, hiSc⟩, ?_, rfl⟩
      intro hpeq
      apply hi
      simp only [hy, dif_pos hiSc]
      rw [hpeq]
    · exfalso; apply hi
      simp only [hy, dif_neg hiSc]
      have hiS : i ∈ S := by simp only [hSc, Finset.mem_compl, not_not] at hiSc; exact hiSc
      exact (hcfC0 j i hiS).symm
  have hpartition := Finset.card_filter_add_card_filter_not (s := Sc.attach)
    (p := fun x => partN x = j)
  have hfiber : Sc.card / (ℓ+1) ≤ (Sc.attach.filter (fun x => partN x = j)).card := by
    have hbase := st20_attach_fiber_ge Sc (ℓ+1) (by omega) j.val j.isLt e
    have hcongr : (Sc.attach.filter (fun x => (e x).val % (ℓ+1) = j.val)).card
        = (Sc.attach.filter (fun x => partN x = j)).card := by
      congr 1; apply Finset.filter_congr; intro x _
      constructor
      · intro h; apply Fin.ext; simp only [hpartN]; exact h
      · intro h; have := congrArg Fin.val h; simpa [hpartN] using this
    rw [← hcongr]; exact hbase
  have hattach_card : Sc.attach.card = Sc.card := Finset.card_attach
  calc (Finset.univ.filter (fun i => y i ≠ cf j i)).card
      ≤ ((Sc.attach.filter (fun x => partN x ≠ j)).image Subtype.val).card :=
        Finset.card_le_card hsub
    _ ≤ (Sc.attach.filter (fun x => partN x ≠ j)).card := Finset.card_image_le
    _ ≤ Sc.card - Sc.card / (ℓ+1) := by
        have hne : (Sc.attach.filter (fun x => partN x ≠ j)).card
            = (Sc.attach.filter (fun x => ¬ (partN x = j))).card := by congr 1
        rw [hne]; omega

-- ===== ST20 (T3.9) helper 6: |C| = q^{finrank C} =====
private theorem st20_ncard_eq (C : Submodule F (ι → F)) :
    Set.ncard (C : Set (ι → F)) = Fintype.card F ^ Module.finrank F C := by
  haveI : Fintype C := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card' (C : Set (ι → F)), Set.toFinset_card]
  have hcong : Fintype.card (↑C : Set (ι → F)) = Fintype.card C := by
    apply Fintype.card_congr; rfl
  rw [hcong, Module.card_eq_pow_finrank (K := F) (V := C)]

/-- **ABF26 Theorem 3.9 [ST20 Thm 1.2], linear refinement.** Generalized Singleton bound
for list decoding. For a linear code `C ⊆ F^n` with `0 < ℓ < |F|`, `δ ∈ (0,1)` and
`|Λ(C, δ)| ≤ ℓ`:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}`.

**PROVEN** here from scratch by Shangguan–Tamo's elementary pigeonhole/partition argument
(SIAM J. Comput. 52(3), eq. (2); the cycle-space machinery in ST20 is only for the
*tightness* results T1.6/T1.9, NOT for this bound). Linear-algebra version: if
`finrank C > n - a`, the restriction-to-`S` map (`|S| = n - a`) has a kernel of dimension
`≥ 1`, hence `≥ |F| ≥ ℓ+1` codewords that vanish on `S`; partitioning `Sᶜ` (size `a`) into
`ℓ+1` near-even blocks and centring a word `y` block-wise puts all `ℓ+1` of them within
relative radius `δ`, contradicting `|Λ(C, δ)| ≤ ℓ`. Converting `finrank C ≤ n - a` to the
real bound via `|C| = |F|^{finrank C}` closes the goal.

**SIGFIX (two hypotheses added vs. the bare ABF26 statement — both are faithful to ST20
and necessary).** The unparameterised statement is *false*: e.g. `C = {0}` (always
`(δ,ℓ)`-list-decodable) with `ℓ = 1`, `δ` near `1` and large `n` gives `a = ⌊(ℓ+1)/ℓ·δ·n⌋
> n`, so the RHS `|F|^{n-a} < 1` while `|C| = 1`. The two added hypotheses are exactly the
regime in which ST20 prove (and state) the bound:
* `hlat` — the **lattice condition** `δ·n = ⌊δ·n⌋` (i.e. `δ·n ∈ ℤ`). ST20 explicitly
  "assume `rn` is an integer so the floor can be removed"; off the lattice the per-codeword
  distance `a - ⌊a/(ℓ+1)⌋` can exceed `⌊δ·n⌋` and the bound genuinely fails. This mirrors
  the lattice fix applied to the sibling MS77 volume bound (C3.8) in this file.
* `ha_le` — the **meaningful-radius regime** `a ≤ n` (equivalent to `δ ≤ ℓ/(ℓ+1)`, the
  Singleton radius regime; for larger `δ` the bound is vacuous/false as above).
Sound and `sorryAx`-free (`#print axioms`: only `propext, Classical.choice, Quot.sound`). -/
theorem linear_C_le_generalized_singleton_st20
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ))
    (ha_le : ⌊((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι⌋₊ ≤ Fintype.card ι)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  classical
  set q : ℕ := Fintype.card F with hq_def
  set n : ℕ := Fintype.card ι with hn_def
  set r₀ : ℕ := ⌊δ * (n : ℝ)⌋₊ with hr₀_def
  set a : ℕ := ⌊((ℓ : ℝ) + 1) / ℓ * δ * n⌋₊ with ha_def
  have hδ_nonneg : (0 : ℝ) ≤ δ := le_of_lt _hδ_pos
  have hℓ1 : 1 ≤ ℓ := _hℓ_pos
  have hq_ge : ℓ + 1 ≤ q := _hℓ_lt
  have hn_pos : 0 < n := Fintype.card_pos
  have ha_le' : a ≤ n := ha_le
  -- a = (ℓ+1)*r₀/ℓ  (nat)
  have ha_eq : a = (ℓ + 1) * r₀ / ℓ := by
    have hℓr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
    have hrw : ((ℓ : ℝ) + 1) / ℓ * δ * n = (((ℓ + 1) * r₀ : ℕ) : ℝ) / (ℓ : ℝ) := by
      have : ((ℓ : ℝ) + 1) / ℓ * δ * n = ((ℓ : ℝ) + 1) / ℓ * (δ * n) := by ring
      rw [this, hlat]
      push_cast
      field_simp
    rw [ha_def, hrw, Nat.floor_div_eq_div]
  have hkey : a - a / (ℓ + 1) ≤ r₀ := by
    rw [ha_eq]; exact st20_nat_ineq ℓ r₀ hℓ1
  -- finrank F C ≤ n - a
  have hfin_le : Module.finrank F C ≤ n - a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
      (n := n - a) (by rw [Finset.card_univ, ← hn_def]; omega)
    have hScard : S.card = n - a := hS
    have hdim : S.card < Module.finrank F C := by rw [hScard]; exact hcon
    obtain ⟨cf, hcf_inj, hcfC, hcf0⟩ := st20_kernel_extract C S ℓ hdim hq_ge
    obtain ⟨y, hy⟩ := st20_dist_bound S ℓ cf hcf0
    have hSc_card : Sᶜ.card = a := by
      rw [Finset.card_compl, hScard, ← hn_def]; omega
    -- each cf j ∈ closeCodewordsRel C y δ
    have hmem : ∀ j, cf j ∈ closeCodewordsRel (↑C : Set (ι → F)) y δ := by
      intro j
      have hdist : hammingDist y (cf j) ≤ r₀ := by
        have h1 := hy j; rw [hSc_card] at h1; exact le_trans h1 hkey
      simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, SetLike.mem_coe]
      refine ⟨hcfC j, ?_⟩
      simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
      rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (n : ℝ))]
      -- goal: ↑Δ₀(y, cf j) ≤ δ * ↑n  (modulo a subsingleton Decidable instance on hammingDist)
      have hcast : (hammingDist y (cf j) : ℝ) ≤ δ * (n : ℝ) := by
        have h1 : (hammingDist y (cf j) : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hdist
        have h2 : (r₀ : ℝ) ≤ δ * (n : ℝ) := by
          rw [hr₀_def]; exact Nat.floor_le (mul_nonneg hδ_nonneg (Nat.cast_nonneg n))
        exact le_trans h1 h2
      convert hcast using 2
      congr!
    -- ℓ+1 distinct elements ⊆ closeCodewordsRel → ncard ≥ ℓ+1
    have hfin_set : (closeCodewordsRel (↑C : Set (ι → F)) y δ).Finite := Set.toFinite _
    have hTcard : (Finset.univ.image cf).card = ℓ + 1 := by
      rw [Finset.card_image_of_injective _ hcf_inj, Finset.card_univ, Fintype.card_fin]
    have hTsub : (↑(Finset.univ.image cf) : Set (ι → F))
        ⊆ closeCodewordsRel (↑C : Set (ι → F)) y δ := by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨j, rfl⟩ := hx; exact hmem j
    have hge : ℓ + 1 ≤ (closeCodewordsRel (↑C : Set (ι → F)) y δ).ncard := by
      calc ℓ + 1 = (Finset.univ.image cf).card := hTcard.symm
        _ = (↑(Finset.univ.image cf) : Set (ι → F)).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ _ := Set.ncard_le_ncard hTsub hfin_set
    -- contradiction with Lambda ≤ ℓ
    have hle : (closeCodewordsRel (↑C : Set (ι → F)) y δ).ncard ≤ ℓ := by
      have hLam : ((closeCodewordsRel (↑C : Set (ι → F)) y δ).ncard : ℕ∞) ≤ (ℓ : ℕ∞) := by
        refine le_trans ?_ _hΛ
        rw [Lambda]
        exact le_iSup (fun f => ((closeCodewordsRel (↑C : Set (ι → F)) f δ).ncard : ℕ∞)) y
      exact_mod_cast hLam
    omega
  -- convert to rpow conclusion
  rw [st20_ncard_eq C]
  have hq1r : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  -- RHS rpow = pow since exponent = (n-a : ℕ)
  have hexp : ((n : ℝ) - (a : ℝ)) = ((n - a : ℕ) : ℝ) := by rw [Nat.cast_sub ha_le']
  calc ((q ^ Module.finrank F C : ℕ) : ℝ)
      = (q : ℝ) ^ Module.finrank F C := by push_cast; ring
    _ ≤ (q : ℝ) ^ (n - a) := by
        apply pow_le_pow_right₀ hq1r hfin_le
    _ = (q : ℝ) ^ ((n - a : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ = (q : ℝ) ^ ((n : ℝ) - (a : ℝ)) := by rw [hexp]

end LowerBounds_General

end CodingTheory
