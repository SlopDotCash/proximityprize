/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4).
-/

import ArkLib.Extensions.Data.CodingTheory.ProximityGap.CapacityBounds.UniqueDecoding.Curves
import ArkLib.Extensions.Data.CodingTheory.ProximityGenerator.LossyMca

/-!
# Lossy mutual correlated agreement for Reed–Solomon curves in the unique-decoding range

Let `C` be the Reed–Solomon code of degree `< k` on `n` points, `ρ = k / n`, and `u₀, …, u_M`
words with curve points `u_z = ∑ⱼ zʲ uⱼ`. If `0 < δ_fld ≤ (1 - ρ) / 2 - 1 / n`,
`δ_fld < δ_int` and `0 < loss`, the number of seeds `z` at which the powers generator
`z ↦ (1, z, …, z^M)` has a lossy MCA event (`IsLossyMCA`) at radius `δ_fld` is
(`card_isLossyMCA_le`)

  `≤ M · max(T₁, T₂, δ_int / loss)`,  `T₁ = (1 - ρ - δ_fld) / (δ_fld (1 - ρ - 2 δ_fld))`,
  `T₂ = δ_int / (δ_int - δ_fld)`,

so `lossyMcaError ≤ M · max(T₁, T₂, δ_int / loss) / q` (`lossyMcaError_le`), independently of
`n`. `δ_int` is a free parameter trading `T₂` against `δ_int / loss`.

## Derivation

Every bad `z` has `u_z` `δ_fld`-close to `C`, so the bad seeds are among the `a` good ones. If
`a ≤ M · max(T₁, T₂)` we are done. Otherwise `exists_jointCodewords` gives codewords `pⱼ`
differing from the `uⱼ` on a set `E`, `|E| ≤ δ_int n`, with every good `u_z` within
`e = ⌊δ_fld n⌋` of `p_z = ∑ⱼ zʲ pⱼ`. For a bad `z` with agreement set `T` and codeword `c`,
`c` and `p_z` are within `2e ≤ n - k`, so `c = p_z`. The words `uⱼ` agree with the codewords `pⱼ`
on `T \ E`, so badness forces `|T ∩ E| > loss · n`, and `T ∩ E` lies in the agreement set
`A_z = {i ∈ E | u_z(i) = p_z(i)}`. Each `i ∈ E` is in `A_z` for at most `M` values of `z`
(`card_filter_agree_le`), so `#bad · loss · n < ∑_z |A_z| ≤ M |E| ≤ M δ_int n`.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S., *On Proximity Gaps for
  Reed–Solomon Codes*][BCHKS25]
-/


namespace CodingTheory.UniqueDecoding

open NNReal Finset Code CoreDefinitions LinearCode Curve
open scoped BigOperators ProbabilityTheory

/-- The bound `max(T₁, T₂, δ_int / loss)` on the exceptional seeds per unit of `M`, for a code of
dimension `k` and length `n`. -/
noncomputable def lossyBound (k n : ℕ) (δ_fld δ_int : ℝ≥0) (loss : ℝ) : ℝ :=
  max (max ((1 - (k : ℝ) / n - δ_fld) / ((δ_fld : ℝ) * (1 - (k : ℝ) / n - 2 * δ_fld)))
    ((δ_int : ℝ) / (δ_int - δ_fld))) ((δ_int : ℝ) / loss)

variable {ι : Type} {F : Type} [Field F]

/-- The powers generator's word at `z` is the curve point. -/
theorem powers_sum_eq_polynomialCurveEval {M : ℕ} (u : Fin (M + 1) → ι → F) (z : F) :
    (fun i => ∑ j, univariatePowersGenerator F M z j • u j i) = polynomialCurveEval u z :=
  funext fun i => by simp only [polynomialCurveEval_apply, smul_eq_mul]

variable [Fintype ι]

/-- Two Reed–Solomon codewords at distance at most `n - k` are equal. -/
theorem eq_of_hammingDist_le [DecidableEq F] (domain : ι ↪ F) {k : ℕ} (hk : k ≤ Fintype.card ι)
    {c c' : ι → F} (hc : c ∈ ReedSolomon.code domain k) (hc' : c' ∈ ReedSolomon.code domain k)
    (hd : Δ₀(c, c') ≤ Fintype.card ι - k) : c = c' := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [ReedSolomon.code_zero, Submodule.mem_bot] at hc hc'
    rw [hc, hc']
  · have : NeZero k := ⟨hk0.ne'⟩
    by_contra hne
    have hmd := Code.minDist_le_dist hc hc' hne
    rw [ReedSolomon.minDist_of_le hk] at hmd
    omega

variable [Fintype F]

/-- A lossy MCA event of the powers generator: the curve point agrees with a codeword `c` on a
set `T` of at least `n - ⌊δ n⌋` points, and no subset of `T` missing at most `loss · n` points
carries codewords for all the `uⱼ`. -/
theorem isLossyMCA_elim (domain : ι ↪ F) {k M : ℕ} {u : Fin (M + 1) → ι → F} {z : F}
    {δ : ℝ≥0} {loss : ℝ}
    (h : IsLossyMCA (univariatePowersGenerator F M) (ReedSolomon.code domain k) z u δ loss) :
    ∃ T : Finset ι, ∃ c ∈ ReedSolomon.code domain k,
      Fintype.card ι - Nat.floor (δ * Fintype.card ι) ≤ T.card ∧
      (∀ i ∈ T, polynomialCurveEval u z i = c i) ∧
      ∀ T' ⊆ T, (T'.card : ℝ) ≥ T.card - loss * Fintype.card ι →
        ∃ j, projectedWord (u j) T' ∉ projectedCodeSubmod (ReedSolomon.code domain k) T' := by
  obtain ⟨T, hT, hmem, hT'⟩ := h
  obtain ⟨c, hc, hcv⟩ := Submodule.mem_map.mp hmem
  refine ⟨T, c, hc, ?_, fun i hi => ?_, hT'⟩
  · apply (Code.relDist_floor_bound_iff_complement_bound _ T.card δ).2
    rcases le_total δ 1 with h1 | h1
    · rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub h1, NNReal.coe_natCast,
        NNReal.coe_natCast, NNReal.coe_one, mul_comm]
      exact hT
    · rw [tsub_eq_zero_of_le h1, zero_mul]
      exact zero_le
  · have h := congrFun hcv ⟨i, hi⟩
    simp only [LinearMap.funLeft_apply, projectedWord, Set.domRestrict_apply] at h
    rw [← powers_sum_eq_polynomialCurveEval]
    exact h.symm

variable [Nonempty ι]

/-- **Lossy curve MCA, count.** At most `M · max(T₁, T₂, δ_int / loss)` seeds of the powers
generator give a lossy MCA event at radius `δ_fld`. -/
theorem card_isLossyMCA_le (domain : ι ↪ F) (k M : ℕ) (u : Fin (M + 1) → ι → F)
    (δ_fld δ_int : ℝ≥0) (loss : ℝ)
    (h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_pos : 0 < δ_fld) (h_lt : δ_fld < δ_int) (h_loss : 0 < loss)
    [DecidablePred fun z => IsLossyMCA (univariatePowersGenerator F M)
      (ReedSolomon.code domain k) z u δ_fld loss] :
    ((univ.filter fun z => IsLossyMCA (univariatePowersGenerator F M)
        (ReedSolomon.code domain k) z u δ_fld loss).card : ℝ) ≤
      M * lossyBound k (Fintype.card ι) δ_fld δ_int loss := by
  classical
  set n := Fintype.card ι
  set e := Nat.floor (δ_fld * n)
  set good := goodCoeffs domain k u δ_fld
  set bad := univ.filter fun z => IsLossyMCA (univariatePowersGenerator F M)
    (ReedSolomon.code domain k) z u δ_fld loss
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hkn : k + 2 * e ≤ n := by
    have heR : (e : ℝ) ≤ δ_fld * n := by
      have : (e : ℝ≥0) ≤ δ_fld * n := Nat.floor_le (by positivity)
      exact_mod_cast this
    have h1 := mul_le_mul_of_nonneg_right h_ud hn.le
    have h2 : ((1 - (k : ℝ) / n) / 2 - 1 / n) * n = (n - k) / 2 - 1 := by field_simp
    have : (k : ℝ) + 2 * e ≤ n := by linarith
    exact_mod_cast this
  have hdata (z : F) (hz : z ∈ bad) := isLossyMCA_elim domain (mem_filter.mp hz).2
  have hsub : bad ⊆ good := by
    intro z hz
    obtain ⟨T, c, hc, hT, hTc, -⟩ := hdata z hz
    refine mem_filter.mpr ⟨mem_univ _, le_trans
      (Code.relDistFromCode_le_relDist_to_mem (polynomialCurveEval u z) c hc) ?_⟩
    have hle : δᵣ(polynomialCurveEval u z, c) ≤ δ_fld := by
      rw [Code.relCloseToWord_iff_exists_agreementCols]
      exact ⟨T, hT, fun i => ⟨hTc i, fun hne hi => hne (hTc i hi)⟩⟩
    exact_mod_cast hle
  rcases le_or_gt (good.card : ℝ) (M * max
      ((1 - (k : ℝ) / n - δ_fld) / ((δ_fld : ℝ) * (1 - (k : ℝ) / n - 2 * δ_fld)))
      ((δ_int : ℝ) / (δ_int - δ_fld))) with hA | hA
  · calc (bad.card : ℝ) ≤ good.card := by exact_mod_cast card_le_card hsub
      _ ≤ _ := hA
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hM
  obtain ⟨p, hp, hclose, hE⟩ :=
    exists_jointCodewords domain k M u δ_fld δ_int h_ud h_pos h_lt hA
  set E := disagree u p
  let agree (z : F) : Finset ι :=
    E.filter fun i => polynomialCurveEval u z i = polynomialCurveEval p z i
  -- A bad seed agrees with the curve of `p` on more than `loss · n` points of `E`.
  have hlarge : ∀ z ∈ bad, loss * n < (agree z).card := by
    intro z hz
    obtain ⟨T, c, hc, hT, hTc, hT'⟩ := hdata z hz
    have hcp : c = polynomialCurveEval p z := by
      have hpz : polynomialCurveEval p z ∈ ReedSolomon.code domain k :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hp j)
      refine eq_of_hammingDist_le domain (by omega) hc hpz ?_
      have h1 : Δ₀(polynomialCurveEval u z, c) ≤ e :=
        (Code.closeToWord_iff_exists_agreementCols _ _ e).2
          ⟨T, hT, fun i => ⟨hTc i, fun hne hi => hne (hTc i hi)⟩⟩
      have h2 : Δ₀(polynomialCurveEval u z, polynomialCurveEval p z) ≤ e := hclose z (hsub hz)
      have := hammingDist_triangle c (polynomialCurveEval u z) (polynomialCurveEval p z)
      have := hammingDist_comm c (polynomialCurveEval u z)
      omega
    have hnot : ¬ ((T \ E).card : ℝ) ≥ T.card - loss * n := by
      intro hge
      obtain ⟨j, hj⟩ := hT' (T \ E) sdiff_subset hge
      refine hj (Submodule.mem_map.mpr ⟨p j, hp j, funext fun i => ?_⟩)
      have hi : i.1 ∉ E := (mem_sdiff.mp i.2).2
      simp only [E, disagree, mem_filter, mem_univ, true_and, not_exists, not_not] at hi
      simp only [LinearMap.funLeft_apply, projectedWord, Set.domRestrict_apply, hi]
    have hsubA : T ∩ E ⊆ agree z := fun i hi => by
      obtain ⟨hiT, hiE⟩ := mem_inter.mp hi
      exact mem_filter.mpr ⟨hiE, by rw [hTc i hiT, hcp]⟩
    have h1 : ((T ∩ E).card : ℝ) ≤ (agree z).card := by exact_mod_cast card_le_card hsubA
    have h2 : ((T \ E).card : ℝ) + (T ∩ E).card = T.card := by
      exact_mod_cast card_sdiff_add_card_inter T E
    push Not at hnot
    linarith
  -- Each point of `E` is in at most `M` agreement sets.
  have hcount : ∑ z ∈ bad, (agree z).card ≤ M * E.card := by
    calc ∑ z ∈ bad, (agree z).card
        = ∑ i ∈ E,
            (bad.filter fun z => polynomialCurveEval u z i = polynomialCurveEval p z i).card := by
          simp only [agree, card_filter]
          exact sum_comm
      _ ≤ ∑ _i ∈ E, M := sum_le_sum fun i hi => card_filter_agree_le u p hi bad
      _ = M * E.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hlow : (bad.card : ℝ) * (loss * n) ≤ M * (δ_int * n) := by
    calc (bad.card : ℝ) * (loss * n) = ∑ _z ∈ bad, loss * n := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ bad, ((agree z).card : ℝ) := sum_le_sum fun z hz => (hlarge z hz).le
      _ = ((∑ z ∈ bad, (agree z).card : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((M * E.card : ℕ) : ℝ) := Nat.cast_le.mpr hcount
      _ = M * E.card := by push_cast; rfl
      _ ≤ M * (δ_int * n) := mul_le_mul_of_nonneg_left hE hM
  have hbad : (bad.card : ℝ) ≤ M * ((δ_int : ℝ) / loss) := by
    rw [← mul_div_assoc, le_div_iff₀ h_loss]
    have : (bad.card : ℝ) * loss * n ≤ M * δ_int * n := by
      simpa only [mul_assoc] using hlow
    exact le_of_mul_le_mul_right this hn
  exact hbad.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hM)

/-- **Lossy curve MCA.** The lossy MCA error of the powers generator `z ↦ (1, z, …, z^M)` for the
Reed–Solomon code at radius `δ_fld` is at most `M · max(T₁, T₂, δ_int / loss) / q`. -/
theorem lossyMcaError_le [SampleableType F] (domain : ι ↪ F) (k M : ℕ) (δ_fld δ_int : ℝ≥0)
    (loss : ℝ)
    (h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_pos : 0 < δ_fld) (h_lt : δ_fld < δ_int) (h_loss : 0 < loss) :
    lossyMcaError (univariatePowersGenerator F M) (ReedSolomon.code domain k) δ_fld loss ≤
      ENNReal.ofReal (M * lossyBound k (Fintype.card ι) δ_fld δ_int loss / Fintype.card F) := by
  classical
  refine iSup_le fun u => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (card_isLossyMCA_le domain k M u δ_fld δ_int loss h_ud h_pos h_lt h_loss)
    (Nat.cast_nonneg _))

end CodingTheory.UniqueDecoding

#print axioms CodingTheory.UniqueDecoding.isLossyMCA_elim
#print axioms CodingTheory.UniqueDecoding.card_isLossyMCA_le
#print axioms CodingTheory.UniqueDecoding.lossyMcaError_le
