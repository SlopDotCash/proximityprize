/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.ListBound
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CodewordBound

/-!
# First-order line-MCA certificates with a closed rank profile

`ScaledFirstOrderSecurity` certifies line MCA beyond the Johnson radius from four slot
inequalities at reference length 128, each evaluated term by term. Here the rank profile
of the first-order interpolation system is summed in closed form. A slot inequality then
costs one kernel evaluation of `μ + 1` terms, so multiplicities in the hundreds are
cheap, and reference length 4096 resolves the radii they certify.

## Main statements

* `rank_sum`: the rank profile at total jet degree `t` equals a capped tent sum.
* `security_of_slots`: one slot inequality at reference length `N` gives 128-bit line-MCA
  security at every length `b N`, with an explicit constant for the exceptional count.
* `four_rates`: under the field-size hypothesis `2^165 n² ≤ p` of the earlier theorem, the
  closed radii are `1262/4096`, `2166/4096`, `2780/4096` and `3195/4096`.
* `four_rates_wide`: under `2^180 n² ≤ p` they are `1269/4096`, `2174/4096`, `2788/4096`
  and `3201/4096`.
* `four_list_bounds`, `four_interleaved_list_bounds`: linear list bounds at the radii of
  `four_rates`, with no field-size hypothesis. `FineGridWideLists` has the bounds at the
  radii of `four_rates_wide`.

Both MCA statements hold on every injective evaluation domain of length `4096 b` in a
prime field.

## References

* [DKT26]
-/

namespace ProximityGap.FineGridFirstOrderSecurity

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions Finset

/-! ### The rank profile in closed form -/

/-- Sum of a tent of base `L` capped at height `w`. -/
def cappedTent (L w : ℕ) : ℕ := if 2*w ≤ L+1 then w*(L+1-w) else (L+1)^2/4

private theorem tent_peel (L w : ℕ) :
    ∑ u ∈ range (L+2), min (L+2-u) (min (u+1) (w+1)) =
      (L+2) + ∑ u ∈ range L, min (L-u) (min (u+1) w) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ v ∈ range L,
      min (L+2-(v+1)) (min (v+1+1) (w+1)) = min (L-v) (min (v+1) w) + 1 := by
    intro v hv
    have := Finset.mem_range.mp hv
    omega
  rw [Finset.sum_congr rfl hmid, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]
  have h0 : min (L+2-0) (min (0+1) (w+1)) = 1 := by omega
  have hL : min (L+2-(L+1)) (min (L+1+1) (w+1)) = 1 := by omega
  rw [h0, hL]
  omega

/-- A tent of base `L` capped at height `w` sums to `cappedTent L w`. -/
theorem tent_sum (w : ℕ) :
    ∀ L, ∑ u ∈ range L, min (L-u) (min (u+1) w) = cappedTent L w := by
  induction w with
  | zero =>
    intro L
    simp [cappedTent]
  | succ w ih =>
    intro L
    match L with
    | 0 => simp [cappedTent]
    | 1 =>
      unfold cappedTent
      split_ifs with h
      · have hw : w = 0 := by omega
        subst hw
        simp
      · simp
    | L+2 =>
      rw [tent_peel, ih L]
      unfold cappedTent
      by_cases h : 2*w ≤ L+1
      · rw [ite_eq_left h, ite_eq_left (by omega)]
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (show w ≤ L+1 by omega)
        have e₁ : L+1-w = c := by omega
        have e₂ : L+2+1-(w+1) = c+1 := by omega
        rw [e₁, e₂]
        nlinarith
      · rw [ite_eq_right h, ite_eq_right (by omega)]
        have e : (L+2+1)^2 = (L+1)^2 + 4*(L+2) := by ring
        rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
        omega

/-- The first-order rank profile at total jet degree `t`: the sources of each `T`-degree
`s < m` are capped by the `m - s` low-contact targets, and the sum is a capped tent. -/
theorem rank_sum (m M t : ℕ) :
    ∑ s ∈ range m, min (m-s) (min t s + 1 - (t-M)) = cappedTent (m-(t-M)) (min t M+1) := by
  rw [← tent_sum]
  rcases le_total (t-M) m with h | h
  · obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, Finset.sum_range_add]
    have hzero : ∑ s ∈ range (t-M), min (t-M+L-s) (min t s + 1 - (t-M)) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have := Finset.mem_range.mp hs
      omega
    rw [hzero, zero_add]
    apply Finset.sum_congr rfl
    intro u hu
    have := Finset.mem_range.mp hu
    omega
  · rw [Nat.sub_eq_zero_of_le h, Finset.range_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro s hs
    have := Finset.mem_range.mp hs
    omega

/-! ### Slot counts at a reference length -/

/-- Row slots of the shifted first-order interpolation system at reference length `n`. -/
def rowSlots (n m M μ h : ℕ) : ℕ :=
  ∑ t ∈ range (μ+1), n * cappedTent (m-(t-M)) (min t M+1) * (h+1-t)

/-- Column slots at reference dimension `k` and agreement count `A`. -/
def columnSlots (k A m M μ h : ℕ) : ℕ :=
  ∑ t ∈ range (μ+1), (min t M+1) * ((m*A-k*t) * (h+1-t))

private theorem row_le (b n D A m M μ h : ℕ) :
    firstOrderCurveShiftedRowSlotBound D A m M μ (b*n) 1 h ≤ b * rowSlots n m M μ h := by
  unfold firstOrderCurveShiftedRowSlotBound rowSlots
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro t _
  rw [one_mul, ← mul_assoc b, ← mul_assoc b]
  gcongr
  rw [← rank_sum]
  unfold firstOrderGradedRankBound
  apply sum_le_sum
  intro s _
  unfold firstOrderGradedSourceCount
  split_ifs <;> simp

private theorem column_le (b k A m M μ h : ℕ) :
    b * columnSlots k A m M μ h ≤
      firstOrderCurveShiftedHeightSlotCount (b*k-1) (b*A) m M μ 1 h := by
  have hcol : columnSlots k A m M μ h =
      ∑ t ∈ range (μ+1), ∑ _j ∈ range (min t M+1), (m*A-k*t)*(h+1-t) := by
    unfold columnSlots
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hcol]
  unfold firstOrderCurveShiftedHeightSlotCount
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro t _
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro j _
  rw [one_mul, ← mul_assoc b, Nat.mul_sub b (m*A) (k*t)]
  apply Nat.mul_le_mul_right
  apply tsub_le_tsub
  · exact (Nat.le_add_right _ j).trans_eq (by ac_rfl)
  · exact (Nat.mul_le_mul_right t (Nat.sub_le (b*k) 1)).trans_eq (by ac_rfl)

/-- A strict slot surplus at the reference length persists at every positive multiple. -/
theorem scaled_slots {b n k A m M μ h : ℕ} (hb : 0 < b)
    (hcert : rowSlots n m M μ h < columnSlots k A m M μ h) :
    firstOrderCurveShiftedRowSlotBound (b*k-1) (b*A) m M μ (b*n) 1 h <
      firstOrderCurveShiftedHeightSlotCount (b*k-1) (b*A) m M μ 1 h :=
  (row_le ..).trans_lt ((Nat.mul_lt_mul_of_pos_left hcert hb).trans_le (column_le ..))

/-! ### From a slot inequality to line-MCA security -/

/-- The closed first-order exception constant is at most an explicit multiple of `n²`
once the agreement-incidence ratio, the relative degree and the staircase are bounded. -/
theorem exception_le {n D A h μ M : ℕ} {Θ ρ T : ℝ} (hn : 1 ≤ n)
    (hρ : 0 ≤ ρ) (hD : (D : ℝ) ≤ ρ * n)
    (hθ : agreementIncidenceRatio n D A ≤ Θ) (hμ0 : 0 < μ)
    (hT : stageStaircase μ M ≤ T) :
    firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D h μ M ≤
      (((2*μ-1 : ℕ) : ℝ) * h + Θ * (h + μ) + (4 * Θ * ρ * μ * h + μ + 8 * ρ * Θ^2 * T) +
        (24 * ρ^2 * h * Θ^2 * T + 4 * ρ * Θ * T)) * (n : ℝ)^2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hθ0 : 0 ≤ agreementIncidenceRatio n D A := by
    unfold agreementIncidenceRatio
    positivity
  have hΘ0 : 0 ≤ Θ := hθ0.trans hθ
  have hT0 : 0 ≤ stageStaircase μ M := stageStaircase_nonneg μ M
  have hTT : 0 ≤ T := hT0.trans hT
  have habs : ((n-D-1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show n-D-1 ≤ n by omega)
  unfold firstOrderExceptionConstant ordinaryTailCharge
  rw [ite_eq_right hμ0.ne']
  calc _ ≤ ((2*μ-1 : ℕ) : ℝ) * h + Θ * (h + μ + 4 * (ρ * n) * μ * h) + (n : ℝ) * μ +
        (24 * (ρ * n)^2 * h + 8 * (ρ * n)) * Θ^2 * T + 4 * (ρ * n) * (n : ℝ) * Θ * T := by
        gcongr
     _ ≤ _ := by
        have h1 : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
        have h0 : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
        have hA0 : 0 ≤ ((2*μ-1 : ℕ) : ℝ) * h + Θ * (h + μ) := by positivity
        have hA1 : 0 ≤ 4 * Θ * ρ * μ * h + μ + 8 * ρ * Θ^2 * T := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h0 hA0, mul_le_mul_of_nonneg_left h1 hA1]

/-- Line-MCA security at closed radius `1 - A/N` from one slot certificate at reference
length `N`. It holds at every length `b N`, on every injective evaluation domain of a
prime field with `2^128 K (b N)² ≤ p`, where `K` bounds the normalized exception constant. -/
theorem security_of_slots {p N b k A m M μ h K : ℕ} {Θ ρ T : ℝ} [Fact p.Prime]
    [SampleableType (ZMod p)] (hb : 0 < b) (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ N)
    (hMN : M ≤ N) (hμ0 : 0 < μ) (hρ : 0 ≤ ρ) (hkρ : (k : ℝ) ≤ ρ * N)
    (hΘ1 : 1 ≤ Θ) (hΘ : ((N - k : ℕ) : ℝ) ≤ Θ * ((A - k : ℕ) : ℝ))
    (hT : stageStaircase μ M ≤ T) (hK1 : 1 ≤ K)
    (hK : ((2*μ-1 : ℕ) : ℝ) * h + Θ * (h + μ) + (4 * Θ * ρ * μ * h + μ + 8 * ρ * Θ^2 * T) +
        (24 * ρ^2 * h * Θ^2 * T + 4 * ρ * Θ * T) ≤ K)
    (hslots : rowSlots N m M μ h < columnSlots k A m M μ h)
    (hp : 2^128 * K * (b*N)^2 ≤ p) (dom : Fin (b*N) ↪ ZMod p) {r : ℝ}
    (hr : r ≤ 1 - (A:ℝ)/N) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom (b*k)) r ≤ ENNReal.ofReal (1/(2:ℝ)^128) := by
  let D := b*k-1
  have hbk : 2 ≤ b*k := by nlinarith
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hsucc : b*k = D+1 := by dsimp [D]; omega
  have hAp : b*k < b*A := Nat.mul_lt_mul_of_pos_left hkA hb
  have hDA : D < b*A := by omega
  have hAn' := Nat.mul_le_mul_left b hAN
  have hNpos : 0 < N := by omega
  have hNb : N ≤ b*N := Nat.le_mul_of_pos_left N hb
  have hn : 1 ≤ b*N := by omega
  have hDn : D ≤ b*N := by omega
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hθ : agreementIncidenceRatio (b*N) D (b*A) ≤ Θ := by
    unfold agreementIncidenceRatio
    apply (div_le_iff₀ (by exact_mod_cast (show 0 < b*A-D by omega))).mpr
    have e₁ : b*N - D = b*(N-k) + 1 := by
      have := Nat.mul_sub b N k
      have := Nat.mul_le_mul_left b (show k ≤ N by omega)
      omega
    have e₂ : b*A - D = b*(A-k) + 1 := by
      have := Nat.mul_sub b A k
      omega
    rw [e₁, e₂]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hΘ hb0]
  have hDρ : (D : ℝ) ≤ ρ * ((b*N : ℕ) : ℝ) := by
    have h₁ : (D : ℝ) ≤ ((b*k : ℕ) : ℝ) := by exact_mod_cast (show D ≤ b*k by omega)
    push_cast at h₁ ⊢
    nlinarith [mul_le_mul_of_nonneg_left hkρ hb0]
  have hnp : b*N < p := by
    have hsq : b*N ≤ (b*N)^2 := Nat.le_self_pow (by decide) _
    have hone : (b*N)^2 ≤ 2^128 * K * (b*N)^2 :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hK1)
    have hlt : b*N < 2^128 * K * (b*N)^2 := by
      have h2 : 2 * (b*N)^2 ≤ 2^128 * K * (b*N)^2 :=
        Nat.mul_le_mul_right _ ((show 2 ≤ 2^128 by decide).trans
          (Nat.le_mul_of_pos_right _ hK1))
      have hpos : 0 < (b*N)^2 := pow_pos (by omega) 2
      omega
    omega
  have hchar : ringChar (ZMod p) = 0 ∨ max D M < ringChar (ZMod p) := by
    right
    rw [ZMod.ringChar_zmod_n]
    omega
  let B := (K : ℝ) * ((b*N : ℕ) : ℝ)^2
  have hline : LineExactAgreementBound dom (b*k) (b*A) B := by
    apply lineExactAgreementBound_of_exactCorrelatedPair
    intro f g
    obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      (F := ZMod p) (k := b*k) hD hsucc.le dom f g (scaled_slots hb hslots)
    obtain ⟨ex,_,_,hc,hfit⟩ := cert.exists_exceptional_hybrid hsucc hD hDA hchar
    exact ⟨ex, hc.trans ((exception_le hn hρ hDρ hθ hμ0 hT).trans
      (mul_le_mul_of_nonneg_right hK (sq_nonneg _))), hfit⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hth : b*A ≤ ⌈(Fintype.card (Fin (b*N)) : ℝ)*(1-r)⌉₊ := by
    calc b*A = ⌈((b*A:ℕ):ℝ)⌉₊ := (Nat.ceil_natCast (R := ℝ) _).symm
         _ ≤ _ := Nat.ceil_mono ?_
    rw [Fintype.card_fin, Nat.cast_mul, Nat.cast_mul]
    have hA : (A : ℝ) ≤ (1-r) * N := (div_le_iff₀ hNR).mp (by linarith)
    calc (b : ℝ) * A ≤ b * ((1-r) * N) := mul_le_mul_of_nonneg_left hA hb0
         _ = b * N * (1-r) := by ring
  refine (mcaError_affineLine_le_of_exactAgreement dom B hline r hth).trans ?_
  rw [ZMod.card]
  apply ENNReal.ofReal_le_ofReal
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (div_le_div_iff₀ hp0 (by norm_num : (0:ℝ) < 2^128)).mpr
  have h : (2:ℝ)^128 * K * ((b*N:ℕ):ℝ)^2 ≤ p := by exact_mod_cast hp
  dsimp [B]
  linarith

/-! ### Certificates at reference length 4096 -/

/-- The four slot inequalities whose normalized exception constants are below `2^37`. -/
theorem slot_certificates :
    rowSlots 4096 116 35 160 10333 < columnSlots 2048 2834 116 35 160 10333 ∧
    rowSlots 4096 112 50 210 13205 < columnSlots 1024 1930 112 50 210 13205 ∧
    rowSlots 4096 108 59 277 16613 < columnSlots 512 1316 108 59 277 16613 ∧
    rowSlots 4096 104 67 365 22123 < columnSlots 256 901 104 67 365 22123 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The four slot inequalities whose normalized exception constants are below `2^52`. -/
theorem wide_slot_certificates :
    rowSlots 4096 824 254 1137 471498 < columnSlots 2048 2827 824 254 1137 471498 ∧
    rowSlots 4096 612 278 1148 360879 < columnSlots 1024 1922 612 278 1148 360879 ∧
    rowSlots 4096 876 483 2237 1058306 < columnSlots 512 1308 876 483 2237 1058306 ∧
    rowSlots 4096 488 321 1705 470485 < columnSlots 256 895 488 321 1705 470485 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- At every length `4096 b` and every prescribed prime-field domain, the four listed
radii give 128-bit line-MCA security when `p ≥ 2^165 n²`. The field-size hypothesis is
the one of `ScaledFirstOrderSecurity.four_rates`; the radii are larger. -/
theorem four_rates {b p : ℕ} [Fact p.Prime] [SampleableType (ZMod p)] (hb : 0 < b)
    (hp : 2^165*(b*4096)^2 ≤ p) (dom : Fin (b*4096) ↪ ZMod p) :
    let good := fun (k : ℕ) (r : ℝ) => mcaError (AffineLineGenerator (ZMod p))
      (code dom (b*k)) r ≤ ENNReal.ofReal (1/(2:ℝ)^128)
    good 2048 (1262/4096) ∧ good 1024 (2166/4096) ∧ good 512 (2780/4096) ∧
      good 256 (3195/4096) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := slot_certificates
  have hp' : 2^128 * 2^37 * (b*4096)^2 ≤ p := by
    rw [← pow_add]
    exact hp
  refine ⟨?_,?_,?_,?_⟩
  · exact security_of_slots (K := 2^37) (Θ := 1024/393) (ρ := 1/2) (T := 172410) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₁ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^37) (Θ := 512/151) (ρ := 1/4) (T := 450925) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₂ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^37) (Θ := 896/201) (ρ := 1/8) (T := 841930) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₃ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^37) (Θ := 256/43) (ρ := 1/16) (T := 1460198) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₄ hp' dom (by norm_num)

/-- With the field-size hypothesis `p ≥ 2^180 n²` the four closed radii rise to
`1269/4096`, `2174/4096`, `2788/4096` and `3201/4096`. At length `2^30` the hypothesis
reads `p ≥ 2^240`. -/
theorem four_rates_wide {b p : ℕ} [Fact p.Prime] [SampleableType (ZMod p)] (hb : 0 < b)
    (hp : 2^180*(b*4096)^2 ≤ p) (dom : Fin (b*4096) ↪ ZMod p) :
    let good := fun (k : ℕ) (r : ℝ) => mcaError (AffineLineGenerator (ZMod p))
      (code dom (b*k)) r ≤ ENNReal.ofReal (1/(2:ℝ)^128)
    good 2048 (1269/4096) ∧ good 1024 (2174/4096) ∧ good 512 (2788/4096) ∧
      good 256 (3201/4096) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := wide_slot_certificates
  have hp' : 2^128 * 2^52 * (b*4096)^2 ≤ p := by
    rw [← pow_add]
    exact hp
  refine ⟨?_,?_,?_,?_⟩
  · exact security_of_slots (K := 2^52) (Θ := 2048/779) (ρ := 1/2) (T := 62686565) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₁ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^52) (Θ := 1536/449) (ρ := 1/4) (T := 74679279) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₂ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^52) (Θ := 896/199) (ρ := 1/8) (T := 447712342) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₃ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^52) (Θ := 1280/213) (ρ := 1/16) (T := 154129969) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₄ hp' dom (by norm_num)

/-- The agreement counts of `four_rates_wide` lie strictly below the finite-length Johnson
threshold `√(n(k−1))` at all four dimensions and every multiple. So do the larger counts of
`four_rates`. -/
theorem below_finite_johnson {b : ℕ} (hb : 0 < b) :
    ((b*2827)^2 < (b*4096)*(b*2048-1) ∧ (b*1922)^2 < (b*4096)*(b*1024-1) ∧
      (b*1308)^2 < (b*4096)*(b*512-1) ∧ (b*895)^2 < (b*4096)*(b*256-1)) ∧
    ((b*2834)^2 < (b*4096)*(b*2048-1) ∧ (b*1930)^2 < (b*4096)*(b*1024-1) ∧
      (b*1316)^2 < (b*4096)*(b*512-1) ∧ (b*901)^2 < (b*4096)*(b*256-1)) := by
  have hpos : (0:ℤ) ≤ b-1 := by omega
  have hb2 : (b:ℤ) ≤ (b:ℤ)^2 := by nlinarith [mul_nonneg hpos (Int.natCast_nonneg b)]
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  all_goals zify [show 1 ≤ b*2048 by omega, show 1 ≤ b*1024 by omega,
    show 1 ≤ b*512 by omega, show 1 ≤ b*256 by omega]; nlinarith

/-! ### List bounds -/

private theorem weight_le_scaled {b : ℕ} (hb : 0 < b) (k μ M : ℕ) :
    firstOrderListWeight (b*k) μ M ≤ b * firstOrderListWeight k μ M := by
  induction μ generalizing M with
  | zero => simp [firstOrderListWeight]
  | succ μ ih =>
    cases M with
    | zero =>
      simp only [firstOrderListWeight, Nat.mul_add]
      have h := ih 0
      nlinarith
    | succ M =>
      simp only [firstOrderListWeight, Nat.mul_add]
      have h := ih M
      nlinarith [Nat.mul_le_mul_left (μ+1) hb]

/-- A slot certificate at reference length `N` bounds the worst-case scalar list at closed
radius `1 - A/N` by `C n`, over every field of characteristic zero or at least `n`. -/
theorem list_of_slots {F : Type*} [Field F] {N b k A m M μ h C : ℕ}
    (hb : 0 < b) (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ N)
    (hμ : μ < N) (hfield : ringChar F = 0 ∨ b*N ≤ ringChar F)
    (hcost : firstOrderListWeight k μ M ≤ C*(A-k))
    (hslots : rowSlots N m M μ h < columnSlots k A m M μ h)
    (dom : Fin (b*N) ↪ F) :
    Code.Lambda (code dom (b*k) : Set (Fin (b*N) → F)) (1-(A:ℝ)/N) ≤
      ((C*(b*N):ℕ):ℕ∞) := by
  classical
  have hNpos : 0 < N := by omega
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNb : N ≤ b*N := Nat.le_mul_of_pos_left N hb
  let g := ((A-k:ℕ):ℝ)/N
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hbR : (b:ℝ) ≠ 0 := by positivity
  have h₁ : capacityAgreementThreshold g (b*N) (b*k) = b*A := by
    have he : g*((b*N:ℕ):ℝ) = ((b*(A-k):ℕ):ℝ) := by
      dsimp [g]
      push_cast
      field_simp
    rw [capacityAgreementThreshold, he, Nat.ceil_natCast, Nat.mul_sub, Nat.add_sub_of_le]
    exact Nat.mul_le_mul_left b hkA.le
  have h₂ : capacityRadius g (b*N) (b*k) = 1-(A:ℝ)/N := by
    unfold capacityRadius g
    rw [Nat.cast_sub hkA.le]
    push_cast
    field_simp
    ring
  rw [← h₂, ← Nat.ceil_natCast (R := ℝ) (C*(b*N))]
  apply lambda_le_ceil_of_closePolynomialSet_bound hg (by omega)
  intro f
  rw [h₁]
  let T := @closePolynomialSet (F) _ (Classical.decEq _) _ dom f (b*k) (b*A)
  have hbk : 2 ≤ b*k := by nlinarith
  have hdiff : 0 < b*A-b*k+1 := Nat.succ_pos _
  have hlt : b*k < b*A := Nat.mul_lt_mul_of_pos_left hkA hb
  have hAn' := Nat.mul_le_mul_left b hAN
  have hchar : ringChar (F) = 0 ∨ max (b*k-1) μ < ringChar (F) := by
    rcases hfield with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by omega)
  have bound (S : Finset (Polynomial (F))) (hST : (↑S : Set _) ⊆ T) : S.card ≤ C*(b*N) := by
    have hpoint (P : Polynomial (F)) (hP : P ∈ S) :
        P.degree < b*k ∧ b*A ≤ ({i : Fin (b*N) | P.eval (dom i) = f i} : Set _).ncard := by
      have h := hST hP
      refine ⟨h.1, h.2.trans_eq ?_⟩
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext i
      simp [polynomialAgreementSet]
    have hbound := finite_firstOrder_list_bound_of_heightSlotCount_sharp
      (D := b*k-1) (K := b*k) (by omega) (by omega) dom f
      (scaled_slots hb hslots) hbk le_rfl (by omega) hlt.le hchar S hpoint
    have hcross := (le_div_iff₀ (by exact_mod_cast hdiff)).mp hbound
    have hN : S.card * (b*A-b*k+1) ≤ (b*N) * firstOrderListWeight (b*k) μ M := by
      exact_mod_cast hcross
    have hw := (weight_le_scaled hb k μ M).trans (Nat.mul_le_mul_left b hcost)
    have hfactor : firstOrderListWeight (b*k) μ M ≤ C*(b*A-b*k+1) := by
      rw [← Nat.mul_sub]
      nlinarith
    exact Nat.le_of_mul_le_mul_right
      (le_trans hN (by simpa [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using
        Nat.mul_le_mul_left (b*N) hfactor)) hdiff
  have hfin : T.Finite := Set.finite_of_forall_finset_card_le (R := ℕ) (ℓ := C*(b*N)) bound
  refine ⟨hfin, ?_⟩
  have h := bound hfin.toFinset (by simp)
  rw [← Set.ncard_eq_toFinset_card _ hfin] at h
  exact_mod_cast h

/-- Linear list bounds at the radii of `four_rates`, over every field of characteristic
zero or at least the block length. -/
theorem four_field_list_bounds {F : Type*} [Field F] {b : ℕ} (hb : 0 < b)
    (hfield : ringChar F = 0 ∨ b*4096 ≤ ringChar F)
    (dom : Fin (b*4096) ↪ F) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (code dom (b*k) : Set (Fin (b*4096) → F)) r ≤ ((C*(b*4096):ℕ):ℕ∞)
    bounded 2048 (1262/4096) 3722270 ∧ bounded 1024 (2166/4096) 3891790 ∧
      bounded 512 (2780/4096) 4624878 ∧ bounded 256 (3195/4096) 5864546 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := slot_certificates
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat, show (1-(2834:ℝ)/4096) = 1262/4096 by norm_num] using
      list_of_slots (C:=3722270) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₁ dom
  · simpa only [Nat.cast_ofNat, show (1-(1930:ℝ)/4096) = 2166/4096 by norm_num] using
      list_of_slots (C:=3891790) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₂ dom
  · simpa only [Nat.cast_ofNat, show (1-(1316:ℝ)/4096) = 2780/4096 by norm_num] using
      list_of_slots (C:=4624878) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₃ dom
  · simpa only [Nat.cast_ofNat, show (1-(901:ℝ)/4096) = 3195/4096 by norm_num] using
      list_of_slots (C:=5864546) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₄ dom

/-- At each prize rate and every prime field admitting the prescribed domain, the scalar
list size at the radii of `four_rates` is at most the indicated constant times the block
length. -/
theorem four_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b*4096) ↪ ZMod p) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (code dom (b*k) : Set (Fin (b*4096) → ZMod p)) r ≤ ((C*(b*4096):ℕ):ℕ∞)
    bounded 2048 (1262/4096) 3722270 ∧ bounded 1024 (2166/4096) 3891790 ∧
      bounded 512 (2780/4096) 4624878 ∧ bounded 256 (3195/4096) 5864546 := by
  apply four_field_list_bounds hb _ dom
  right
  simpa [ZMod.ringChar_zmod_n] using Fintype.card_le_of_injective dom dom.injective

/-- Packing all rows into a rational function preserves the four linear bounds at every
finite interleaving width and for every domain in a prime field. -/
theorem four_interleaved_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b*4096) ↪ ZMod p) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code dom (b*k) : Set (Fin (b*4096) → ZMod p))) r ≤ ((C*(b*4096):ℕ):ℕ∞)
    bounded 2048 (1262/4096) 3722270 ∧ bounded 1024 (2166/4096) 3891790 ∧
      bounded 512 (2780/4096) 4624878 ∧ bounded 256 (3195/4096) 5864546 := by
  let φ := algebraMap (ZMod p) (RatFunc (ZMod p))
  have hsize : b*4096 ≤ p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have hchar : ringChar (RatFunc (ZMod p)) = p := ringChar.eq _ p
  have hlarge : b*4096 ≤ ringChar (RatFunc (ZMod p)) := hsize.trans_eq hchar.symm
  obtain ⟨h₁,h₂,h₃,h₄⟩ := four_field_list_bounds hb (Or.inr hlarge) (dom.trans ⟨φ,φ.injective⟩)
  exact ⟨(Lambda_interleaved_le_ratFunc dom _ width _).trans h₁,
    (Lambda_interleaved_le_ratFunc dom _ width _).trans h₂,
    (Lambda_interleaved_le_ratFunc dom _ width _).trans h₃,
    (Lambda_interleaved_le_ratFunc dom _ width _).trans h₄⟩

end ProximityGap.FineGridFirstOrderSecurity

#print axioms ProximityGap.FineGridFirstOrderSecurity.rank_sum

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_rates

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_rates_wide

#print axioms ProximityGap.FineGridFirstOrderSecurity.below_finite_johnson

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_list_bounds

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_interleaved_list_bounds
