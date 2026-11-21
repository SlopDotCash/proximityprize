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
# First-order certificates on the 4096 agreement grid

`ScaledFirstOrderSecurity` certifies line MCA beyond the Johnson radius from slot
inequalities at reference length 128. The same first-order interpolation system has
strict surpluses at larger radii when the reference length is 4096 and the
interpolation parameters are larger. This file states the transfer for an arbitrary
reference length and an explicit exceptional-count constant, and instantiates it twice.

* `four_rates` keeps the field-size hypothesis `2^165 n² ≤ p` of the earlier theorem and
  raises the closed radii to `1260/4096`, `2164/4096`, `2778/4096`, `3194/4096`.
* `four_rates_wide` assumes `2^171 n² ≤ p` and reaches `1265/4096`, `2170/4096`,
  `2783/4096`, `3197/4096`.

Both hold on every injective evaluation domain of length `4096 b` in a prime field.
The matching scalar and interleaved list bounds need no field-size hypothesis.

## References

* [DKT26]
-/

namespace ProximityGap.FineGridFirstOrderSecurity

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions Finset

/-- Row slots of the shifted first-order interpolation system at reference length `n`. -/
def rowSlots (n m M μ h : ℕ) : ℕ :=
  ∑ t ∈ range (μ+1), n * (∑ s ∈ range m,
    min (m-s) (min t s + 1 - (t-M))) * (h+1-t)

/-- Column slots at reference dimension `k` and agreement count `A`. -/
def columnSlots (k A m M μ h : ℕ) : ℕ :=
  ∑ t ∈ range (μ+1), ∑ _b ∈ range (min t M+1), (m*A-k*t)*(h+1-t)

private theorem row_le (b n D A m M μ h : ℕ) :
    firstOrderCurveShiftedRowSlotBound D A m M μ (b*n) 1 h ≤ b * rowSlots n m M μ h := by
  unfold firstOrderCurveShiftedRowSlotBound rowSlots
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro t _
  rw [one_mul, ← mul_assoc b, ← mul_assoc b]
  gcongr
  unfold firstOrderGradedRankBound
  apply sum_le_sum
  intro s _
  unfold firstOrderGradedSourceCount
  split_ifs <;> simp

private theorem column_le (b k A m M μ h : ℕ) :
    b * columnSlots k A m M μ h ≤
      firstOrderCurveShiftedHeightSlotCount (b*k-1) (b*A) m M μ 1 h := by
  unfold firstOrderCurveShiftedHeightSlotCount columnSlots
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
  apply (div_le_div_iff₀ (by exact_mod_cast (Fact.out : p.Prime).pos) (by norm_num : (0:ℝ)<2^128)).mpr
  have h : (2:ℝ)^128 * K * ((b*N:ℕ):ℝ)^2 ≤ p := by exact_mod_cast hp
  dsimp [B]
  linarith

/-! Each slot inequality is a separate kernel evaluation, so the eight checks elaborate
independently. -/

private theorem slots_half :
    rowSlots 4096 86 24 215 17200 < columnSlots 2048 2836 86 24 215 17200 := by
  decide +kernel

private theorem slots_quarter :
    rowSlots 4096 86 39 172 13760 < columnSlots 1024 1932 86 39 172 13760 := by
  decide +kernel

private theorem slots_eighth :
    rowSlots 4096 86 47 215 17200 < columnSlots 512 1318 86 47 215 17200 := by
  decide +kernel

private theorem slots_sixteenth :
    rowSlots 4096 86 60 387 30960 < columnSlots 256 902 86 60 387 30960 := by
  decide +kernel

private theorem wide_slots_half :
    rowSlots 4096 170 54 612 48960 < columnSlots 2048 2831 170 54 612 48960 := by
  decide +kernel

private theorem wide_slots_quarter :
    rowSlots 4096 170 76 935 74800 < columnSlots 1024 1926 170 76 935 74800 := by
  decide +kernel

private theorem wide_slots_eighth :
    rowSlots 4096 170 94 510 40800 < columnSlots 512 1313 170 94 510 40800 := by
  decide +kernel

private theorem wide_slots_sixteenth :
    rowSlots 4096 170 102 612 48960 < columnSlots 256 899 170 102 612 48960 := by
  decide +kernel

/-- The four slot inequalities at reference length 4096 whose exception constants stay
below `2^37 n²`. -/
theorem slot_certificates :
    rowSlots 4096 86 24 215 17200 < columnSlots 2048 2836 86 24 215 17200 ∧
    rowSlots 4096 86 39 172 13760 < columnSlots 1024 1932 86 39 172 13760 ∧
    rowSlots 4096 86 47 215 17200 < columnSlots 512 1318 86 47 215 17200 ∧
    rowSlots 4096 86 60 387 30960 < columnSlots 256 902 86 60 387 30960 :=
  ⟨slots_half, slots_quarter, slots_eighth, slots_sixteenth⟩

/-- The four slot inequalities at reference length 4096 whose exception constants stay
below `2^43 n²`. -/
theorem wide_slot_certificates :
    rowSlots 4096 170 54 612 48960 < columnSlots 2048 2831 170 54 612 48960 ∧
    rowSlots 4096 170 76 935 74800 < columnSlots 1024 1926 170 76 935 74800 ∧
    rowSlots 4096 170 94 510 40800 < columnSlots 512 1313 170 94 510 40800 ∧
    rowSlots 4096 170 102 612 48960 < columnSlots 256 899 170 102 612 48960 :=
  ⟨wide_slots_half, wide_slots_quarter, wide_slots_eighth, wide_slots_sixteenth⟩

/-- At every length `4096 b` and every prescribed prime-field domain, the four listed
radii give 128-bit line MCA security when `p ≥ 2^165 n²`. The field-size hypothesis is
the one of `ScaledFirstOrderSecurity.four_rates`; the radii are larger. -/
theorem four_rates {b p : ℕ} [Fact p.Prime] [SampleableType (ZMod p)] (hb : 0 < b)
    (hp : 2^165*(b*4096)^2 ≤ p) (dom : Fin (b*4096) ↪ ZMod p) :
    let good := fun (k : ℕ) (r : ℝ) => mcaError (AffineLineGenerator (ZMod p))
      (code dom (b*k)) r ≤ ENNReal.ofReal (1/(2:ℝ)^128)
    good 2048 (1260/4096) ∧ good 1024 (2164/4096) ∧ good 512 (2778/4096) ∧
      good 256 (3194/4096) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := slot_certificates
  have hp' : 2^128 * 2^37 * (b*4096)^2 ≤ p := by
    rw [← pow_add]
    exact hp
  refine ⟨?_,?_,?_,?_⟩
  · exact security_of_slots (K := 2^37) (Θ := 13/5) (ρ := 1/2) (T := 119500) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₁ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^37) (Θ := 17/5) (ρ := 1/4) (T := 228020) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₂ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^37) (Θ := 9/2) (ρ := 1/8) (T := 414728) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₃ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^37) (Θ := 6) (ρ := 1/16) (T := 1270630) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₄ hp' dom (by norm_num)

/-- With the larger field-size hypothesis `p ≥ 2^171 n²` the four closed radii rise to
`1265/4096`, `2170/4096`, `2783/4096` and `3197/4096`. At length `2^30` the hypothesis
reads `p ≥ 2^231`. -/
theorem four_rates_wide {b p : ℕ} [Fact p.Prime] [SampleableType (ZMod p)] (hb : 0 < b)
    (hp : 2^171*(b*4096)^2 ≤ p) (dom : Fin (b*4096) ↪ ZMod p) :
    let good := fun (k : ℕ) (r : ℝ) => mcaError (AffineLineGenerator (ZMod p))
      (code dom (b*k)) r ≤ ENNReal.ofReal (1/(2:ℝ)^128)
    good 2048 (1265/4096) ∧ good 1024 (2170/4096) ∧ good 512 (2783/4096) ∧
      good 256 (3197/4096) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := wide_slot_certificates
  have hp' : 2^128 * 2^43 * (b*4096)^2 ≤ p := by
    rw [← pow_add]
    exact hp
  refine ⟨?_,?_,?_,?_⟩
  · exact security_of_slots (K := 2^43) (Θ := 21/8) (ρ := 1/2) (T := 1711215) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₁ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^43) (Θ := 7/2) (ρ := 1/4) (T := 5176094) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₂ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^43) (Θ := 9/2) (ρ := 1/8) (T := 3996175) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₃ hp' dom (by norm_num)
  · exact security_of_slots (K := 2^43) (Θ := 6) (ρ := 1/16) (T := 5717015) hb
      (by decide) (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [stageStaircase]) (by decide) (by norm_num)
      h₄ hp' dom (by norm_num)

/-- The agreement counts of `four_rates` lie strictly below the finite-length Johnson
threshold `√(n(k−1))` at all four dimensions and every multiple. The counts of
`four_rates_wide` are smaller still. -/
theorem below_finite_johnson {b : ℕ} (hb : 0 < b) :
    (b*2836)^2 < (b*4096)*(b*2048-1) ∧ (b*1932)^2 < (b*4096)*(b*1024-1) ∧
    (b*1318)^2 < (b*4096)*(b*512-1) ∧ (b*902)^2 < (b*4096)*(b*256-1) := by
  have hpos : (0:ℤ) ≤ b-1 := by omega
  have hb2 : (b:ℤ) ≤ (b:ℤ)^2 := by nlinarith [mul_nonneg hpos (Int.natCast_nonneg b)]
  refine ⟨?_,?_,?_,?_⟩
  all_goals zify [show 1 ≤ b*2048 by omega, show 1 ≤ b*1024 by omega,
    show 1 ≤ b*512 by omega, show 1 ≤ b*256 by omega]; nlinarith

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
    bounded 2048 (1260/4096) 5146851 ∧ bounded 1024 (2164/4096) 2056867 ∧
      bounded 512 (2778/4096) 2200781 ∧ bounded 256 (3194/4096) 6075100 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := slot_certificates
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat, show (1-(2836:ℝ)/4096) = 1260/4096 by norm_num] using
      list_of_slots (C:=5146851) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₁ dom
  · simpa only [Nat.cast_ofNat, show (1-(1932:ℝ)/4096) = 2164/4096 by norm_num] using
      list_of_slots (C:=2056867) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₂ dom
  · simpa only [Nat.cast_ofNat, show (1-(1318:ℝ)/4096) = 2778/4096 by norm_num] using
      list_of_slots (C:=2200781) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₃ dom
  · simpa only [Nat.cast_ofNat, show (1-(902:ℝ)/4096) = 3194/4096 by norm_num] using
      list_of_slots (C:=6075100) hb (by decide) (by decide) (by decide) (by decide) hfield
        (by decide +kernel) h₄ dom

/-- At each prize rate and every prime field admitting the prescribed domain, the scalar
list size at the radii of `four_rates` is at most the indicated constant times the block
length. -/
theorem four_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b*4096) ↪ ZMod p) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (code dom (b*k) : Set (Fin (b*4096) → ZMod p)) r ≤ ((C*(b*4096):ℕ):ℕ∞)
    bounded 2048 (1260/4096) 5146851 ∧ bounded 1024 (2164/4096) 2056867 ∧
      bounded 512 (2778/4096) 2200781 ∧ bounded 256 (3194/4096) 6075100 := by
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
    bounded 2048 (1260/4096) 5146851 ∧ bounded 1024 (2164/4096) 2056867 ∧
      bounded 512 (2778/4096) 2200781 ∧ bounded 256 (3194/4096) 6075100 := by
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

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_rates

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_rates_wide

#print axioms ProximityGap.FineGridFirstOrderSecurity.below_finite_johnson

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_list_bounds

#print axioms ProximityGap.FineGridFirstOrderSecurity.four_interleaved_list_bounds
