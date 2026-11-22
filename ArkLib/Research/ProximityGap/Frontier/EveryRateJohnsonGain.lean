/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.RateBounds

/-! # An explicit positive Johnson improvement at every physical rate

Rationalizing the canonical first-order agreement threshold gives a lower
bound on its distance below `sqrt R`. Half this improvement can be spent on
interpolation slack while retaining explicit field and list bounds.
-/
namespace ProximityGap.EveryRateJohnsonGain
open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions

/-- The explicit additive radius improvement at physical rate `R`. -/
noncomputable def gain (R : ℝ) : ℝ := (3/32)*Real.sqrt R*(1-Real.sqrt R)^2

theorem gain_pos {R : ℝ} (hr : 0<R) (hr' : R<1) : 0<gain R := by
  have hx := Real.sqrt_lt_sqrt hr.le hr'
  rw [Real.sqrt_one] at hx
  dsimp [gain]
  positivity [sub_pos.mpr hx]

/-- The canonical first-order threshold leaves at least twice `gain R` of
room below the Johnson agreement fraction. -/
theorem threshold_margin {R : ℝ} (hr : 0<R) (hr' : R<1) :
    firstOrderRateThreshold R+2*gain R ≤ Real.sqrt R := by
  let x := Real.sqrt R
  let s := Real.sqrt (R*(5-R)*(2-R))
  let a := firstOrderRateThreshold R
  let D := x*(8-R)-3*R
  have xp : 0<x := Real.sqrt_pos.mpr hr
  have xs : x^2=R := Real.sq_sqrt hr.le
  have ss : s^2=R*(5-R)*(2-R) := Real.sq_sqrt (firstOrderRateThreshold_radicand_pos hr (by linarith)).le
  have dr : 0<8-R := by linarith
  have ea : a*(8-R) = 3*R+2*s := div_mul_cancel₀ _ dr.ne'
  have xa : a<x := firstOrderRateThreshold_lt_sqrt hr hr'
  have fac : (x-a)*(8-R)=D-2*s := by dsimp [D]; linarith only [ea]
  have sq : (D-2*s)*(D+2*s)=3*R*(1-x)^2*(8-R) := by
    dsimp [D]
    rw [show (x*(8-R)-3*R-2*s)*(x*(8-R)-3*R+2*s)=(x*(8-R)-3*R)^2-4*s^2 by ring,ss,←xs]
    ring
  have prod : (x-a)*(D+2*s)=3*R*(1-x)^2 := by
    apply mul_right_cancel₀ dr.ne'
    calc (x-a)*(D+2*s)*(8-R) = ((x-a)*(8-R))*(D+2*s) := by ring
         _ = _ := by rw [fac,sq]
  have small : 2*s≤D := by linarith only [fac,mul_pos (sub_pos.mpr xa) dr]
  have cap : D+2*s≤16*x := by
    dsimp [D] at small ⊢
    nlinarith only [small,mul_nonneg xp.le hr.le,hr]
  have bound := mul_le_mul_of_nonneg_left cap (sub_nonneg.mpr xa.le)
  rw [prod,←xs] at bound
  have bound' : (3/16*x*(1-x)^2)*x ≤ (x-a)*x := by linarith only [bound]
  have unc := (mul_le_mul_iff_left₀ xp).mp bound'
  change a+2*(3/32*x*(1-x)^2) ≤ x
  linarith only [unc]

/-- One rate-only coefficient suffices to cover both the characteristic
requirement and the normalized exceptional-scalar count. -/
noncomputable def coefficient (R : ℝ) : ℝ := max
  (automaticExceptionBoundConstant R/(gain R)^5) (1+automaticMultiplicityBoundConstant R/gain R)

private theorem slack {R : ℝ} (hr : 0<R) (hr' : R<1) : let a := Real.sqrt R-gain R
    let η := a-firstOrderRateThreshold R
    0<η ∧ gain R≤η ∧ firstOrderRateThreshold R+η=a ∧ a<1 := by
  dsimp only
  have gp := gain_pos hr hr'
  have marg := threshold_margin hr hr'
  have hx := Real.sqrt_lt_sqrt hr.le hr'
  rw [Real.sqrt_one] at hx
  exact ⟨by linarith,by linarith,by ring,by linarith⟩

/-- On any supplied prime-field domain and at any tolerance `1/Q`, field
size `Q C(R) n²` suffices at radius `1−sqrt R+gain R`. The rate may be any
real upper bound for the actual dimension divided by the block length. -/
theorem every_rate_security {R : ℝ} (hr : 0<R) (hr' : R<1) {p n k Q : ℕ}
    [Fact p.Prime] [SampleableType (ZMod p)] (hk : 2≤k) (hkR : (k:ℝ)≤R*n)
    (hQ : 1≤Q) (hp : (Q:ℝ)*coefficient R*(n:ℝ)^2≤p) (dom : Fin n ↪ ZMod p) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom k) (1-Real.sqrt R+gain R) ≤
      ENNReal.ofReal (1/(Q:ℝ)) := by
  let a := Real.sqrt R-gain R
  let η := a-firstOrderRateThreshold R
  obtain ⟨he,hg,ha,ha1⟩ := slack hr hr'
  change 0<η at he
  change gain R≤η at hg
  change firstOrderRateThreshold R+η=a at ha
  change a<1 at ha1
  have haOne := ha.trans_lt ha1
  have gpos := gain_pos hr hr'
  have mc := automaticMultiplicityBoundConstant_pos (rho:=R) hr'
  have ec := automaticExceptionBoundConstant_pos R
  have coeffp : 0≤coefficient R := (div_nonneg ec.le (pow_pos gpos _).le).trans (le_max_left ..)
  have qr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have nn : 1≤n := by
    by_contra! hn
    have : n=0 := by omega
    rw [this,Nat.cast_zero,mul_zero] at hkR
    exact (not_lt_of_ge hkR) (by exact_mod_cast (show 0<k by omega))
  have n1 : (1:ℝ)≤n := by exact_mod_cast nn
  have small : coefficient R ≤ p := calc
    _ = (1:ℝ)*coefficient R*1^2 := by ring
    _ ≤ (Q:ℝ)*coefficient R*(n:ℝ)^2 := by gcongr
    _ ≤ _ := hp
  have ch : ringChar (ZMod p)=0 ∨ max (k-1) (automaticDerivativeCap R (firstOrderRateThreshold R+η))<ringChar (ZMod p) := by
    right
    rw [ZMod.ringChar_zmod_n]
    have dim : (k:ℝ)<n := hkR.trans_lt ((mul_lt_mul_iff_left₀ (lt_of_lt_of_le zero_lt_one n1)).mpr hr' |>.trans_eq (one_mul _))
    have np : n≤p := by simpa using Fintype.card_le_of_injective dom dom.injective
    have kb : k<n := by exact_mod_cast dim
    refine max_lt (by omega) ?_
    have capp := (automaticDerivativeCap_le_inv_eta hr hr' he haOne).trans
      (div_le_div_of_nonneg_left mc.le gpos hg)
    have coeff2 := (le_max_right (automaticExceptionBoundConstant R/gain R^5)
      (1+automaticMultiplicityBoundConstant R/gain R)).trans small
    exact_mod_cast (show (automaticDerivativeCap R (firstOrderRateThreshold R+η):ℝ)<p by linarith)
  have raw := automaticFirstOrder_rate_mcaError_le R η n k hr' he haOne hk hkR dom ch
  rw [ha,ZMod.card] at raw
  change mcaError _ _ (1-Real.sqrt R+gain R) ≤ _
  rw [show 1-Real.sqrt R+gain R=1-a by dsimp only [a]; ring]
  apply (raw.trans (min_le_right ..)).trans
  apply ENNReal.ofReal_le_ofReal
  have ppos : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (div_le_div_iff₀ ppos (by linarith : (0:ℝ)<Q)).mpr
  have cb : automaticExceptionBoundConstant R/η^5 ≤ coefficient R :=
    (div_le_div_of_nonneg_left ec.le (pow_pos gpos 5) (pow_le_pow_left₀ gpos.le hg 5)).trans
      (le_max_left ..)
  have total := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cb (Nat.cast_nonneg Q))
    (sq_nonneg (n:ℝ))).trans hp
  simp only [div_eq_mul_inv, one_mul] at total ⊢
  linarith only [total]

/-- For the actual code rate, block lengths with `n sqrt(R) gain(R) ≥ 2`
allow half the explicit gain beyond the *finite-length* Johnson radius. -/
theorem finite_johnson_security {R : ℝ} (hr : 0<R) (hr' : R<1) {p n k Q : ℕ}
    [Fact p.Prime] [SampleableType (ZMod p)] (hk : 2≤k) (hkR : (k:ℝ)=R*n)
    (hlen : 2≤gain R*Real.sqrt R*n) (hQ : 1≤Q)
    (hp : (Q:ℝ)*coefficient R*(n:ℝ)^2≤p) (dom : Fin n ↪ ZMod p) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom k)
      (1-Real.sqrt (((k:ℝ)-1)/n)+gain R/2) ≤ ENNReal.ofReal (1/(Q:ℝ)) := by
  let x := Real.sqrt R
  let y := Real.sqrt (((k:ℝ)-1)/n)
  have nn : (0:ℝ)<n := by
    by_contra! h
    have ez := le_antisymm h (Nat.cast_nonneg n)
    rw [ez,mul_zero] at hkR
    have : (2:ℝ)≤k := by exact_mod_cast hk
    linarith
  have xp : 0<x := Real.sqrt_pos.mpr hr
  have yp : 0≤y := Real.sqrt_nonneg _
  have kpos : (2:ℝ)≤k := by exact_mod_cast hk
  have squareX : x^2*(n:ℝ)=k := by rw [show x^2=R from Real.sq_sqrt hr.le,←hkR]
  have squareY : y^2*(n:ℝ)=(k:ℝ)-1 := by
    rw [show y^2=((k:ℝ)-1)/n from Real.sq_sqrt (div_nonneg (by linarith) nn.le),div_mul_cancel₀ _ nn.ne']
  have yx : y≤x := Real.sqrt_le_sqrt ((div_le_iff₀ nn).mpr (by linarith))
  have eq : (x-y)*(x+y)*n=1 := by linarith only [squareX,squareY]
  have comp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right yp : x≤x+y) (sub_nonneg.mpr yx)) nn.le
  change 2≤gain R*x*n at hlen
  have hdiff : (x-y)*(x*n)≤(gain R/2)*(x*n) := by linarith only [eq,comp,hlen]
  have hd := (mul_le_mul_iff_left₀ (mul_pos xp nn)).mp hdiff
  apply (mcaError_mono _ _ ?_).trans (every_rate_security hr hr' hk hkR.le hQ hp dom)
  change 1-y+gain R/2≤1-x+gain R
  linarith only [hd]

end ProximityGap.EveryRateJohnsonGain

#print axioms ProximityGap.EveryRateJohnsonGain.threshold_margin
#print axioms ProximityGap.EveryRateJohnsonGain.every_rate_security
#print axioms ProximityGap.EveryRateJohnsonGain.finite_johnson_security
