/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionRaiseMCA
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadThresholdCurve

/-! # Exact three-head thresholds below rate one sixteenth

The dimension comparison transfers safety to smaller Reed–Solomon codes.
Where three exceptional heads fit in the domain, the same threshold is exact.
At the second designated field budget this reaches every dimension from two
through 2^26, on every injective domain and at every positive interleaving width.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TerminalDimensionThreshold
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

private theorem attack (dom : I ↪ F) (hn : Fintype.card I=n) {K e B : ℕ}
    (hk : 2≤K) (hK : K≤k) (hl : 671088640≤e) (hu : e≤715827882)
    (hfit : 2*n≤3*e+2*K) (hB : Fintype.card F/2^128=B) (hb : B<3*(e+1)) :
    tolerance < epsMCA (F:=F) (ReedSolomon.code dom K : Set (I → F)) ((e:ℝ≥0)/n) := by
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
  have hs := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0<2^128)
  have hq : Fintype.card F≤2^256 := by omega
  by_cases h3 : 3≤K
  · refine ExceptionalHeadLocatorMass.over_budget_128 (m:=3) (t:=n-e) x _ (by decide) h3
      (by dsimp [n,k] at hK ⊢; omega) (Nat.sub_le ..) (by dsimp [n] at hfit ⊢; omega) ?_ hq ?_
    · rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n]),← Nat.cast_tsub]
    · rw [hB,show n-(n-e)=e by dsimp [n]; omega]
      exact hb
  · have he : e=715827882 := by dsimp [n] at hfit; omega
    subst e
    apply ManyHeadLocatorMass.over_budget_128 (h:=0) (d:=2) (r:=357913941) x _
      (by decide) hk (by dsimp [k] at hK; omega) ?_ hq (by rw [hB]; exact hb)
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n])]
    exact tsub_le_iff_right.mpr (by norm_num [n])

/-- Field budgets and dimensions for which the numerator bound and the three-head construction meet. -/
theorem prime_classification {p B K : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hk : 2≤K) (hK : K≤k) (hB : p/2^128=B) (hl : 1565873494≤B) (hu : B≤2147483648)
    (hfit : 2*n≤3*(max 671088640 (B/3))+2*K) (width : ℕ) [NeZero width] :
    let e := max 671088640 (B/3)
    let t : ℝ≥0 := (e:ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom K : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance=t ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) ((ReedSolomon.code dom K : Set (I → ZMod p)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<t := by
  classical
  let e := max 671088640 (B/3)
  let t : ℝ≥0 := (e:ℝ≥0)/n
  let pred : ℝ≥0 := ((e-1:ℕ):ℝ≥0)/n
  have he : 671088640≤e := le_max_left ..
  have he' : e≤715827882 := by dsimp [e]; omega
  have ht : k<⌈(1-pred)*(Fintype.card I:ℝ≥0)⌉₊ := by
    have h := TwoCorePackingThreshold.agreement_ceiling (e-1) (by change e-1≤1073741824; omega)
    rw [Fintype.card_fin] at h
    rw [hn]
    change k<⌈(1-((e-1:ℕ):ℝ≥0)/n)*(n:ℝ≥0)⌉₊
    rw [h]
    change 67108864<1073741824-(e-1)
    omega
  have hp : epsMCA (F:=ZMod p) (ReedSolomon.code dom K : Set (I → ZMod p)) pred≤tolerance := by
    apply (DimensionRaiseMCA.eps_mono_dimension dom (by omega) hK pred ht).trans
    have h := (ThreeHeadThresholdCurve.prime_classification dom hn hB hl hu 1).2 pred
    rw [epsMCA_interleaved_eq] at h
    apply h.mpr
    change ((e-1:ℕ):ℝ≥0)/n < (e:ℝ≥0)/n
    apply (div_lt_div_iff_of_pos_right (by norm_num [n] : (0:ℝ≥0)<n)).mpr
    exact_mod_cast (show e-1<e by omega)
  have hb : tolerance < epsMCA (F:=ZMod p) (ReedSolomon.code dom K : Set (I → ZMod p)) t :=
    attack dom hn hk hK he he' hfit (by simpa only [ZMod.card] using hB) (by dsimp [e]; omega)
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) K
  have heq : mcaDeltaStar (F:=ZMod p) (ReedSolomon.code dom K : Set (I → ZMod p)) tolerance=t := by
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
    exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a:=e) (by omega) (by dsimp [n]; omega) _ _ (by rw [← hre]; exact hp) (by rw [← hre]; exact hb)
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact heq,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! hδ
    exact hb.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! bad
    have h := mcaDeltaStar_le_of_bad _ _ bad
    rw [heq] at h
    exact hδ.not_ge h

/-- At the second designated prime's budget the same sharp cutoff applies to
all 67,108,863 code dimensions from two through 2^26. -/
theorem twice_length_budget {p K : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I=n)
    (hk : 2≤K) (hK : K≤k) (hB : p/2^128=2147483648) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=ZMod p) ((ReedSolomon.code dom K : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance=boundary ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod p) ((ReedSolomon.code dom K : Set (I → ZMod p)) ^⋈ (Fin width)) δ≤tolerance ↔ δ<boundary :=
  prime_classification dom hn hk hK hB (by decide) (by decide) (by dsimp [n]; omega) width

section Named
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.PrizeShapePrimeP30Second
local instance : Fact P.Prime := ⟨prime_P⟩

/-- Literal specialization to the second production subgroup at every covered dimension. -/
theorem second_prime {K : ℕ} (hk : 2≤K) (hK : K≤67108864) (width : ℕ) [NeZero width] :
    let C := (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2^30) (K-1)) ^⋈ (Fin width)
    mcaDeltaStar (F:=ZMod P) C tolerance=boundary ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod P) C δ≤tolerance ↔ δ<boundary := by
  let G := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
  have hG := KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g
  dsimp only
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon G orderOf_g hG (K-1),show K-1+1=K by omega]
  exact twice_length_budget _ (by simp [n]) hk hK (by decide) width
end Named

#print axioms second_prime
#print axioms prime_classification
#print axioms twice_length_budget
end ArkLib.ProximityGap.Frontier.TerminalDimensionThreshold
