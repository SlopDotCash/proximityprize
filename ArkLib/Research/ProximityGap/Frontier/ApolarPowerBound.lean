/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA

/-! # Optimizing the apolar interpolation power for the scalar MCA event

The numerator at the unique-decoding endpoint is bounded by a multiple
of the size of one exceptional fiber. Below it, the optimal interpolation
power is the first integer exceeding the ratio of the two coordinate degrees.
-/

set_option autoImplicit false
open Finset Code ProximityGap
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.KKH26
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.ApolarPowerBound

/-- The smallest admissible interpolation power in the unique-decoding range
gives a uniform count for the actual scalar MCA event. -/
theorem family {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {dom : ι ↪ F} {k e d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (hed : e≤d) (hlen : 2*e≤d+1)
    (hk : 1≤k) (hd : k+d<Fintype.card ι)
    (he : Fintype.card ι-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊) :
    let power := (Fintype.card ι-e)/(d+2-e)+1
    fam.G.card ≤ max (e+1) (power*(e/(d+2-2*e)+1)) := by
  dsimp only
  apply SharpApolarMCA.family_bound_power _ (Nat.succ_pos _) fam fam.G Finset.Subset.rfl hed hlen hk hd he
  have hdiv := (Nat.div_lt_iff_lt_mul (k:=d+2-e) (by omega)).mp
    (Nat.lt_succ_self ((Fintype.card ι-e)/(d+2-e)))
  calc
    Fintype.card ι = (Fintype.card ι-e)+e := (Nat.sub_add_cancel (by omega)).symm
    _ < _ := Nat.add_lt_add_right hdiv _

/-- At the exact unique-decoding endpoint, the worst-case numerator is at
most the largest multiple of e+1 less than or equal to n+1. -/
theorem endpoint {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {dom : ι ↪ F} {n k e : ℕ}
    {δ : ℝ≥0} {u : WordStack F (Fin 2) ι} (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card ι=n) (hshape : n=k+2*e) (hk : 1≤k) (herr : 0<e)
    (he : n-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊) :
    fam.G.card ≤ ((n+1)/(e+1))*(e+1) := by
  let m := (n+1)/(e+1)
  have hm : 0 < m := Nat.div_pos (by omega) (by omega)
  have hs := (Nat.div_lt_iff_lt_mul (k:=e+1) (by omega)).mp (Nat.lt_succ_self m)
  rw [Nat.succ_mul] at hs
  have h := SharpApolarMCA.family_bound_power m hm (d:=2*e-1) (e:=e) fam fam.G
    Finset.Subset.rfl (by omega) (by omega) hk (by omega) (by simpa only [hn] using he) (by
      rw [hn,show 2*e-1+2-e = e+1 by omega]
      omega)
  rw [show 2*e-1+2-2*e=1 by omega,Nat.div_one,max_eq_right] at h
  · exact h
  · simpa only [one_mul] using Nat.mul_le_mul_right (e+1) (show 1 ≤ m from hm)

/-- Before the unique-decoding boundary, the spike bound is exact on the
upper side for every domain satisfying the same rate condition. -/
theorem lower_rate_interior_family {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {dom : ι ↪ F} {n k a e : ℕ}
    {δ : ℝ≥0} {u : WordStack F (Fin 2) ι} (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card ι=n) (hshape : n=k+2*a) (hk : 1≤k) (hea : e<a) (hlow : n≤3*a+1)
    (he : n-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊) : fam.G.card ≤ e+1 := by
  classical
  let d := 2*a-1
  have hed : e≤d := by dsimp [d]; omega
  have hlen : 2*e≤d+1 := by dsimp [d]; omega
  have hdeg : k+d<Fintype.card ι := by dsimp [d]; omega
  have hag : Fintype.card ι-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊ := by simpa only [hn] using he
  by_cases hz : e=0
  · by_contra! hmany
    obtain ⟨r,hre,l,hr,_⟩ := _root_.ProximityGap.ApolarUnitChartData.of_mca_family
      (algebraMap F (AlgebraicClosure F)) fam fam.G Finset.Subset.rfl hmany hed hlen hk hdeg hag
    omega
  have hsize : Fintype.card ι < 2*(d+2-e)+e := by dsimp [d]; omega
  have h := SharpApolarMCA.family_bound_power 2 (by decide) fam fam.G Finset.Subset.rfl
      hed hlen hk hdeg hag hsize
  have h3 : 3 ≤ d+2-2*e := by dsimp [d]; omega
  have hquot : 3*(e/(d+2-2*e)) ≤ e :=
    (Nat.mul_le_mul_right _ h3).trans (Nat.mul_div_le e (d+2-2*e))
  apply h.trans (max_le (le_refl _) (by omega))

/-- Every Hamming step strictly before the low-rate endpoint has exactly
e+1 bad scalars in the worst case on a prime-field subgroup. -/
theorem lower_rate_interior_mass {p n k a e : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p}
    (hg : orderOf g=n) (hshape : n=k+2*a) (hk : 1≤k) (hea : e<a) (hlow : n≤3*a+1) :
    epsMCA (F := ZMod p) (evalCode g n (k-1)) (1-((n-e:ℕ):ℝ≥0)/(n:ℝ≥0)) =
      ((e+1:ℕ):ℝ≥0∞)/(p:ℝ≥0∞) := by
  apply le_antisymm
  · classical
    let dom := KKH26RegimeSplit.powDomain g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
    let δ : ℝ≥0 := 1-((n-e:ℕ):ℝ≥0)/(n:ℝ≥0)
    rw [KKH26RegimeSplit.evalCode_eq_reedSolomon g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg),
      show k-1+1=k by omega]
    apply (epsMCA_le_of_badCount_le _ _ (e+1) ?_).trans (by rw [ZMod.card])
    intro u
    let fam := canonicalBadScalarRichPointFamily dom δ u hk
    have hceil := ceil_one_sub_one_sub_div (ι:=Fin n) (n-e) (by simp)
    exact lower_rate_interior_family fam (Fintype.card_fin _) hshape hk hea hlow (by
      simpa only [δ,Fintype.card_fin] using hceil.ge)
  · let dom := Ownership.smoothDom g n hg
    let pos : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
    have hn : (n:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne n
    have hfrac : (e:ℝ≥0)/(n:ℝ≥0)≤1 :=
      (div_le_one (pos_iff_ne_zero.mpr hn)).2 (by exact_mod_cast (by omega : e≤n))
    rw [Ownership.evalCode_pred_eq_rsCode hg hk]
    conv_lhs => rw [← ZMod.card p]
    apply SpikeFloor.epsMCA_ge_j_div_card (SpikeFloor.rsCode dom k)
      (SpikeFloor.rsCode_noWeightLE dom (by omega : e+1+k≤n)) _ (by omega)
      (by rw [Fintype.card_fin]; omega) pos (pos.trans dom) (b:=(1:ZMod p)) one_ne_zero
    rw [Fintype.card_fin,Nat.add_sub_cancel,Nat.cast_tsub,tsub_div,div_self hn,
      tsub_tsub_cancel_of_le hfrac,div_mul_cancel₀ _ hn]

/-- Every prime-field subgroup realizes exactly two full exceptional sets at
the unique-decoding endpoint when n is at most 3e+1 and the dimension is at least two. -/
theorem lower_rate_mass {p n k e : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p}
    (hg : orderOf g=n) (hshape : n=k+2*e) (hk : 2≤k) (herr : 0<e) (hlow : n≤3*e+1) :
    epsMCA (F := ZMod p) (evalCode g n (k-1)) (1-((n-e:ℕ):ℝ≥0)/(n:ℝ≥0)) =
      ((2*e+2:ℕ):ℝ≥0∞)/(p:ℝ≥0∞) := by
  apply le_antisymm
  · classical
    let dom := KKH26RegimeSplit.powDomain g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
    let δ : ℝ≥0 := 1-((n-e:ℕ):ℝ≥0)/(n:ℝ≥0)
    rw [KKH26RegimeSplit.evalCode_eq_reedSolomon g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg),
      show k-1+1=k by omega]
    apply (epsMCA_le_of_badCount_le _ _ (2*e+2) ?_).trans (by rw [ZMod.card])
    intro u
    let fam := canonicalBadScalarRichPointFamily dom δ u (by omega : 1≤k)
    change fam.G.card ≤ 2*e+2
    have hceil := ceil_one_sub_one_sub_div (ι:=Fin n) (n-e) (by simp)
    have h := endpoint (n:=n) (e:=e) fam (Fintype.card_fin _) hshape (by omega) herr (by
      simpa only [δ,Fintype.card_fin] using hceil.ge)
    have htwo : (n+1)/(e+1)=2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rwa [htwo, Nat.mul_add, Nat.mul_one] at h
  · exact BadFamilyCensus.bisimplex_epsMCA_lower_bound hg (by omega) (by omega) (by omega) (by omega)

/-- The exact scalar numerators at the last unique-decoding step of each
of the three lower production rates on every eligible subgroup. -/
theorem production_lower_rates {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g=1073741824) :
    epsMCA (F := ZMod p) (FourRatePairBudget.code g (2^28)) (3/8) = 805306370/(p:ℝ≥0∞) ∧
    epsMCA (F := ZMod p) (FourRatePairBudget.code g (2^27)) (7/16) = 939524098/(p:ℝ≥0∞) ∧
    epsMCA (F := ZMod p) (FourRatePairBudget.code g (2^26)) (15/32) = 1006632962/(p:ℝ≥0∞) := by
  refine ⟨?_,?_,?_⟩
  · have h := lower_rate_mass (k:=2^28) (e:=402653184) hg (by decide) (by decide) (by decide) (by decide)
    norm_num at h
    norm_num [FourRatePairBudget.code,FourRatePairBudget.n]
    simpa only [show (1:ℝ≥0)-5/8=3/8 from tsub_eq_of_eq_add (by norm_num)] using h
  · have h := lower_rate_mass (k:=2^27) (e:=469762048) hg (by decide) (by decide) (by decide) (by decide)
    norm_num at h
    norm_num [FourRatePairBudget.code,FourRatePairBudget.n]
    simpa only [show (1:ℝ≥0)-9/16=7/16 from tsub_eq_of_eq_add (by norm_num)] using h
  · have h := lower_rate_mass (k:=2^26) (e:=503316480) hg (by decide) (by decide) (by decide) (by decide)
    norm_num at h
    norm_num [FourRatePairBudget.code,FourRatePairBudget.n]
    simpa only [show (1:ℝ≥0)-17/32=15/32 from tsub_eq_of_eq_add (by norm_num)] using h

#print axioms lower_rate_interior_family
#print axioms lower_rate_interior_mass
#print axioms lower_rate_mass
#print axioms production_lower_rates
#print axioms family
#print axioms endpoint
end ArkLib.ProximityGap.Frontier.ApolarPowerBound
