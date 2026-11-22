/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFourPairSmooth
import ArkLib.Research.ProximityGap.Frontier.DyadicMeanPairTransfer

/-! # The averaged height criterion for four transpositions and exact list thresholds -/

namespace ProximityGap.DyadicMeanPairThreshold
open ReflectionListSampling DyadicPairMinorTransfer DyadicFourPairGeometry Code

/-- The mean-square test classifies four disjoint transpositions on every
dyadic prime-field orbit. -/
theorem dihedral {m p : ℕ} [Fact p.Prime] {z : ZMod p} (hz : IsPrimitiveRoot z (2^m))
    (large : 54^(2^m).totient < p^4) (q : Fin 4 × Fin 2 ↪ Fin (2^m)) (a b c : ZMod p)
    (det : a^2+b*c≠0)
    (law : ∀ i,c*z^(q (i,0)).val*z^(q (i,1)).val-a*(z^(q (i,0)).val+z^(q (i,1)).val)=b) :
    a=0 ∨ c=0 ∧ b=0 := by
  have enough := Fintype.card_le_of_injective q q.injective
  simp only [Fintype.card_prod,Fintype.card_fin] at enough
  cases m with
  | zero => norm_num at enough
  | succ j =>
    let n := 2^(j+1)
    have np : 0<n := by dsimp [n];positivity
    have hn : n∣p-1 := hz.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one (hz.ne_zero np.ne'))
    have pp := (Fact.out : p.Prime).one_lt
    have below : n<p := (Nat.le_of_dvd (by omega) hn).trans_lt (by omega)
    let _ : NeZero (n:ZMod p) := ⟨fun e => below.not_ge (Nat.le_of_dvd np ((ZMod.natCast_eq_zero_iff n p).mp e))⟩
    obtain ⟨w,hw⟩ : ∃ w : ℂ, IsPrimitiveRoot w n := ⟨_,Complex.isPrimitiveRoot_exp n np.ne'⟩
    apply DyadicFourPairPrime.of_minors hz hw q a b c law
    intro i
    let r : Fin 3 → Fin 4 := ![0,1,i]
    let X (j : Fin 3) := q (r j,0)
    let Y (j : Fin 3) := q (r j,1)
    have sep (j : Fin 3) : X j≠Y j := q.injective.ne (fun e => (by decide : (0:Fin 2)≠1) (congrArg Prod.snd e))
    apply DyadicMeanPairTransfer.transfer (m:=j) (by omega) hz hw X Y sep _ large
    exact incident det (law 0) (law 1) (law i)

/-- The sharp cap of three non-dihedral transpositions on any smooth coset
when the squared norm criterion holds. -/
theorem cap {I : Type} [Fintype I] [DecidableEq I] {p m : ℕ} [Fact p.Prime]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=2^m)
    (large : 54^(2^m).totient < p^4) : PairCap D 3 := by
  obtain ⟨e,he⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  exact pairCap_of_involutions D (by decide)
    (fun i => he i ▸ mul_ne_zero (ReedSolomon.Smooth.a D).ne_zero (e i).val.ne_zero)
    (DyadicFourPairSmooth.dihedral_of_power D hn (fun _ hz => dihedral hz large))

/-- The first over-budget error count is n−k−1 throughout the sampling window
under the averaged height condition. -/
theorem threshold {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] {e k r B : ℕ} [NeZero k]
    (hn : Fintype.card I=2^e) (large : 54^(2^e).totient < p^4) (length : 2^e=k+3+r)
    (hr : 2≤r) (payment : r≤k ∨ ((r+1).choose 2-(r+1)/2)*(k+2)≤2*(2*k+2).choose (k+1))
    (upper : bound k r 3≤B) (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ:=Fin m) (ReedSolomon.code D k : Set (I → ZMod p))) δ ≤ (B : ℕ∞) ↔
    δ < ((r+2 : ℕ):ℝ)/(Fintype.card I:ℝ) :=
  threshold_of_payment D (hn.trans length) hr (endpoint_payment_wide payment) (cap D hn large) (by decide)
    upper lower m hm δ

end ProximityGap.DyadicMeanPairThreshold
#print axioms ProximityGap.DyadicMeanPairThreshold.threshold
