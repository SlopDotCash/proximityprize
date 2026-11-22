/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.JointMinorNorm
import ArkLib.Research.ProximityGap.Frontier.JointPairCounting
import ArkLib.Research.ProximityGap.Frontier.JointPairEnergy
import ArkLib.Research.ProximityGap.Frontier.DyadicFourPairSmooth

/-! # A joint height test for modular involutions on arbitrary dyadic cosets -/

namespace ProximityGap.JointPairThreshold
open Finset DyadicMeanPairTransfer ReflectionListSampling Code
open ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm

/-- A non-dihedral modular involution admitting L transpositions must pay for
at least L(L−1)(L−3) nonzero ordered cyclotomic determinants. -/
theorem dihedral {m p L : ℕ} [Fact p.Prime] {z : ZMod p} (hz : IsPrimitiveRoot z (2^m))
    (size : 4≤L) (large : (12*L^3)^(2^m).totient < (L*(L-1)*(L-3))^(2^m).totient*p^4)
    (q : Fin L × Fin 2 ↪ Fin (2^m)) (a b c : ZMod p) (det : a^2+b*c≠0)
    (law : ∀ i,c*z^(q (i,0)).val*z^(q (i,1)).val-a*(z^(q (i,0)).val+z^(q (i,1)).val)=b) :
    a=0 ∨ c=0 ∧ b=0 := by
  classical
  have enough := Fintype.card_le_of_injective q q.injective
  simp only [Fintype.card_prod,Fintype.card_fin] at enough
  cases m with
  | zero => norm_num at enough;omega
  | succ j =>
    let n := 2^(j+1)
    have np : 0<n := by dsimp [n];positivity
    have hn : n∣p-1 := hz.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one (hz.ne_zero np.ne'))
    have pp := (Fact.out : p.Prime).one_lt
    have below : n<p := (Nat.le_of_dvd (by omega) hn).trans_lt (by omega)
    let _ : NeZero (n:ZMod p) := ⟨fun e => below.not_ge (Nat.le_of_dvd np ((ZMod.natCast_eq_zero_iff n p).mp e))⟩
    obtain ⟨w,hw⟩ : ∃ w : ℂ, IsPrimitiveRoot w n := ⟨_,Complex.isPrimitiveRoot_exp n np.ne'⟩
    let P (f : Fin 3 → Fin L) := cert (fun i => q (f i,0)) (fun i => q (f i,1))
    let S := univ.filter (fun f => valAt (P f) w≠0)
    by_contra nonDihedral
    have card : L*(L-1)*(L-3)≤S.card := by
      apply JointPairCounting.count
      intro u v uv
      have ext := JointPairCounting.zero_extensions hz hw q a b c law nonDihedral u v uv
      simp only [P,valAt,eval_cert,form,not_ne_iff]
      exact ext
    have nonzero (f) (hf : f∈S) : cycloNorm n (P f)≠0 :=
      fun eq => (mem_filter.mp hf).2 (eval_zero_of_cyclo_dvd hw (dvd_of_norm_zero eq))
    have div (f) (_hf : f∈S) : (p:ℤ)^2 ∣ cycloNorm n (P f) := by
      apply square_dvd (n:=n) (by dsimp [n];omega) hz
      exact DyadicFourPairGeometry.incident det (law (f 0)) (law (f 1)) (law (f 2))
    have energy : (∑ t : primitiveRoots n ℂ,∑ f,‖valAt (P f) t‖^2)≤(n.totient:ℝ)*(12*L^3:ℕ) := by
      push_cast
      exact JointPairEnergy.total q
    have price := JointMinorNorm.price P S nonzero div energy
    exact large.not_ge ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_left card n.totient)).trans price)

/-- On every smooth coset the joint test bounds the two-error sampling row
at T when L=T+1 transpositions are excluded. -/
theorem cap {I : Type} [Fintype I] [DecidableEq I] {p m T : ℕ} [Fact p.Prime]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=2^m) (size : 3≤T)
    (large : (12*(T+1)^3)^(2^m).totient < ((T+1)*T*(T-2))^(2^m).totient*p^4) :
    PairCap D T := by
  obtain ⟨e,he⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  apply pairCap_of_involutions D (by omega)
    (fun i => he i ▸ mul_ne_zero (ReedSolomon.Smooth.a D).ne_zero (e i).val.ne_zero)
  apply DyadicFourPairSmooth.dihedral_of_power D hn
  intro z hz
  apply dihedral hz (by omega)
  simpa only [Nat.add_sub_cancel,show T+1-3=T-2 by omega] using large

end ProximityGap.JointPairThreshold
#print axioms ProximityGap.JointPairThreshold.cap
