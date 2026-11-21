/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CubicApolarAttainment
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA
import Mathlib.NumberTheory.PrimesCongruentOne

/-! # Exact unrestricted-domain rate-half MCA error at the predecessor -/

set_option autoImplicit false
open Finset Code ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.CubicApolarExtremum
open CubicApolarWitness CubicApolarAttainment HalfPredecessorBadEventRichPointBridge
open PrizeShapeRateHalfBracket ProximityGap.MCAThresholdLedger ProximityGap.MCAStepFunction

local instance : Fact (Nat.Prime productionPrime) := ⟨productionPrime_prime⟩

open Classical in
/-- The family bound on the actual bad-event filter at an integer error count. -/
theorem count_bound {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (dom : ι ↪ K)
    (k e d : ℕ) (hed : e≤d) (hlen : 2*e≤d+1) (hk : 1≤k) (hd : k+d<Fintype.card ι)
    (hcoord : Fintype.card ι < 3*(d+2-e)+e) (u v : ι → K) :
    (univ.filter fun t : K => mcaEvent (ReedSolomon.code dom k : Set (ι → K))
      ((e:ℝ≥0)/Fintype.card ι) u v t).card ≤ max (e+1) (3*(e/(d+2-2*e)+1)) := by
  classical
  let W : WordStack K (Fin 2) ι := fun j => if j=0 then u else v
  let fam := canonicalBadScalarRichPointFamily dom ((e:ℝ≥0)/Fintype.card ι) W hk
  have ht : Fintype.card ι-e ≤ ⌈(1-(e:ℝ≥0)/Fintype.card ι)*(Fintype.card ι:ℝ≥0)⌉₊ := by
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by positivity),← Nat.cast_tsub,
      Nat.ceil_natCast]
  have h := SharpApolarMCA.family_bound fam fam.G Finset.Subset.rfl hed hlen hk hd ht hcoord
  simpa [fam,canonicalBadScalarRichPointFamily,badScalars,W] using h

open Classical in
/-- Uniform rate-half predecessor bound at every length of the form 4(e+1). -/
theorem rate_half_cap {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (dom : ι ↪ K)
    (e : ℕ) (hn : Fintype.card ι=4*(e+1)) (u v : ι → K) :
    (univ.filter fun t : K => mcaEvent (ReedSolomon.code dom (2*(e+1)) : Set (ι → K))
      ((e:ℝ≥0)/Fintype.card ι) u v t).card ≤ max (e+1) (3*(e/3+1)) := by
  have h := count_bound dom (2*(e+1)) e (2*e+1) (by omega) (by omega) (by omega)
    (by omega) (by omega) u v
  rwa [show 2*e+1+2-2*e=3 by omega] at h

open Classical in
/-- The cubic construction attains the unrestricted-domain cap for every
admissible three-coset configuration of length 4(e+1) with 3 dividing e. -/
theorem three_coset_extremum {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (e L : ℕ) (he : 2≤e) (hM : e+3=3*L) {g₁ g₂ : K}
    (h₁ : IsPrimitiveRoot g₁ (e+3)) (h₂ : IsPrimitiveRoot g₂ 3)
    (I : Finset K) (hI : I.card=3) (hpow : ∀ c ∈ I, c≠0 ∧ ∃ x : K, x^(e+3)=c)
    (hroom : 3*(e+3) ≤ 4*(e+1)) (hfield : 4*(e+1) ≤ Fintype.card K) :
    ∃ D : Finset K, D.card=4*(e+1) ∧
      ∃ u v : D → K, (univ.filter fun t : K => mcaEvent
        (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2*(e+1)) : Set (D → K))
        ((e:ℝ≥0)/D.card) u v t).card=e+3 := by
  classical
  obtain ⟨D,hD,u,v,hlo⟩ := three_cosets e L he hM h₁ h₂ I hI hpow hroom hfield
  have hn : Fintype.card D = 4*(e+1) := (Fintype.card_coe D).trans hD
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have h := rate_half_cap (Function.Embedding.subtype (·∈D)) e hn u v
  rw [Fintype.card_coe] at h
  exact ⟨D,hD,u,v,(h.trans (by omega)).antisymm hlo⟩

open Classical in
/-- For every l ≥ 2 the extremal numerator 3l+3 is attained on arbitrarily
large prime fields at length 4(3l+1), dimension 2(3l+1) and 3l errors. -/
theorem arbitrarily_large_prime_extrema (l bound : ℕ) (hl : 2≤l) :
    ∃ (p : ℕ) (hp : Nat.Prime p), bound<p ∧
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      ∃ D : Finset (ZMod p), D.card=4*(3*l+1) ∧ ∃ u v : D → ZMod p,
        (univ.filter fun t : ZMod p => mcaEvent
          (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2*(3*l+1)) : Set (D → ZMod p))
          (((3*l:ℕ):ℝ≥0)/D.card) u v t).card=3*l+3 := by
  classical
  let M := 3*l+3
  obtain ⟨p,hp,hlarge,hmod⟩ := Nat.exists_prime_gt_modEq_one (max bound (4*(3*l+1)))
    (show M≠0 by dsimp [M];omega)
  have hsize := (le_max_right bound (4*(3*l+1))).trans_lt hlarge
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨z,hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  let g := (z : ZMod p)
  have hg : IsPrimitiveRoot g (p-1) := IsPrimitiveRoot.coe_units_iff.mpr <|
    IsPrimitiveRoot.iff_orderOf.mpr <| by simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hz
  have hd : M∣p-1 := hmod.symm.dvd'
  obtain ⟨c,hc⟩ := hd
  have h₁ : IsPrimitiveRoot (g^c) M := IsPrimitiveRoot.pow (by omega : 0<p-1) hg
    (hc.trans (Nat.mul_comm ..))
  have h₂ : IsPrimitiveRoot ((g^c)^(l+1)) 3 :=
    IsPrimitiveRoot.pow (by dsimp [M];omega : 0<M) h₁ (by dsimp [M];omega)
  let a := g^M
  let b := g^(2*M)
  have hmlt : 2*M<p-1 := by dsimp [M];omega
  have hmpos : 0<M := by dsimp [M];omega
  have ha : a≠1 := hg.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have hb : b≠1 := hg.pow_ne_one_of_pos_of_lt (by omega) hmlt
  have hab : a≠b := fun heq => by have hi := hg.pow_inj (by omega) hmlt heq;omega
  let I : Finset (ZMod p) := {1,a,b}
  have hi : I.card=3 := by simp [I,ha.symm,hb.symm,hab]
  have hpow : ∀ d ∈ I, d≠0 ∧ ∃ x : ZMod p, x^M=d := by
    intro d hd
    simp only [I,mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl|rfl
    · exact ⟨one_ne_zero,1,one_pow _⟩
    · exact ⟨pow_ne_zero _ z.ne_zero,g,rfl⟩
    · exact ⟨pow_ne_zero _ z.ne_zero,g^2,(pow_mul ..).symm⟩
  refine ⟨p,hp,(le_max_left ..).trans_lt hlarge,?_⟩
  exact three_coset_extremum (3*l) (l+1) (by omega) (by omega) h₁ h₂ I hi hpow
    (by omega) (by rw [ZMod.card];omega)

open Classical in
/-- Every pair on an arbitrary field and domain obeys the sharp numerator. -/
theorem count_le {K ι : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (dom : ι ↪ K)
    (hn : Fintype.card ι = 1073741824) (u v : ι → K) :
    (univ.filter fun t : K => mcaEvent
      (ReedSolomon.code dom (2^29) : Set (ι → K))
      ((268435455:ℝ≥0)/Fintype.card ι) u v t).card ≤ 268435458 := by
  exact count_bound dom (2^29) 268435455 536870911 (by decide) (by decide)
    (by decide) (by rw [hn]; decide) (by rw [hn]; decide) u v

open Classical in
/-- On one explicit prime field an injective noncoset evaluation set of size
2³⁰ attains the exact unrestricted-domain numerator and MCA probability. -/
theorem production_extremum :
    ∃ D : Finset (ZMod productionPrime), D.card=2^30 ∧
      (¬ ∃ c : ZMod productionPrime, ∀ x∈D, x^(2^30)=c) ∧
      let C := (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2^29) : Set (D → ZMod productionPrime))
      let δ := (268435455:ℝ≥0)/D.card
      (∃ u v : D → ZMod productionPrime,
        (univ.filter fun t : ZMod productionPrime => mcaEvent C δ u v t).card=268435458) ∧
        epsMCA (F:=ZMod productionPrime) C δ = (268435458:ℝ≥0∞)/productionPrime := by
  classical
  obtain ⟨D,hD,hcos,u,v,hlo⟩ := production_lower_noncoset
  have hn : Fintype.card D = 1073741824 := by rw [Fintype.card_coe,hD];decide
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  let dom := Function.Embedding.subtype (·∈D)
  let C := (ReedSolomon.code dom (2^29) : Set (D → ZMod productionPrime))
  let δ := (268435455:ℝ≥0)/D.card
  have hu (u v : D → ZMod productionPrime) :
      (univ.filter fun t : ZMod productionPrime => mcaEvent C δ u v t).card ≤ 268435458 := by
    simpa only [Fintype.card_coe] using count_le dom hn u v
  let G := univ.filter fun t : ZMod productionPrime => mcaEvent C δ u v t
  have hG : G.card=268435458 := (hu u v).antisymm hlo
  refine ⟨D,hD,hcos,⟨u,v,hG⟩,le_antisymm ?_ ?_⟩
  · have h := epsMCA_le_of_badCount_le C δ 268435458 (fun W => hu (W 0) (W 1))
    simpa only [ZMod.card,Nat.cast_ofNat] using h
  · let W : WordStack (ZMod productionPrime) (Fin 2) D := fun j => if j=0 then u else v
    have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set C δ W G (fun t ht => by
      simpa [W] using (mem_filter.mp ht).2)
    simpa only [ZMod.card,hG,Nat.cast_ofNat] using h

/-- The same unconstrained evaluation domain has its first 128-bit failure at
268435455 errors and hence this exact excluded operational supremum. -/
theorem production_threshold :
    ∃ D : Finset (ZMod productionPrime), D.card=2^30 ∧
      (¬ ∃ c : ZMod productionPrime, ∀ x∈D, x^(2^30)=c) ∧
      let C := (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2^29) : Set (D → ZMod productionPrime))
      mcaDeltaStar (F:=ZMod productionPrime) C (epsStar:ℝ≥0∞) = (268435455:ℝ≥0)/1073741824 ∧
      ∀ δ : ℝ≥0, epsMCA (F:=ZMod productionPrime) C δ ≤ (epsStar:ℝ≥0∞) ↔ δ < (268435455:ℝ≥0)/1073741824 := by
  classical
  obtain ⟨D,hD,hcos,_,hm⟩ := production_extremum
  have hn : Fintype.card D=1073741824 := (Fintype.card_coe D).trans hD
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  let dom := Function.Embedding.subtype (·∈D)
  let C := (ReedSolomon.code dom (2^29) : Set (D → ZMod productionPrime))
  have hprev : epsMCA (F:=ZMod productionPrime) C ((268435454:ℝ≥0)/Fintype.card D) ≤
      (epsStar:ℝ≥0∞) := by
    have h := epsMCA_le_of_badCount_le C ((268435454:ℝ≥0)/Fintype.card D) 268435455
      (fun W => count_bound dom (2^29) 268435454 536870911 (by decide) (by decide) (by decide)
        (by rw [hn];decide) (by rw [hn];decide) (W 0) (W 1))
    rw [ZMod.card] at h
    rw [epsStar_coe_eq_natCast_inv]
    exact h.trans (natCast_div_le_inv_of_mul_le (Q:=2^128) (by decide) productionPrime_prime.pos (by decide))
  have hbad : (epsStar:ℝ≥0∞) < epsMCA (F:=ZMod productionPrime) C ((268435455:ℝ≥0)/1073741824) := by
    change epsMCA (F:=ZMod productionPrime) C ((268435455:ℝ≥0)/D.card) = _ at hm
    rw [show D.card=1073741824 from hD, Nat.cast_ofNat] at hm
    rw [hm,epsStar_coe_eq_natCast_inv]
    have hp : (productionPrime:ℝ≥0∞) ≠ 0 := by exact_mod_cast productionPrime_prime.ne_zero
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl (ENNReal.natCast_ne_top _)),
      ← ENNReal.div_eq_inv_mul,ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _))]
    exact_mod_cast (by decide : productionPrime < 268435458 * 2^128)
  have hr (t a : ℕ) (ha : t+a=1073741824) : floorRadius (Fintype.card D) t = (a:ℝ≥0)/1073741824 := by
    rw [hn,floorRadius,Nat.cast_ofNat]
    apply (eq_div_iff (by norm_num : (1073741824:ℝ≥0) ≠ 0)).mpr
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num)]
    exact_mod_cast (by omega : 1073741824-t=a)
  rw [hn] at hprev
  have hstar := mcaDeltaStar_eq_of_floor_values (F:=ZMod productionPrime) C (epsStar:ℝ≥0∞)
    (t₀:=805306370) (by decide) (by rw [hn];decide)
    (by rw [hr _ 268435454 (by decide)];exact hprev)
    (by rw [hr _ 268435455 (by decide)];exact hbad)
  rw [hr _ 268435455 (by decide)] at hstar
  refine ⟨D,hD,hcos,hstar,fun δ => ⟨?_,?_⟩⟩
  · intro h
    by_contra! he
    exact hbad.not_ge ((epsMCA_mono C he).trans h)
  · intro h
    by_contra! hb
    have hi := mcaDeltaStar_le_of_bad C _ hb
    rw [hstar] at hi
    exact h.not_ge hi

/-- All positive interleaving widths have the same exact strict good interval
on the production-length noncoset evaluation domain. -/
theorem production_interleaved :
    ∃ D : Finset (ZMod productionPrime), D.card=2^30 ∧
      (¬ ∃ c : ZMod productionPrime, ∀ x∈D, x^(2^30)=c) ∧
      let C := (ReedSolomon.code (Function.Embedding.subtype (·∈D)) (2^29) : Set (D → ZMod productionPrime))
      ∀ (w : ℕ) [NeZero w] (δ : ℝ≥0), epsMCA (F:=ZMod productionPrime) (A:=Fin w → ZMod productionPrime)
        (C ^⋈ (Fin w)) δ ≤ (epsStar:ℝ≥0∞) ↔ δ < (268435455:ℝ≥0)/1073741824 := by
  obtain ⟨D,hD,hnc,_,h⟩ := production_threshold
  have hn : Fintype.card D=1073741824 := (Fintype.card_coe D).trans hD
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  refine ⟨D,hD,hnc,fun w _ δ => ?_⟩
  rw [epsMCA_interleaved_eq]
  exact h δ

#print axioms production_interleaved
#print axioms rate_half_cap
#print axioms arbitrarily_large_prime_extrema
#print axioms production_threshold
#print axioms count_bound
#print axioms three_coset_extremum
#print axioms count_le
#print axioms production_extremum
end ArkLib.ProximityGap.Frontier.CubicApolarExtremum
