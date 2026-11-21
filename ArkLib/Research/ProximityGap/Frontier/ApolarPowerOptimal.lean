/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarPowerBound
import ArkLib.Research.ProximityGap.Frontier.PowerFiberEndpoint

/-! # Domain-optimal scalar MCA counts at the unique-decoding endpoint

For n=k+2e, the universal endpoint upper bound is attained as soon as
the largest multiple of e+1 at most n+1 also fits inside n positions.
The construction works on every sufficiently large splitting prime field.
-/

set_option autoImplicit false
open Finset Code ProximityGap
attribute [local instance] Classical.propDecidable
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.ApolarPowerOptimal

/-- At the Hamming-grid radius the scalar numerator is bounded for the
literal pair of received words on every finite injective domain. -/
theorem pair_bound {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (dom : ι ↪ F) (u v : ι → F) {k e n : ℕ}
    (hn : Fintype.card ι=n) (hshape : n=k+2*e) (hk : 0<k) (he : 0<e) :
    (univ.filter fun t : F => mcaEvent (ReedSolomon.code dom k : Set (ι → F))
      ((e:ℝ≥0)/n) u v t).card ≤ ((n+1)/(e+1))*(e+1) := by
  classical
  let w : WordStack F (Fin 2) ι := ![u,v]
  let fam := canonicalBadScalarRichPointFamily dom ((e:ℝ≥0)/n) w hk
  apply ApolarPowerBound.endpoint fam hn hshape hk he
  have h := one_sub_div_mul_cast (ι:=ι) e (by omega)
  rw [hn] at h ⊢
  rw [h,Nat.ceil_natCast]

private theorem fits {n e : ℕ} (hnd : ¬ e+1 ∣ n+1) : ((n+1)/(e+1))*(e+1) ≤ n := by
  have h := Nat.div_mul_le_self (n+1) (e+1)
  by_contra! hno
  exact hnd ⟨_,(show n+1=((n+1)/(e+1))*(e+1) by omega).trans (Nat.mul_comm ..)⟩

/-- On every sufficiently large splitting prime field there is one domain
and pair attaining the absolute bound, and the worst-case error probability
on that same domain is exactly this numerator divided by p. -/
theorem prime (k e p : ℕ) [Fact p.Prime] (hk : 0<k) (he : 0<e)
    (hnd : ¬ e+1 ∣ k+2*e+1) (hp : k+2*e<p) (hsplit : e+1 ∣ p-1) :
    let n := k+2*e
    let count := ((n+1)/(e+1))*(e+1)
    ∃ D : Finset (ZMod p), D.card=n ∧
      let C := (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → ZMod p))
      (∃ u v : D → ZMod p, (univ.filter fun t : ZMod p => mcaEvent C ((e:ℝ≥0)/D.card) u v t).card=count) ∧
      epsMCA (F:=ZMod p) C ((e:ℝ≥0)/D.card)=(count:ℝ≥0∞)/(p:ℝ≥0∞) := by
  classical
  let n := k+2*e
  let count := ((n+1)/(e+1))*(e+1)
  obtain ⟨D,hD,u,v,hu⟩ := PowerFiberEndpoint.prime_attain k e ((n+1)/(e+1)) p hk he
    (fits hnd) hp hsplit
  have hn : Fintype.card D=n := (Fintype.card_coe D).trans hD
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by rw [hn]; dsimp [n]; omega)
  let dom := Function.Embedding.subtype (·∈D)
  let C := (ReedSolomon.code dom k : Set (D → ZMod p))
  have bound (u v : D → ZMod p) :
      (univ.filter fun t : ZMod p => mcaEvent C ((e:ℝ≥0)/D.card) u v t).card≤count := by
    rw [hD]
    exact pair_bound dom u v hn rfl hk he
  refine ⟨D,hD,⟨u,v,(bound u v).antisymm hu⟩,le_antisymm ?_ ?_⟩
  · apply (epsMCA_le_of_badCount_le C _ count ?_).trans (by rw [ZMod.card])
    intro w
    exact bound (w 0) (w 1)
  · rw [epsMCA_eq_iSup_badCount_div,ZMod.card]
    apply ENNReal.div_le_div_right
    let w : WordStack (ZMod p) (Fin 2) D := ![u,v]
    apply LE.le.trans _ (le_iSup _ w)
    exact_mod_cast hu

/-- The matching extremizers exist over arbitrarily large prime fields. -/
theorem arbitrarily_large (k e bound : ℕ) (hk : 0<k) (he : 0<e) (hnd : ¬ e+1 ∣ k+2*e+1) :
    let n := k+2*e
    let count := ((n+1)/(e+1))*(e+1)
    ∃ (p : ℕ) (hp : Nat.Prime p), bound<p ∧
      let _ : Fact p.Prime := ⟨hp⟩
      ∃ D : Finset (ZMod p), D.card=n ∧
        let C := (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → ZMod p))
        (∃ u v : D → ZMod p, (univ.filter fun t : ZMod p => mcaEvent C ((e:ℝ≥0)/D.card) u v t).card=count) ∧
        epsMCA (F:=ZMod p) C ((e:ℝ≥0)/D.card)=(count:ℝ≥0∞)/(p:ℝ≥0∞) := by
  obtain ⟨p,hp,hbig,hcong⟩ := Nat.exists_prime_gt_modEq_one (max bound (k+2*e)) (Nat.succ_ne_zero e)
  let _ : Fact p.Prime := ⟨hp⟩
  refine ⟨p,hp,(le_max_left ..).trans_lt hbig,prime k e p hk he hnd ((le_max_right ..).trans_lt hbig) ?_⟩
  exact hcong.symm.dvd'

#print axioms pair_bound
#print axioms prime
#print axioms arbitrarily_large
end ArkLib.ProximityGap.Frontier.ApolarPowerOptimal
