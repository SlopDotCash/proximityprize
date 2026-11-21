/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarEndpointExact

/-! # Exact unique-decoding endpoint on prescribed multiplicative cosets -/

set_option autoImplicit false
open Finset Polynomial Code ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SmoothPowerEndpoint

private theorem numerator_of_dvd {n e : ℕ} (he : 0 < e) (hdiv : e+1 ∣ n) :
    ApolarEndpointExact.numerator n e = n := by
  have hnd : ¬ e+1 ∣ n+1 := by
    intro h
    have h1 := (Nat.dvd_add_right hdiv).mp h
    exact (by omega : e+1 ≠ 1) (Nat.dvd_one.mp h1)
  obtain ⟨m, hm⟩ := hdiv
  rw [ApolarEndpointExact.numerator, ite_eq_right hnd, hm, Nat.add_comm ((e+1)*m) 1,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega : 1 < e+1), zero_add,
    Nat.mul_comm]

open Classical in
/-- On *every* prescribed split nonzero multiplicative coset of size n=k+2e,
if e+1 divides n, one received pair has the evaluation coset itself as its
bad-scalar set. The exact worst-case probability is n divided by the field size. -/
theorem coset {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g b : K} {n k e : ℕ} (hg : IsPrimitiveRoot g n) (hb : b ≠ 0)
    (hn : n=k+2*e) (hk : 0<k) (he : 0<e) (hdiv : e+1 ∣ n) :
    let D := nthRootsFinset n (b^n)
    let C := (ReedSolomon.code (Function.Embedding.subtype (· ∈ D)) k : Set (D → K))
    (∃ u v : D → K, (univ.filter fun t : K => mcaEvent C ((e:ℝ≥0)/n) u v t) = D) ∧
      epsMCA (F:=K) C ((e:ℝ≥0)/n) = (n:ℝ≥0∞)/(Fintype.card K:ℝ≥0∞) := by
  classical
  let D := nthRootsFinset n (b^n)
  let dom := Function.Embedding.subtype (· ∈ D)
  let C := (ReedSolomon.code dom k : Set (D → K))
  let V := Lagrange.nodal D id
  let u : D → K := fun x => ((V*Polynomial.X) /ₘ (Polynomial.X : K[X])^(e+1)).eval x.val
  let v : D → K := fun x => -(V /ₘ (Polynomial.X : K[X])^(e+1)).eval x.val
  have hpos : 0<n := by omega
  have hD : D.card=n :=
    (CubicApolarAttainment.full_power_fiber hpos hg (pow_ne_zero _ hb) ⟨b,rfl⟩).1
  obtain ⟨m, hm⟩ := hdiv
  have hdiv : e+1 ∣ n := ⟨m,hm⟩
  have hroot := IsPrimitiveRoot.pow hpos hg (hm.trans (Nat.mul_comm _ _))
  have hcard : Fintype.card D=n := (Fintype.card_coe D).trans hD
  let _ : Nonempty D := Fintype.card_pos_iff.mp (hcard.symm ▸ hpos)
  have upper (u' v' : D → K) :
      (univ.filter fun t : K => mcaEvent C ((e:ℝ≥0)/n) u' v' t).card ≤ n := by
    exact (ApolarEndpointExact.pair_bound dom u' v' hcard hn hk he).trans_eq (numerator_of_dvd he hdiv)
  have sub : D ⊆ univ.filter fun t : K => mcaEvent C ((e:ℝ≥0)/n) u v t := by
    intro t ht
    have htp := (mem_nthRootsFinset hpos _).mp ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      simpa [zero_pow hpos.ne'] using htp.trans_ne (pow_ne_zero _ hb)
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    have h := PowerFiberEndpoint.event_of_fiber D k e hk he (hD.trans hn)
      hroot ht0 (by
        intro x hx
        apply (mem_nthRootsFinset hpos _).mpr
        calc
          x^n = (x^(e+1))^m := by rw [← pow_mul, ← hm]
          _ = (t^(e+1))^m := by rw [(mem_nthRootsFinset (Nat.succ_pos e) _).mp hx]
          _ = t^n := by rw [← pow_mul, ← hm]
          _ = b^n := htp)
    simpa only [hD] using h
  have eq := Finset.eq_of_subset_of_card_le sub ((upper u v).trans_eq hD.symm)
  refine ⟨⟨u,v,eq.symm⟩, le_antisymm ?_ ?_⟩
  · exact epsMCA_le_of_badCount_le C _ n (fun w => upper (w 0) (w 1))
  · rw [epsMCA_eq_iSup_badCount_div]
    apply ENNReal.div_le_div_right
    let w : WordStack K (Fin 2) D := ![u,v]
    apply LE.le.trans _ (le_iSup _ w)
    exact_mod_cast (show n ≤ (univ.filter fun t : K => mcaEvent C ((e:ℝ≥0)/n) u v t).card
      from hD.ge.trans (card_le_card sub))

#print axioms coset
end ArkLib.ProximityGap.Frontier.SmoothPowerEndpoint
