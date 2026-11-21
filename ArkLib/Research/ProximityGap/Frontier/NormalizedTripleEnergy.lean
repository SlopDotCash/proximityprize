/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Third additive energy from normalized pairs of roots of unity

For a subgroup consisting of all nth roots of unity, put an ordered pair
(x,y) in bin (1+x+y)^n. The zero bin and the sum of squared nonzero bin
counts recover the sixfold ordered additive energy.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.NormalizedTripleEnergy

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment (addEnergy3)

variable {F : Type*} [Field F] [DecidableEq F]

/-- The number of ordered pairs in the specified nth-power bin. -/
def profile (H : Finset F) (n : ℕ) (u : F) : ℕ :=
  ((H ×ˢ H).filter (fun P => (1 + P.1 + P.2)^n = u)).card

omit [DecidableEq F] in
/-- Equality of signatures is exactly membership of the quotient in the group of nth roots. -/
theorem pow_eq_iff_div_mem {H : Finset F} {n : ℕ} (hH : ∀ x, x ∈ H ↔ x^n = 1)
    {x y : F} (hy : y ≠ 0) : x^n = y^n ↔ x/y ∈ H := by
  rw [hH, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hy)]

private def tripleWeight (H : Finset F) (f : F → ℕ) : ℕ :=
  ∑ a ∈ H, ∑ b ∈ H, ∑ c ∈ H, f (a+b+c)

omit [DecidableEq F] in
private theorem normalized_weight {H : Finset F} {n : ℕ} (hn : 0 < n)
    (hH : ∀ x, x ∈ H ↔ x^n = 1) (f : F → ℕ) :
    tripleWeight H f = ∑ P ∈ H ×ˢ H, ∑ a ∈ H, f (a*(1+P.1+P.2)) := by
  rw [sum_product]
  conv_rhs => rw [Finset.sum_comm]; enter [2, y]; rw [Finset.sum_comm]
  unfold tripleWeight
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl (fun a ha => ?_)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simpa [zero_pow hn.ne'] using (hH _).mp ha
  have hreindex (w : F → ℕ) : ∑ j ∈ H, w (a*j) = ∑ j ∈ H, w j := by
    apply sum_nbij' (i := fun j => a*j) (j := fun j => a⁻¹*j)
    · intro x hx
      exact (hH _).mpr (by rw [mul_pow, (hH _).mp ha, (hH _).mp hx, one_mul])
    · intro x hx
      exact (hH _).mpr (by rw [mul_pow, inv_pow, (hH _).mp ha, (hH _).mp hx, inv_one, one_mul])
    · intro x _
      exact inv_mul_cancel_left₀ ha0 x
    · intro x _
      exact mul_inv_cancel_left₀ ha0 x
    · intro _ _
      rfl
  rw [← hreindex (fun b => ∑ c ∈ H, f (a+b+c))]
  refine sum_congr rfl (fun b _ => ?_)
  rw [← hreindex (fun c => f (a+a*b+c))]
  exact sum_congr rfl (fun c _ => congrArg f (by ring))

private theorem scale_count {H : Finset F} {n : ℕ} (hn : 0 < n)
    (hH : ∀ x, x ∈ H ↔ x^n = 1) (c z : F) :
    (∑ a ∈ H, if c = a*z then 1 else 0) =
      if c = 0 then (if z^n = 0 then H.card else 0)
      else (if z^n = c^n then 1 else 0) := by
  by_cases hz : z = 0
  · subst z
    by_cases hc : c = 0
    · simp [hc, hn.ne']
    · simp [hc, hn.ne', (pow_ne_zero n hc).symm]
  · have he (a : F) : c = a*z ↔ a = c/z := by
      rw [eq_div_iff hz, eq_comm]
    simp_rw [he]
    rw [sum_ite_eq' H _ (fun _ => (1:ℕ))]
    simp only [← pow_eq_iff_div_mem hH hz]
    by_cases hc : c = 0
    · simp [hc, hn.ne', pow_ne_zero n hz, (pow_ne_zero n hz).symm]
    · simp [hc, eq_comm]

private theorem profile_weight [Fintype F] (H : Finset F) (n : ℕ) (f : F → ℕ) :
    (∑ P ∈ H ×ˢ H, f ((1+P.1+P.2)^n)) = ∑ u, profile H n u * f u := by
  simpa only [profile, sum_const, nsmul_eq_mul, Nat.cast_id] using
    (sum_fiberwise' (H ×ˢ H) (fun P => (1+P.1+P.2)^n) f).symm

/-- The number of ordered triples with sum c. -/
def tripleCount (H : Finset F) (c : F) : ℕ :=
  ∑ a ∈ H, ∑ b ∈ H, ∑ d ∈ H, if c = a+b+d then 1 else 0

/-- Each normalized pair in a nonzero bin has one scaling for a fixed target.
A pair in the zero bin has every subgroup element as a scaling for the zero target. -/
theorem tripleCount_eq_profile [Fintype F] {H : Finset F} {n : ℕ} (hn : 0 < n)
    (hH : ∀ x, x ∈ H ↔ x^n = 1) (c : F) :
    tripleCount H c = if c^n = 0 then H.card * profile H n 0 else profile H n (c^n) := by
  change tripleWeight H (fun z => if c = z then 1 else 0) = _
  rw [normalized_weight hn hH]
  simp_rw [scale_count hn hH]
  by_cases hc : c = 0
  · subst c
    simp only [zero_pow hn.ne', ite_true]
    rw [profile_weight H n (fun u => if u = 0 then H.card else 0)]
    simp [mul_ite, Nat.mul_comm]
  · simp only [hc, pow_ne_zero _ hc, ite_false]
    rw [profile_weight H n (fun u => if u = c^n then 1 else 0)]
    simp [mul_ite]

/-- The exact ordered energy from the normalized-pair histogram. -/
theorem addEnergy3_eq_profile [Fintype F] {H : Finset F} {n : ℕ} (hn : 0 < n)
    (hH : ∀ x, x ∈ H ↔ x^n = 1) :
    addEnergy3 H = (H.card * profile H n 0)^2 +
      H.card * ∑ u ∈ (univ : Finset F).erase 0, (profile H n u)^2 := by
  let f (u : F) := if u = 0 then H.card * profile H n 0 else profile H n u
  have hcount (c : F) : tripleCount H c = f (c^n) := tripleCount_eq_profile hn hH c
  change tripleWeight H (tripleCount H) = _
  rw [show tripleCount H = (fun c => f (c^n)) by funext c; exact hcount c]
  rw [normalized_weight hn hH]
  have hscale (P : F × F) :
      (∑ a ∈ H, f ((a*(1+P.1+P.2))^n)) = H.card * f ((1+P.1+P.2)^n) := by
    apply sum_const_nat
    intro a ha
    rw [mul_pow, (hH _).mp ha, one_mul]
  simp_rw [hscale]
  rw [← Finset.mul_sum, profile_weight H n f]
  rw [← Finset.add_sum_erase (univ : Finset F) (fun u => profile H n u * f u) (mem_univ 0)]
  have hnonzero : (∑ u ∈ (univ : Finset F).erase 0, profile H n u * f u) =
      ∑ u ∈ (univ : Finset F).erase 0, (profile H n u)^2 := by
    apply sum_congr rfl
    intro u hu
    simp [f, (mem_erase.mp hu).1, pow_two]
  rw [hnonzero]
  simp only [f, ite_true]
  ring

omit [DecidableEq F] in
private theorem tripleWeight_eq_piSum (H : Finset F) (f : F → ℕ) :
    tripleWeight H f = ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => H), f (∑ i, v i) := by
  unfold tripleWeight
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => ![p.1.1, p.1.2, p.2]) (fun v => ((v 0, v 1), v 2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product] at hp
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i <;> simp [hp.1.1, hp.1.2, hp.2]
  · intro v hv
    rw [Fintype.mem_piFinset] at hv
    simp [hv 0, hv 1, hv 2]
  · intro p _
    rfl
  · intro v _
    funext i
    fin_cases i <;> rfl
  · intro p _
    simp [Fin.sum_univ_three]

/-- The same normalized-pair histogram for the depth-three energy used in
the repository's DC-subtracted moment bound. -/
theorem rEnergy_three_eq_profile [Fintype F] {H : Finset F} {n : ℕ} (hn : 0 < n)
    (hH : ∀ x, x ∈ H ↔ x^n = 1) :
    ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy H 3 =
      (H.card * profile H n 0)^2 +
      H.card * ∑ u ∈ (univ : Finset F).erase 0, (profile H n u)^2 := by
  rw [← addEnergy3_eq_profile hn hH]
  have h (z : F) : (∑ w ∈ Fintype.piFinset (fun _ : Fin 3 => H),
      if z = ∑ i, w i then 1 else 0) = tripleCount H z :=
    (tripleWeight_eq_piSum H (fun c => if z = c then 1 else 0)).symm
  unfold ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy
  simp_rw [h]
  exact (tripleWeight_eq_piSum H (tripleCount H)).symm

/-- For a primitive root the group has cardinality n, giving the usual scaled formula. -/
theorem addEnergy3_nthRoots [Fintype F] {n : ℕ} (hn : 0 < n) {g : F}
    (hg : IsPrimitiveRoot g n) :
    let H := Polynomial.nthRootsFinset n (1 : F)
    addEnergy3 H = (n * profile H n 0)^2 + n *
      ∑ u ∈ (univ : Finset F).erase 0, (profile H n u)^2 := by
  dsimp only
  simpa only [hg.card_nthRootsFinset] using
    (addEnergy3_eq_profile hn (fun x => Polynomial.mem_nthRootsFinset hn (1 : F) (x := x)))

#print axioms pow_eq_iff_div_mem
#print axioms tripleCount_eq_profile
#print axioms addEnergy3_eq_profile
#print axioms rEnergy_three_eq_profile
#print axioms addEnergy3_nthRoots

end ArkLib.ProximityGap.Frontier.NormalizedTripleEnergy
