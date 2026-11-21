/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX - License - Identifier: MIT OR Apache - 2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SquareSpecialization
import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.DegreeLTDimension
import ArkLib.Research.ProximityGap.Frontier.SylvesterLocalMultiplicity
import Mathlib.Tactic

/-! # Power fibers of a bivariate polynomial with degree loss -/

open Polynomial Matrix Module Finset
namespace ProximityGap.PaddedPowerSpecialization

variable {K : Type*} [Field K]

private theorem degreeLT_mul {m s : ℕ} (p : K[X]) (hp : p.natDegree + s ≤ m)
    (u : degreeLT K s) : p * u.val ∈ degreeLT K m := by
  by_cases h : p * u.val = 0
  · simpa only [h] using (degreeLT K m).zero_mem
  have hu := (natDegree_lt_iff_degree_lt (right_ne_zero_of_mul h)).mpr
    (mem_degreeLT.mp u.property)
  exact mem_degreeLT.mpr ((natDegree_lt_iff_degree_lt h).mp
    ((natDegree_mul_le ..).trans_lt (by omega)))

set_option maxHeartbeats 600000 in
/-- A specialized syzygy with two bounded polynomial cofactors contributes
its full number of monomial multiples to the order of the resultant. -/
theorem pow_dvd_resultant_of_syzygy (F G : K[X][X]) (t : K)
    {m n s : ℕ} (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n)
    (P Q : K[X]) (hP : P ≠ 0) (hp : P.natDegree + s ≤ m)
    (hq : Q = 0 ∨ Q.natDegree + s ≤ n)
    (hsyz : F.map (evalRingHom t) * Q = G.map (evalRingHom t) * P) :
    (X - C t) ^ s ∣ resultant F G m n := by
  classical
  let f := F.map (evalRingHom t)
  let g := G.map (evalRingHom t)
  have hf : f.natDegree ≤ m := natDegree_map_le.trans hF
  have hg : g.natDegree ≤ n := natDegree_map_le.trans hG
  let L := sylvesterMap f g hf hg
  let iota : degreeLT K s →ₗ[K] LinearMap.ker L :=
    { toFun := fun u => ⟨(⟨P * u.val, degreeLT_mul P hp u⟩,
          ⟨-(Q * u.val), (degreeLT K n).neg_mem <|
            hq.elim (fun h => by simp [h]) (fun h => degreeLT_mul Q h u)⟩), by
        apply Subtype.ext
        change f * -(Q * u.val) + g * (P * u.val) = 0
        change f * Q = g * P at hsyz
        linear_combination -u.val * hsyz⟩
      map_add' := fun u v => by ext1; apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]; abel
      map_smul' := fun c v => by ext1; apply Prod.ext <;> apply Subtype.ext <;> simp }
  have inj : Function.Injective iota := by
    intro u v huv
    apply Subtype.ext
    apply mul_left_cancel₀ hP
    exact congrArg (fun b : LinearMap.ker L => b.val.1.val) huv
  have hnull : s ≤ finrank K (LinearMap.ker L) := by
    simpa using LinearMap.finrank_le_finrank_of_injective inj
  let M := sylvester f g m n
  have hcod := M.mulVecLin.finrank_range_add_finrank_ker
  have hdom := L.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hcod
  rw [Module.finrank_prod, finrank_degreeLT, finrank_degreeLT] at hdom
  have heq : M.rank = finrank K (LinearMap.range L) := by
    rw [M.rank_eq_finrank_range_toLin (degreeLT.basis K (m + n))
      (((degreeLT.basis K m).prod (degreeLT.basis K n)).reindex finSumFinEquiv)]
    change _ = finrank K (LinearMap.range (sylvesterMap f g hf hg))
    rw [show M = _ from (toMatrix_sylvesterMap' f g hf hg).symm, Matrix.toLin_toMatrix]
  have hle : s ≤ finrank K (LinearMap.ker M.mulVecLin) := by
    change finrank K (LinearMap.range M.mulVecLin) = _ at heq
    omega
  have hcor : s ≤ m + n - ((sylvester F G m n).map (eval t)).rank := by
    have he : M = (sylvester F G m n).map (eval t) := sylvester_map_map F G m n _
    change finrank K (LinearMap.range M.mulVecLin) + _ = _ at hcod
    change M.rank + _ = _ at hcod
    rw [← he]
    omega
  apply (pow_dvd_pow (X - C t) hcor).trans
  simpa only [Fintype.card_fin, resultant] using
    SquareSpecialization.corank_dvd_det (sylvester F G m n) t

/-- A power fiber of any coordinate degree contributes
at least the stated order. The unused highest coefficients supply additional syzygies. -/
theorem power_fiber_order (H : K[X][X]) (t : K) (W : K[X]) {k : ℕ} (hk : 2 ≤ k)
    (h : H.map (evalRingHom t) = W ^ k) :
    (X - C t) ^ (H.natDegree - H.natDegree / k) ∣
      resultant H H.derivative H.natDegree (H.natDegree - 1) := by
  have hm : k * W.natDegree ≤ H.natDegree := by
    simpa only [h, natDegree_pow] using (natDegree_map_le (p := H) (f := evalRingHom t))
  have hw : W.natDegree ≤ H.natDegree / k := (Nat.le_div_iff_mul_le (by omega)).mpr
    (by simpa [Nat.mul_comm] using hm)
  have hdiv := Nat.div_le_self H.natDegree k
  by_cases hdeg : W.natDegree = 0
  · apply pow_dvd_resultant_of_syzygy H H.derivative t le_rfl (natDegree_derivative_le H)
      1 0 one_ne_zero (by simp) (Or.inl rfl)
    simp only [mul_zero, mul_one]
    rw [← derivative_map, h, eq_C_of_natDegree_eq_zero hdeg, ← map_pow, derivative_C]
  · have hw0 : W ≠ 0 := by intro hh; simp [hh] at hdeg
    have hdq : (C (k : K) * W.derivative).natDegree +
        (H.natDegree - H.natDegree / k) ≤ H.natDegree - 1 := by
      have hh := (natDegree_C_mul_le (k : K) W.derivative).trans (natDegree_derivative_le W)
      omega
    apply pow_dvd_resultant_of_syzygy H H.derivative t le_rfl (natDegree_derivative_le H)
      W (C (k : K) * W.derivative) hw0 (by omega) (Or.inr hdq)
    · rw [← derivative_map, h, derivative_pow]
      have hpow : W ^ k = W ^ (k - 1) * W :=
        (show W ^ k = W ^ (k - 1 + 1) by congr 1; omega).trans (pow_succ ..)
      rw [hpow]
      ring

/-- Padded resultant bound for all power fibers, including constants, zero and
specializations whose top coordinate coefficients vanish. -/
theorem power_fiber_count (H : K[X][X]) (S : Finset K) {k : ℕ} (hk : 2 ≤ k)
    (hres : resultant H H.derivative H.natDegree (H.natDegree - 1) ≠ 0)
    (hs : ∀ t ∈ S, ∃ W : K[X], H.map (evalRingHom t) = W ^ k) :
    S.card * (H.natDegree - H.natDegree / k) ≤
      (2 * H.natDegree - 1) * Bivariate.degreeX H := by
  have h := ArkLib.ProximityGap.Frontier.SylvesterLocalMultiplicity.sum_local_orders_le_natDegree
    _ hres S (fun _ => H.natDegree - H.natDegree / k) (by
      intro t ht
      obtain ⟨W, hW⟩ := hs t ht
      exact power_fiber_order H t W hk hW)
  simpa only [sum_const, smul_eq_mul] using h.trans (natDegree_resultant_derivative_padded_le H)

/-- A nonempty collection of square fibers has cardinality strictly less than
four times the parameter degree, with no condition on the individual fiber degrees. -/
theorem square_fibers_lt (H : K[X][X]) (S : Finset K) (hne : S.Nonempty)
    (hr : 0 < H.natDegree) (hres : resultant H H.derivative H.natDegree (H.natDegree - 1) ≠ 0)
    (hs : ∀ t ∈ S, ∃ W : K[X], H.map (evalRingHom t) = W ^ 2) :
    S.card < 4 * Bivariate.degreeX H := by
  have hb := power_fiber_count H S (by decide : 2 ≤ 2) hres hs
  have hd : 0 < H.natDegree - H.natDegree / 2 := by omega
  have hs0 := card_pos.mpr hne
  have hh : 0 < Bivariate.degreeX H := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hb
    exact (Nat.mul_pos hs0 hd).not_ge hb
  apply Nat.lt_of_mul_lt_mul_right
  calc
    S.card * H.natDegree ≤ S.card * (2 * (H.natDegree - H.natDegree / 2)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (S.card * (H.natDegree - H.natDegree / 2)) := by ring
    _ ≤ 2 * ((2 * H.natDegree - 1) * Bivariate.degreeX H) := Nat.mul_le_mul_left 2 hb
    _ < 2 * ((2 * H.natDegree) * Bivariate.degreeX H) := by gcongr; omega
    _ = 4 * Bivariate.degreeX H * H.natDegree := by ring

/-- At most three times the parameter degree many cube fibers can occur. If there
is at least one such fiber, the inequality is strict. -/
theorem cube_fibers_lt (H : K[X][X]) (S : Finset K) (hne : S.Nonempty)
    (hr : 0 < H.natDegree) (hres : resultant H H.derivative H.natDegree (H.natDegree - 1) ≠ 0)
    (hs : ∀ t ∈ S, ∃ W : K[X], H.map (evalRingHom t) = W ^ 3) :
    S.card < 3 * Bivariate.degreeX H := by
  have hb := power_fiber_count H S (by decide : 2 ≤ 3) hres hs
  have hd : 0 < H.natDegree - H.natDegree / 3 := by omega
  have hs0 := card_pos.mpr hne
  have hh : 0 < Bivariate.degreeX H := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hb
    exact (Nat.mul_pos hs0 hd).not_ge hb
  apply Nat.lt_of_mul_lt_mul_right
  calc
    S.card * (2 * H.natDegree) ≤ S.card * (3 * (H.natDegree - H.natDegree / 3)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 3 * (S.card * (H.natDegree - H.natDegree / 3)) := by ring
    _ ≤ 3 * ((2 * H.natDegree - 1) * Bivariate.degreeX H) := Nat.mul_le_mul_left 3 hb
    _ < 3 * ((2 * H.natDegree) * Bivariate.degreeX H) := by gcongr; omega
    _ = 3 * Bivariate.degreeX H * (2 * H.natDegree) := by ring

#print axioms power_fiber_count
#print axioms cube_fibers_lt
#print axioms square_fibers_lt

end ProximityGap.PaddedPowerSpecialization
