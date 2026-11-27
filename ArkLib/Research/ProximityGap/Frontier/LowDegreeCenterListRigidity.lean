/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFoldedNorm
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # Fourier rigidity for differences of agreement indicators

In a large split prime, a signed indicator with the first eighth of its
Fourier coefficients zero has period four on a dyadic domain.
-/

set_option autoImplicit false
namespace ProximityGap.LowDegreeCenterListRigidity
open Finset

/-- Evaluation of the integer coefficient vector on its indicated prefix. -/
def eval {p : ℕ} (b : ℕ → ℤ) (n : ℕ) (z : ZMod p) : ZMod p :=
  ∑ i ∈ range n, (b i : ZMod p) * z ^ i

private theorem split_eval {m p : ℕ} (b : ℕ → ℤ) (z : ZMod p) :
    eval b (m + m) z =
      ∑ j : Fin m, ((b j.val : ZMod p) * z ^ j.val +
        (b (j.val + m) : ZMod p) * z ^ (j.val + m)) := by
  rw [eval, sum_range_add, sum_add_distrib]
  congr 1
  · exact (Fin.sum_univ_eq_sum_range (fun i => (b i : ZMod p) * z ^ i) m).symm
  · simpa [Nat.add_comm] using
      (Fin.sum_univ_eq_sum_range (fun i => (b (i+m) : ZMod p) * z ^ (i+m)) m).symm

private theorem half_power {p m : ℕ} [Fact p.Prime] {g : ZMod p}
    (hm : 0 < m) (hg : IsPrimitiveRoot g (m + m)) : g ^ m = -1 := by
  have sq : g ^ m * g ^ m = 1 := by rw [← pow_add, hg.pow_eq_one]
  have hz : (g ^ m - 1) * (g ^ m + 1) = 0 := by linear_combination sq
  rcases mul_eq_zero.mp hz with h | h
  · exact False.elim (hg.pow_ne_one_of_pos_of_lt hm.ne' (by omega) (sub_eq_zero.mp h))
  · exact eq_neg_of_add_eq_zero_left h

/-- One dyadic descent step. Enough odd tests force the integer halves to agree. -/
theorem equal_halves {p k c : ℕ} [Fact p.Prime] (b : ℕ → ℤ) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2^k + 2^k))
    (bounds : ∀ i < 2^k + 2^k, -1 ≤ b i ∧ b i ≤ 1)
    (hc : 0 < c) (hcm : c ≤ 2^k) (cover : 2^k ≤ 8*c)
    (large : (4 * 2^k)^4 < p)
    (tests : ∀ j < c, eval b (2^k + 2^k) (g^(2*j+1)) = 0) :
    ∀ j < 2^k, b j = b (j + 2^k) := by
  let m := 2^k
  let a (j : Fin m) : ℤ := b j.val - b (j.val + m)
  let node (j : Fin m) := g ^ (2*j.val+1)
  let emb : Fin c ↪ Fin m := ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hcm⟩,
    fun _ _ h => Fin.ext (congrArg (Fin.val : Fin m → ℕ) h)⟩
  let S := (univ : Finset (Fin c)).map emb
  have card : S.card = c := by simp [S]
  have inj : Function.Injective node := by
    intro i j e
    have hi := i.isLt
    have hj := j.isLt
    have eq := hg.pow_inj (i := 2*i.val+1) (j := 2*j.val+1)
      (by change 2*i.val+1 < m+m; omega) (by change 2*j.val+1 < m+m; omega) e
    exact Fin.ext (by omega)
  have odd (j : Fin m) : (node j)^m = -1 := by
    calc (node j)^m = (g^m)^(2*j.val+1) := by
           simp only [node, ← pow_mul, Nat.mul_comm (2*j.val+1) m]
         _ = -1 := by rw [half_power (by positivity) hg, pow_succ, pow_mul]; simp
  have energy : ∑ j, (a j)^2 ≤ ((4*m : ℕ) : ℤ) := by
    calc ∑ j, (a j)^2 ≤ ∑ _ : Fin m, (4 : ℤ) := by
           apply sum_le_sum
           intro j _
           obtain ⟨h₁,h₂⟩ := bounds j.val (by change j.val < m+m; have := j.isLt; omega)
           obtain ⟨h₃,h₄⟩ := bounds (j.val+m) (by change j.val+m < m+m; have := j.isLt; omega)
           have lo : 0 ≤ 2 + a j := by dsimp [a]; omega
           have hi : 0 ≤ 2 - a j := by dsimp [a]; omega
           nlinarith [mul_nonneg lo hi]
         _ = _ := by simp; ring
  have comparison : (4*m)^m < p^(2*S.card) := by
    rw [card]
    calc (4*m)^m ≤ (4*m)^(8*c) := Nat.pow_le_pow_right (by dsimp [m]; positivity) cover
         _ = ((4*m)^4)^(2*c) := by rw [← pow_mul]; congr 1; omega
         _ < _ := Nat.pow_lt_pow_left large (by omega)
  have zero := DyadicFoldedNorm.zero_of_moments (k := k) a node inj S (fun j _ => odd j)
    (by
      intro j hj
      obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      rw [show (∑ v, (a v : ZMod p)*(node (emb i))^v.val) = _ from
        DyadicFoldedNorm.fold_eval (fun v => b v.val) (fun v => b (v.val+m)) _ (odd (emb i)),
        ← split_eval]
      exact tests i.val i.isLt) energy comparison
  intro j hj
  exact sub_eq_zero.mp (congrFun zero ⟨j,hj⟩)

private theorem descend_eval {m p : ℕ} [Fact p.Prime] (b : ℕ → ℤ) {z : ZMod p}
    (half : ∀ i < m, b i = b (i+m)) (hz : z^m = 1) :
    eval b (m+m) z = 2 * eval b m z := by
  rw [split_eval, eval, ← Fin.sum_univ_eq_sum_range, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [← half i.val i.isLt, pow_add, hz, mul_one, two_mul]

/-- On every dyadic domain of length at least four, the first eighth of the
positive moments determines a signed vector up to period four. -/
theorem period_four {p : ℕ} [Fact p.Prime] (r : ℕ) (b : ℕ → ℤ) (g : ZMod p)
    (hg : IsPrimitiveRoot g (2^(r+2)))
    (bounds : ∀ i < 2^(r+2), -1 ≤ b i ∧ b i ≤ 1)
    (large : (2 * 2^(r+2))^4 < p)
    (tests : ∀ u, 0 < u → u ≤ (2^(r+2))/8 → eval b (2^(r+2)) (g^u) = 0) :
    ∀ i < 2^(r+2), b i = b (i%4) := by
  induction r generalizing g with
  | zero =>
    intro i hi
    rw [Nat.mod_eq_of_lt (by simpa using hi)]
  | succ r ih =>
    let m := 2^(r+2)
    have full : 2^(r+1+2) = m+m := by change 2^((r+2)+1) = _; rw [pow_succ, Nat.mul_two]
    rw [full] at hg bounds large tests ⊢
    obtain ⟨c, hc, hcm, cover, count⟩ : ∃ c : ℕ, 0<c ∧ c≤m ∧ m≤8*c ∧
        ∀ j<c, 2*j+1≤(m+m)/8 := by
      cases r with
      | zero =>
        refine ⟨1, by decide, by decide, by decide, ?_⟩
        intro j hj
        obtain rfl : j = 0 := by omega
        decide
      | succ r =>
        have mm : m = 8*2^r := by change 2^(r+3) = _; rw [pow_add]; ring
        have h : 0 < 2^r := by positivity
        refine ⟨2^r, h, by omega, by omega, ?_⟩
        intro j hj
        omega
    have half := equal_halves b hg bounds hc hcm cover
      (by change (4*m)^4 < p; rwa [show 4*m = 2*(m+m) by omega])
      (fun j hj => tests _ (by omega) (count j hj))
    have root : IsPrimitiveRoot (g^2) m := by
      have hd : 2 ∣ m+m := ⟨m, by omega⟩
      have eq : (m+m)/2=m := by omega
      simpa only [eq] using hg.pow_of_dvd (by decide : 2 ≠ 0) hd
    have small : (2*m)^4 < p := by
      exact (Nat.pow_le_pow_left (by omega : 2*m ≤ 2*(m+m)) 4).trans_lt large
    have down : ∀ v, 0 < v → v ≤ m/8 → eval b m ((g^2)^v) = 0 := by
      intro v hv h
      have hz : ((g^2)^v)^m = 1 := by
        rw [← pow_mul, Nat.mul_comm v m, pow_mul, root.pow_eq_one, one_pow]
      have z := tests (2*v) (by omega) (by omega)
      rw [pow_mul, descend_eval b half hz] at z
      apply (mul_eq_zero.mp z).resolve_left
      intro two
      have dv := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using two)
      have hp : 2 < p := by
        have mpos : 0 < m := by dsimp [m]; positivity
        have low := Nat.pow_le_pow_left (by omega : 2 ≤ 2*(m+m)) 4
        omega
      exact (Nat.not_dvd_of_pos_of_lt (by decide) hp) dv
    have prev := ih (g^2) root (fun i hi => bounds i (by omega)) small down
    have mult : 4 ∣ m := ⟨2^r, by dsimp [m]; rw [pow_add]; ring⟩
    intro i hi
    by_cases low : i < m
    · exact prev i low
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt low)
      have hj : j < m := by omega
      calc b (m+j) = b j := by simpa [Nat.add_comm] using (half j hj).symm
           _ = b (j%4) := prev j hj
           _ = b ((m+j)%4) := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd mult]; simp

/-- Counting the choices of whole full blocks in the exchangeable coordinates. -/
theorem exchange_bound {α β : Type*} [DecidableEq α] [DecidableEq β] (L : Finset α)
    (blocks : Finset β) (full : α → Finset β) {f e F E : ℕ}
    (classes : ∀ x ∈ L, full x ⊆ blocks ∧ (full x).card = f)
    (inj : Set.InjOn full (↑L : Set α)) (size : blocks.card = f+e)
    (hf : f ≤ F) (he : e ≤ E) : L.card ≤ (F+E).choose F := by
  calc L.card = (L.image full).card := (card_image_of_injOn inj).symm
       _ ≤ (blocks.powersetCard f).card := by
         apply card_le_card
         intro s hs
         obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
         exact mem_powersetCard.mpr (classes x hx)
       _ = (f+e).choose f := by rw [card_powersetCard, size]
       _ ≤ (f+E).choose f := Nat.choose_le_choose _ (by omega)
       _ = (f+E).choose E := Nat.choose_symm_add
       _ ≤ (F+E).choose E := Nat.choose_le_choose _ (by omega)
       _ = (F+E).choose F := Nat.choose_symm_add.symm

/-- The full- and empty-block floors give the sharp named caps when the
agreement size is a nonintegral number of quarter blocks. -/
theorem named_exchange_counts :
    let n := 2^30
    let cap (blocks t : ℕ) := ((t/(n/blocks)) + ((n-t)/(n/blocks))).choose (t/(n/blocks))
    (cap 4 759250124, cap 4 536870910, cap 4 379625061, cap 4 379625060,
      cap 4 268435453) = (3,3,3,3,1) ∧
    (cap 8 759250124, cap 8 536870910, cap 8 379625061, cap 8 379625060,
      cap 8 268435453) = (21,35,21,21,7) := by decide

/-- The largest fixed-residue population of fixed-cardinality eighth-class labels. -/
def residueMaximum (labels : Finset (Fin 8)) (j : ℕ) : ℕ :=
  univ.sup fun r : Fin 8 =>
    ((labels.powersetCard j).filter fun I => ∑ i ∈ I, i = r).card

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
/-- The two exact finite tables governing shifted rational centers. -/
theorem eighth_residue_census :
    (List.range 9).map (residueMaximum univ) = [1,1,4,7,10,7,4,1,1] ∧
    (List.range 8).map (residueMaximum (univ.erase 0)) = [1,1,3,5,5,3,1,1] := by decide

#print axioms equal_halves
#print axioms period_four
#print axioms exchange_bound
#print axioms named_exchange_counts
#print axioms eighth_residue_census
end ProximityGap.LowDegreeCenterListRigidity
