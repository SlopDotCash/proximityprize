/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent
import ArkLib.Data.CodingTheory.ProximityGap.UniversalSpikeFloor
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Data.Nat.Choose.Vandermonde

/-! # Arbitrarily large failure of reverse MCA transfer, on a common Hamming grid

At rate one half and radius one quarter, the length-four base has at most four
bad scalars. At length 4m, the spike construction supplies at least m+1.
Every dyadic multiplicity is realized on an actual prime-field smooth tower.
-/
set_option autoImplicit false
namespace ProximityGap.FiberReverseRatio
open Finset
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

private theorem large_error (D : I ↪ F) {m : ℕ} (hm : 0 < m) (hn : Fintype.card I = 4*m) :
    ((m+1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code D (2*m) : Set (I → F)) (1/4) := by
  classical
  have hpos : m+1 ≤ Fintype.card I := by omega
  let pos : Fin (m+1) ↪ I := (Fin.castLEEmb hpos).trans (Fintype.equivFin I).symm.toEmbedding
  apply SpikeFloor.epsMCA_ge_j_div_card (j := m+1) (p := pos) (a := pos.trans D) (b := 1)
    (ReedSolomon.code D (2*m)) ?_ ?_ (by omega) hpos one_ne_zero
  · rintro w hw ⟨T,hT,hzero⟩
    apply ReedSolomon.eq_of_agree_of_card_le hw (Submodule.zero_mem _) (T := univ \ T)
    · rw [card_sdiff_of_subset (subset_univ _), card_univ]; omega
    · intro i hi; exact hzero i (mem_sdiff.mp hi).2
  · rw [hn]; simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat]
    norm_num [← mul_assoc]

/-- At identical relative radius 1/4, the length-4 power image has at most four bad
scalars and its half-rate smooth lift admits at least m+1 bad scalars. -/
theorem ratio_witness (D : I ↪ F) [ReedSolomon.Smooth D] {m : ℕ} (hm : 0 < m)
    (hn : Fintype.card I = 4*m) :
    ∃ V : Finset F, V.card = 4 ∧ (∀ i, D i ^ m ∈ V) ∧
      (∀ v ∈ V, (univ.filter fun i => D i ^ m = v).card = m) ∧
      epsMCA (F := F) (ReedSolomon.code (Function.Embedding.subtype (· ∈ V)) 2 : Set (V → F)) (1/4)
        ≤ (4 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ∧
      ((m+1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
        epsMCA (F := F) (ReedSolomon.code D (2*m) : Set (I → F)) (1/4) := by
  classical
  obtain ⟨V,hV,hmem,hf,_,_⟩ := SmoothPowerMcaDescent.exists_smooth_base D hm
    (hn.trans (Nat.mul_comm ..)) (h := 4) ⟨2,rfl⟩
  let : Nonempty V := Fintype.card_pos_iff.mp (by simp [hV])
  refine ⟨V,hV,hmem,hf,?_,large_error D hm hn⟩
  apply epsMCA_le_of_badCount_le (ℓ := 4)
  intro u
  exact (CircuitDensity.mca_count_le_choose _ 2 _ (u 0) (u 1)).trans (by simp [hV])

/-- No fixed reverse multiplicative factor bounds the MCA error of arbitrary received
stacks by the MCA error of their power-image code. The strict separation holds over
a prime field on a smooth tower, at half rate and the common grid point 1/4. -/
theorem no_uniform_reverse_factor (R : ℕ) :
    ∃ (m p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
    ∃ D : Fin (4*m) ↪ ZMod p, Nonempty (ReedSolomon.Smooth D) ∧
    ∃ V : Finset (ZMod p), V.card = 4 ∧ (∀ i, D i ^ m ∈ V) ∧
      (∀ v ∈ V, (univ.filter fun i => D i ^ m = v).card = m) ∧
      (R : ℝ≥0∞) * epsMCA (F := ZMod p)
        (ReedSolomon.code (Function.Embedding.subtype (· ∈ V)) 2 : Set (V → ZMod p)) (1/4) <
      epsMCA (F := ZMod p) (ReedSolomon.code D (2*m) : Set (Fin (4*m) → ZMod p)) (1/4) := by
  classical
  let m := 2^(R+3)
  have hm : 0 < m := by dsimp [m]; positivity
  have hpower : 4*m = 2^(R+5) := by
    rw [show R+5 = R+3+2 by omega, pow_add]
    simp [m,Nat.mul_comm]
  obtain ⟨p,hp,_,hcon⟩ := Nat.exists_prime_gt_modEq_one (k := 4*m) R (by omega)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨D,⟨sm⟩⟩ := SmoothPowerMcaDescent.exists_prime_domain (p := p) hcon.symm.dvd' ⟨R+5,hpower⟩
  let := sm
  let : NeZero (4*m) := ⟨by omega⟩
  obtain ⟨V,hV,hmem,hf,hlo,hhi⟩ := ratio_witness D hm (Fintype.card_fin _)
  refine ⟨m,p,hp,D,⟨sm⟩,V,hV,hmem,hf,?_⟩
  apply (mul_le_mul_right hlo _).trans_lt
  rw [← mul_div_assoc]
  apply lt_of_lt_of_le _ hhi
  apply ENNReal.div_lt_div_right (by exact_mod_cast Fintype.card_ne_zero) (by simp)
  exact_mod_cast (show R*4 < m+1 by
    have h := Nat.lt_two_pow_self (n := R)
    dsimp [m]; rw [pow_add]; omega)

private theorem choose_product_le (n₀ n₁ a b : ℕ) :
    n₀.choose a * n₁.choose b ≤ (n₀+n₁).choose (a+b) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (a := (a,b)) (f := fun ij : ℕ × ℕ => n₀.choose ij.1 * n₁.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp)

/-- Even the single squaring step can increase the worst-case error by an arbitrarily large
factor. Both dimensions have rate one half. The radius is (k−1)/(2k), on both Hamming grids. -/
theorem no_reverse_factor_for_squaring (R : ℕ) :
    ∃ (k p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
    let δ := ((4*k-(2*k+2) : ℕ) : ℝ≥0) / ((4*k : ℕ) : ℝ≥0)
    0 < k ∧ ∃ D : Fin (4*k) ↪ ZMod p, Nonempty (ReedSolomon.Smooth D) ∧
    ∃ V : Finset (ZMod p), V.card = 2*k ∧ (∀ i, D i ^ 2 ∈ V) ∧
      (∀ v ∈ V, (univ.filter fun i => D i ^ 2 = v).card = 2) ∧
      (R : ℝ≥0∞) * epsMCA (F := ZMod p)
        (ReedSolomon.code (Function.Embedding.subtype (· ∈ V)) k : Set (V → ZMod p)) δ <
      epsMCA (F := ZMod p) (ReedSolomon.code D (2*k) : Set (Fin (4*k) → ZMod p)) δ := by
  classical
  let k := 2^(R+3)
  have hR : 4*R < k-1 := by
    have h := Nat.lt_two_pow_self (n := R)
    dsimp [k]; rw [pow_add]; omega
  have hk : 1 ≤ k := by omega
  let M := (2*k).choose (k+1)
  have hM : 4*k*R < M := by
    have hc : k-1 ≤ k.choose 2 := by
      obtain ⟨z,hz⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [hz, Nat.choose_succ_succ, Nat.choose_one_right]
      omega
    have hex := choose_product_le k k (k-1) 2
    rw [Nat.choose_symm hk,Nat.choose_one_right,← two_mul,
      show k-1+2=k+1 by omega] at hex
    calc 4*k*R = k*(4*R) := by ring
      _ < k*(k-1) := Nat.mul_lt_mul_of_pos_left hR (by omega)
      _ ≤ k*k.choose 2 := Nat.mul_le_mul_left _ hc
      _ ≤ M := hex
  let B := R*M
  have hnM : 4*k*B < (4*k).choose (2*k+2) := by
    calc 4*k*B = (4*k*R)*M := by dsimp [B]; ring
      _ < M*M := Nat.mul_lt_mul_of_pos_right hM (by omega)
      _ ≤ (4*k).choose (2*k+2) := by
        simpa only [show 2*k+2*k = 4*k by omega, show k+1+(k+1) = 2*k+2 by omega] using
          choose_product_le (2*k) (2*k) (k+1) (k+1)
  obtain ⟨p,hp,hlarge,hcon⟩ := Nat.exists_prime_gt_modEq_one (k := 4*k)
    (2*k*(B+1).choose 2 + 4*k) (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hpw : 4*k = 2^(R+5) := by
    rw [show R+5=R+3+2 by omega, pow_add]; simp [k,Nat.mul_comm]
  obtain ⟨D,⟨sm⟩⟩ := SmoothPowerMcaDescent.exists_prime_domain (p := p) hcon.symm.dvd' ⟨_,hpw⟩
  let := sm
  let : NeZero (4*k) := ⟨by omega⟩
  have hn : Fintype.card (Fin (4*k)) = 4*k := Fintype.card_fin _
  obtain ⟨V,hV,hmem,hf,_,_⟩ := SmoothPowerMcaDescent.exists_smooth_base D (m := 2)
    (h := 2*k) (by decide) (hn.trans (by omega)) ⟨R+4,by dsimp [k]; rw [← Nat.pow_succ']⟩
  let : Nonempty V := Fintype.card_pos_iff.mp (by simp [hV]; omega)
  let δ := ((4*k-(2*k+2) : ℕ) : ℝ≥0) / ((4*k : ℕ) : ℝ≥0)
  let E := Function.Embedding.subtype (· ∈ V)
  have hlo : epsMCA (F := ZMod p) (ReedSolomon.code E k : Set (V → ZMod p)) δ ≤
      (M : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞) := by
    apply epsMCA_le_of_badCount_le
    intro u
    simpa only [Fintype.card_coe,hV] using CircuitDensity.mca_count_le_choose E k δ (u 0) (u 1)
  refine ⟨k,p,hp,by omega,D,⟨sm⟩,V,hV,hmem,hf,?_⟩
  apply (mul_le_mul_right hlo _).trans_lt
  rw [← mul_div_assoc, ← Nat.cast_mul]
  apply SmoothDeepMcaThreshold.lt_epsMCA_of_product D (k := 2*k) (a := 0) (t := 2*k+2)
    (B := B) (L := B) (by omega) rfl (by rw [hn]; omega) (by simpa [hn] using hnM)
    (by rw [hn,ZMod.card,show B+1-B=1 by omega,Nat.mul_one]; omega) _
    (ENNReal.div_lt_div_right (by exact_mod_cast Fintype.card_ne_zero) (by simp) (by
      exact_mod_cast Nat.lt_succ_self B)) δ
  have ht : 2*k+2 ≤ 4*k := by omega
  rw [hn, tsub_mul, one_mul, show δ * ((4*k : ℕ) : ℝ≥0) =
    ((4*k-(2*k+2) : ℕ) : ℝ≥0) by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity),
    Nat.cast_tsub, tsub_tsub_cancel_of_le (by exact_mod_cast ht)]

#print axioms no_reverse_factor_for_squaring
#print axioms no_uniform_reverse_factor
end ProximityGap.FiberReverseRatio
