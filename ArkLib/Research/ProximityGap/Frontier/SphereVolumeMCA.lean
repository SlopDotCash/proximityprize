/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DeepListMcaTransfer
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
import Mathlib.Data.Nat.Choose.Central

/-! # The sphere-volume failure criterion for arbitrary Reed–Solomon domains

An oversized average list in dimension k+1 produces a genuinely bad affine
line in dimension k by evaluation at one off-domain point.
-/
set_option autoImplicit false
namespace ProximityGap.SphereVolumeMCA
open Finset Polynomial Code CodingTheory
open scoped NNReal
variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq I] [DecidableEq F] in
/-- At the exact Hamming radius of e errors the volume criterion for an
oversized list is an integer inequality. -/
theorem large_list_of_volume (D : I ↪ F) {k e L : ℕ} (hkn : k ≤ Fintype.card I)
    (hvol : Fintype.card F ^ Fintype.card I * L <
      Fintype.card F ^ k * (∑ i ∈ range (e+1), (Fintype.card I).choose i * (Fintype.card F-1)^i)) :
    (L : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F)) ((e : ℝ) / Fintype.card I) := by
  classical
  let : DecidableEq I := fun i j => Classical.propDecidable (i=j)
  let r := (e : ℝ) / Fintype.card I
  let C := ReedSolomon.code D k
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfloor : ⌊r * (Fintype.card I : ℝ)⌋₊ = e := by simp [r, hn]
  have hdim : Module.finrank F C = k := ReedSolomon.dim_eq_deg_of_le (α := D) hkn
  have mass := sum_ncard_closeCodewordsRel_eq C r hr
  rw [submodule_ncard_eq_pow_finrank, hdim, hammingBallVolume, hfloor] at mass
  by_contra! h
  have ub := Lambda_le_iff_forall_ncard_le.mp h
  have compact : ∑ y : I → F, (closeCodewordsRel (C : Set (I → F)) y r).ncard ≤
      ∑ _y : I → F, L := sum_le_sum fun y _ => (ub y).2
  simp only [sum_const, card_univ, Fintype.card_fun, smul_eq_mul] at compact
  exact (not_le_of_gt hvol) (mass.symm.le.trans compact)

omit [DecidableEq I] in
open Classical in
/-- An explicit arithmetic failure criterion in every minimum-agreement band.
The first hypothesis on counts is the mean list size in dimension k+1, the
second bounds the loss under a single evaluation outside the domain. -/
theorem exists_bad_count_of_volume (D : I ↪ F) (δ : ℝ≥0) {k t B L : ℕ}
    (hk : 0 < k) (hkt : k < t) (htn : t ≤ Fintype.card I)
    (hδ : (1-δ) * (Fintype.card I : ℝ≥0) ≤ t)
    (hvol : Fintype.card F ^ Fintype.card I * L < Fintype.card F ^ (k+1) *
      (∑ i ∈ range (Fintype.card I-t+1), (Fintype.card I).choose i * (Fintype.card F-1)^i))
    (hroom : k * (L+1).choose 2 < (Fintype.card F-Fintype.card I) * (L+1-B)) :
    ∃ u₀ u₁ : I → F, B <
      (univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)).card :=
  DeepListMcaTransfer.exists_bad_count_of_list D δ hk hkt htn hδ
    (large_list_of_volume D (by omega) hvol) hroom

private theorem alphabet_correction (q e : ℕ) (hq : 0<q) (he : 2*e ≤ q) :
    q^e ≤ 2*(q-1)^e := by
  have bern (j : ℕ) (hj : j ≤ q) : (q-j)*q^j ≤ q*(q-1)^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have old := ih (by omega)
      have prod : (q-(j+1))*q ≤ (q-j)*(q-1) := by
        have h₁ : q-(j+1)+1 = q-j := by omega
        have h₂ : q-1+1 = q := by omega
        calc
          _ = (q-(j+1))*(q-1+1) := congrArg ((q-(j+1))*·) h₂.symm
          _ = (q-(j+1))*(q-1)+(q-(j+1)) := by ring
          _ ≤ (q-(j+1))*(q-1)+(q-1) := by omega
          _ = (q-j)*(q-1) := by rw [← h₁]; ring
      calc
        _ = ((q-(j+1))*q)*q^j := by rw [pow_succ]; ring
        _ ≤ ((q-j)*(q-1))*q^j := Nat.mul_le_mul_right _ prod
        _ = ((q-j)*q^j)*(q-1) := by ring
        _ ≤ (q*(q-1)^j)*(q-1) := Nat.mul_le_mul_right _ old
        _ = _ := by rw [pow_succ]; ring
  have h := bern e (by omega)
  have low : q*q^e ≤ 2*((q-e)*q^e) := by
    simpa [mul_assoc] using Nat.mul_le_mul_right (q^e) (show q ≤ 2*(q-e) by omega)
  exact Nat.le_of_mul_le_mul_left (low.trans ((Nat.mul_le_mul_left 2 h).trans_eq (by ring))) hq

omit [DecidableEq I] in
open Classical in
/-- The final Hamming shell alone supplies enough candidates if
twice the desired list size times q^(t-k-1) is below the binomial count.
The alphabet loss is at most a factor of two when q ≥ 2(n−t). -/
theorem exists_bad_count_of_shell (D : I ↪ F) (δ : ℝ≥0) {k t B L : ℕ}
    (hk : 0 < k) (hkt : k < t) (htn : t ≤ Fintype.card I)
    (hδ : (1-δ) * (Fintype.card I : ℝ≥0) ≤ t)
    (hq : 2*(Fintype.card I-t) ≤ Fintype.card F)
    (hshell : 2*L*Fintype.card F^(t-(k+1)) < (Fintype.card I).choose t)
    (hroom : k*(L+1).choose 2 < (Fintype.card F-Fintype.card I)*(L+1-B)) :
    ∃ u₀ u₁ : I → F, B <
      (univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)).card := by
  classical
  apply exists_bad_count_of_volume D δ hk hkt htn hδ _ hroom
  let q := Fintype.card F
  let n := Fintype.card I
  let e := n-t
  have geom := alphabet_correction q e Fintype.card_pos hq
  have shell : n.choose t*(q-1)^e ≤
      ∑ i ∈ range (e+1), n.choose i*(q-1)^i := by
    rw [← Nat.choose_symm htn]
    exact single_le_sum (f := fun i => n.choose i*(q-1)^i) (fun i _ => Nat.zero_le _)
      (mem_range.mpr (by omega : e < e+1))
  have hpos : 0<(q-1)^e := by
    exact pow_pos (by have := Fintype.one_lt_card (α := F); dsimp [q]; omega) _
  calc
    q^n * L = q^(k+1)*(L*q^(t-(k+1))*q^e) := by
      rw [show n = k+1+(t-(k+1))+e by dsimp [n,e];omega, pow_add, pow_add]
      ring
    _ ≤ q^(k+1)*(L*q^(t-(k+1))*(2*(q-1)^e)) := by gcongr
    _ = q^(k+1)*((2*L*q^(t-(k+1)))*(q-1)^e) := by ring
    _ < q^(k+1)*(n.choose t*(q-1)^e) := by
      exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hshell hpos)
        (pow_pos Fintype.card_pos _)
    _ ≤ _ := Nat.mul_le_mul_left _ shell

private theorem pow_lt_choose (n k s b d : ℕ) (hs : s ≤ k) (hkn : 2*k ≤ n)
    (hlen : 2*(k-s)+1 < 2^d) (hexp : b+d ≤ 2*(k-s)) :
    2^b < n.choose (k+s) := by
  have hc : (k-s).centralBinom ≤ n.choose (k+s) := by
    calc
      _ = (2*(k-s)).choose (k-s) := rfl
      _ ≤ (2*k).choose (k-s) := Nat.choose_le_choose _ (by omega)
      _ = (2*k).choose (k+s) := by
        rw [← Nat.choose_symm (show k+s ≤ 2*k by omega)]
        congr 1
        omega
      _ ≤ _ := Nat.choose_le_choose _ hkn
  by_contra! h
  have upper := (Nat.four_pow_le_two_mul_add_one_mul_centralBinom (k-s)).trans
    (Nat.mul_le_mul_left _ (hc.trans h))
  have strict := upper.trans_lt (Nat.mul_lt_mul_of_pos_right hlen (by positivity : 0 < 2^b))
  have hle : 2^d * 2^b ≤ 4^(k-s) := by
    rw [← pow_add, show (4:ℕ)=2^2 by decide, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact (not_lt_of_ge hle) strict

omit [DecidableEq I] in
open Classical in
/-- Uniform failure-side bandwidth at length 2^30 for fields of at most 256 bits.
For each positive s satisfying the displayed linear inequality, the code already
exceeds the 128-bit budget at k+s agreements. -/
theorem production_band (D : I ↪ F) (δ : ℝ≥0) {k s : ℕ}
    (hn : Fintype.card I = 2^30) (hqlo : 2^128 ≤ Fintype.card F)
    (hqhi : Fintype.card F < 2^256) (hs : 1 ≤ s) (hsk : s ≤ k) (hk : 2*k ≤ 2^30)
    (hband : 130+256*(s-1)+31 ≤ 2*(k-s))
    (hδ : (1-δ)*(Fintype.card I : ℝ≥0) ≤ (k+s : ℕ)) :
    ∃ u₀ u₁ : I → F, Fintype.card F / 2^128 <
      (univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)).card := by
  classical
  let q := Fintype.card F
  let B := q / 2^128
  have hcard : Fintype.card F = q := rfl
  have Bsmall : B < 2^128 := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0<2^128)).2
    exact hqhi
  have Bbudget : B*2^128 ≤ q := Nat.div_mul_le_self ..
  apply exists_bad_count_of_shell D δ (L := 2*B) (by omega) (by omega) (by omega) hδ
    (by rw [hn]; omega)
  · rw [hn, hcard, show k+s-(k+1) = s-1 by omega]
    have hb : 2*(2*B) ≤ 2^130 := by omega
    calc
      _ ≤ 2^130*(2^256)^(s-1) := Nat.mul_le_mul hb (Nat.pow_le_pow_left hqhi.le _)
      _ = 2^(130+256*(s-1)) := by rw [← pow_mul, ← pow_add]
      _ < _ := pow_lt_choose _ k s _ 31 hsk hk (by omega) hband
  · change k*(2*B+1).choose 2 < (q-Fintype.card I)*(2*B+1-B)
    rw [hn, show 2*B+1-B=B+1 by omega]
    have choose : (2*B+1).choose 2 = (2*B+1)*B := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel]
      exact Nat.div_eq_of_eq_mul_right (by decide) (by ring)
    rw [choose]
    have hB : k*(2*B+1) < q-2^30 := by
      have hk' : k*(2*B+1) ≤ 2^29*(2*B+1) := Nat.mul_le_mul_right _ (by omega)
      have hq' : 2^128 ≤ q := hqlo
      omega
    rw [← mul_assoc]
    exact (Nat.mul_le_mul_right B hB.le).trans_lt
      (Nat.mul_lt_mul_of_pos_left (by omega) (by omega))

open Classical in
/-- A strict integer-budget failure implies a strict failure of the canonical
generator error at the corresponding security level. -/
theorem mcaError_gt_of_count [SampleableType F] (D : I ↪ F) (k Q : ℕ) (δ : ℝ≥0)
    (hQ : 0<Q) (h : ∃ u₀ u₁ : I → F, Fintype.card F/Q <
      (univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)).card) :
    ENNReal.ofReal (1/(Q:ℝ)) <
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D k) (δ:ℝ) := by
  classical
  obtain ⟨u,v,hm⟩ := h
  unfold CoreDefinitions.mcaError
  apply lt_of_lt_of_le _ (le_iSup _ ![u,v])
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp_rw [← mcaEvent_iff_isMCA]
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  rw [one_mul]
  exact_mod_cast (Nat.div_lt_iff_lt_mul hQ).1 hm

/-- The dimensions of the four sponsor rates at length 2^30. -/
def productionDimension : Fin 4 → ℕ := ![536870912,268435456,134217728,67108864]

/-- Hamming counts at which the field-independent volume attack already works. -/
def productionErrors : Fin 4 → ℕ := ![532709122,803225473,938483649,1006112736]

set_option maxRecDepth 4096 in
/-- All four canonical affine-line generator errors exceed 2^(-128) at these
explicit Hamming counts, for every evaluation embedding and every field size
between 2^128 and 2^256. -/
theorem four_rates_error [SampleableType F] (D : I ↪ F) (j : Fin 4) (hn : Fintype.card I=2^30)
    (hqlo : 2^128 ≤ Fintype.card F) (hqhi : Fintype.card F < 2^256) :
    ENNReal.ofReal (1/(2:ℝ)^128) < CoreDefinitions.mcaError
      (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D (productionDimension j))
      ((productionErrors j : ℝ) / 2^30) := by
  let δ : ℝ≥0 := (productionErrors j : ℝ≥0) / 2^30
  let s : Fin 4 → ℕ := ![4161790,2080895,1040447,520224]
  have bound := production_band D δ (k := productionDimension j) (s := s j) hn hqlo hqhi
    (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide)
    (by
      have he : δ*2^30 = (productionErrors j : ℝ≥0) := by
        dsimp only [δ]
        exact div_mul_cancel₀ _ (by positivity)
      rw [hn, Nat.cast_pow, Nat.cast_ofNat, tsub_mul, one_mul, tsub_le_iff_right, he]
      exact_mod_cast (show 2^30 ≤ productionDimension j+s j+productionErrors j by
        fin_cases j <;> decide))
  have err := mcaError_gt_of_count D (productionDimension j) (2^128) δ (by decide) bound
  simpa only [δ, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_natCast,
    Nat.cast_pow, Nat.cast_ofNat] using err

#print axioms four_rates_error
#print axioms production_band
#print axioms exists_bad_count_of_shell
#print axioms large_list_of_volume
#print axioms exists_bad_count_of_volume
end ProximityGap.SphereVolumeMCA
