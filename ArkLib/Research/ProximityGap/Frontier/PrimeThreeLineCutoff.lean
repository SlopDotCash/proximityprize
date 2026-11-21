/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeThreeLineFamily
import ArkLib.Research.ProximityGap.Frontier.ArbitraryDomainHeadThreshold

/-! # An effective prime cutoff for the 128-bit three-line family

The pairwise difference test and the predecessor counting inequalities already
hold at every prime at least 2^258. The resulting classification covers the
entire real-radius interval for each domain of the prescribed length.
-/

set_option autoImplicit false
namespace ProximityGap.PrimeThreeLineCutoff
open MCAThresholdLedger PrimeThreeLineFamily
open scoped NNReal ENNReal

/-- A length-uniform certificate with first failure near two thirds of the
sites. Every dimension in the indicated interval has the same cutoff. -/
theorem classification_of_band {p n k j : ℕ} [Fact p.Prime] [NeZero n]
    (x : Fin n ↪ ZMod p) (big : 65536≤n) (index : j=p/2^128/3)
    (rel : 2*n≤3*j+4 ∧ 3*j≤2*n) (kp : 3≤k) (kr : 28*k≤n)
    (room : (n*n-n)*(4*3+1)≤(p-1)*(k-2)) :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p))
    let ε := 1/(2:ℝ≥0∞)^128
    let b := (j:ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C ε=b ∧ ∀ δ, epsMCA (F:=ZMod p) C δ≤ε ↔ δ<b := by
  have jp : 30000≤j+1 := by omega
  have jn : j≤n := by omega
  have core : k<n-j := by omega
  have packing : 3*(n-j-k+1)≤n-k+2 := by omega
  have cubic : (j+1)*k*n^2+(32+2)*n^3 < (j+1)*(n-j+1)^3 := by
    have one := Nat.mul_le_mul_left (j+1) (Nat.pow_le_pow_left (show n≤3*(n-j+1) by omega) 3)
    have two := Nat.mul_le_mul_left ((j+1)*n^2) kr
    have three := Nat.mul_le_mul_right (n^3) jp
    have four : 0<n^3 := pow_pos (by omega) _
    nlinarith only [one,two,three,four]
  have geom : (n+(Nat.choose 3 2+3)*k)*32+3*n < (3+1)*(n-j+1)*32 := by
    norm_num
    omega
  have bad : 1/((2^128:ℕ):ℝ≥0∞) < epsMCA (F:=ZMod p)
      (ReedSolomon.code x k : Set (Fin n → ZMod p)) ((j:ℝ≥0)/n) := by
    have mass := PrimeHeadDifferences.grid_mass (m:=3) (t:=n-j) (k:=k) x ((j:ℝ≥0)/n)
      (by decide) (by omega : 2≤k) core (Nat.sub_le ..) packing
      (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne n),←Nat.cast_tsub]) room
    apply lt_of_lt_of_le _ mass
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=p.Prime)).pos (by decide : 0<2^128)]
    rw [show n-(n-j)=j by omega]
    rw [index]
    exact Nat.not_le_of_lt (Nat.lt_mul_div_succ _ (by decide : 0<3))
  have result := ArbitraryDomainHeadThreshold.exact_threshold_of_bad (Q:=2^128) (m:=3)
    (j:=j) (L:=32) (k:=k) x (by decide) (by decide) (by simpa only [ZMod.card] using index) (by omega)
    jn (by omega) core (by decide) cubic geom bad
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using result

/-- For each prime p at least 2^258, and every domain of the indicated
length, the first failure is the rounded third of the scalar budget and
the good real radii form the open interval below that grid boundary. -/
theorem classification {p : ℕ} [Fact p.Prime] (hp : 2^258≤p)
    (x : Fin (length p) ↪ ZMod p) :
    let C := (ReedSolomon.code x (length p/2^125) : Set (Fin (length p) → ZMod p))
    let ε := 1/(2:ℝ≥0∞)^128
    let b := ((p/2^128/3:ℕ):ℝ≥0)/(length p)
    mcaDeltaStar (F:=ZMod p) C ε=b ∧ ∀ δ, epsMCA (F:=ZMod p) C δ≤ε ↔ δ<b := by
  let n := length p
  let k := n/2^125
  let j := p/2^128/3
  have big : 2^129≤n := by dsimp [n,length];omega
  apply classification_of_band (k:=k) (j:=j) x (by omega) rfl
    (by dsimp [n,length,j];omega) (by dsimp [k];omega) (by dsimp [k];omega)
  have qbound : 99*2^129*n≤100*(p-1) := by dsimp [n,length];omega
  have kbound : 14*n≤17*2^125*(k-2) := by dsimp [k];omega
  change (n*n-n)*(4*3+1)≤(p-1)*(k-2)
  apply le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  have scale := Nat.mul_le_mul qbound kbound
  nlinarith only [scale]

/-- At dimension floor(n/2^122), the improved prime-field separation test
already gives the same classification for every prime at least 2^253,
including the 254- to 256-bit portion of this family. -/
theorem classification_254_bits {p : ℕ} [Fact p.Prime] (hp : 2^253≤p)
    (x : Fin (length p) ↪ ZMod p) :
    let C := (ReedSolomon.code x (length p/2^122) : Set (Fin (length p) → ZMod p))
    let ε := 1/(2:ℝ≥0∞)^128
    let b := ((p/2^128/3:ℕ):ℝ≥0)/(length p)
    mcaDeltaStar (F:=ZMod p) C ε=b ∧ ∀ δ, epsMCA (F:=ZMod p) C δ≤ε ↔ δ<b := by
  let n := length p
  let k := n/2^122
  let j := p/2^128/3
  have big : 2^124≤n := by dsimp [n,length];omega
  apply classification_of_band (k:=k) (j:=j) x (by omega) rfl
    (by dsimp [n,length,j];omega) (by dsimp [k];omega) (by dsimp [k];omega)
  have qbound : 2^129*n≤2*(p-1) := by dsimp [n,length];omega
  have kbound : n≤4*2^122*(k-2) := by dsimp [k];omega
  change (n*n-n)*(4*3+1)≤(p-1)*(k-2)
  apply le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  have scale := Nat.mul_le_mul qbound kbound
  nlinarith only [scale]

end ProximityGap.PrimeThreeLineCutoff
#print axioms ProximityGap.PrimeThreeLineCutoff.classification
#print axioms ProximityGap.PrimeThreeLineCutoff.classification_of_band
#print axioms ProximityGap.PrimeThreeLineCutoff.classification_254_bits
