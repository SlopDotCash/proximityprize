/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DoubleQuadraticHeadCount
import ArkLib.Research.ProximityGap.Frontier.UniversalTwoHeadBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA

/-! # The finite double-interpolant two-head window through rate one third

The first possible missing error count is within a constant of the linear
agreement boundary. The estimate is uniform over all evaluation domains.
-/
set_option autoImplicit false
namespace ProximityGap.DoubleQuadraticThreshold
open MCAThresholdLedger ArkLib.ProximityGap.Frontier ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Smallest allowed agreement count for a uniform fourteen-unit interpolation margin. -/
def agreements (n k : ℕ) := (n+3*(k-1)+13)/3+1

private theorem room {n k e : ℕ} (large : 65536 ≤ n) (hk : 2 ≤ k)
    (rate : 3*k ≤ n) (en : e ≤ n) (lower : n ≤ k+2*e+2) (safe : agreements n k ≤ n-e) :
    ∃ s L : ℕ, 2 ≤ s ∧ (s+1)*n+(3*s-2)*(k-1) < 3*s*(n-e) ∧
      512 ≤ L ∧ 4*s+32 ≤ L ∧ s+2*L < e+2 ∧
      n+3*(k-1) < n-e+2*(n-e-n/L) := by
  unfold agreements at safe
  let d := k-1
  have kd : d+1=k := by dsimp [d]; omega
  have ad : 2*d ≤ n := by omega
  have window (s : ℕ) (hs : 2 ≤ s)
      (capacity : n+s*(n+3*d)<2*d+s*(3*(n-e)))
      (slack : s+2*(4*s+32)<e+2) (slack' : s+2*(n/7+2)<e+2) :
      ∃ L : ℕ, (s+1)*n+(3*s-2)*(k-1)<3*s*(n-e) ∧
        512 ≤ L ∧ 4*s+32 ≤ L ∧ s+2*L<e+2 ∧ n+3*(k-1)<n-e+2*(n-e-n/L) := by
    let L := max (4*s+32) (n/7+2)
    have left : 4*s+32 ≤ L := le_max_left ..
    have right : n/7+2 ≤ L := le_max_right ..
    have trim : 3*s-2+2=3*s := by omega
    have cover : n/L < 7 := (Nat.div_lt_iff_lt_mul (by omega : 0 < L)).mpr (by omega)
    refine ⟨L,?_,by omega,left,?_,by omega⟩
    · change (s+1)*n+(3*s-2)*d<3*s*(n-e)
      nlinarith only [capacity,congrArg (·*d) trim]
    · rcases le_total (4*s+32) (n/7+2) with h|h
      · simpa [L,max_eq_right h] using slack'
      · simpa [L,max_eq_left h] using slack
  by_cases wide : n+3*d+20 ≤ 3*(n-e)
  · let s := (n-2*d)/20+2
    have hs : 2 ≤ s := by dsimp [s];omega
    have gain : n<2*d+s*20 := by dsimp [s];omega
    obtain ⟨L,h⟩ := window s hs
      (by nlinarith only [Nat.mul_le_mul_left s wide,gain])
      (by dsimp [s];omega) (by dsimp [s];omega)
    exact ⟨s,L,hs,h⟩
  · let s := (n-2*d)/14+2
    have hs : 2 ≤ s := by dsimp [s];omega
    have gain : n<2*d+s*14 := by dsimp [s];omega
    have narrow : n+3*d+14 ≤ 3*(n-e) := by omega
    obtain ⟨L,h⟩ := window s hs
      (by nlinarith only [Nat.mul_le_mul_left s narrow,gain])
      (by dsimp [s];omega) (by dsimp [s];omega)
    exact ⟨s,L,hs,h⟩

/-- Every received pair has at most two heads' worth of bad scalars. -/
theorem upper {n k e : ℕ} [NeZero n] (x : Fin n ↪ F) (large : 65536 ≤ n)
    (hk : 2 ≤ k) (rate : 3*k ≤ n) (en : e ≤ n)
    (lower : n ≤ k+2*e+2) (safe : agreements n k ≤ n-e)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(n-e-1) → (i:F) ≠ 0) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) ≤
      ((2*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F) := by
  classical
  obtain ⟨s,L,hs,sur,cut,rbound,occupancy,geometry⟩ := room large hk rate en lower safe
  unfold agreements at safe
  apply epsMCA_le_of_badCount_le
  intro u
  let fam := HalfPredecessorBadEventRichPointBridge.canonicalBadScalarRichPointFamily x
    (k:=k) ((e:ℝ≥0)/n) u (by omega)
  have grid : ⌈(1-(e:ℝ≥0)/n)*(Fintype.card (Fin n):ℝ≥0)⌉₊=n-e := by
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne n),
      ←Nat.cast_tsub,Nat.ceil_natCast]
  change fam.G.card ≤ 2*(e+1)
  have bound := DoubleQuadraticHeadCount.family_cap fam (Fintype.card_fin _) (Nat.add_sub_of_le en)
    (by omega) le_rfl grid hs (by omega) sur (by omega) (by omega) cut rbound occupancy geometry hchar
  simpa only [Nat.mul_add,Nat.mul_one] using bound

/-- The exact bad probability, including the case where the two heads exhaust the field. -/
theorem exact_mass {n k e : ℕ} [NeZero n] (x : Fin n ↪ F) (hk : 2≤k) (rate : 3*k≤n)
    (large : 65536 ≤ n) (pack : n≤k+2*e) (pin : k+e+1≤n) (enough : agreements n k ≤ n-e)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(n-e-1) → (i:F)≠0) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) =
      ((min (Fintype.card F) (2*(e+1)):ℕ):ℝ≥0∞)/(Fintype.card F) := by
  apply le_antisymm _ (by
    simpa only [Fintype.card_fin] using UniversalTwoHeadBudget.mass (e:=e) x hk
      (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin]))
  by_cases supply : 2*(e+1) ≤ Fintype.card F
  · rw [min_eq_right supply]
    exact upper x large hk rate (by omega) (by omega) enough hchar
  · rw [min_eq_left (by omega : Fintype.card F≤2*(e+1)),
      ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
    exact epsMCA_le_one _ _

/-- The first failing grid point at tolerance 1/Q, and the full real good interval. -/
theorem classification {n k Q j : ℕ} [NeZero n] (x : Fin n ↪ F) (Qbig : 2≤Q)
    (index : j=Fintype.card F/Q/2) (hk : 2≤k) (rate : 3*k≤n) (large : 65536 ≤ n)
    (pack : n≤k+2*j) (pin : k+j+1≤n) (prev : agreements n k ≤ n-j+1)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(n-j) → (i:F)≠0) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let ε := 1/(Q:ℝ≥0∞)
    let bound := (j:ℝ≥0)/n
    mcaDeltaStar (F:=F) C ε = bound ∧ ∀ δ, epsMCA (F:=F) C δ≤ε ↔ δ<bound := by
  dsimp only
  let C := (ReedSolomon.code x k : Set (Fin n → F))
  have good : epsMCA (F:=F) C (predecessorRadius n j) ≤ 1/(Q:ℝ≥0∞) := by
    apply (upper (e:=j-1) x large hk rate (by omega) (by omega) (by omega) (by
      intro i hi hb; exact hchar i hi (by omega))).trans
    rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega : 0 < Q)]
    omega
  have bad : 1/(Q:ℝ≥0∞) < epsMCA (F:=F) C ((j:ℝ≥0)/n) := by
    have mass := UniversalTwoHeadBudget.mass (e:=j) x hk (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin])
    rw [Fintype.card_fin] at mass
    apply lt_of_lt_of_le _ mass
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega : 0 < Q)]
    exact Nat.not_le_of_lt (lt_min (Nat.div_lt_self Fintype.card_pos (by omega)) (by omega))
  have result := le_antisymm (mcaDeltaStar_le_of_bad C _ bad)
    (latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by omega : 1≤j) (by omega : j≤n) C _ good)
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact result,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro h
    by_contra! beyond
    exact bad.not_ge ((epsMCA_mono C beyond).trans h)
  · intro h
    by_contra! fail
    exact h.not_ge (result ▸ mcaDeltaStar_le_of_bad C _ fail)

/-- For any feasible two-head crossing in a prime field, the scalar budget
already supplies the characteristic required by the discriminant. -/
theorem prime_classification {p n k Q j : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (Qbig : 2 ≤ Q) (index : j=p/Q/2) (hk : 2 ≤ k) (rate : 3*k ≤ n) (large : 65536 ≤ n)
    (pack : n ≤ k+2*j) (pin : k+j+1 ≤ n) (prev : agreements n k ≤ n-j+1)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let ε := 1/(Q:ℝ≥0∞)
    let bound := (j:ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C ε = bound ∧ ∀ δ, epsMCA (F:=ZMod p) C δ ≤ ε ↔ δ<bound := by
  apply classification x Qbig (by simpa using index) hk rate large pack pin prev _ width
  have scaled := (Nat.le_div_iff_mul_le (by omega : 0 < Q)).mp (show 2*j ≤ p/Q by omega)
  have fieldRoom : 4*j ≤ p := by
    have h := Nat.mul_le_mul_left (2*j) Qbig
    omega
  intro i hi bound zero
  have divides := Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod p) p i).mp zero)
  have equality : p=4*j := by omega
  have even : 2 ∣ p := ⟨2*j,by omega⟩
  have alternatives := (Nat.dvd_prime (Fact.out : p.Prime)).mp even
  omega

/-- At rate three tenths this gives every finite 128-bit first failure throughout
the specified budget interval, including the upper endpoint beyond degree 34. -/
theorem three_tenths {p m n B : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (size : 328 ≤ m) (length : n=200*m) (budget : p/2^128=B)
    (lo : 140*m ≤ B) (hi : B ≤ 146*m+1) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x (60*m) : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let bound := ((B/2:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/2^128) = bound ∧
      ∀ δ, epsMCA (F:=ZMod p) C δ ≤ 1/2^128 ↔ δ<bound := by
  have result := prime_classification (Q:=2^128) (j:=B/2) (k:=60*m) x
    (by decide) (by rw [budget]) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by unfold agreements;omega) width
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using result

/-- Every prime of at least this size yields a rate-three-tenths family
at the upper end of the explicit budget range. -/
theorem three_tenths_family {p B n : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (budget : p/2^128=B) (large : 65536 ≤ B) (length : n=200*(B/146+1))
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x (60*(B/146+1)) : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let bound := ((B/2:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/2^128) = bound ∧
      ∀ δ, epsMCA (F:=ZMod p) C δ ≤ 1/2^128 ↔ δ<bound :=
  three_tenths x (by omega) length budget (by omega) (by omega) width

end ProximityGap.DoubleQuadraticThreshold
#print axioms ProximityGap.DoubleQuadraticThreshold.exact_mass
#print axioms ProximityGap.DoubleQuadraticThreshold.classification
#print axioms ProximityGap.DoubleQuadraticThreshold.three_tenths
#print axioms ProximityGap.DoubleQuadraticThreshold.prime_classification
#print axioms ProximityGap.DoubleQuadraticThreshold.three_tenths_family
