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

/-- The integer margin needed after subtracting the length and three times the degree. -/
def margin (n k : ℕ) := if 11*n ≤ 54*k ∨ 128 ≤ k ∧ 186*k ≤ 29*n then 3
  else if n+512 ≤ 6*k ∨ 186*k ≤ 29*n then 4 else 5

theorem margin_le_five (n k : ℕ) : margin n k ≤ 5 := by
  unfold margin
  split_ifs <;> decide

private theorem margin_ge_three (n k : ℕ) : 3 ≤ margin n k := by
  unfold margin
  split_ifs <;> decide

/-- Smallest allowed agreement count for the two-interpolant proof. -/
def agreements (n k : ℕ) := (n+3*(k-1)+margin n k-1)/3+1

private theorem simple_cubic_capacity {n d t : ℕ} (surplus : 35*n+196*d<134*t) :
    n*(34+1)<Fintype.card (SecondPrimeQuarticInterpolation.Monomials 34 3 d t) := by
  simp only [SecondPrimeQuarticInterpolation.Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  omega

private theorem cubic_capacity {n d t : ℕ} (surplus : 104*n+196*d<268*t) :
    n*(2*(34+1)+34)<Fintype.card (SecondPrimeQuarticInterpolation.Monomials 34 3 d (2*t)) := by
  simp only [SecondPrimeQuarticInterpolation.Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  omega

private theorem room {n k e : ℕ} (large : 65536 ≤ n) (hk : 2 ≤ k)
    (rate : 3*k ≤ n) (en : e ≤ n) (lower : n ≤ k+2*e+2) (safe : agreements n k ≤ n-e) :
    ∃ s b v : ℕ, 2 ≤ s ∧ (s+1)*n+(3*s-2)*(k-1) < 3*s*(n-e) ∧
      0 < b ∧ b ≤ 34 ∧
      (n*(b+1)<Fintype.card (SecondPrimeQuarticInterpolation.Monomials b v (k-1) (n-e)) ∨
       n*(2*(b+1)+b)<Fintype.card (SecondPrimeQuarticInterpolation.Monomials b v (k-1) (2*(n-e)))) ∧
      2*b+v*s ≤ 2*e+2 ∧ b+(v-1)*s ≤ e+1 := by
  let d := k-1
  have kd : d+1=k := by dsimp [d];omega
  have ad : 2*d ≤ n := by omega
  unfold agreements at safe
  have minimum : 3 ≤ margin n k := margin_ge_three n k
  have base : n+3*d+3 ≤ 3*(n-e) := by omega
  have window {s D : ℕ} (hs : 2 ≤ s) (gain : n < 2*d+s*D) (room : n+3*d+D ≤ 3*(n-e)) :
      (s+1)*n+(3*s-2)*(k-1)<3*s*(n-e) := by
    change (s+1)*n+(3*s-2)*d<3*s*(n-e)
    have trim : 3*s-2+2=3*s := by omega
    nlinarith only [gain,Nat.mul_le_mul_left s room,congrArg (·*d) trim]
  have quartic := DoubleQuadraticHeadCount.double_capacity (n:=n) (d:=k-1) (t:=n-e) (by omega)
  by_cases wide : n+3*d+10 ≤ 3*(n-e)
  · let s := (n-2*d)/10+2
    have hs : 2 ≤ s := by dsimp [s];omega
    refine ⟨s,16,4,hs,window hs (by dsimp [s];omega) wide,by decide,by decide,Or.inr quartic,?_,?_⟩ <;> dsimp [s] <;> omega
  by_cases high : 11*n ≤ 54*k
  · have cubic := cubic_capacity (n:=n) (d:=k-1) (t:=n-e) (by omega)
    let s := (n-2*d)/3+2
    have hs : 2 ≤ s := by dsimp [s];omega
    refine ⟨s,34,3,hs,window hs (by dsimp [s];omega) base,by decide,by decide,Or.inr cubic,?_,?_⟩ <;> dsimp [s] <;> omega
  by_cases low : 186*k ≤ 29*n
  · have cubic := simple_cubic_capacity (n:=n) (d:=k-1) (t:=n-e) (by omega)
    by_cases degree : 128 ≤ k
    · let s := (n-2*d)/3+2
      have hs : 2 ≤ s := by dsimp [s];omega
      refine ⟨s,34,3,hs,window hs (by dsimp [s];omega) base,by decide,by decide,Or.inl cubic,?_,?_⟩ <;> dsimp [s] <;> omega
    · simp [margin,high,low,degree] at safe
      let s := (n-2*d)/4+2
      have hs : 2 ≤ s := by dsimp [s];omega
      have room : n+3*d+4 ≤ 3*(n-e) := by omega
      refine ⟨s,34,3,hs,window hs (by dsimp [s];omega) room,by decide,by decide,Or.inl cubic,?_,?_⟩ <;> dsimp [s] <;> omega
  by_cases mid : n+512 ≤ 6*k
  · simp [margin,high,mid,low] at safe
    let s := (n-2*d)/4+2
    have hs : 2 ≤ s := by dsimp [s];omega
    have room : n+3*d+4 ≤ 3*(n-e) := by omega
    refine ⟨s,16,4,hs,window hs (by dsimp [s];omega) room,by decide,by decide,Or.inr quartic,?_,?_⟩ <;> dsimp [s] <;> omega
  · simp [margin,high,mid,low] at safe
    let s := (n-2*d)/5+2
    have hs : 2 ≤ s := by dsimp [s];omega
    have room : n+3*d+5 ≤ 3*(n-e) := by omega
    refine ⟨s,16,4,hs,window hs (by dsimp [s];omega) room,by decide,by decide,Or.inr quartic,?_,?_⟩ <;> dsimp [s] <;> omega

/-- Every received pair has at most two heads' worth of bad scalars. -/
theorem upper {n k e : ℕ} [NeZero n] (x : Fin n ↪ F) (large : 65536 ≤ n)
    (hk : 2 ≤ k) (rate : 3*k ≤ n) (en : e ≤ n)
    (lower : n ≤ k+2*e+2) (safe : agreements n k ≤ n-e)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(n-e-1-(k-1)) → (i:F) ≠ 0) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) ≤
      ((2*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F) := by
  classical
  obtain ⟨s,b,v,hs,sur,bh,bd,aux,first,second⟩ := room large hk rate en lower safe
  have base : 3 ≤ margin n k := margin_ge_three n k
  unfold agreements at safe
  apply epsMCA_le_of_badCount_le
  intro u
  let fam := HalfPredecessorBadEventRichPointBridge.canonicalBadScalarRichPointFamily x
    (k:=k) ((e:ℝ≥0)/n) u (by omega)
  have grid : ⌈(1-(e:ℝ≥0)/n)*(Fintype.card (Fin n):ℝ≥0)⌉₊=n-e := by
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne n),
      ←Nat.cast_tsub,Nat.ceil_natCast]
  change fam.G.card ≤ 2*(e+1)
  have bound := DoubleQuadraticHeadCount.primitive_cap fam (Fintype.card_fin _) (Nat.add_sub_of_le en)
    (by omega) le_rfl grid hs (by omega) sur bh bd aux (by omega) (by omega) first second hchar
  simpa only [Nat.mul_add,Nat.mul_one] using bound

/-- The exact bad probability, including the case where the two heads exhaust the field. -/
theorem exact_mass {n k e : ℕ} [NeZero n] (x : Fin n ↪ F) (hk : 2≤k) (rate : 3*k≤n)
    (large : 65536 ≤ n) (pack : n≤k+2*e) (pin : k+e+1≤n) (enough : agreements n k ≤ n-e)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(n-e-1-(k-1)) → (i:F)≠0) :
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

/-- On every injective prime-field domain the exact probability curve requires
only the length, rate and agreement window. This includes fields just above the length. -/
theorem prime_mass {p n k e : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (hk : 2 ≤ k) (rate : 3*k ≤ n) (large : 65536 ≤ n) (pack : n ≤ k+2*e)
    (pin : k+e+1 ≤ n) (safe : agreements n k ≤ n-e) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    epsMCA (F:=ZMod p) C ((e:ℝ≥0)/n) = ((min p (2*(e+1)):ℕ):ℝ≥0∞)/p := by
  dsimp only
  rw [epsMCA_interleaved_eq]
  have population := exact_mass x hk rate large pack pin safe (by
    have fieldRoom : n ≤ p := by simpa using Fintype.card_le_of_injective _ x.injective
    intro i hi bound zero
    have divides := Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod p) p i).mp zero)
    omega)
  simpa only [ZMod.card] using population

/-- The first failing grid point at tolerance 1/Q, and the full real good interval. -/
theorem classification {n k Q j : ℕ} [NeZero n] (x : Fin n ↪ F) (Qbig : 2≤Q)
    (index : j=Fintype.card F/Q/2) (hk : 2≤k) (rate : 3*k≤n) (large : 65536 ≤ n)
    (pack : n≤k+2*j) (pin : k+j+1≤n) (prev : agreements n k ≤ n-j+1)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(n-j-(k-1)) → (i:F)≠0) (width : ℕ) [NeZero width] :
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
    (by omega) (by omega) (by simp [agreements,margin,show 11*n ≤ 54*(60*m) by omega];omega) width
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

section Fermat
local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- In the Fermat prime field, even a domain missing only one field element
has the exact two-head mass on 1,093 consecutive error counts. -/
theorem fermat_mass (x : Fin 65536 ↪ ZMod 65537) {e : ℕ} (lo : 22938 ≤ e) (hi : e ≤ 24030)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x 19660 : Set (Fin 65536 → ZMod 65537)) ^⋈ (Fin width)
    epsMCA (F:=ZMod 65537) C ((e:ℝ≥0)/65536) = ((2*(e+1):ℕ):ℝ≥0∞)/65537 := by
  have cut : agreements 65536 19660=41506 := by decide
  have result := prime_mass (k:=19660) (e:=e) x (by decide) (by decide) (by decide)
    (by omega) (by omega) (by omega) width
  simpa only [min_eq_right (by omega : 2*(e+1) ≤ 65537),Nat.cast_ofNat] using result
end Fermat

end ProximityGap.DoubleQuadraticThreshold
#print axioms ProximityGap.DoubleQuadraticThreshold.exact_mass
#print axioms ProximityGap.DoubleQuadraticThreshold.classification
#print axioms ProximityGap.DoubleQuadraticThreshold.three_tenths
#print axioms ProximityGap.DoubleQuadraticThreshold.prime_classification
#print axioms ProximityGap.DoubleQuadraticThreshold.three_tenths_family
#print axioms ProximityGap.DoubleQuadraticThreshold.prime_mass
#print axioms ProximityGap.DoubleQuadraticThreshold.fermat_mass
