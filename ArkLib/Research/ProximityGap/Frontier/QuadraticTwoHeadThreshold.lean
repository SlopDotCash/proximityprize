/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuadraticTwoHeadCount
import ArkLib.Research.ProximityGap.Frontier.UniversalTwoHeadBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA

/-! # Finite two-head probability curves from quadratic interpolation

The linear surplus inequality controls the exact bad count on a whole interval.
At rates one eighth and one sixteenth, a prime field containing the domain
automatically has the characteristic required by the quadratic argument.
-/
set_option autoImplicit false
namespace ProximityGap.QuadraticTwoHeadThreshold
open MCAThresholdLedger ArkLib.ProximityGap.Frontier ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The number of agreements required by the degree-34 quadratic interpolant. -/
def agreements (n k : ℕ) := (35*n+100*(k-1))/102+1

theorem upper {n k e : ℕ} [NeZero n] (x : Fin n ↪ F) (hk : 1≤k) (rate : 3*k≤n)
    (he : 2080<e) (en : e≤n) (enough : agreements n k ≤ n-e)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(agreements n k-1) → (i:F)≠0) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) ≤
      ((2*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F) := by
  classical
  apply epsMCA_le_of_badCount_le
  intro u
  let fam := HalfPredecessorBadEventRichPointBridge.canonicalBadScalarRichPointFamily x
    (k:=k) ((e:ℝ≥0)/n) u hk
  have grid : ⌈(1-(e:ℝ≥0)/n)*(Fintype.card (Fin n):ℝ≥0)⌉₊=n-e := by
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne n),
      ←Nat.cast_tsub,Nat.ceil_natCast]
  change fam.G.card ≤ 2*(e+1)
  have estimate := QuadraticTwoHeadCount.family_cap fam (Fintype.card_fin _) (Nat.add_sub_of_le en)
    hk rate he enough (show 35*n+100*(k-1)<102*agreements n k by unfold agreements;omega) grid hchar
  simpa only [Nat.mul_add,Nat.mul_one] using estimate

/-- The exact bad probability, including the case where the two heads exhaust the field. -/
theorem exact_mass {n k e : ℕ} [NeZero n] (x : Fin n ↪ F) (hk : 2≤k) (rate : 3*k≤n)
    (he : 2080<e) (pack : n≤k+2*e) (pin : k+e+1≤n) (enough : agreements n k ≤ n-e)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(agreements n k-1) → (i:F)≠0) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) =
      ((min (Fintype.card F) (2*(e+1)):ℕ):ℝ≥0∞)/(Fintype.card F) := by
  apply le_antisymm _ (by
    simpa only [Fintype.card_fin] using UniversalTwoHeadBudget.mass (e:=e) x hk
      (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin]))
  by_cases supply : 2*(e+1) ≤ Fintype.card F
  · rw [min_eq_right supply]
    exact upper x (by omega) rate he (by omega) enough hchar
  · rw [min_eq_left (by omega : Fintype.card F≤2*(e+1)),
      ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
    exact epsMCA_le_one _ _

/-- The first failing grid point at tolerance 1/Q, and the full real good interval. -/
theorem classification {n k Q j : ℕ} [NeZero n] (x : Fin n ↪ F) (Qbig : 2≤Q)
    (index : j=Fintype.card F/Q/2) (hk : 2≤k) (rate : 3*k≤n) (large : 2081<j)
    (pack : n≤k+2*j) (pin : k+j+1≤n) (prev : agreements n k ≤ n-j+1)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(agreements n k-1) → (i:F)≠0) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let ε := 1/(Q:ℝ≥0∞)
    let bound := (j:ℝ≥0)/n
    mcaDeltaStar (F:=F) C ε = bound ∧ ∀ δ, epsMCA (F:=F) C δ≤ε ↔ δ<bound := by
  dsimp only
  let C := (ReedSolomon.code x k : Set (Fin n → F))
  have good : epsMCA (F:=F) C (predecessorRadius n j) ≤ 1/(Q:ℝ≥0∞) := by
    apply (upper (e:=j-1) x (by omega) rate (by omega) (by omega) (by omega) hchar).trans
    rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega : 0<Q)]
    omega
  have bad : 1/(Q:ℝ≥0∞) < epsMCA (F:=F) C ((j:ℝ≥0)/n) := by
    have mass := UniversalTwoHeadBudget.mass (e:=j) x hk (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin])
    rw [Fintype.card_fin] at mass
    apply lt_of_lt_of_le _ mass
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega : 0<Q)]
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

/-- At rate at most one eighth, the injection alone implies the characteristic
condition for the full finite budget classification in prime fields. -/
theorem prime_low_rate {p n k Q j : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (Qbig : 2≤Q) (index : j=p/Q/2) (hk : 2≤k) (rate : 8*k≤n) (large : 2081<j)
    (pack : n≤k+2*j) (pin : k+j+1≤n) (prev : agreements n k ≤ n-j+1)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let ε := 1/(Q:ℝ≥0∞)
    let bound := (j:ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C ε = bound ∧ ∀ δ, epsMCA (F:=ZMod p) C δ≤ε ↔ δ<bound := by
  apply classification x Qbig (by simpa using index) hk (by omega) large pack pin prev _ width
  have fieldRoom : n≤p := by simpa using Fintype.card_le_of_injective _ x.injective
  intro i hi bound eq
  have divides := Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod p) p i).mp eq)
  unfold agreements at bound
  omega

/-- The complete rate-one-eighth crossing at length 2^30 throughout a finite
128-bit budget interval. The predecessor and the first failure are uniform
over every domain and every positive interleaving width. -/
theorem production_eighth {p B : ℕ} [Fact p.Prime] (x : Fin 1073741824 ↪ ZMod p)
    (budget : p/2^128=B) (lower : 939524096≤B) (upper : B≤1147429993)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x 134217728 : Set (Fin 1073741824 → ZMod p)) ^⋈ (Fin width)
    let bound := ((B/2:ℕ):ℝ≥0)/1073741824
    mcaDeltaStar (F:=ZMod p) C (1/2^128) = bound ∧
      ∀ δ, epsMCA (F:=ZMod p) C δ≤1/2^128 ↔ δ<bound := by
  have endpoint : agreements 1073741824 134217728 = 500026829 := by decide
  have result := prime_low_rate (Q:=2^128) (j:=B/2) (k:=134217728) x
    (by decide) (by rw [budget]) (by decide) (by decide) (by omega)
    (by omega) (by omega) (by omega) width
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using result

/-- For every prime with 128-bit scalar budget B at least 65536, choosing
n = 16 floor(B/17) gives an exact rate-one-eighth threshold on every
embedding. The normalized threshold tends to 17/32 as the prime grows. -/
theorem eighth_family {p B n : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (budget : p/2^128=B) (large : 65536≤B) (length : n=16*(B/17))
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x (n/8) : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let bound := ((B/2:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/2^128) = bound ∧
      ∀ δ, epsMCA (F:=ZMod p) C δ≤1/2^128 ↔ δ<bound := by
  have result := prime_low_rate (Q:=2^128) (j:=B/2) (k:=n/8) x
    (by decide) (by rw [budget]) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by unfold agreements; omega) width
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using result

end ProximityGap.QuadraticTwoHeadThreshold
#print axioms ProximityGap.QuadraticTwoHeadThreshold.exact_mass
#print axioms ProximityGap.QuadraticTwoHeadThreshold.classification
#print axioms ProximityGap.QuadraticTwoHeadThreshold.prime_low_rate

#print axioms ProximityGap.QuadraticTwoHeadThreshold.production_eighth
#print axioms ProximityGap.QuadraticTwoHeadThreshold.eighth_family
