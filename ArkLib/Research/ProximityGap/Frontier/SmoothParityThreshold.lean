/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.OddSmoothPrimeThreshold
import ArkLib.Research.ProximityGap.Frontier.ApolarPowerBound

/-! # A single finite prime-field threshold for both redundancy parities

On smooth even lengths the exceptional budget is present exactly when the
redundancy is one modulo four. The grid probability and the entire real safe
interval are explicit at every dimension from two through one third of the length.
-/
set_option autoImplicit false
namespace ProximityGap.SmoothParityThreshold
open MCAThresholdLedger ArkLib.ProximityGap.Frontier
open HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

/-- The rounded-up half redundancy specifies the first two-head error count. -/
def halfDistance (n k : ℕ) := (n-k+1)/2

/-- The first failure is one step earlier at the exceptional budget. -/
def firstFailure (n k B : ℕ) :=
  let h := halfDistance n k
  if (n-k)%2=1 then OddSmoothPrimeThreshold.index B h else ThreeRegimePrimeThreshold.index B h

/-- The worst-pair numerator at each error grid point in the certified window. -/
def numerator (p n k e : ℕ) :=
  let h := halfDistance n k
  if e<h then e+1+(if (n-k)%2=1 ∧ e+1=h then h%2 else 0) else min p (2*(e+1))

private theorem even_interior {F : Type} [Field F] [Fintype F] {n k h e : ℕ} [NeZero n]
    (x : Fin n ↪ F) (hk : 2 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h) (low : e<h) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) =
      ((e+1:ℕ):ℝ≥0∞)/Fintype.card F := by
  classical
  have nz : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le
    intro u
    let fam := canonicalBadScalarRichPointFamily x ((e:ℝ≥0)/n) u (by omega : 1 ≤ k)
    exact ApolarPowerBound.lower_rate_interior_family fam (Fintype.card_fin _) length (by omega)
      low (by omega) (by rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ nz,←Nat.cast_tsub,Nat.ceil_natCast])
  · rw [← BoundarySecurityBudget.rsCode_eq_code]
    let sites : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
    exact SpikeFloor.epsMCA_ge_j_div_card (j:=e+1) (SpikeFloor.rsCode x k)
      (SpikeFloor.rsCode_noWeightLE x (by omega))
      (by simp [Fintype.card_fin,div_mul_cancel₀ _ nz]) (by omega) (by rw [Fintype.card_fin];omega)
      sites (sites.trans x) (b:=(1:F)) one_ne_zero

/-- The exact probability at every Hamming step in the certified window.
There is no parity or field-size hypothesis on the dimension or the prime. -/
theorem mass {p n k e : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p) [ReedSolomon.Smooth x]
    (large : 65536 ≤ n) (hk : 2 ≤ k) (rate : 3*k ≤ n) (even : n%2=0)
    (enough : e+DoubleQuadraticThreshold.agreements n k ≤ n) (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      (numerator p n k e:ℝ≥0∞)/p := by
  let h := halfDistance n k
  have hh : h=(n-k+1)/2 := rfl
  by_cases odd : (n-k)%2=1
  · have r := OddSmoothPrimeThreshold.mass (h:=h) x large (by omega : 3 ≤ k) rate (by omega) even enough width
    have eq : numerator p n k e = (if e+1<h then e+1 else if e<h then h+h%2 else min p (2*(e+1))) := by
      change (if e<h then e+1+(if (n-k)%2=1 ∧ e+1=h then h%2 else 0) else _) = _
      split_ifs <;> omega
    rwa [eq]
  · by_cases low : e<h
    · rw [epsMCA_interleaved_eq]
      have eq : numerator p n k e=e+1 := by simp [numerator,odd,show e<halfDistance n k from low]
      rw [eq]
      simpa only [ZMod.card] using even_interior x hk rate (by omega : n=k+2*h) low
    · have eq : numerator p n k e=min p (2*(e+1)) := by simp [numerator,show ¬ e<halfDistance n k from low]
      rw [eq]
      have cap := enough
      have margin := DoubleQuadraticThreshold.margin_le_five n k
      unfold DoubleQuadraticThreshold.agreements at cap
      exact DoubleQuadraticThreshold.prime_mass x hk rate large (by omega) (by omega) (by omega) width

private theorem even_plateau {p n k h B Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (hk : 2 ≤ k) (rate : 3*k ≤ n) (len : n=k+2*h) (two : 2 ≤ Q) (budget : p/Q=B)
    (upper : B ≤ 2*h+1) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let r : ℝ≥0 := ((min B h:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=ZMod p) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  let C := (ReedSolomon.code x k : Set (Fin n → ZMod p))
  let j := min B h
  let r : ℝ≥0 := (j:ℝ≥0)/n
  have ratio (i : ℕ) : ((i:ℝ≥0∞)/Fintype.card (ZMod p) ≤ 1/(Q:ℝ≥0∞)) ↔ i ≤ B := by
    rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega : 0<Q),ZMod.card,budget]
  have fail : 1/(Q:ℝ≥0∞) < epsMCA (F:=ZMod p) C r := by
    by_cases small : B<h
    · dsimp only [C,r,j]
      rw [min_eq_left small.le,even_interior x hk rate len small]
      exact lt_of_not_ge (fun safe => (by omega : ¬ B+1 ≤ B) ((ratio _).mp safe))
    · dsimp only [C,r,j]
      rw [min_eq_right (by omega : h ≤ B)]
      have attack := TwoHeadLinearBudget.errors (e:=h) (k:=k) x
        (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega)
      rw [Fintype.card_fin] at attack
      apply lt_of_lt_of_le _ attack
      exact lt_of_not_ge (fun safe => (by omega : ¬ 2*(h+1) ≤ B) ((ratio _).mp safe))
  have result : mcaDeltaStar (F:=ZMod p) C (1/(Q:ℝ≥0∞)) = r := by
    by_cases zero : j=0
    · exact le_antisymm (mcaDeltaStar_le_of_bad C _ fail) (by simp [r,zero])
    refine MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad (a:=j)
      (by omega) (by dsimp [j];omega) C _ ?_ fail
    have safe := even_interior (e:=j-1) x hk rate len (by dsimp [j];omega)
    exact safe.le.trans ((ratio _).mpr (by dsimp [j];omega))
  dsimp only
  rw [mcaDeltaStar_interleaved_eq]
  refine ⟨result,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro safe
    by_contra! outside
    exact fail.not_ge ((epsMCA_mono C outside).trans safe)
  · intro below
    by_contra! fails
    have bound := mcaDeltaStar_le_of_bad C _ fails
    rw [result] at bound
    exact below.not_ge bound

/-- The complete real good interval on every even smooth prime-field domain.
One formula covers both parities and includes dimension exactly n/3. -/
theorem classification {p n k B Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    [ReedSolomon.Smooth x] (large : 65536 ≤ n) (hk : 2 ≤ k) (rate : 3*k ≤ n) (even : n%2=0)
    (two : 2 ≤ Q) (budget : p/Q=B) (ceiling : B/2+DoubleQuadraticThreshold.agreements n k ≤ n+1)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → ZMod p)) ^⋈ (Fin width)
    let r := ((firstFailure n k B:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=ZMod p) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  let h := halfDistance n k
  have hh : h=(n-k+1)/2 := rfl
  by_cases odd : (n-k)%2=1
  · rw [firstFailure,ite_eq_left odd]
    exact OddSmoothPrimeThreshold.classification (h:=h) x large (by omega) rate
      (by omega) even two budget ceiling width
  rw [firstFailure,ite_eq_right odd]
  by_cases low : B ≤ 2*h+1
  · have ix : ThreeRegimePrimeThreshold.index B h=min B h := by unfold ThreeRegimePrimeThreshold.index;omega
    change mcaDeltaStar _ _ = ((ThreeRegimePrimeThreshold.index B h:ℕ):ℝ≥0)/n ∧ _
    rw [ix]
    exact even_plateau x hk rate (by omega : n=k+2*h) two budget low width
  · have ix : ThreeRegimePrimeThreshold.index B h=B/2 := by unfold ThreeRegimePrimeThreshold.index;omega
    change mcaDeltaStar _ _ = ((ThreeRegimePrimeThreshold.index B h:ℕ):ℝ≥0)/n ∧ _
    rw [ix]
    have cap := ceiling
    have margin := DoubleQuadraticThreshold.margin_le_five n k
    unfold DoubleQuadraticThreshold.agreements at cap
    exact DoubleQuadraticThreshold.prime_classification x two (by rw [budget]) hk rate large
      (by omega) (by omega) (by omega) width

end ProximityGap.SmoothParityThreshold
#print axioms ProximityGap.SmoothParityThreshold.mass
#print axioms ProximityGap.SmoothParityThreshold.classification
