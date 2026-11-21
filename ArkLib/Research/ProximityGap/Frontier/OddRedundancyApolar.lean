/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarAllFieldPlateau
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA

/-! # The apolar count below half distance at odd redundancy

At the last step the denominator in the power-two count is exactly two.
This distinguishes the two residue classes of the half-distance parameter.
-/
set_option autoImplicit false
namespace ProximityGap.OddRedundancyApolar
open MCAThresholdLedger ArkLib.ProximityGap.Frontier
open HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F]

private theorem upper_of_count {n k h e B : ℕ} [NeZero n] (x : Fin n ↪ F)
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h)
    (error : e ≤ h-1) (cut : max (e+1) (2*(e/(2*h-2*e)+1)) ≤ B) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) ≤
      (B:ℝ≥0∞)/Fintype.card F := by
  classical
  apply epsMCA_le_of_badCount_le
  intro u
  let δ : ℝ≥0 := (e:ℝ≥0)/n
  let fam := canonicalBadScalarRichPointFamily x δ u (by omega : 1 ≤ k)
  change fam.G.card ≤ B
  have nonzero : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  have lim := SharpApolarMCA.family_bound_power 2 (by decide) (d:=2*h-2) (e:=e) fam fam.G
    Finset.Subset.rfl (by omega) (by omega) (by omega) (by rw [Fintype.card_fin];omega)
    (by dsimp [δ];rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ nonzero,
        ←Nat.cast_tsub,Nat.ceil_natCast])
    (by rw [Fintype.card_fin];omega)
  rw [show 2*h-2+2=2*h by omega] at lim
  exact lim.trans cut

/-- The spike reaches e+1 labels at every step up to and including h−1. -/
theorem spike_lower {n k h e : ℕ} [NeZero n] (x : Fin n ↪ F)
    (hk : 3 ≤ k) (length : n=k+2*h-1) (large : 4 ≤ h) (error : e ≤ h-1) :
    ((e+1:ℕ):ℝ≥0∞)/Fintype.card F ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) := by
  classical
  have nonzero : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [← BoundarySecurityBudget.rsCode_eq_code]
  let sites : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
  exact SpikeFloor.epsMCA_ge_j_div_card (j:=e+1) (SpikeFloor.rsCode x k)
    (SpikeFloor.rsCode_noWeightLE x (by omega))
    (by simp [Fintype.card_fin,div_mul_cancel₀ _ nonzero]) (by omega) (by rw [Fintype.card_fin];omega)
    sites (sites.trans x) (b:=(1:F)) one_ne_zero

/-- At every step through h−2 errors the spike is extremal on every injective
evaluation domain, in every finite field. -/
theorem preunique_mass {n k h e : ℕ} [NeZero n] (x : Fin n ↪ F)
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h) (error : e ≤ h-2) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) =
      ((e+1:ℕ):ℝ≥0∞)/Fintype.card F := by
  classical
  apply le_antisymm
  · by_cases zero : e=0
    · subst e
      rw [← BoundarySecurityBudget.rsCode_eq_code]
      exact SpikeFloor.epsMCA_le_j_div_card (j:=1) (SpikeFloor.rsCode x k)
        (SpikeFloor.rsCode_noWeightLE x (by omega)) (by simp)
    apply upper_of_count x hk rate length large (by omega)
    have bound := Nat.div_le_div_left (a:=e) (show 4 ≤ 2*h-2*e by omega) (by decide : 0 < 4)
    omega
  · exact spike_lower x hk length large (by omega)

/-- At h−1 errors the numerator is at most h when h is even and h+1 when h is odd. -/
theorem endpoint_upper {n k h : ℕ} [NeZero n] (x : Fin n ↪ F)
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (((h-1:ℕ):ℝ≥0)/n) ≤
      ((h+h%2:ℕ):ℝ≥0∞)/Fintype.card F := by
  apply upper_of_count x hk rate length large le_rfl
  rw [show 2*h-2*(h-1)=2 by omega]
  omega

/-- At the endpoint with even h the spike already supplies the exact probability. -/
theorem endpoint_even {n k h : ℕ} [NeZero n] (x : Fin n ↪ F)
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h) (even : h%2=0) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (((h-1:ℕ):ℝ≥0)/n) =
      (h:ℝ≥0∞)/Fintype.card F := by
  apply le_antisymm
  · simpa only [even,Nat.add_zero] using endpoint_upper x hk rate length large
  · simpa only [show h-1+1=h by omega] using spike_lower (e:=h-1) x hk length large le_rfl

/-- On any finite-field domain and at all positive widths, the first failing
index through the initial plateau is min(B,h), except possibly at B=h with odd h. -/
theorem classification {n k h B Q : ℕ} [NeZero n] (x : Fin n ↪ F)
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h)
    (security : 0 < Q) (budget : Fintype.card F/Q=B) (upper : B ≤ 2*h+1)
    (regular : B ≠ h ∨ h%2=0) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let r : ℝ≥0 := ((min B h:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  classical
  let C := (ReedSolomon.code x k : Set (Fin n → F))
  let j := min B h
  let r : ℝ≥0 := (j:ℝ≥0)/n
  have ratio (i : ℕ) : ((i:ℝ≥0∞)/Fintype.card F ≤ 1/(Q:ℝ≥0∞)) ↔ i ≤ B := by
    rw [← budget]
    exact BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos security
  have fail : 1/(Q:ℝ≥0∞) < epsMCA (F:=F) C r := by
    by_cases small : B<h
    · dsimp only [C,r,j]
      rw [min_eq_left small.le]
      apply lt_of_lt_of_le _ (spike_lower x hk length large (by omega : B ≤ h-1))
      exact lt_of_not_ge (fun safe => (by omega : ¬ B+1 ≤ B) ((ratio _).mp safe))
    · dsimp only [C,r,j]
      rw [min_eq_right (by omega : h ≤ B)]
      have two := TwoHeadLinearBudget.errors (e:=h) (k:=k) x
        (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega)
      rw [Fintype.card_fin] at two
      apply lt_of_lt_of_le _ two
      exact lt_of_not_ge (fun safe => (by omega : ¬ 2*(h+1) ≤ B) ((ratio _).mp safe))
  have result : mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞)) = r := by
    by_cases zero : j=0
    · exact le_antisymm (mcaDeltaStar_le_of_bad C _ fail) (by simp [r,zero])
    refine MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad (a:=j)
      (by omega) (by dsimp [j];omega) C _ ?_ fail
    dsimp only [C]
    by_cases below : j<h
    · have safe := preunique_mass (e:=j-1) x hk rate length large (by omega)
      apply safe.le.trans ((ratio _).mpr ?_)
      dsimp [j] at zero ⊢
      omega
    · have atH : j=h := le_antisymm (min_le_right ..) (by omega)
      rw [atH]
      exact (endpoint_upper x hk rate length large).trans ((ratio _).mpr (by dsimp [j] at atH;omega))
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

/-- Any construction producing h+1 labels at the odd-redundancy predecessor
certifies the full real cutoff at the budget equal to h. -/
theorem exceptional_of_lower {n k h Q : ℕ} [NeZero n] (x : Fin n ↪ F)
    (hk : 3 ≤ k) (rate : 3*k ≤ n) (length : n=k+2*h-1) (large : 4 ≤ h)
    (security : 0 < Q) (budget : Fintype.card F/Q=h)
    (lower : ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n)) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let r := ((h-1:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<r := by
  classical
  let C := (ReedSolomon.code x k : Set (Fin n → F))
  let j := h-1
  have ratio (m : ℕ) : ((m:ℝ≥0∞)/Fintype.card F ≤ 1/(Q:ℝ≥0∞)) ↔ m ≤ h := by
    rw [← budget]
    exact BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos security
  have bad : 1/(Q:ℝ≥0∞) < epsMCA (F:=F) C ((j:ℝ≥0)/n) := by
    exact lt_of_lt_of_le (lt_of_not_ge (fun safe => (by omega : ¬ h+1 ≤ h) ((ratio _).mp safe))) lower
  have result := MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
    (a:=j) (by dsimp [j];omega) (by dsimp [j];omega) C (1/(Q:ℝ≥0∞)) (by
      have prev := preunique_mass (e:=j-1) x hk rate length large (by dsimp [j];omega)
      exact prev.le.trans ((ratio _).mpr (by dsimp [j];omega))) bad
  dsimp only
  rw [mcaDeltaStar_interleaved_eq]
  refine ⟨result,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro safe
    by_contra! outside
    exact bad.not_ge ((epsMCA_mono C outside).trans safe)
  · intro below
    by_contra! failed
    have bound := mcaDeltaStar_le_of_bad C _ failed
    rw [result] at bound
    exact below.not_ge bound

end ProximityGap.OddRedundancyApolar
#print axioms ProximityGap.OddRedundancyApolar.preunique_mass
#print axioms ProximityGap.OddRedundancyApolar.endpoint_upper
#print axioms ProximityGap.OddRedundancyApolar.endpoint_even
#print axioms ProximityGap.OddRedundancyApolar.classification
#print axioms ProximityGap.OddRedundancyApolar.exceptional_of_lower
