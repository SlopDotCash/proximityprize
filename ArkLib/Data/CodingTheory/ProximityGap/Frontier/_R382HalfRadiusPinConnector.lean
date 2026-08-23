/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveProperQuotientBall
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveWorstCaseIncidence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PackingBudgetFirstJump

/-!
# R382: the exact half-radius projective pin connector

R383 refutes the unrestricted R382 half-radius MDS-line conjecture at rate `1/2` with nine
proper points on an `[8,4]` syndrome line.  The production-rate remnant `k <= n/4` is not
refuted by that example.  Any surviving half-radius bound must control the *proper* quotient ball,
not only ordinary ball incidence on pencils which are jointly far.  MCA properness is local to the
witness support: a pencil may lie in one support subspace and still have bad slots witnessed by
other support subspaces.  This file makes that distinction exact.

`properIncidenceBounded_iff_far_and_close` splits the required bound into the ordinary R382
far-line statement and the residual bound on jointly-close pencils.  The latter does not follow
from the former by definition.  `evalCode_deltaStar_eq_half_of_r382ProperBound` proves the full
operational payoff: at a tight field-normalized budget, a rank-two proper-incidence bound `<= n`
at the lattice predecessor of `1/2` combines with the overlap-packing ceiling to pin
`mcaDeltaStar = 1/2` exactly for every rate-at-most-`1/4` smooth Reed--Solomon instance.

The syndrome--Kronecker route has a separate structural limit: at the half predecessor its
generic locator-kernel nullity is `k-1`, so the one-corank split-fibre theorem applies directly
only at `k=2`.  The arithmetic statement is recorded below.  Finally, the local line-core identity
used by the new rate-`1/16` rich-point manuscript is formalized as
`affineAgreementSet_inter_eq_jointCore`; the global rich-line/third-moment theorem remains open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap Code ProximityGap.MCAThresholdLedger
open ProximityGap.MCAProjectiveEquivariance
open ProximityGap.ProjectiveQuotientSupport
open ProximityGap.ProjectiveQuotientBall
open ProximityGap.ProjectiveProperQuotientBall
open ProximityGap.ProjectiveWorstCaseIncidence
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PackingBudgetFirstJump

namespace ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The normalized lattice point immediately below `1/2` at even length `n`. -/
noncomputable def halfPredecessorRadius (n : ℕ) : ℝ≥0 :=
  ((n / 2 - 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)

/-! ## The syndrome-pencil corank audit -/

/-- At the half predecessor `h=n/2-1`, the Hankel syndrome pencil has `D-h` rows and
`h+1` locator columns, hence generic right nullity `k-1` when `D=n-k`. -/
theorem halfSyndromePencil_nullity
    {n k : ℕ} (hnEven : n % 2 = 0) (hk : 2 ≤ k) (hkhalf : k ≤ n / 2 - 1) :
    let h := n / 2 - 1
    let D := n - k
    (h + 1) - (D - h) = k - 1 := by
  dsimp only
  omega

/-- Consequently, under the nontrivial coding hypotheses, the direct one-corank branch is
equivalent to dimension `k=2`. -/
theorem halfSyndromePencil_oneCorank_iff
    {n k : ℕ} (hnEven : n % 2 = 0) (hk : 2 ≤ k) (hkhalf : k ≤ n / 2 - 1) :
    (let h := n / 2 - 1
     let D := n - k
     (h + 1) - (D - h) = 1) ↔ k = 2 := by
  dsimp only
  rw [halfSyndromePencil_nullity hnEven hk hkhalf]
  omega

/-! ## The first rate-sixteenth rich-point lemma -/

/-- Agreement with the polynomial line `a + gamma*r` at the received-word slot
`u0 + gamma*u1`. -/
def affineAgreementSet
    (u₀ u₁ a r : ι → F) (γ : F) : Finset ι :=
  Finset.univ.filter fun i => u₀ i + γ * u₁ i = a i + γ * r i

/-- The coordinates on which the two received rows are jointly represented by the polynomial
line `(a,r)`. -/
def affineJointCore (u₀ u₁ a r : ι → F) : Finset ι :=
  Finset.univ.filter fun i => u₀ i = a i ∧ u₁ i = r i

/-- **Line-core identity.** Agreement sets at two distinct parameters on the same polynomial
line intersect exactly in the joint core.  This is equation (L1) of the rate-`1/16` rich-point
argument. -/
theorem affineAgreementSet_inter_eq_jointCore
    (u₀ u₁ a r : ι → F) {γ β : F} (hγβ : γ ≠ β) :
    affineAgreementSet u₀ u₁ a r γ ∩ affineAgreementSet u₀ u₁ a r β =
      affineJointCore u₀ u₁ a r := by
  ext i
  simp only [affineAgreementSet, affineJointCore, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hγ, hβ⟩
    have hdiff : (γ - β) * (u₁ i - r i) = 0 := by
      linear_combination hγ - hβ
    have hγβ0 : γ - β ≠ 0 := sub_ne_zero.mpr hγβ
    have hdir : u₁ i = r i := sub_eq_zero.mp
      ((mul_eq_zero.mp hdiff).resolve_left hγβ0)
    have hbase : u₀ i = a i := by simpa [hdir] using hγ
    exact ⟨hbase, hdir⟩
  · rintro ⟨hbase, hdir⟩
    simp [hbase, hdir]

/-- The non-core parts of distinct agreement fibres on a polynomial line are pairwise disjoint.
This is the counting input immediately following the line-core identity. -/
theorem affineAgreementSet_sdiff_jointCore_disjoint
    (u₀ u₁ a r : ι → F) {γ β : F} (hγβ : γ ≠ β) :
    Disjoint
      (affineAgreementSet u₀ u₁ a r γ \ affineJointCore u₀ u₁ a r)
      (affineAgreementSet u₀ u₁ a r β \ affineJointCore u₀ u₁ a r) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  have hiγ := (Finset.mem_sdiff.mp hi).1
  have hiβ := (Finset.mem_sdiff.mp hj).1
  have hicore : i ∈ affineJointCore u₀ u₁ a r := by
    rw [← affineAgreementSet_inter_eq_jointCore u₀ u₁ a r hγβ]
    exact Finset.mem_inter.mpr ⟨hiγ, hiβ⟩
  exact (Finset.mem_sdiff.mp hi).2 hicore

/-- The exact all-pencil incidence predicate seen by MCA after retaining support-local
properness. -/
def ProperProjectiveIncidenceBounded
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    properProjectiveBallIncidence C δ (u 0) (u 1) ≤ E

/-- The ordinary quotient-ball bound on pencils which are jointly far.  This is the direct
formal version of the far-line reading of the R382 MDS-line conjecture. -/
def FarProjectiveBallIncidenceBounded
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    PencilJointFar C δ (quotientPencil C (u 0) (u 1)) →
      projectiveBallIncidence C δ (u 0) (u 1) ≤ E

/-- The branch not covered by a far-line-only theorem: proper incidence for pencils contained
in at least one admissible support subspace. -/
def CloseProperProjectiveIncidenceBounded
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    ¬ PencilJointFar C δ (quotientPencil C (u 0) (u 1)) →
      properProjectiveBallIncidence C δ (u 0) (u 1) ≤ E

/-- Proper-ball incidence is exactly the projective MCA census, for every pencil and without a
joint-farness hypothesis. -/
theorem properIncidenceBounded_iff_projectiveWorstCase
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) :
    ProperProjectiveIncidenceBounded C δ E ↔
      ProjectiveWorstCaseIncidenceBounded C δ E := by
  constructor
  · intro h u
    rw [badSlotCount_eq_properProjectiveBallIncidence]
    exact h u
  · intro h u
    rw [← badSlotCount_eq_properProjectiveBallIncidence]
    exact h u

/-- **Exact obstruction to the far-line-only R382 route.**  The full proper-incidence target is
equivalent to the conjunction of the ordinary bound on jointly-far pencils and a separate proper
bound on jointly-close pencils. -/
theorem properIncidenceBounded_iff_far_and_close
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) :
    ProperProjectiveIncidenceBounded C δ E ↔
      FarProjectiveBallIncidenceBounded C δ E ∧
        CloseProperProjectiveIncidenceBounded C δ E := by
  constructor
  · intro h
    constructor
    · intro u hfar
      rw [← properProjectiveBallIncidence_eq_projectiveBallIncidence_of_pencilJointFar
        C δ (u 0) (u 1) hfar]
      exact h u
    · intro u _hclose
      exact h u
  · rintro ⟨hfar, hclose⟩ u
    by_cases hP : PencilJointFar C δ (quotientPencil C (u 0) (u 1))
    · rw [properProjectiveBallIncidence_eq_projectiveBallIncidence_of_pencilJointFar
        C δ (u 0) (u 1) hP]
      exact hfar u hP
    · exact hclose u hP

/-- Proper projective incidence is always bounded by ordinary projective quotient-ball
incidence.  Consequently, an ordinary-ball theorem for *all* rank-two lines would be stronger
than the exact MCA target; the gap only appears when the ordinary theorem is restricted to
jointly-far lines. -/
theorem properProjectiveBallIncidence_le_projectiveBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    properProjectiveBallIncidence C δ u₀ u₁ ≤
      projectiveBallIncidence C δ u₀ u₁ := by
  classical
  unfold properProjectiveBallIncidence projectiveBallIncidence
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1,
    properQuotientBall_subset_quotientSyndromeBall C δ (quotientPencil C u₀ u₁) hs.2⟩

/-- For budgets at least one, the proper-incidence target only needs genuine rank-two quotient
pencils. -/
theorem properIncidenceBounded_iff_rankTwo
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) (hE : 1 ≤ E) :
    ProperProjectiveIncidenceBounded C δ E ↔
      ∀ u : WordStack A (Fin 2) ι,
        RowsIndependentModCode C (u 0) (u 1) →
          properProjectiveBallIncidence C δ (u 0) (u 1) ≤ E := by
  rw [properIncidenceBounded_iff_projectiveWorstCase,
    projectiveWorstCaseIncidenceBounded_iff_rankTwo C δ E hE]
  constructor
  · intro h u hu
    rw [← badSlotCount_eq_properProjectiveBallIncidence]
    exact h u hu
  · intro h u hu
    rw [badSlotCount_eq_properProjectiveBallIncidence]
    exact h u hu

/-- A uniform ordinary quotient-ball bound on every genuine rank-two pencil implies the exact
proper-incidence target. -/
theorem properIncidenceBounded_of_rankTwo_projectiveBallBound
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) (hE : 1 ≤ E)
    (hball : ∀ u : WordStack A (Fin 2) ι,
      RowsIndependentModCode C (u 0) (u 1) →
        projectiveBallIncidence C δ (u 0) (u 1) ≤ E) :
    ProperProjectiveIncidenceBounded C δ E := by
  apply (properIncidenceBounded_iff_rankTwo C δ E hE).2
  intro u hu
  exact le_trans
    (properProjectiveBallIncidence_le_projectiveBallIncidence C δ (u 0) (u 1))
    (hball u hu)

/-- A good half-radius predecessor fills the entire open interval below `1/2`, because `epsMCA`
depends only on `floor(delta*n)`. -/
theorem half_le_mcaDeltaStar_of_predecessor_good
    {n : ℕ} [NeZero n] (hnEven : n % 2 = 0) (hn2 : 2 ≤ n)
    (C : Set (Fin n → A)) (εstar : ℝ≥0∞)
    (hprev : epsMCA (F := F) (A := A) C (halfPredecessorRadius n) ≤ εstar) :
    (1 / 2 : ℝ≥0) ≤ mcaDeltaStar (F := F) (A := A) C εstar := by
  let w : ℕ := n / 2 - 1
  let δprev : ℝ≥0 := halfPredecessorRadius n
  have hnpos : 0 < n := by omega
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnHalf : n = 2 * (n / 2) := by omega
  have hw : w = n / 2 - 1 := rfl
  have hprev_mul : δprev * (n : ℝ≥0) = (w : ℝ≥0) := by
    dsimp only [δprev, halfPredecessorRadius, w]
    exact div_mul_cancel₀ _ hn0
  have hhalf_mul : (1 / 2 : ℝ≥0) * (n : ℝ≥0) = ((n / 2 : ℕ) : ℝ≥0) := by
    have hncast : (n : ℝ≥0) = 2 * ((n / 2 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnHalf
    rw [hncast]
    field_simp
  have hgood : ∀ δ : ℝ≥0, δ < (1 / 2 : ℝ≥0) →
      epsMCA (F := F) (A := A) C δ ≤ εstar := by
    intro δ hδ
    by_cases hle : δ ≤ δprev
    · exact le_trans (epsMCA_mono C hle) hprev
    · have hprevδ : δprev < δ := lt_of_not_ge hle
      have hlowerFloor : (w : ℝ≥0) ≤ δ * (n : ℝ≥0) := by
        have hm := mul_lt_mul_of_pos_right hprevδ (by positivity)
        rw [hprev_mul] at hm
        exact hm.le
      have hupperFloor : δ * (n : ℝ≥0) < ((n / 2 : ℕ) : ℝ≥0) := by
        have hm := mul_lt_mul_of_pos_right hδ (by positivity)
        rwa [hhalf_mul] at hm
      have hfloorδ : Nat.floor (δ * (Fintype.card (Fin n) : ℝ≥0)) = w := by
        rw [Fintype.card_fin, Nat.floor_eq_iff (zero_le _)]
        constructor
        · exact hlowerFloor
        · rw [hw]
          have hsucc : n / 2 - 1 + 1 = n / 2 := by omega
          have hcast : (((n / 2 - 1 : ℕ) : ℝ≥0) + 1) =
              ((n / 2 : ℕ) : ℝ≥0) := by
            exact_mod_cast hsucc
          rw [hcast]
          exact hupperFloor
      have hfloorPrev :
          Nat.floor (δprev * (Fintype.card (Fin n) : ℝ≥0)) = w := by
        rw [Fintype.card_fin, hprev_mul, Nat.floor_natCast]
      rw [ProximityGap.epsMCA_eq_of_floor_eq (F := F) (A := A) C
        (hfloorδ.trans hfloorPrev.symm)]
      exact hprev
  by_contra hnot
  rw [not_le] at hnot
  obtain ⟨δ, hstarδ, hδhalf⟩ := exists_between hnot
  have hδle := le_mcaDeltaStar_of_good (F := F) (A := A) C εstar
    (le_trans hδhalf.le (by norm_num)) (hgood δ hδhalf)
  exact (not_lt_of_ge hδle) hstarδ

/-- A proper projective bound at the half-radius predecessor plus any independently proved
`1/2` ceiling gives an exact operational pin. -/
theorem mcaDeltaStar_eq_half_of_proper_predecessor_and_upper
    {n E : ℕ} [NeZero n] (hnEven : n % 2 = 0) (hn2 : 2 ≤ n)
    (C : Submodule F (Fin n → A)) (εstar : ℝ≥0∞)
    (hEfield : E < Fintype.card F)
    (hproper : ProperProjectiveIncidenceBounded C (halfPredecessorRadius n) E)
    (hbudget : (E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hupper : mcaDeltaStar (F := F) (A := A) (C : Set (Fin n → A)) εstar ≤
      (1 / 2 : ℝ≥0)) :
    mcaDeltaStar (F := F) (A := A) (C : Set (Fin n → A)) εstar =
      (1 / 2 : ℝ≥0) := by
  have hprojective : ProjectiveWorstCaseIncidenceBounded C (halfPredecessorRadius n) E :=
    (properIncidenceBounded_iff_projectiveWorstCase C _ E).1 hproper
  have hprev : epsMCA (F := F) (A := A) (C : Set (Fin n → A))
      (halfPredecessorRadius n) ≤ εstar :=
    le_trans ((epsMCA_le_iff_projective C _ E hEfield).2 hprojective) hbudget
  exact le_antisymm hupper
    (half_le_mcaDeltaStar_of_predecessor_good hnEven hn2 (C : Set (Fin n → A)) εstar hprev)

open Classical in
/-- **R382 payoff.**  Suppose every genuine rank-two quotient pencil for the smooth
`[n,k]` Reed--Solomon code has proper half-predecessor incidence at most `n`.  At the tight
budget `floor(p/Q)=n`, overlap packing is already known to force the `1/2` ceiling, so the
operational threshold is exactly `1/2`.

This theorem exposes the precise remaining hypothesis.  A bound only on ordinary ball incidence
for jointly-far pencils must additionally discharge `CloseProperProjectiveIncidenceBounded`, as
shown by `properIncidenceBounded_iff_far_and_close`. -/
theorem evalCode_deltaStar_eq_half_of_r382ProperBound
    {p n k Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hQ : 0 < Q) (hk : 2 ≤ k) (hnEven : n % 2 = 0)
    (hfloor : p / Q = n) (hkquarter : k ≤ n / 4)
    (hsupply : 4 ≤ p - n)
    (hR382 :
      let dom := ProximityGap.KKH26RegimeSplit.powDomain g hg
        (ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
      let C : Submodule (ZMod p) (Fin n → ZMod p) := ReedSolomon.code dom k
      ∀ u : WordStack (ZMod p) (Fin 2) (Fin n),
        RowsIndependentModCode C (u 0) (u 1) →
          properProjectiveBallIncidence C (halfPredecessorRadius n) (u 0) (u 1) ≤ n) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
        ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) = (1 / 2 : ℝ≥0) := by
  have hg0 : g ≠ 0 := ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom : Fin n ↪ ZMod p := ProximityGap.KKH26RegimeSplit.powDomain g hg hg0
  let C : Submodule (ZMod p) (Fin n → ZMod p) := ReedSolomon.code dom k
  have hcode : evalCode g n (k - 1) = (C : Set (Fin n → ZMod p)) := by
    dsimp only [C, dom]
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon g hg hg0 (k - 1))
  have hproper : ProperProjectiveIncidenceBounded C (halfPredecessorRadius n) n := by
    apply (properIncidenceBounded_iff_rankTwo C _ n (by omega)).2
    simpa only [C, dom] using hR382
  have hnfield : n < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  have hbudget : ((n : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞) ≤
      ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
    rw [ZMod.card]
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact (Fact.out (p := p.Prime)).ne_zero
    rw [ENNReal.div_le_iff hp0 (ENNReal.natCast_ne_top _)]
    have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
    calc
      (n : ℝ≥0∞) = (n : ℝ≥0∞) * Q * (Q : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQtop, mul_one]
      _ ≤ (p : ℝ≥0∞) * (Q : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast (show n * Q ≤ p by
          have hmul := Nat.mul_div_le p Q
          simpa [hfloor, Nat.mul_comm] using hmul)
      _ = (Q : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := mul_comm _ _
  have hupper : mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (C : Set (Fin n → ZMod p)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0) := by
    rw [← hcode]
    exact mcaDeltaStar_le_half_of_floor_eq_length hg hQ hk hnEven hfloor hkquarter hsupply
  simpa [hcode] using
    (mcaDeltaStar_eq_half_of_proper_predecessor_and_upper hnEven (by omega) C
      ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) hnfield hproper hbudget hupper)

end ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms
  ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfSyndromePencil_oneCorank_iff
#print axioms
  ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.affineAgreementSet_inter_eq_jointCore
#print axioms
  ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.properIncidenceBounded_iff_far_and_close
#print axioms
  ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.half_le_mcaDeltaStar_of_predecessor_good
#print axioms
  ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.evalCode_deltaStar_eq_half_of_r382ProperBound
