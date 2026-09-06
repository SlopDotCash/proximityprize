/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #407 frontier: saturated-incidence threshold interface

This scratch lane records the strongest honest #407 survivor after the current
propose/refute loop.

The prize threshold can be attacked through the integer agreement parameter
`w = #(agreement coordinates)`, where `δ = 1 - w/n`.  The live R4-style claim is
not the refuted uniform `O(1)` coset-rigidity statement.  The corrected version is:

* there is a finite, characteristic-zero saturated incidence profile `I∞ w`;
* in the non-saturated prize regime the actual worst far-line incidence at
  agreement `w` is equal to `I∞ w`;
* hence the operational threshold is exactly the inverse profile
  `sup {w : I∞ w ≤ n}`.

This file proves only the deterministic threshold plumbing around that statement.
The mathematical content remains the equality between the actual incidence profile
and the saturated profile.  That equality is the current open core, equivalent in
the other faces to the thin-subgroup Gauss-period sup-norm bound.

No theorem in this file claims the prize is solved.
-/

namespace ProximityGap.Frontier.Issue407

open Finset

/-- A finite agreement-index profile.  `profile w` is the worst incidence count at
agreement size `w`; a radius is good when this count is at most the bad-scalar
budget. -/
abbrev IncidenceProfile := ℕ → ℕ

/-- Agreement index `w` is good at budget `B` for profile `I`. -/
def GoodAgreement (I : IncidenceProfile) (B w : ℕ) : Prop :=
  I w ≤ B

/-- Finite search range for agreement indices. -/
def agreementRange (W : ℕ) : Finset ℕ :=
  range (W + 1)

/-- Convert an integer agreement level `w` on a block of length `n` into the
corresponding relative radius `δ = 1 - w/n`. This is the bridge from the finite
profile formulation back to the `δ*` language of the prize statement. -/
noncomputable def agreementRadius (n w : ℕ) : ℝ :=
  1 - (w : ℝ) / (n : ℝ)

/-- Agreement radii lie in `[0,1]` for in-range agreement levels. -/
theorem agreementRadius_mem_unit {n w : ℕ} (hn : 0 < n) (hw : w ≤ n) :
    0 ≤ agreementRadius n w ∧ agreementRadius n w ≤ 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwR : (w : ℝ) ≤ (n : ℝ) := by exact_mod_cast hw
  unfold agreementRadius
  constructor
  · have hdiv : (w : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact hwR
    linarith
  · have hdiv_nonneg : (0 : ℝ) ≤ (w : ℝ) / (n : ℝ) := by positivity
    linarith

/-- Larger agreement means smaller radius. -/
theorem agreementRadius_strictAnti {n w₁ w₂ : ℕ} (hn : 0 < n) (hw : w₁ < w₂) :
    agreementRadius n w₂ < agreementRadius n w₁ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwR : (w₁ : ℝ) < (w₂ : ℝ) := by exact_mod_cast hw
  have hdiv : (w₁ : ℝ) / (n : ℝ) < (w₂ : ℝ) / (n : ℝ) :=
    div_lt_div_of_pos_right hwR hnR
  unfold agreementRadius
  linarith

/-- Non-strict version: larger agreement cannot increase the radius. -/
theorem agreementRadius_antitone {n w₁ w₂ : ℕ} (hn : 0 < n) (hw : w₁ ≤ w₂) :
    agreementRadius n w₂ ≤ agreementRadius n w₁ := by
  rcases lt_or_eq_of_le hw with hlt | heq
  · exact le_of_lt (agreementRadius_strictAnti hn hlt)
  · subst heq
    rfl

/-- Candidate good agreement indices in the finite range `0..W`. -/
noncomputable def goodAgreementSet (I : IncidenceProfile) (B W : ℕ) : Finset ℕ := by
  classical
  exact (agreementRange W).filter fun w => GoodAgreement I B w

/-- The profile `Iinf` is saturated for the actual profile `I` through agreement
level `W`.  This is the closed finite equality that probes try to verify or refute. -/
def SaturatedThrough (I Iinf : IncidenceProfile) (W : ℕ) : Prop :=
  ∀ w, w ≤ W → I w = Iinf w

/-- If the actual and saturated profiles agree through `W`, then they have the
same good agreement indices through `W`. -/
theorem goodAgreementSet_eq_of_saturatedThrough {I Iinf : IncidenceProfile} {B W : ℕ}
    (hsat : SaturatedThrough I Iinf W) :
    goodAgreementSet I B W = goodAgreementSet Iinf B W := by
  classical
  apply Finset.ext
  intro w
  by_cases hw : w ≤ W
  · simp [goodAgreementSet, agreementRange, GoodAgreement, hsat w hw]
  · have hnot : w ∉ agreementRange W := by
      simp [agreementRange, hw]
    simp [goodAgreementSet, hnot]

/-- Pointwise refutation hook: a single in-range disagreement refutes saturation. -/
theorem not_saturatedThrough_of_profile_ne {I Iinf : IncidenceProfile} {W w : ℕ}
    (hw : w ≤ W) (hne : I w ≠ Iinf w) :
    ¬ SaturatedThrough I Iinf W := by
  intro hsat
  exact hne (hsat w hw)

/-- Budget refutation hook: if a candidate saturated profile says a level is good
but the actual profile exceeds the budget, then saturation through that level is false. -/
theorem not_saturatedThrough_of_false_good {I Iinf : IncidenceProfile} {B W w : ℕ}
    (hw : w ≤ W) (hinf : Iinf w ≤ B) (hactual : B < I w) :
    ¬ SaturatedThrough I Iinf W := by
  intro hsat
  have : I w ≤ B := by simpa [hsat w hw] using hinf
  exact not_lt_of_ge this hactual

/-- A finite closed threshold statement for a saturated profile.  This is the
integer version of "`δ*` is the inverse saturated-incidence profile".  It says:
`wStar` is good, and every larger in-range agreement size is bad. -/
def IsSaturatedThreshold (Iinf : IncidenceProfile) (B W wStar : ℕ) : Prop :=
  wStar ≤ W ∧ Iinf wStar ≤ B ∧ ∀ w, w ≤ W → wStar < w → B < Iinf w

/--
`wStar` is the largest good agreement level through `W`.

This is the operational inverse-profile form: agreement levels are good exactly while the incidence
count is within the bad-scalar budget, and `wStar` is the maximal in-window level satisfying that
budget.
-/
def IsMaxGoodAgreement (I : IncidenceProfile) (B W wStar : ℕ) : Prop :=
  wStar ≤ W ∧ I wStar ≤ B ∧ ∀ w, w ≤ W → I w ≤ B → w ≤ wStar

/-- The saturated-threshold certificate is equivalent to saying that `wStar` is the largest
good agreement level through the finite window. -/
theorem isSaturatedThreshold_iff_isMaxGoodAgreement
    {I : IncidenceProfile} {B W wStar : ℕ} :
    IsSaturatedThreshold I B W wStar ↔ IsMaxGoodAgreement I B W wStar := by
  constructor
  · intro hthr
    refine ⟨hthr.1, hthr.2.1, ?_⟩
    intro w hw hgood
    by_contra hnot
    have hlt : wStar < w := Nat.lt_of_not_ge hnot
    exact not_lt_of_ge hgood (hthr.2.2 w hw hlt)
  · intro hmax
    refine ⟨hmax.1, hmax.2.1, ?_⟩
    intro w hw hlt
    by_contra hnot
    have hgood : I w ≤ B := Nat.le_of_not_gt hnot
    have hwle : w ≤ wStar := hmax.2.2 w hw hgood
    exact not_lt_of_ge hwle hlt

/-- A maximal-good certificate can be used wherever the saturated-threshold certificate is
expected. -/
theorem saturatedThreshold_of_isMaxGoodAgreement
    {I : IncidenceProfile} {B W wStar : ℕ}
    (hmax : IsMaxGoodAgreement I B W wStar) :
    IsSaturatedThreshold I B W wStar :=
  isSaturatedThreshold_iff_isMaxGoodAgreement.2 hmax

/-- A saturated-threshold certificate gives the maximal-good inverse-profile formulation. -/
theorem isMaxGoodAgreement_of_saturatedThreshold
    {I : IncidenceProfile} {B W wStar : ℕ}
    (hthr : IsSaturatedThreshold I B W wStar) :
    IsMaxGoodAgreement I B W wStar :=
  isSaturatedThreshold_iff_isMaxGoodAgreement.1 hthr

/-- The same finite threshold certificate, packaged with its radius value. This
does not add any mathematical assumption; it only records that the radius named
by the certificate is `1 - wStar/n`. -/
def IsSaturatedRadiusThreshold
    (Iinf : IncidenceProfile) (B W n wStar : ℕ) (δStar : ℝ) : Prop :=
  δStar = agreementRadius n wStar ∧ IsSaturatedThreshold Iinf B W wStar

/-- Saturation transports the finite threshold from the saturated profile to the
actual profile.  This is the deterministic consumer a future proof should use. -/
theorem actualThreshold_of_saturatedThreshold {I Iinf : IncidenceProfile} {B W wStar : ℕ}
    (hsat : SaturatedThrough I Iinf W)
    (hthr : IsSaturatedThreshold Iinf B W wStar) :
    wStar ≤ W ∧ I wStar ≤ B ∧ ∀ w, w ≤ W → wStar < w → B < I w := by
  refine ⟨hthr.1, ?_, ?_⟩
  · simpa [hsat wStar hthr.1] using hthr.2.1
  · intro w hw hlt
    simpa [hsat w hw] using hthr.2.2 w hw hlt

/-- Saturation transports the maximal-good inverse-profile certificate to the actual profile. -/
theorem actualMaxGoodAgreement_of_saturatedMaxGoodAgreement
    {I Iinf : IncidenceProfile} {B W wStar : ℕ}
    (hsat : SaturatedThrough I Iinf W)
    (hmax : IsMaxGoodAgreement Iinf B W wStar) :
    IsMaxGoodAgreement I B W wStar :=
  isMaxGoodAgreement_of_saturatedThreshold <|
    actualThreshold_of_saturatedThreshold hsat (saturatedThreshold_of_isMaxGoodAgreement hmax)

/-- Radius-packaged version of `actualThreshold_of_saturatedThreshold`: once the
saturated profile is proved equal to the actual profile through the relevant
window, the radius `δStar = 1 - wStar/n` carries the actual finite threshold
certificate. -/
theorem actualRadiusThreshold_of_saturatedRadiusThreshold
    {I Iinf : IncidenceProfile} {B W n wStar : ℕ} {δStar : ℝ}
    (hsat : SaturatedThrough I Iinf W)
    (hthr : IsSaturatedRadiusThreshold Iinf B W n wStar δStar) :
    δStar = agreementRadius n wStar ∧
      wStar ≤ W ∧ I wStar ≤ B ∧ ∀ w, w ≤ W → wStar < w → B < I w := by
  refine ⟨hthr.1, ?_⟩
  exact actualThreshold_of_saturatedThreshold hsat hthr.2

/-! ## Complete-homogeneous envelope correction -/

/--
A family of direction/readout profiles.  In the newest #407 complete-homogeneous reformulation,
`H j w` is the number of distinct `h_{j+1}` readouts on `w`-sets satisfying `h_j = 0`.
-/
abbrev ReadoutProfileFamily := ℕ → IncidenceProfile

/--
Concrete constrained-readout profile for the complete-homogeneous formulation.  Given statistics
`h j T`, this counts distinct `h (j+1)` values among `w`-subsets satisfying `h j = 0`.
-/
noncomputable def constrainedReadoutProfile {α β : Type*}
    [Fintype α] [DecidableEq α] [DecidableEq β] [Zero β]
    (h : ℕ → Finset α → β) : ReadoutProfileFamily :=
  fun j w =>
    (((Finset.univ : Finset α).powersetCard w).filter fun T => h j T = 0).image
      (fun T => h (j + 1) T) |>.card

/-- A constrained witness set contributes its `h_{j+1}` value to the readout image. -/
theorem readout_mem_constrainedReadoutImage {α β : Type*}
    [Fintype α] [DecidableEq β] [Zero β]
    (h : ℕ → Finset α → β) {j w : ℕ} {T : Finset α}
    (hcard : T.card = w) (hzero : h j T = 0) :
    h (j + 1) T ∈
      (((Finset.univ : Finset α).powersetCard w).filter fun U => h j U = 0).image
        (fun U => h (j + 1) U) := by
  refine Finset.mem_image.mpr ⟨T, ?_, rfl⟩
  simp [hcard, hzero]

/-- `J` envelopes a readout family through the finite agreement window `W`. -/
def EnvelopeThrough (H : ReadoutProfileFamily) (J : IncidenceProfile) (W : ℕ) : Prop :=
  ∀ j w, w ≤ W → H j w ≤ J w

/--
Finite version of the latest #407 complete-homogeneous profile

`J(w) = max_{j≥1} #{ h_{j+1}(T) : |T| = w, h_j(T)=0 }`.

The parameter `JBound` records a finite direction/readout search window.  Thus
`finiteReadoutEnvelope H JBound w` is the maximum of `H j w` over `1 ≤ j ≤ JBound`.
This names the exact finite object used by the current probes without claiming a closed form for
the unbounded worst-direction profile.
-/
noncomputable def finiteReadoutEnvelope (H : ReadoutProfileFamily) (JBound : ℕ) :
    IncidenceProfile :=
  fun w => (range JBound).sup fun j => H (j + 1) w

/-- Every included positive readout index is bounded by the finite readout envelope. -/
theorem readout_le_finiteReadoutEnvelope {H : ReadoutProfileFamily} {JBound j w : ℕ}
    (hj : j < JBound) :
    H (j + 1) w ≤ finiteReadoutEnvelope H JBound w := by
  unfold finiteReadoutEnvelope
  exact Finset.le_sup (s := range JBound) (f := fun t => H (t + 1) w) (by simp [hj])

/-- Bounded-envelope form for a finite complete-homogeneous readout search window. -/
def BoundedEnvelopeThrough
    (H : ReadoutProfileFamily) (J : IncidenceProfile) (JBound W : ℕ) : Prop :=
  ∀ j w, j < JBound → w ≤ W → H (j + 1) w ≤ J w

/-- The finite readout envelope envelopes its own bounded readout family. -/
theorem finiteReadoutEnvelope_boundedEnvelopeThrough
    (H : ReadoutProfileFamily) (JBound W : ℕ) :
    BoundedEnvelopeThrough H (finiteReadoutEnvelope H JBound) JBound W := by
  intro j w hj _hw
  exact readout_le_finiteReadoutEnvelope hj

/-- A good finite-envelope certificate certifies every included complete-homogeneous readout. -/
theorem readout_good_of_finiteEnvelope_good {H : ReadoutProfileFamily} {B JBound j w : ℕ}
    (hj : j < JBound)
    (hgood : GoodAgreement (finiteReadoutEnvelope H JBound) B w) :
    GoodAgreement (H (j + 1)) B w :=
  (readout_le_finiteReadoutEnvelope (H := H) (w := w) hj).trans hgood

/-- A pointwise profile comparison through a finite agreement window. -/
def ProfileLeThrough (A B : IncidenceProfile) (W : ℕ) : Prop :=
  ∀ w, w ≤ W → A w ≤ B w

/-- A good certificate for the complete-homogeneous envelope certifies each indexed readout. -/
theorem readout_good_of_envelope_good {H : ReadoutProfileFamily} {J : IncidenceProfile}
    {B W j w : ℕ} (henv : EnvelopeThrough H J W) (hw : w ≤ W)
    (hgood : GoodAgreement J B w) :
    GoodAgreement (H j) B w :=
  (henv j w hw).trans hgood

/--
If the elementary/spectrum profile `E` undercounts the complete-homogeneous envelope `J`, then a
band where `E` is good but `J` is bad refutes using `E` as the saturated actual profile.
-/
theorem not_saturatedThrough_of_profile_undercount
    {E J : IncidenceProfile} {B W w : ℕ}
    (hw : w ≤ W) (hEgood : E w ≤ B) (hJbad : B < J w) :
    ¬ SaturatedThrough J E W := by
  exact not_saturatedThrough_of_false_good (I := J) (Iinf := E) hw hEgood hJbad

/--
Deterministic part of the newest #407 correction: a threshold must be certified against the
complete-homogeneous envelope `J`, not merely against a smaller elementary/spectrum profile `E`.
-/
theorem spectrum_threshold_bounded_by_completeHomEnvelope
    {E J : IncidenceProfile} {B W wJ : ℕ}
    (hEJ : ProfileLeThrough E J W)
    (hthrJ : IsSaturatedThreshold J B W wJ) :
    wJ ≤ W ∧ J wJ ≤ B ∧
      ∀ w, w ≤ W → wJ < w → E w ≤ J w ∧ B < J w := by
  refine ⟨hthrJ.1, hthrJ.2.1, ?_⟩
  intro w hw hlt
  exact ⟨hEJ w hw, hthrJ.2.2 w hw hlt⟩

/-! ## Bad-reduction / eliminant-denominator faithfulness -/

/--
Profile-level bad reduction predicate.  For a fixed field characteristic/prime and fixed
direction data, `BadReduction w` means the deployed characteristic-`p` incidence profile may
fail to equal the characteristic-zero complete-homogeneous profile at agreement level `w`.

The latest #407 addendum localizes the char-p residual exactly to this predicate: the prize prime
would need to divide the relevant eliminant denominator/discriminant for the worst band.
-/
abbrev BadReductionProfile := ℕ → Prop

/-- Characteristic-`p` profile `Ip` is faithful to characteristic-zero profile `I0` at all
non-bad-reduction levels through the finite window `W`. -/
def FaithfulOutsideBadReduction
    (Ip I0 : IncidenceProfile) (BadReduction : BadReductionProfile) (W : ℕ) : Prop :=
  ∀ w, w ≤ W → ¬ BadReduction w → Ip w = I0 w

/-- No bad reduction occurs through a finite agreement window. -/
def NoBadReductionThrough (BadReduction : BadReductionProfile) (W : ℕ) : Prop :=
  ∀ w, w ≤ W → ¬ BadReduction w

/-- No bad reduction through `W` upgrades conditional faithfulness to saturation through `W`. -/
theorem saturatedThrough_of_faithfulOutsideBadReduction
    {Ip I0 : IncidenceProfile} {BadReduction : BadReductionProfile} {W : ℕ}
    (hfaith : FaithfulOutsideBadReduction Ip I0 BadReduction W)
    (hno : NoBadReductionThrough BadReduction W) :
    SaturatedThrough Ip I0 W := by
  intro w hw
  exact hfaith w hw (hno w hw)

/--
If no bad reduction occurs through the relevant window, a characteristic-zero saturated threshold
certificate is also a deployed characteristic-`p` threshold certificate.  This is the formal
consumer of the newest #407 localization: after the eliminant denominator is shown prime-to the
prize field, no additional char-p excess remains in the finite profile calculation.
-/
theorem deployedThreshold_of_charZeroThreshold_noBadReduction
    {Ip I0 : IncidenceProfile} {BadReduction : BadReductionProfile} {B W wStar : ℕ}
    (hfaith : FaithfulOutsideBadReduction Ip I0 BadReduction W)
    (hno : NoBadReductionThrough BadReduction W)
    (hthr : IsSaturatedThreshold I0 B W wStar) :
    wStar ≤ W ∧ Ip wStar ≤ B ∧ ∀ w, w ≤ W → wStar < w → B < Ip w :=
  actualThreshold_of_saturatedThreshold
    (saturatedThrough_of_faithfulOutsideBadReduction hfaith hno) hthr

/--
Pointwise refutation hook for the bad-reduction-free claim.  If deployed and characteristic-zero
profiles differ at an in-window level where faithfulness is known outside bad reduction, then that
level must be bad reduction.
-/
theorem badReduction_of_profile_ne
    {Ip I0 : IncidenceProfile} {BadReduction : BadReductionProfile} {W w : ℕ}
    (hfaith : FaithfulOutsideBadReduction Ip I0 BadReduction W)
    (hw : w ≤ W) (hne : Ip w ≠ I0 w) :
    BadReduction w := by
  by_contra hnot
  exact hne (hfaith w hw hnot)

/-! ## Finite bad-prime gate -/

/--
A deployed characteristic-`p` profile family.  `Ip p w` is the deployed incidence count at
agreement level `w` in characteristic/field parameter `p`.
-/
abbrev PrimeIndexedProfile := ℕ → IncidenceProfile

/--
Bad reduction indexed by the deployed prime/field parameter.  `Bad p w` means that at agreement
level `w`, characteristic `p` may fail to match the characteristic-zero complete-homogeneous
profile because the eliminant/discriminant/denominator has bad reduction.
-/
abbrev PrimeBadReductionProfile := ℕ → BadReductionProfile

/-- No bad reduction occurs for a fixed deployed prime through a finite agreement window. -/
def NoBadReductionForPrimeThrough
    (Bad : PrimeBadReductionProfile) (p W : ℕ) : Prop :=
  NoBadReductionThrough (Bad p) W

/--
A finite bad-prime certificate through a finite agreement window: every prime/field parameter
outside `badPrimes` has no bad reduction through `W`.

This is the profile-level form of the latest #407 localization.  The remaining hard arithmetic
task is to produce such a finite set from the eliminant denominator and show the deployed field
parameter is not in it.
-/
def BadPrimesCoverThrough
    (Bad : PrimeBadReductionProfile) (badPrimes : Finset ℕ) (W : ℕ) : Prop :=
  ∀ p, p ∉ badPrimes → NoBadReductionForPrimeThrough Bad p W

/-- Outside a finite bad-prime certificate, deployed and characteristic-zero profiles saturate. -/
theorem saturatedThrough_of_prime_notMem_badPrimes
    {Ip : PrimeIndexedProfile} {I0 : IncidenceProfile}
    {Bad : PrimeBadReductionProfile} {badPrimes : Finset ℕ} {p W : ℕ}
    (hfaith : ∀ p, FaithfulOutsideBadReduction (Ip p) I0 (Bad p) W)
    (hcover : BadPrimesCoverThrough Bad badPrimes W)
    (hp : p ∉ badPrimes) :
    SaturatedThrough (Ip p) I0 W := by
  exact saturatedThrough_of_faithfulOutsideBadReduction (hfaith p) (hcover p hp)

/--
Finite bad-prime consumer for the deployed threshold.  A characteristic-zero threshold transfers
to the deployed profile for any prime/field parameter outside the finite bad-prime certificate.
-/
theorem deployedThreshold_of_charZeroThreshold_prime_notMem_badPrimes
    {Ip : PrimeIndexedProfile} {I0 : IncidenceProfile}
    {Bad : PrimeBadReductionProfile} {badPrimes : Finset ℕ} {p B W wStar : ℕ}
    (hfaith : ∀ p, FaithfulOutsideBadReduction (Ip p) I0 (Bad p) W)
    (hcover : BadPrimesCoverThrough Bad badPrimes W)
    (hp : p ∉ badPrimes)
    (hthr : IsSaturatedThreshold I0 B W wStar) :
    wStar ≤ W ∧ Ip p wStar ≤ B ∧ ∀ w, w ≤ W → wStar < w → B < Ip p w :=
  actualThreshold_of_saturatedThreshold
    (saturatedThrough_of_prime_notMem_badPrimes hfaith hcover hp) hthr

/--
Finite bad-prime consumer in the inverse-profile form.  Outside the finite bad-prime set, a
characteristic-zero largest-good certificate for the complete-homogeneous profile is also the
deployed largest-good certificate.
-/
theorem deployedMaxGoodAgreement_of_charZeroMaxGood_prime_notMem_badPrimes
    {Ip : PrimeIndexedProfile} {I0 : IncidenceProfile}
    {Bad : PrimeBadReductionProfile} {badPrimes : Finset ℕ} {p B W wStar : ℕ}
    (hfaith : ∀ p, FaithfulOutsideBadReduction (Ip p) I0 (Bad p) W)
    (hcover : BadPrimesCoverThrough Bad badPrimes W)
    (hp : p ∉ badPrimes)
    (hmax : IsMaxGoodAgreement I0 B W wStar) :
    IsMaxGoodAgreement (Ip p) B W wStar :=
  actualMaxGoodAgreement_of_saturatedMaxGoodAgreement
    (saturatedThrough_of_prime_notMem_badPrimes hfaith hcover hp) hmax

/--
Refutation hook for a proposed finite bad-prime certificate.  If an outside prime has a
profile mismatch in the certified window, then it must in fact belong to the finite bad-prime set.
-/
theorem badPrime_mem_of_profile_ne
    {Ip : PrimeIndexedProfile} {I0 : IncidenceProfile}
    {Bad : PrimeBadReductionProfile} {badPrimes : Finset ℕ} {p W w : ℕ}
    (hfaith : ∀ p, FaithfulOutsideBadReduction (Ip p) I0 (Bad p) W)
    (hcover : BadPrimesCoverThrough Bad badPrimes W)
    (hw : w ≤ W) (hne : Ip p w ≠ I0 w) :
    p ∈ badPrimes := by
  by_contra hp
  have hno : ¬ Bad p w := hcover p hp w hw
  exact hne (hfaith p w hw hno)

/-- The scorecard used for the current #407 survivor.  A score below `9` is a
machine-readable warning that the item is not a claimed closure of the prize. -/
structure ConjectureScore where
  novelty : ℕ
  insight : ℕ
  proximity : ℕ
  feasibility : ℕ
deriving DecidableEq, Repr

/-- Current honest score for the saturated-incidence inverse-profile conjecture:
near the prize regime and structurally useful, but feasibility remains below the
user-requested closure bar because the profile equality is still open. -/
def saturatedIncidenceScore : ConjectureScore :=
  { novelty := 8, insight := 9, proximity := 9, feasibility := 6 }

/-- The current survivor is not yet a 9/10-all-around prize solution. -/
theorem saturatedIncidenceScore_not_closure :
    saturatedIncidenceScore.feasibility < 9 := by
  decide

end ProximityGap.Frontier.Issue407

#print axioms ProximityGap.Frontier.Issue407.agreementRadius_mem_unit
#print axioms ProximityGap.Frontier.Issue407.agreementRadius_strictAnti
#print axioms ProximityGap.Frontier.Issue407.agreementRadius_antitone
#print axioms ProximityGap.Frontier.Issue407.goodAgreementSet_eq_of_saturatedThrough
#print axioms ProximityGap.Frontier.Issue407.not_saturatedThrough_of_profile_ne
#print axioms ProximityGap.Frontier.Issue407.not_saturatedThrough_of_false_good
#print axioms ProximityGap.Frontier.Issue407.isSaturatedThreshold_iff_isMaxGoodAgreement
#print axioms ProximityGap.Frontier.Issue407.saturatedThreshold_of_isMaxGoodAgreement
#print axioms ProximityGap.Frontier.Issue407.isMaxGoodAgreement_of_saturatedThreshold
#print axioms ProximityGap.Frontier.Issue407.actualThreshold_of_saturatedThreshold
#print axioms ProximityGap.Frontier.Issue407.actualMaxGoodAgreement_of_saturatedMaxGoodAgreement
#print axioms ProximityGap.Frontier.Issue407.actualRadiusThreshold_of_saturatedRadiusThreshold
#print axioms ProximityGap.Frontier.Issue407.readout_mem_constrainedReadoutImage
#print axioms ProximityGap.Frontier.Issue407.readout_le_finiteReadoutEnvelope
#print axioms ProximityGap.Frontier.Issue407.finiteReadoutEnvelope_boundedEnvelopeThrough
#print axioms ProximityGap.Frontier.Issue407.readout_good_of_finiteEnvelope_good
#print axioms ProximityGap.Frontier.Issue407.readout_good_of_envelope_good
#print axioms ProximityGap.Frontier.Issue407.not_saturatedThrough_of_profile_undercount
#print axioms ProximityGap.Frontier.Issue407.spectrum_threshold_bounded_by_completeHomEnvelope
#print axioms ProximityGap.Frontier.Issue407.saturatedThrough_of_faithfulOutsideBadReduction
#print axioms ProximityGap.Frontier.Issue407.deployedThreshold_of_charZeroThreshold_noBadReduction
#print axioms ProximityGap.Frontier.Issue407.badReduction_of_profile_ne
#print axioms ProximityGap.Frontier.Issue407.saturatedThrough_of_prime_notMem_badPrimes
#print axioms
  ProximityGap.Frontier.Issue407.deployedThreshold_of_charZeroThreshold_prime_notMem_badPrimes
#print axioms
  ProximityGap.Frontier.Issue407.deployedMaxGoodAgreement_of_charZeroMaxGood_prime_notMem_badPrimes
#print axioms ProximityGap.Frontier.Issue407.badPrime_mem_of_profile_ne
#print axioms ProximityGap.Frontier.Issue407.saturatedIncidenceScore_not_closure
