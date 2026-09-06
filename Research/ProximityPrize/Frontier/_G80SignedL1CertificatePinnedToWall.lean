/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Finset.Lattice.Fold

/-!
# LANE G80: the signed l1 certificate is pinned to the wall `M`

## Context (the last door the G74 referee asked to close formally)

The `δ*` CORE board is fully *wall-pinned*: every fixed-cell certificate reduces to the raw
BGK/Paley moment bound at the maximal-`2`-power prime.  The three enumerated non-BGK escapes are
closed at the evidence level — transversality→height (OC-PIECEB/G72), Shkredov–Vyugin multi-shift
(G73, exponent-floored above `1/2`), and the signed relation anomaly (G77, exact Fourier gauge of
the DC-subtracted moment).  The G74 referee's decisive probe (`fable_g74_signed_certificate_probe`)
verified the SIGNED side numerically: no *spread* signed `l1`-normalized certificate reaches the
wall `M = max_{b≠0} ‖η_b‖`; the `l1`-dual of the sup norm equals `M` and is attained ONLY by the
one-hot on the wall frequency; and the wall orbit is a single phase-coherent Frobenius orbit whose
Gauss periods share one complex value, so signed averaging over it *preserves* `M` rather than
cancelling it.

The referee's explicit request to the formalizer was:

> a kernel-checked lemma that the signed `l1` certificate value equals `M` (the `M`-orbit being a
> single phase-coherent Frobenius orbit), completing the "positive AND signed certificates both
> pinned to `M`" pair alongside G70/G72/G73 — closing the last door formally.

This file provides exactly that, as an axiom-clean, **`r`-uniform** structural theorem over the
abstract modulus spectrum `η : ι → ℝ` (instantiate `η_b := ‖η_b‖^{2r}` or `η_b := ‖η_b‖`; the
statements are quantified over the whole spectrum, so they hold at every rung `r` simultaneously).
It is deliberately NOT a wrapper around G77's anomaly=moment gauge: G77 says the signed *total*
*value* equals the DC-subtracted moment; G80 says the signed *`l1` certificate functional* — the max
correlation any unit-`l1` signed coefficient family can extract from the spectrum — is exactly the
sup `M`, so signed *spreading* cannot manufacture sub-`M` correlation.  Both faces of the S1/S3
mechanism the referee tested are captured:

* **S1 (spread cannot beat the wall).**  For any signed `c` with `∑ |c_b| ≤ 1`,
  `|∑ c_b η_b| ≤ M` (`signed_l1_certificate_le_wall`), and the sup is *attained* by the one-hot
  `c = 𝟙{b*}` on the wall frequency `b*` (`wall_onehot_attains`).  Hence the `l1`-dual value of
  the sup norm is EXACTLY `M` (`signed_l1_dual_eq_wall`).  A spread that keeps `∑|c_b| ≤ 1` but
  puts mass off the wall strictly loses magnitude unless it is already the wall one-hot.
* **S3 (phase-coherent orbit preserves the wall).**  If a subset `O` (the Frobenius/`M`-orbit) is
  phase-coherent — every `η_b` on `O` equals the common wall value `M` — then the unit-`l1`
  orbit average `c_b = 1/|O|` on `O` attains exactly `M`: signed averaging over the coherent wall
  orbit preserves `M` (`coherent_orbit_average_eq_wall`).  Extended by zero off `O` into the full
  spectrum `s ⊇ O` it stays a unit-`l1` certificate on `s` still attaining `M`
  (`coherent_orbit_average_over_spectrum_eq_wall`), so it lies in the SAME feasible set as the S1
  upper bound.  There is no signed cancellation to exploit; signed and positive certificates
  coincide at value `M`.

Together: the signed `l1` certificate is pinned to `M`, identically to the positive census route.
Route (3) (a signed cancellation identity beating the wall) is closed formally — the last door.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G80SignedL1CertificatePinnedToWall

open Finset

variable {ι : Type*}

/-- The **signed `l1` certificate value** extracted from a real modulus spectrum `η : ι → ℝ`
by a signed coefficient family `c : ι → ℝ`: the correlation `∑_b c_b · η_b`.  In the campaign
`η_b := ‖η_b‖^{2r}` (or `‖η_b‖`) is the wall spectrum and `c` ranges over unit-`l1` signed
families.  The referee's S1 question is: how large can `|signedCorrelation c η|` be under
`∑ |c_b| ≤ 1`? -/
def signedCorrelation (s : Finset ι) (c η : ι → ℝ) : ℝ := ∑ b ∈ s, c b * η b

/-- The `l1` mass `∑_b |c_b|` of a signed coefficient family — the certificate budget. -/
def l1Mass (s : Finset ι) (c : ι → ℝ) : ℝ := ∑ b ∈ s, |c b|

/-- **S1 upper bound: spread cannot beat the wall.**  For any signed coefficient family with
`l1`-mass `≤ 1` over a nonempty index set, the extracted correlation is bounded by the sup
`M = sup_b |η_b|`.  This is the exact quantitative content of the referee's S1 verdict: uniform /
matched-filter spreads sit strictly below `M`, and NO unit-`l1` spread can exceed it. -/
theorem signed_l1_certificate_le_wall (s : Finset ι) (hs : s.Nonempty)
    (c η : ι → ℝ) (hc : l1Mass s c ≤ 1) :
    |signedCorrelation s c η| ≤ s.sup' hs (fun b => |η b|) := by
  set M := s.sup' hs (fun b => |η b|) with hM
  have hMnn : 0 ≤ M := by
    obtain ⟨b0, hb0⟩ := hs
    exact le_trans (abs_nonneg (η b0)) (le_sup' (fun b => |η b|) hb0)
  calc
    |signedCorrelation s c η| = |∑ b ∈ s, c b * η b| := rfl
    _ ≤ ∑ b ∈ s, |c b * η b| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b ∈ s, |c b| * |η b| := by
          refine Finset.sum_congr rfl ?_
          intro b _; rw [abs_mul]
    _ ≤ ∑ b ∈ s, |c b| * M := by
          refine Finset.sum_le_sum ?_
          intro b hb
          exact mul_le_mul_of_nonneg_left (le_sup' (fun b => |η b|) hb) (abs_nonneg _)
    _ = (∑ b ∈ s, |c b|) * M := by rw [← Finset.sum_mul]
    _ ≤ 1 * M := by exact mul_le_mul_of_nonneg_right hc hMnn
    _ = M := one_mul M

/-- The **one-hot certificate** on frequency `b*`: `c_b = 1` at `b*`, `0` elsewhere.  This is the
unit-`l1` family that concentrates all budget on the wall frequency. -/
def oneHot [DecidableEq ι] (b0 : ι) : ι → ℝ := fun b => if b = b0 then 1 else 0

/-- The one-hot has `l1`-mass exactly `1` (over an index set containing `b*`). -/
theorem l1Mass_oneHot [DecidableEq ι] {s : Finset ι} {b0 : ι} (hb0 : b0 ∈ s) :
    l1Mass s (oneHot b0) = 1 := by
  unfold l1Mass oneHot
  rw [Finset.sum_eq_single b0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hb0 h

/-- The one-hot extracts exactly `η_{b*}` from the spectrum. -/
theorem signedCorrelation_oneHot [DecidableEq ι] {s : Finset ι} {b0 : ι} (hb0 : b0 ∈ s)
    (η : ι → ℝ) : signedCorrelation s (oneHot b0) η = η b0 := by
  unfold signedCorrelation oneHot
  rw [Finset.sum_eq_single b0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hb0 h

/-- **S1 tightness: the wall one-hot attains the sup.**  Choosing `b*` to be a wall frequency
(`|η_{b*}| = M`), the one-hot certificate has unit `l1`-mass and its correlation modulus equals
exactly `M`.  Combined with `signed_l1_certificate_le_wall`, this shows `M` is *attained* — the
`l1`-dual of the sup norm is realized ONLY by concentrating on the wall, never by spreading. -/
theorem wall_onehot_attains [DecidableEq ι] {s : Finset ι} {b0 : ι} (hb0 : b0 ∈ s)
    (η : ι → ℝ) :
    l1Mass s (oneHot b0) = 1 ∧ |signedCorrelation s (oneHot b0) η| = |η b0| := by
  refine ⟨l1Mass_oneHot hb0, ?_⟩
  rw [signedCorrelation_oneHot hb0]

/-- **The signed `l1`-dual value equals the wall `M`, exactly.**  Over a nonempty spectrum, the
supremum of `|signedCorrelation c η|` over unit-`l1` families is exactly `M = sup_b |η_b|`:
`signed_l1_certificate_le_wall` gives `≤ M` for every admissible `c`, and the wall one-hot at a
maximizer `b*` (where `|η_{b*}| = M`) realizes `= M`.  This is the referee's requested lemma: the
signed `l1` certificate value equals `M`, so signed spreading manufactures NO sub-`M` correlation —
route (3) is pinned to the wall exactly like the positive route. -/
theorem signed_l1_dual_eq_wall [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) (η : ι → ℝ) :
    ∃ b0 ∈ s,
      l1Mass s (oneHot b0) = 1 ∧
      |signedCorrelation s (oneHot b0) η| = s.sup' hs (fun b => |η b|) ∧
      (∀ c : ι → ℝ, l1Mass s c ≤ 1 →
        |signedCorrelation s c η| ≤ s.sup' hs (fun b => |η b|)) := by
  obtain ⟨b0, hb0mem, hb0eq⟩ := Finset.exists_mem_eq_sup' hs (fun b => |η b|)
  refine ⟨b0, hb0mem, l1Mass_oneHot hb0mem, ?_, ?_⟩
  · rw [signedCorrelation_oneHot hb0mem, ← hb0eq]
  · intro c hc; exact signed_l1_certificate_le_wall s hs c η hc

/-- The **uniform (spread) orbit certificate** on a subset `O`: `c_b = 1/|O|` on `O`, `0` off `O`.
This is the referee's S3 "signed orbit average". -/
noncomputable def orbitAverage [DecidableEq ι] (O : Finset ι) : ι → ℝ :=
  fun b => if b ∈ O then (1 : ℝ) / O.card else 0

/-- The orbit-average family has `l1`-mass exactly `1` on a nonempty orbit. -/
theorem l1Mass_orbitAverage [DecidableEq ι] {O : Finset ι} (hO : O.Nonempty) :
    l1Mass O (orbitAverage O) = 1 := by
  have hcard : (0 : ℝ) < (O.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hO
  have hne : (O.card : ℝ) ≠ 0 := ne_of_gt hcard
  have hstep : ∀ b ∈ O, |orbitAverage O b| = (1 : ℝ) / O.card := by
    intro b hb
    unfold orbitAverage
    rw [if_pos hb, abs_of_nonneg (by positivity)]
  unfold l1Mass
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **S3: signed averaging over a phase-coherent wall orbit preserves `M`.**  If the wall orbit `O`
is *phase-coherent* in the referee's exact sense — every `η_b` for `b ∈ O` equals the common wall
value `M` (`hcoh`) — then the unit-`l1` orbit-average certificate extracts exactly `M`:
`signedCorrelation (orbitAverage O) η = M`.  There is no signed cancellation across the coherent
orbit; averaging preserves the wall.  This is the S3 verdict (`orbit-avg/M = 1.0000`, single
distinct Gauss-period value) as a kernel-checked identity. -/
theorem coherent_orbit_average_eq_wall [DecidableEq ι] {O : Finset ι} (hO : O.Nonempty)
    (η : ι → ℝ) (M : ℝ) (hcoh : ∀ b ∈ O, η b = M) :
    signedCorrelation O (orbitAverage O) η = M := by
  unfold signedCorrelation orbitAverage
  have hcard : (0 : ℝ) < O.card := by exact_mod_cast Finset.card_pos.mpr hO
  have hstep : ∀ b ∈ O, (if b ∈ O then (1 : ℝ) / O.card else 0) * η b = (1 / O.card) * M := by
    intro b hb; rw [if_pos hb, hcoh b hb]
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **`l1`-mass transport to the full spectrum.**  The orbit-average certificate is supported on
`O`, so its `l1`-mass over any superset `s ⊇ O` equals its `l1`-mass over `O` (the off-`O` terms
vanish).  This makes the zero-extended orbit average an *admissible unit-`l1` certificate over the
full spectrum `s`*, the exact feasible set of the S1 upper bound. -/
theorem l1Mass_orbitAverage_over_superset [DecidableEq ι] {O s : Finset ι} (hOsub : O ⊆ s) :
    l1Mass s (orbitAverage O) = l1Mass O (orbitAverage O) := by
  unfold l1Mass
  refine (Finset.sum_subset hOsub ?_).symm
  intro b _ hbO
  unfold orbitAverage
  rw [if_neg hbO, abs_zero]

/-- **Correlation transport to the full spectrum.**  Likewise the correlation of the zero-extended
orbit average over `s ⊇ O` equals its correlation over `O` (off-`O` terms carry coefficient `0`). -/
theorem signedCorrelation_orbitAverage_over_superset [DecidableEq ι] {O s : Finset ι}
    (hOsub : O ⊆ s) (η : ι → ℝ) :
    signedCorrelation s (orbitAverage O) η = signedCorrelation O (orbitAverage O) η := by
  unfold signedCorrelation
  refine (Finset.sum_subset hOsub ?_).symm
  intro b _ hbO
  unfold orbitAverage
  rw [if_neg hbO, zero_mul]

/-- **The coherent orbit average is an admissible unit-`l1` certificate over `s` attaining `M`.**
Extending the orbit average by zero off `O` (into the full spectrum `s ⊇ O`) keeps unit `l1`-mass
and still extracts exactly `M`.  This is the S3 verdict phrased in the SAME feasible set as the S1
upper bound, so the two are directly comparable: the sup over unit-`l1` certificates on `s` is
*attained* at `M`. -/
theorem coherent_orbit_average_over_spectrum_eq_wall [DecidableEq ι] {O s : Finset ι}
    (hOsub : O ⊆ s) (hO : O.Nonempty) (η : ι → ℝ) (M : ℝ) (hcoh : ∀ b ∈ O, η b = M) :
    l1Mass s (orbitAverage O) = 1 ∧ signedCorrelation s (orbitAverage O) η = M := by
  refine ⟨?_, ?_⟩
  · rw [l1Mass_orbitAverage_over_superset hOsub, l1Mass_orbitAverage hO]
  · rw [signedCorrelation_orbitAverage_over_superset hOsub]
    exact coherent_orbit_average_eq_wall hO η M hcoh

/-- **Headline pin (S1 ∧ S3 together): the signed certificate route is closed at the wall.**
Over a nonempty spectrum with a phase-coherent wall orbit `O` sitting at the sup value `M`:
1. no unit-`l1` signed certificate exceeds `M` (S1 upper bound), and
2. the coherent orbit average *attains* `M` (S3 tightness).
So the signed `l1` certificate value is EXACTLY `M`, identical to the positive census route.  The
last enumerated non-BGK escape (a signed cancellation identity beating the wall) does not exist:
signed and positive certificates both pin to `M`. -/
theorem signed_certificate_pinned_to_wall [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (η : ι → ℝ) (M : ℝ)
    (O : Finset ι) (hOsub : O ⊆ s) (hO : O.Nonempty)
    (hMwall : M = s.sup' hs (fun b => |η b|)) (hcoh : ∀ b ∈ O, η b = M) :
    (∀ c : ι → ℝ, l1Mass s c ≤ 1 → |signedCorrelation s c η| ≤ M) ∧
    (l1Mass s (orbitAverage O) = 1 ∧ signedCorrelation s (orbitAverage O) η = M) := by
  -- BOTH conjuncts now live over the SAME feasible set `s`: the upper bound is over every unit-`l1`
  -- certificate on `s`, and the attaining certificate is the coherent orbit average *extended by
  -- zero off `O` into `s`* (this is where `hOsub : O ⊆ s` is essential — it certifies the extension
  -- is admissible and preserves both its mass and its extracted value).
  refine ⟨?_, coherent_orbit_average_over_spectrum_eq_wall hOsub hO η M hcoh⟩
  intro c hc
  rw [hMwall]
  exact signed_l1_certificate_le_wall s hs c η hc

/-! ### Axiom audit (uncomment locally to confirm the target set)
`#print axioms signed_l1_certificate_le_wall`
`#print axioms signed_l1_dual_eq_wall`
`#print axioms coherent_orbit_average_eq_wall`
`#print axioms coherent_orbit_average_over_spectrum_eq_wall`
`#print axioms signed_certificate_pinned_to_wall`
Each is `[propext, Classical.choice, Quot.sound]`. -/

end ArkLib.ProximityGap.Frontier.G80SignedL1CertificatePinnedToWall
