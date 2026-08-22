/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaAutocorrInvolutionPaired
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R348PeriodSquareRecursion

/-!
# Fourier-cone duality for the centered translate restriction

This file computes the exact finite-dimensional linear program behind the tempting
"zero mean + additive PSD + multiplicative invariance" attack on the centered depth-seven
restriction.

In Fourier coordinates, a zero-DC positive-semidefinite translation kernel has nonnegative
weights `w_b`, and multiplicative `G`-invariance makes those weights constant on the orbits
`bG`.  If

`D_w(x) = sum_b w_b Re(psi(b*x))`,

then the exact restriction identity is

`sum_(u in G) D_w(1-u) = (1/|G|) sum_b w_b |eta_b|^2`.

Consequently, at fixed normalization `D_w(0) = sum_b w_b = 1`, the linear-programming optimum
is exactly

`max_(b != 0) |eta_b|^2 / |G|`.

It is attained by putting uniform Fourier mass on a single multiplicative orbit.  Thus the
universal cone problem is not weaker than the worst Gauss-period (Paley spectral) problem: it is
the same problem in dual coordinates.

The actual depth-six centered autocorrelation is much more special: its Fourier weights are
`w_b = |eta_b|^12`.  Its objective is therefore the ratio of adjacent moments

`(1/|G|) sum_(b != 0) |eta_b|^14`.

That nonlinear weight constraint is genuine extra information, but merely inserting it into the
linear program supplies no saving: the generic estimate is still the worst-period bound.  A useful
improvement must exploit arithmetic relations among the complete period profile, not only PSD,
zero DC, and orbit invariance.  No production Paley or proximity bound is claimed here. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKCenteredTranslateConeDuality

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.GaussPeriodCosetReduction
open ArkLib.ProximityGap.EtaAutocorrInvolutionPaired
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The centered-translate objective occurring in the depth-seven convolution collapse. -/
noncomputable def signedRestriction (G : Finset F) (D : F → ℝ) : ℝ :=
  ∑ u ∈ G, D (1 - u)

/-! ## Multiplicative-subgroup bookkeeping -/

/-- A finite multiplicative subgroup of a field cannot contain zero. -/
theorem zero_not_mem (G : Finset F) (hG : IsMulSubgroup G) : (0 : F) ∉ G := by
  intro hzero
  obtain ⟨z, _hz, hzz⟩ := hG.exists_inv 0 hzero
  simpa using hzz

/-- Left multiplication by a subgroup element permutes the subgroup. -/
theorem image_mul_left_eq (G : Finset F) (hG : IsMulSubgroup G)
    {g : F} (hg : g ∈ G) :
    G.image (fun x => g * x) = G := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hG.mul_mem g hg y hy
  · intro x hx
    obtain ⟨gi, hgi, hggi⟩ := hG.exists_inv g hg
    refine Finset.mem_image.mpr ⟨gi * x, hG.mul_mem gi hgi x hx, ?_⟩
    rw [← mul_assoc, hggi, one_mul]

/-- The subgroup is nonempty, so its real cardinality is positive. -/
theorem card_pos_real (G : Finset F) (hG : IsMulSubgroup G) :
    (0 : ℝ) < G.card := by
  exact_mod_cast Finset.card_pos.mpr ⟨1, hG.one_mem⟩

/-! ## The Fourier cone and its signed restriction -/

/-- Nonnegative, zero-DC Fourier weights constant on every multiplicative `G`-orbit. -/
structure OrbitSpectralWeight (G : Finset F) (w : F → ℝ) : Prop where
  zero : w 0 = 0
  nonneg : ∀ b, 0 ≤ w b
  invariant : ∀ g ∈ G, ∀ b, w (g * b) = w b

/-- The Fourier mass.  For the corresponding kernel this is its value at zero. -/
noncomputable def spectralMass (w : F → ℝ) : ℝ := ∑ b : F, w b

/-- A real translation kernel written with nonnegative additive Fourier weights. -/
noncomputable def spectralKernel (psi : AddChar F ℂ) (w : F → ℝ) (x : F) : ℝ :=
  ∑ b : F, w b * (psi (b * x)).re

/-- The orbit-averaged period-square objective. -/
noncomputable def coneObjective (psi : AddChar F ℂ) (G : Finset F)
    (w : F → ℝ) : ℝ :=
  (∑ b : F, w b * ‖eta psi G b‖ ^ 2) / (G.card : ℝ)

/-- The raw translate coefficient at a frequency. -/
noncomputable def translateCoefficient (psi : AddChar F ℂ) (G : Finset F)
    (b : F) : ℝ :=
  ∑ u ∈ G, (psi (b * (1 - u))).re

/-- Averaging a translate coefficient over one multiplicative orbit gives exactly the period
square.  This is the finite-field Fourier atom behind the cone duality. -/
theorem sum_translateCoefficient_mul_orbit_eq_normSq
    (psi : AddChar F ℂ) (G : Finset F) (hG : IsMulSubgroup G) (b : F) :
    ∑ g ∈ G, translateCoefficient psi G (g * b) = ‖eta psi G b‖ ^ 2 := by
  classical
  have hbij : ∀ g ∈ G, G.image (fun x => g * x) = G :=
    fun g hg => image_mul_left_eq G hG hg
  have hzero : (0 : F) ∉ G := zero_not_mem G hG
  have hpoint :=
    ArkLib.ProximityGap.EtaPointwiseAutocorr.eta_normSq_eq_sum_groupShift
      (ψ := psi) hbij hzero (-b)
  have hcomplex :
      (∑ g ∈ G, ∑ u ∈ G, psi ((g * b) * (1 - u))) =
        ((‖eta psi G b‖ ^ 2 : ℝ) : ℂ) := by
    calc
      (∑ g ∈ G, ∑ u ∈ G, psi ((g * b) * (1 - u))) =
          ∑ u ∈ G, ∑ g ∈ G, psi (((-b) * (u - 1)) * g) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        refine Finset.sum_congr rfl (fun g _ => ?_)
        congr 1
        ring
      _ = ∑ u ∈ G, eta psi G ((-b) * (u - 1)) := by
        rfl
      _ = ((‖eta psi G (-b)‖ ^ 2 : ℝ) : ℂ) := hpoint.symm
      _ = ((‖eta psi G b‖ ^ 2 : ℝ) : ℂ) := by
        rw [eta_neg_eq_conj]
        simp
  have hre := congrArg Complex.re hcomplex
  rw [Complex.ofReal_re] at hre
  simpa [translateCoefficient, map_sum] using hre

/-- Expanding the spectral kernel inside the signed restriction exposes the raw translate
coefficients frequency by frequency. -/
theorem signedRestriction_spectralKernel_eq_raw
    (psi : AddChar F ℂ) (G : Finset F) (w : F → ℝ) :
    signedRestriction G (spectralKernel psi w) =
      ∑ b : F, w b * translateCoefficient psi G b := by
  classical
  unfold signedRestriction spectralKernel translateCoefficient
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Reindexing all frequencies by a subgroup element rotates the translate coefficients while
leaving an orbit-invariant weighted sum unchanged. -/
theorem weighted_translate_reindex
    (psi : AddChar F ℂ) (G : Finset F) (hG : IsMulSubgroup G)
    (w : F → ℝ) (hw : OrbitSpectralWeight G w) {g : F} (hg : g ∈ G) :
    (∑ b : F, w b * translateCoefficient psi G b) =
      ∑ b : F, w b * translateCoefficient psi G (g * b) := by
  have hg0 : g ≠ 0 := by
    intro h
    exact zero_not_mem G hG (h ▸ hg)
  calc
    (∑ b : F, w b * translateCoefficient psi G b) =
        ∑ b : F, w (g * b) * translateCoefficient psi G (g * b) := by
      exact (Fintype.sum_equiv (Equiv.mulLeft₀ g hg0)
        (fun b => w (g * b) * translateCoefficient psi G (g * b))
        (fun b => w b * translateCoefficient psi G b)
        (fun _ => rfl)).symm
    _ = ∑ b : F, w b * translateCoefficient psi G (g * b) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hw.invariant g hg b]

/-- **Exact restriction formula.**  On the nonnegative zero-DC orbit-invariant Fourier cone,
the signed translate restriction is the weighted average of the squared Gauss periods. -/
theorem signedRestriction_spectralKernel_eq_coneObjective
    (psi : AddChar F ℂ) (G : Finset F) (hG : IsMulSubgroup G)
    (w : F → ℝ) (hw : OrbitSpectralWeight G w) :
    signedRestriction G (spectralKernel psi w) = coneObjective psi G w := by
  classical
  rw [signedRestriction_spectralKernel_eq_raw]
  unfold coneObjective
  have hnpos : (0 : ℝ) < G.card := card_pos_real G hG
  rw [eq_div_iff hnpos.ne']
  calc
    (∑ b : F, w b * translateCoefficient psi G b) * (G.card : ℝ) =
        ∑ g ∈ G, ∑ b : F, w b * translateCoefficient psi G b := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ∑ g ∈ G, ∑ b : F, w b * translateCoefficient psi G (g * b) := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      exact weighted_translate_reindex psi G hG w hw hg
    _ = ∑ b : F, ∑ g ∈ G, w b * translateCoefficient psi G (g * b) := by
      rw [Finset.sum_comm]
    _ = ∑ b : F, w b * ∑ g ∈ G, translateCoefficient psi G (g * b) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum]
    _ = ∑ b : F, w b * ‖eta psi G b‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [sum_translateCoefficient_mul_orbit_eq_normSq psi G hG b]

/-! ## Exact fixed-mass linear-programming duality -/

/-- The orbit-supported spectral weight with total mass `M`. -/
noncomputable def orbitWeight (G : Finset F) (b0 : F) (M : ℝ) (b : F) : ℝ :=
  if b ∈ G.image (fun g => g * b0) then M / (G.card : ℝ) else 0

/-- Membership in a nonzero multiplicative orbit is invariant under multiplying by `G`. -/
theorem mem_mul_orbit_iff (G : Finset F) (hG : IsMulSubgroup G)
    {g b0 b : F} (hg : g ∈ G) :
    g * b ∈ G.image (fun u => u * b0) ↔ b ∈ G.image (fun u => u * b0) := by
  constructor
  · intro hb
    obtain ⟨u, hu, hub⟩ := Finset.mem_image.mp hb
    obtain ⟨gi, hgi, hggi⟩ := hG.exists_inv g hg
    refine Finset.mem_image.mpr ⟨gi * u, hG.mul_mem gi hgi u hu, ?_⟩
    calc
      (gi * u) * b0 = gi * (u * b0) := by ring
      _ = gi * (g * b) := by rw [hub]
      _ = b := by rw [← mul_assoc, mul_comm gi g, hggi, one_mul]
  · intro hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨g * u, hG.mul_mem g hg u hu, by ring⟩

/-- A single-orbit weight is an admissible cone point when its mass is nonnegative. -/
theorem orbitWeight_admissible (G : Finset F) (hG : IsMulSubgroup G)
    {b0 : F} (hb0 : b0 ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    OrbitSpectralWeight G (orbitWeight G b0 M) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold orbitWeight
    rw [if_neg]
    intro hmem
    obtain ⟨g, hg, hgb⟩ := Finset.mem_image.mp hmem
    have hg0 : g ≠ 0 := fun h => zero_not_mem G hG (h ▸ hg)
    exact hb0 (mul_eq_zero.mp hgb |>.resolve_left hg0)
  · intro b
    unfold orbitWeight
    split_ifs
    · exact div_nonneg hM (le_of_lt (card_pos_real G hG))
    · exact le_rfl
  · intro g hg b
    unfold orbitWeight
    rw [if_congr (mem_mul_orbit_iff G hG hg) rfl rfl]

/-- The orbit-supported weight has exactly the prescribed total mass. -/
theorem spectralMass_orbitWeight (G : Finset F) (hG : IsMulSubgroup G)
    {b0 : F} (hb0 : b0 ≠ 0) (M : ℝ) :
    spectralMass (orbitWeight G b0 M) = M := by
  classical
  let O : Finset F := G.image (fun g => g * b0)
  have hcard : O.card = G.card := by
    dsimp [O]
    exact Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel₀ hb0 h)
  have hnpos : (0 : ℝ) < G.card := card_pos_real G hG
  unfold spectralMass orbitWeight
  change (∑ b : F, if b ∈ O then M / (G.card : ℝ) else 0) = M
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_const, nsmul_eq_mul, hcard]
  field_simp

/-- The objective of a single-orbit weight is exactly the corresponding normalized period square.
This proves attainability of every vertex of the dual simplex. -/
theorem coneObjective_orbitWeight (psi : AddChar F ℂ)
    (G : Finset F) (hG : IsMulSubgroup G)
    {b0 : F} (hb0 : b0 ≠ 0) (M : ℝ) :
    coneObjective psi G (orbitWeight G b0 M) =
      M * (‖eta psi G b0‖ ^ 2 / (G.card : ℝ)) := by
  classical
  let O : Finset F := G.image (fun g => g * b0)
  have hcard : O.card = G.card := by
    dsimp [O]
    exact Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel₀ hb0 h)
  have hbij : ∀ g ∈ G, G.image (fun x => g * x) = G :=
    fun g hg => image_mul_left_eq G hG hg
  have hzero : (0 : F) ∉ G := zero_not_mem G hG
  have hconst : ∀ b ∈ O, ‖eta psi G b‖ ^ 2 = ‖eta psi G b0‖ ^ 2 := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hb
    rw [eta_mul_left hbij hzero hg]
  have hnpos : (0 : ℝ) < G.card := card_pos_real G hG
  unfold coneObjective orbitWeight
  change (∑ b : F,
      (if b ∈ O then M / (G.card : ℝ) else 0) * ‖eta psi G b‖ ^ 2) /
        (G.card : ℝ) = _
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_congr rfl (fun b hb => by rw [hconst b hb]),
    Finset.sum_const, nsmul_eq_mul, hcard]
  field_simp

/-- A worst-period bound gives the corresponding bound for every nonnegative spectral weight. -/
theorem coneObjective_le_of_period_bound
    (psi : AddChar F ℂ) (G : Finset F) (hG : IsMulSubgroup G)
    (w : F → ℝ) (hw : OrbitSpectralWeight G w) {M S : ℝ}
    (hmass : spectralMass w = M)
    (hS : ∀ b, b ≠ 0 → ‖eta psi G b‖ ^ 2 ≤ S) :
    coneObjective psi G w ≤ M * (S / (G.card : ℝ)) := by
  have hnpos : (0 : ℝ) < G.card := card_pos_real G hG
  unfold coneObjective
  rw [div_le_iff₀ hnpos]
  calc
    (∑ b : F, w b * ‖eta psi G b‖ ^ 2) ≤ ∑ b : F, w b * S := by
      refine Finset.sum_le_sum (fun b _ => ?_)
      by_cases hb : b = 0
      · subst b
        simp [hw.zero]
      · exact mul_le_mul_of_nonneg_left (hS b hb) (hw.nonneg b)
    _ = M * S := by
      rw [← Finset.sum_mul, ← hmass]
      rfl
    _ = M * (S / (G.card : ℝ)) * (G.card : ℝ) := by
      field_simp

/-- **Exact Fourier linear-programming duality.**  Bounding the signed restriction on every
unit-mass nonnegative zero-DC orbit-invariant spectral kernel is equivalent to the pointwise
worst Gauss-period bound.  The reverse implication uses the single-orbit extremizer above. -/
theorem unitMass_cone_bound_iff_worst_period
    (psi : AddChar F ℂ) (G : Finset F) (hG : IsMulSubgroup G) (S : ℝ) :
    (∀ w : F → ℝ, OrbitSpectralWeight G w → spectralMass w = 1 →
        signedRestriction G (spectralKernel psi w) ≤ S / (G.card : ℝ)) ↔
      ∀ b, b ≠ 0 → ‖eta psi G b‖ ^ 2 ≤ S := by
  constructor
  · intro hall b hb
    let w := orbitWeight G b 1
    have hw : OrbitSpectralWeight G w := orbitWeight_admissible G hG hb (by norm_num)
    have hmass : spectralMass w = 1 := spectralMass_orbitWeight G hG hb 1
    have hobj := hall w hw hmass
    rw [signedRestriction_spectralKernel_eq_coneObjective psi G hG w hw,
      coneObjective_orbitWeight psi G hG hb 1] at hobj
    have hnpos : (0 : ℝ) < G.card := card_pos_real G hG
    simpa [div_le_div_iff_of_pos_right hnpos] using hobj
  · intro hperiod w hw hmass
    rw [signedRestriction_spectralKernel_eq_coneObjective psi G hG w hw]
    simpa using coneObjective_le_of_period_bound psi G hG w hw hmass hperiod

/-! ## The actual autocorrelation weights -/

/-- The nonlinear spectral weights of the centered depth-six autocorrelation. -/
noncomputable def depthSixWeight (psi : AddChar F ℂ) (G : Finset F) (b : F) : ℝ :=
  if b = 0 then 0 else ‖eta psi G b‖ ^ 12

/-- The actual depth-six weight profile belongs to the orbit spectral cone. -/
theorem depthSixWeight_admissible (psi : AddChar F ℂ)
    (G : Finset F) (hG : IsMulSubgroup G) :
    OrbitSpectralWeight G (depthSixWeight psi G) := by
  have hbij : ∀ g ∈ G, G.image (fun x => g * x) = G :=
    fun g hg => image_mul_left_eq G hG hg
  have hzero : (0 : F) ∉ G := zero_not_mem G hG
  refine ⟨by simp [depthSixWeight], ?_, ?_⟩
  · intro b
    simp only [depthSixWeight]
    split_ifs
    · exact le_rfl
    · positivity
  · intro g hg b
    have hg0 : g ≠ 0 := fun h => hzero (h ▸ hg)
    unfold depthSixWeight
    by_cases hb : b = 0
    · subst b
      simp
    · have hgb : g * b ≠ 0 := mul_ne_zero hg0 hb
      rw [if_neg hb, if_neg hgb, eta_mul_left hbij hzero hg]

/-- The actual cone objective is `1/|G|` times the nonzero fourteenth Gauss-period moment.
Dividing it by `spectralMass = sum |eta|^12` gives the adjacent `12`/`14` moment ratio. -/
theorem coneObjective_depthSixWeight (psi : AddChar F ℂ)
    (G : Finset F) (hG : IsMulSubgroup G) :
    coneObjective psi G (depthSixWeight psi G) =
      (∑ b ∈ Finset.univ.erase (0 : F), ‖eta psi G b‖ ^ 14) / (G.card : ℝ) := by
  have hsum :
      (∑ b : F, (if b = 0 then 0 else ‖eta psi G b‖ ^ 12) *
        ‖eta psi G b‖ ^ 2) =
      ∑ b ∈ Finset.univ.erase (0 : F), (‖eta psi G b‖ ^ 14 : ℝ) := by
    have hterm (b : F) :
        (if b = 0 then 0 else ‖eta psi G b‖ ^ 12) * ‖eta psi G b‖ ^ 2 =
          (if b = 0 then 0 else ‖eta psi G b‖ ^ 14 : ℝ) := by
      by_cases hb : b = 0
      · simp [hb]
      · rw [if_neg hb, if_neg hb]
        ring
    have herase :
        (∑ b ∈ Finset.univ.erase (0 : F), (‖eta psi G b‖ ^ 14 : ℝ)) =
          ∑ b : F, (if b = 0 then 0 else ‖eta psi G b‖ ^ 14 : ℝ) := by
      calc
        (∑ b ∈ Finset.univ.erase (0 : F), (‖eta psi G b‖ ^ 14 : ℝ)) =
            ∑ b ∈ Finset.univ.erase (0 : F),
              (if b = 0 then 0 else ‖eta psi G b‖ ^ 14 : ℝ) := by
          refine Finset.sum_congr rfl (fun b hb => ?_)
          rw [if_neg (Finset.ne_of_mem_erase hb)]
        _ = ∑ b : F, (if b = 0 then 0 else ‖eta psi G b‖ ^ 14 : ℝ) :=
          Finset.sum_erase (s := Finset.univ)
            (f := fun b : F => (if b = 0 then 0 else ‖eta psi G b‖ ^ 14 : ℝ)) (by simp)
    rw [herase]
    exact Finset.sum_congr rfl (fun b _ => hterm b)
  unfold coneObjective depthSixWeight
  exact congrArg (fun x : ℝ => x / (G.card : ℝ)) hsum

/-- The actual nonlinear cone objective is exactly the DC-subtracted depth-seven moment after
multiplication by `|G|`.  Combined with the independent centered-convolution collapse, this is the
signed depth-six translate average. -/
theorem card_mul_coneObjective_depthSixWeight_eq_dcMoment
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive)
    (G : Finset F) (hG : IsMulSubgroup G) :
    (G.card : ℝ) * coneObjective psi G (depthSixWeight psi G) =
      (Fintype.card F : ℝ) *
          (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G 7 : ℝ) -
        (G.card : ℝ) ^ 14 := by
  have hnne : (G.card : ℝ) ≠ 0 := (card_pos_real G hG).ne'
  rw [coneObjective_depthSixWeight psi G hG]
  rw [mul_div_cancel₀ _ hnne]
  simpa using sum_nonzero_moment hpsi G 7

/-- Specializing the generic cone estimate to the actual `|eta|^12` weights still returns the
worst-period coefficient.  This is the precise residual boundary: an improvement must exploit
relations among the period weights beyond their sign and orbit invariance. -/
theorem actualWeight_bound_from_worstPeriod
    (psi : AddChar F ℂ) (G : Finset F) (hG : IsMulSubgroup G) {S : ℝ}
    (hS : ∀ b, b ≠ 0 → ‖eta psi G b‖ ^ 2 ≤ S) :
    coneObjective psi G (depthSixWeight psi G) ≤
      spectralMass (depthSixWeight psi G) * (S / (G.card : ℝ)) := by
  exact coneObjective_le_of_period_bound psi G hG _
    (depthSixWeight_admissible psi G hG) rfl hS

#print axioms sum_translateCoefficient_mul_orbit_eq_normSq
#print axioms signedRestriction_spectralKernel_eq_coneObjective
#print axioms unitMass_cone_bound_iff_worst_period
#print axioms card_mul_coneObjective_depthSixWeight_eq_dcMoment
#print axioms actualWeight_bound_from_worstPeriod

end ArkLib.ProximityGap.Frontier.BGKCenteredTranslateConeDuality
