/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCenteredTranslateConeDuality

/-!
# The full Schur--Krein hierarchy does not shrink the centered spectral cone

This file tests the association-scheme refinement of the centered translate attack from
`_BGKCenteredTranslateConeDuality`.  The cyclotomic scheme is a translation scheme, so entrywise
(Schur) multiplication of translation kernels is additive convolution of their Fourier weights.
Consequently every nonnegative multiplicatively orbit-invariant spectrum is automatically closed
under **all** Schur powers: convolution preserves both nonnegativity and orbit invariance.

This is precisely the positivity content of the Krein hierarchy.  In a formally self-dual scheme,
intersection numbers and Krein parameters agree (Nomura--Terwilliger, arXiv:2405.10491); the
cyclotomic translation scheme is the self-dual case relevant here.  The result below is stronger
than checking finitely many scalar moments: it retains the complete frequency profile and every
iterated convolution coefficient.

## Verdict

The hierarchy is nevertheless automatic on the whole Fourier cone.  The single-orbit extremizer
from `_BGKCenteredTranslateConeDuality` survives every convolution power, so adding all Schur/Krein
positivity constraints to the unit-mass linear program leaves its optimum exactly the worst
Gaussian-period square.  Thus this refinement cannot provide the missing depth-seven saving.  A
successful use of the cyclotomic scheme must impose the **arithmetic values** of its intersection
numbers (equivalently the nonlinear period fixed point), not merely their nonnegativity.

At the production parameters, the generic valency bound `|eta_b| <= n` misses the repaired
fourteenth-moment target by strictly 191--192 bits.  By contrast the primitive depth-seven Wick
coefficient needs the much finer reduction `135135 -> 126871`, a saving between `6.115%` and
`6.116%`.  Positivity of every Schur power supplies no part of that saving.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKCyclotomicKreinSchurNoGo

open ArkLib.ProximityGap.Frontier.BGKCenteredTranslateConeDuality
open ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion (IsMulSubgroup)
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

/-! ## Additive convolution and the Fourier product identity -/

/-- Additive convolution of two functions on a finite additive group. -/
def additiveConvolution {F R : Type*} [AddCommGroup F] [Fintype F]
    [Semiring R] (w v : F → R) (b : F) : R :=
  ∑ a : F, w a * v (b - a)

/-- Fourier synthesis of a weight against an additive character. -/
def characterKernel {F R : Type*} [CommRing F] [Fintype F]
    [CommRing R] (psi : AddChar F R) (w : F → R) (x : F) : R :=
  ∑ b : F, w b * psi (b * x)

/-- **Schur/Fourier dictionary.** Pointwise multiplication of translation kernels is additive
convolution of their Fourier weights.  This is the exact algebraic operation whose nonnegative
structure constants are the Krein coefficients of a translation association scheme. -/
theorem characterKernel_additiveConvolution {F R : Type*}
    [CommRing F] [Fintype F] [CommRing R]
    (psi : AddChar F R) (w v : F → R) (x : F) :
    characterKernel psi (additiveConvolution w v) x =
      characterKernel psi w x * characterKernel psi v x := by
  classical
  unfold characterKernel additiveConvolution
  calc
    (∑ b : F, (∑ a : F, w a * v (b - a)) * psi (b * x)) =
        ∑ b : F, ∑ a : F, w a * v (b - a) * psi (b * x) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
    _ = ∑ a : F, ∑ b : F, w a * v (b - a) * psi (b * x) := by
      rw [Finset.sum_comm]
    _ =
        ∑ a : F, ∑ c : F, w a * v c * psi ((a + c) * x) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      symm
      exact Fintype.sum_equiv (Equiv.addLeft a)
        (fun c => w a * v c * psi ((a + c) * x))
        (fun b => w a * v (b - a) * psi (b * x)) (fun c => by simp)
    _ = ∑ a : F, ∑ c : F, (w a * psi (a * x)) * (v c * psi (c * x)) := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
      rw [show (a + c) * x = a * x + c * x by ring, AddChar.map_add_eq_mul]
      ring
    _ = (∑ a : F, w a * psi (a * x)) * ∑ c : F, v c * psi (c * x) := by
      rw [Finset.sum_mul_sum]

/-! ## The all-orders Krein cone -/

/-- Nonnegative Fourier weights invariant on multiplicative `G`-orbits.  Unlike
`OrbitSpectralWeight`, no zero-DC condition is imposed: Schur products can recreate DC mass. -/
structure OrbitKreinWeight {F : Type*} [Field F] [Fintype F]
    (G : Finset F) (w : F → ℝ) : Prop where
  nonneg : ∀ b, 0 ≤ w b
  invariant : ∀ g ∈ G, ∀ b, w (g * b) = w b

/-- A zero-DC orbit spectral weight is, after forgetting DC, an admissible Krein weight. -/
theorem orbitSpectralWeight_toOrbitKreinWeight
    {F : Type*} [Field F] [Fintype F]
    {G : Finset F} {w : F → ℝ} (hw : OrbitSpectralWeight G w) :
    OrbitKreinWeight G w :=
  ⟨hw.nonneg, hw.invariant⟩

/-- Convolution of nonnegative weights remains nonnegative. -/
theorem additiveConvolution_nonneg {F : Type*} [AddCommGroup F] [Fintype F]
    (w v : F → ℝ) (hw : ∀ b, 0 ≤ w b) (hv : ∀ b, 0 ≤ v b) (b : F) :
    0 ≤ additiveConvolution w v b := by
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (hv (b - a)))

/-- Multiplicative orbit invariance is preserved by additive convolution. -/
theorem additiveConvolution_invariant
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hG : IsMulSubgroup G)
    (w v : F → ℝ) (hw : OrbitKreinWeight G w) (hv : OrbitKreinWeight G v)
    {g : F} (hg : g ∈ G) (b : F) :
    additiveConvolution w v (g * b) = additiveConvolution w v b := by
  have hg0 : g ≠ 0 := by
    intro h
    exact zero_not_mem G hG (h ▸ hg)
  unfold additiveConvolution
  calc
    (∑ a : F, w a * v (g * b - a)) =
        ∑ a : F, w (g * a) * v (g * b - g * a) := by
      exact (Fintype.sum_equiv (Equiv.mulLeft₀ g hg0)
        (fun a => w (g * a) * v (g * b - g * a))
        (fun a => w a * v (g * b - a)) (fun _ => rfl)).symm
    _ = ∑ a : F, w a * v (b - a) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hw.invariant g hg a]
      have harg : g * b - g * a = g * (b - a) := by ring
      rw [harg, hv.invariant g hg (b - a)]

/-- The orbit Krein cone is closed under convolution, hence under Schur multiplication of the
corresponding translation kernels. -/
theorem OrbitKreinWeight.convolution
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hG : IsMulSubgroup G)
    {w v : F → ℝ} (hw : OrbitKreinWeight G w) (hv : OrbitKreinWeight G v) :
    OrbitKreinWeight G (additiveConvolution w v) := by
  refine ⟨additiveConvolution_nonneg w v hw.nonneg hv.nonneg, ?_⟩
  intro g hg b
  exact additiveConvolution_invariant G hG w v hw hv hg b

/-- Iterated convolution, with exponent `r+1` at index `r`. -/
def convolutionIter {F R : Type*} [AddCommGroup F] [Fintype F]
    [Semiring R] (w : F → R) : Nat → F → R
  | 0 => w
  | r + 1 => additiveConvolution (convolutionIter w r) w

/-- Every convolution power of an orbit Krein weight remains in the cone. -/
theorem convolutionIter_admissible
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hG : IsMulSubgroup G)
    {w : F → ℝ} (hw : OrbitKreinWeight G w) :
    ∀ r, OrbitKreinWeight G (convolutionIter w r) := by
  intro r
  induction r with
  | zero => exact hw
  | succ r ihr =>
      exact ihr.convolution G hG hw

/-- On the kernel side, iterated convolution is exactly an iterated Schur power. -/
theorem characterKernel_convolutionIter {F R : Type*}
    [CommRing F] [Fintype F] [CommRing R]
    (psi : AddChar F R) (w : F → R) (x : F) :
    ∀ r, characterKernel psi (convolutionIter w r) x =
      characterKernel psi w x ^ (r + 1) := by
  intro r
  induction r with
  | zero => simp [convolutionIter]
  | succ r ihr =>
      calc
        characterKernel psi (convolutionIter w (Nat.succ r)) x =
            characterKernel psi (convolutionIter w r) x * characterKernel psi w x := by
          rw [convolutionIter, characterKernel_additiveConvolution]
        _ = characterKernel psi w x ^ (r + 1) * characterKernel psi w x := by rw [ihr]
        _ = characterKernel psi w x ^ ((r + 1) + 1) := (pow_succ _ (r + 1)).symm
        _ = characterKernel psi w x ^ (Nat.succ r + 1) := by rfl

/-- Having every Schur/Krein power admissible is automatic for every point of the original
zero-DC orbit spectral cone. -/
theorem all_krein_powers_of_orbitSpectralWeight
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hG : IsMulSubgroup G)
    {w : F → ℝ} (hw : OrbitSpectralWeight G w) :
    ∀ r, OrbitKreinWeight G (convolutionIter w r) :=
  convolutionIter_admissible G hG (orbitSpectralWeight_toOrbitKreinWeight hw)

/-! ## The all-Krein LP is still exactly the worst-period problem -/

/-- **All-orders Krein no-go.** Adding admissibility of every Schur power to the unit-mass
centered-translate LP does not change its feasible optimum.  The reverse direction is witnessed by
the same single-orbit weight as before, and that weight passes the complete Krein hierarchy by the
preceding theorem. -/
theorem allKrein_unitMass_cone_bound_iff_worst_period
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (psi : AddChar F ℂ) (G : Finset F) (hG : IsMulSubgroup G) (S : ℝ) :
    (∀ w : F → ℝ, OrbitSpectralWeight G w →
        (∀ r, OrbitKreinWeight G (convolutionIter w r)) →
        spectralMass w = 1 →
        signedRestriction G (spectralKernel psi w) ≤ S / (G.card : ℝ)) ↔
      ∀ b, b ≠ 0 → ‖eta psi G b‖ ^ 2 ≤ S := by
  constructor
  · intro hall b hb
    let w := orbitWeight G b 1
    have hw : OrbitSpectralWeight G w := orbitWeight_admissible G hG hb (by norm_num)
    have hpow : ∀ r, OrbitKreinWeight G (convolutionIter w r) :=
      all_krein_powers_of_orbitSpectralWeight G hG hw
    have hmass : spectralMass w = 1 := spectralMass_orbitWeight G hG hb 1
    have hobj := hall w hw hpow hmass
    rw [signedRestriction_spectralKernel_eq_coneObjective psi G hG w hw,
      coneObjective_orbitWeight psi G hG hb 1] at hobj
    have hnpos : (0 : ℝ) < G.card := card_pos_real G hG
    simpa [div_le_div_iff_of_pos_right hnpos] using hobj
  · intro hperiod w hw _ hmass
    rw [signedRestriction_spectralKernel_eq_coneObjective psi G hG w hw]
    simpa using coneObjective_le_of_period_bound psi G hG w hw hmass hperiod

/-! ## Production-scale quantitative verdict -/

/-- Production subgroup size. -/
def productionN : Nat := 2 ^ 30

/-- Number of nonzero multiplicative orbits. -/
def productionM : Nat := 2 ^ 128 + 192

/-- Production field cardinality. -/
def productionQ : Nat := productionN * productionM + 1

/-- Fourteenth-moment ceiling obtained only from the valency bound `|eta_b| <= n`. -/
def productionValencyFourteenthCeiling : Nat :=
  (productionQ - 1) * productionN ^ 14

/-- The repaired public fourteenth-moment target. -/
def productionFourteenthTarget : Nat :=
  productionQ * 2 ^ 18 * productionN ^ 7

/-- The all-Krein cone plus the generic valency bound remains between 191 and 192 bits above the
production target.  Thus an all-orders positivity LP is enormously too weak before the delicate
primitive coefficient saving is even considered. -/
theorem production_valency_ceiling_gap :
    2 ^ 191 * productionFourteenthTarget < productionValencyFourteenthCeiling ∧
      productionValencyFourteenthCeiling < 2 ^ 192 * productionFourteenthTarget := by
  norm_num [productionFourteenthTarget, productionValencyFourteenthCeiling,
    productionQ, productionM, productionN]

/-- Exact primitive depth-seven coefficient deficit. -/
theorem primitive_depthSeven_exact_gap : (135135 : Nat) - 126871 = 8264 := by
  norm_num

/-- The required primitive saving is strictly between `6.115%` and `6.116%`. -/
theorem primitive_depthSeven_saving_window :
    6115 * 135135 < 100000 * 8264 ∧ 100000 * 8264 < 6116 * 135135 := by
  norm_num

/-- Consolidated boundary: all Schur powers are automatically Krein-admissible, while the
production-scale positivity/valency relaxation misses by 191--192 bits and therefore cannot force
the separate `6.115%` primitive saving. -/
theorem cyclotomic_krein_schur_boundary
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hG : IsMulSubgroup G)
    {w : F → ℝ} (hw : OrbitSpectralWeight G w) :
    (∀ r, OrbitKreinWeight G (convolutionIter w r)) ∧
      2 ^ 191 * productionFourteenthTarget < productionValencyFourteenthCeiling ∧
      6115 * 135135 < 100000 * 8264 := by
  exact ⟨all_krein_powers_of_orbitSpectralWeight G hG hw,
    production_valency_ceiling_gap.1, primitive_depthSeven_saving_window.1⟩

end ArkLib.ProximityGap.Frontier.BGKCyclotomicKreinSchurNoGo

/-! ## Axiom audit (expected: standard axioms only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCyclotomicKreinSchurNoGo.characterKernel_additiveConvolution
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCyclotomicKreinSchurNoGo.allKrein_unitMass_cone_bound_iff_worst_period
#print axioms
  ArkLib.ProximityGap.Frontier.BGKCyclotomicKreinSchurNoGo.cyclotomic_krein_schur_boundary
