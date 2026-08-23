/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The CUMULANT moment-method Gauss-period bound for the smooth domain (#407)

This file SHARPENS the moment-method consumer of `GaussPeriodMomentBound.lean` to the **tight**
identity, fixing a provable looseness that is exactly the content of the in-tree
`docs/kb/deltastar-cumulant-not-moment-2026-06-13.md` note ("the prize is a cumulant, not a
moment").

## The looseness, and the fix

`GaussPeriodMomentBound.eta_pow_le_of_energyBound` bounds a single far period by the **full** moment
`‖η_b‖^{2r} ≤ ∑_{b'} ‖η_{b'}‖^{2r} = q·E_r(G)` — which **includes the principal term**
`‖η_0‖^{2r} = |G|^{2r}`.  The cumulant note proves that in characteristic `p` the energy is
DOMINATED by exactly this principal/equidistribution mass for `r > log_n p`
(`E_r ≈ |G|^{2r}/q`), so the named input `GaussianEnergyBound : E_r ≤ (2r-1)‼·|G|^r` is
**provably false** past `r ≈ log_n p` — precisely the regime the prize needs (`r ≈ ln q`).

The fix is to subtract the principal term and bound the worst FAR period by the **cumulant**

  `∑_{b ≠ 0} ‖η_b‖^{2r}  =  q·E_r(G) − |G|^{2r}`   (`cumulant_eq`),

whose Wick bound `CumulantEnergyBound : ∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r` is the genuinely-open
object.  The principal `|G|^{2r}` cancels — the prize is the *connected/cumulant* part, never the
raw moment.

## What is proven here (axiom-clean)

* `cumulant_eq` — the exact cumulant identity (principal term subtracted).
* `eta_pow_le_of_cumulantBound` — the tight single-frequency bound from the cumulant input.
* `worstCaseIncompleteSumBound_of_cumulantBound` — discharges the in-tree open residual
  `WorstCaseIncompleteSumBound` at the SAME scale `M_r = (q·(2r-1)‼·|G|^r)^{1/r}` as the
  raw-moment consumer, but from the tight (genuinely-open) cumulant input.  Minimising over `r`
  (optimum `r* ≈ ln q`) still gives `B ≤ √(2 n ln q)`.
* `cumulantBound_iff_random_plus_diagonal` — the cumulant bound is EXACTLY the "random + diagonal"
  energy budget `E_r ≤ (2r-1)‼·|G|^r + |G|^{2r}/q`, with the random baseline `|G|^{2r}/q`
  identified as the (subtracted) principal contribution.  This makes the abstract `random`/`diag`
  split of `Frontier/_ConstantIndexMomentGate.lean` concrete.
* `cumulantBound_of_gaussianEnergyBound` — the raw `GaussianEnergyBound` is STRICTLY STRONGER; the
  cumulant form is the honest weakest input that still drives the bound.
* `not_cumulantBound_of_excess` — the falsification hook: a measured cumulant excess (e.g. the
  Fermat prime `p = 65537`, `n = 64`, where `(1/p)∑_{b≠0}‖η_b‖^{10} ≈ 29·(9‼)·n^5`, probe
  `scripts/probes/probe_cumulant_generic.py`) refutes `CumulantEnergyBound` at that `r`.  So the
  cumulant bound is necessarily CONDITIONAL on an explicit genericity hypothesis on `p` — it holds
  generically and is refuted at the 2-power-structured primes.

**Honest scope.**  This does NOT close the prize: the cumulant bound for `r ≈ ln q` is the
recognized open core (second-order equidistribution of the Gauss-period family = Paley-graph /
BGK).  The contribution is to (1) name the *correct* open object (cumulant, not raw moment),
(2) prove the tight consumer feeding it into δ\*, and (3) record that the bound is provably
non-uniform (Fermat-refuted), so any pin must be conditioned on a checkable genericity invariant of
`p`.  Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.CumulantGaussPeriodBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The principal frequency.** `η_0 = ∑_{y∈G} ψ(0·y) = ∑_{y∈G} 1 = |G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  unfold eta
  simp [AddChar.map_zero_eq_one]

/-- **The cumulant identity (#407).** The far-frequency mass is the full `2r`-th moment with the
principal term removed:
  `∑_{b ≠ 0} ‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}`.
The prize quantity `max_{b≠0}‖η_b‖` is controlled by this connected/cumulant part; the principal
`|G|^{2r}` is exactly the equidistribution mass that dominates the raw moment and CANCELS here. -/
theorem cumulant_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)), subgroup_gaussSum_moment hψ G r]
  congr 1
  rw [eta_zero, Complex.norm_natCast]

/-- **The cumulant energy bound** — the genuinely-open prize input at order `r`: the far-frequency
mass is bounded by the real-Gaussian (Wick) value,
  `∑_{b ≠ 0} ‖η_b‖^{2r} = q·E_r − |G|^{2r} ≤ q·(2r-1)‼·|G|^r`.
Weaker than `GaussianEnergyBound` (which omits the `−|G|^{2r}` subtraction); this is the honest
weakest input that still drives the per-frequency bound, and the one the numerics support
generically (`probe_cumulant_generic.py`). -/
def CumulantEnergyBound (G : Finset F) (r : ℕ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)

/-- **Tight single-frequency bound from the cumulant input.** For every FAR frequency `b ≠ 0`,
`‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r`.  Proof: a single far term is `≤` the cumulant `∑_{b'≠0}`, then
apply `CumulantEnergyBound`.  (Sharper than `eta_pow_le_of_energyBound`, which bounds by the full
moment including the principal term.) -/
theorem eta_pow_le_of_cumulantBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (h : CumulantEnergyBound G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  have hmem : b ∈ Finset.univ.erase (0 : F) := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hterm : ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ b' ∈ Finset.univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) hmem
  rw [cumulant_eq hψ G r] at hterm
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := hterm
    _ ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := h
    _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by ring

/-- **Bridge to the in-tree open residual (cumulant form).** `CumulantEnergyBound` at order `r ≥ 1`
discharges `WorstCaseIncompleteSumBound` at the SAME scale
`M_r = (q·(2r-1)‼·|G|^r)^{1/r}` as the raw-moment consumer
(`GaussPeriodMomentBound.worstCaseIncompleteSumBound_of_energyBound`), but from the tight,
genuinely-open cumulant input.  Minimising `M_r` over `r` (optimum `r* ≈ ln q`) yields the
`√(2 n ln q)` per-frequency target. -/
theorem worstCaseIncompleteSumBound_of_cumulantBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r) (h : CumulantEnergyBound G r) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        ^ ((r : ℝ)⁻¹)) := by
  intro b hb
  set X : ℝ := (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
    with hX
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]; exact eta_pow_le_of_cumulantBound hψ h hb
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- **The cumulant bound is the "diagonal + principal" energy budget, made concrete.**
`CumulantEnergyBound G r` ⟺ `q·E_r(G) ≤ q·(2r-1)‼·|G|^r + |G|^{2r}`, i.e. the energy is bounded by
the real-Gaussian (diagonal) value PLUS the principal term `|G|^{2r}` (`= q · |G|^{2r}/q`, the
random/equidistribution baseline that the moment method must subtract).  This pins the abstract
`random`/`diag` split of `Frontier/_ConstantIndexMomentGate.lean`: `random` is the principal
`|G|^{2r}/q` and `diag` is `(2r-1)‼·|G|^r`.  Division-free form for robustness. -/
theorem cumulantBound_iff_le_diag_add_principal {G : Finset F} {r : ℕ} :
    CumulantEnergyBound G r ↔
      (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
        ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          + (G.card : ℝ) ^ (2 * r) := by
  unfold CumulantEnergyBound
  rw [sub_le_iff_le_add]

/-- **The raw Gaussian energy bound is strictly stronger.** `GaussianEnergyBound` (no subtraction)
implies `CumulantEnergyBound` (it subtracts the nonnegative `|G|^{2r}`).  So the cumulant form is
the honest weakest input — the raw bound, known false past `r ≈ log_n p`, is not needed. -/
theorem cumulantBound_of_gaussianEnergyBound {G : Finset F} {r : ℕ}
    (h : GaussianEnergyBound G r) :
    CumulantEnergyBound G r := by
  unfold CumulantEnergyBound GaussianEnergyBound at *
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hscaled : (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
    mul_le_mul_of_nonneg_left h hq
  have hsubnn : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
  linarith

/-- **Falsification hook (#407).** A measured cumulant excess over the Wick value at some order `r`
refutes `CumulantEnergyBound` at that `r`.  Instantiated by the structured-prime probe
(`probe_cumulant_generic.py`): at the Fermat prime `p = 65537`, `n = 64`, the cumulant
`(1/p)∑_{b≠0}‖η_b‖^{2r}` exceeds `(2r-1)‼·n^r` by factors `1.6, 3.9, 10.8, 29, …` at `r = 2..5`.
Hence the cumulant bound is provably NON-uniform: it holds generically and is refuted at the
2-power-structured primes, so any δ\* pin must be conditioned on an explicit genericity invariant
of `p`. -/
theorem not_cumulantBound_of_excess {G : Finset F} {r : ℕ}
    (hbad : (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        < (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) :
    ¬ CumulantEnergyBound G r := by
  unfold CumulantEnergyBound
  exact not_le_of_gt hbad

end ArkLib.ProximityGap.CumulantGaussPeriodBound

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.CumulantGaussPeriodBound.cumulant_eq
#print axioms ArkLib.ProximityGap.CumulantGaussPeriodBound.eta_pow_le_of_cumulantBound
#print axioms ArkLib.ProximityGap.CumulantGaussPeriodBound.worstCaseIncompleteSumBound_of_cumulantBound
#print axioms ArkLib.ProximityGap.CumulantGaussPeriodBound.cumulantBound_iff_le_diag_add_principal
#print axioms ArkLib.ProximityGap.CumulantGaussPeriodBound.cumulantBound_of_gaussianEnergyBound
#print axioms ArkLib.ProximityGap.CumulantGaussPeriodBound.not_cumulantBound_of_excess
