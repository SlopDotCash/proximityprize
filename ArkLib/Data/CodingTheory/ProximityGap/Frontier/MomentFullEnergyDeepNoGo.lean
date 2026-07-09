/-
# The FULL-energy moment hypothesis is PROVABLY FALSE at prize depth (#444)

The moment-method route to the Gauss-period house bound `M(μ_n) ≤ √(2n log q)` is in-tree via
`GaussPeriodMomentBound.eta_pow_le_of_energyBound`, whose hypothesis is

  `GaussianEnergyBound G r := rEnergy G r ≤ (2r−1)‼ · |G|^r`   (the FULL additive energy `E_r`).

This hypothesis is unsatisfiable at the prize once `r` passes the `b=0` crossover — conjecture-free.
The moment identity `∑_b ‖η_b‖^{2r} = q·rEnergy` (`subgroup_gaussSum_moment`) has a DC term
`b=0`, where `η_0 = ∑_{x∈G} ψ(0) = |G|`, contributing `|G|^{2r}`. Hence `q·rEnergy ≥ |G|^{2r}`
unconditionally, so `rEnergy ≥ |G|^{2r}/q`. Once `|G|^{2r}/q > (2r−1)‼·|G|^r`, i.e.
`|G|^r > q·(2r−1)‼`, the bound `rEnergy ≤ Wick` is impossible. At the prize (`|G|=2^30, q≈2^158`)
this holds for `r > 6.6`, violated by `≈ 2^{24r−158}` (`≈ 2^2458` at `r ≈ ln q ≈ 109`).

Consequence: any moment reduction whose hypothesis is the full-energy `GaussianEnergyBound` at depth
`r ≈ ln q` is **vacuous at the prize** (false antecedent). The house bound must instead use the
**reduced** energy `∑_{b≠0} ‖η_b‖^{2r} = q·rEnergy − |G|^{2r}` (in-tree `eta_pow_le_energyR`, which
subtracts the DC mass). Empirical `K_eff=(E_r/Wick)^{1/r}≈0.6` on the FULL `E_r` is
a finite-size illusion: at the small `|G|` where it is computable the crossover `r*` is unreached
(verified `r*=7` at n=64, `r*=10` at n=32; `_probe_444_b0_crossover_illusion.py`).

A no-go on a *formulation*, not on the prize: the house is well-behaved
(`house/√(2n ln m) ∈ [0.85,0.96]`); only the full-energy hypothesis is dead — use reduced energy.
Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`.
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.MomentFullEnergyDeepNoGo

open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

-- The `b=0` simp below legitimately needs `mul_one` (without it the goal `↑|G| * ψ 0 = ↑|G|` is
-- left unsolved); the `unusedSimpArgs` linter flags it as a false positive, so disable it locally.
set_option linter.unusedSimpArgs false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Unconditional DC lower bound on the full additive energy:** `|G|^{2r} ≤ q · rEnergy G r`.
The `b=0` term `η_0 = ∑_{x∈G} ψ(0) = |G|` alone contributes `|G|^{2r}` to the moment
`∑_b ‖η_b‖^{2r} = q·rEnergy` (`subgroup_gaussSum_moment`), giving an unconditional lower bound. -/
theorem card_pow_le_card_mul_rEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) :
    (G.card : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * rEnergy G r := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by
    simp only [eta, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hzero : ‖eta ψ G 0‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [h0, Complex.norm_natCast]
  have hsum : ‖eta ψ G 0‖ ^ (2 * r) ≤ ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) (fun i _ => by positivity)
      (Finset.mem_univ 0)
  rw [subgroup_gaussSum_moment hψ G r, hzero] at hsum
  exact hsum

/-- **The full-energy `GaussianEnergyBound` is FALSE past the `b=0` crossover depth.** If
`q·(2r−1)‼·|G|^r < |G|^{2r}` (the "deep" regime — prize `r>6.6`), then `GaussianEnergyBound`
cannot hold: the DC term forces `rEnergy ≥ |G|^{2r}/q > (2r−1)‼·|G|^r`. So a moment reduction whose
antecedent is the full-energy hypothesis at `r ≈ ln q` is vacuous at the prize; feed the house bound
the reduced energy `q·rEnergy − |G|^{2r}` instead. -/
theorem gaussianEnergyBound_false_of_deep {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ)
    (hdeep : (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      < (G.card : ℝ) ^ (2 * r)) :
    ¬ GaussianEnergyBound G r := by
  intro hGEB
  simp only [GaussianEnergyBound] at hGEB
  have hlb := card_pow_le_card_mul_rEnergy hψ G r
  have hub : (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
    mul_le_mul_of_nonneg_left hGEB (by positivity)
  linarith [hlb, hub, hdeep]

end ArkLib.ProximityGap.MomentFullEnergyDeepNoGo
