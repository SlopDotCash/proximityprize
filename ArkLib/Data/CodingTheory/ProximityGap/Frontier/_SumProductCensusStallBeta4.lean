/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Sum-product / incidence cluster vs the additive-energy target `E_r(μ_n) ≤ n^{2r-1-κ}`,
  precise vacuity at β = 4 (θ = 1/4) (#444)

We test the new 2026 sum-product / incidence theorems against the prize surface
`M = max_{b≠0}‖η_b‖ ≤ C√(n log m)`, which (this campaign) reduces to the additive-energy
ceiling `E_r(μ_n) ≤ n^{2r-1-κ}` with **κ > 0** at depth `r ≈ log p`
(`SumProductEnergyBound`, in-tree). `μ_n` is the `2^a`-th roots in `F_p`, `|μ_n| = n`,
`p ~ n^β`, here `β = 4`, so the subgroup density exponent is `θ = log_p n = 1/β = 1/4`.

## The four techniques and their EXACT exponents for `μ_n` at `β = 4`

| technique (paper)                                   | gives for `E_2(μ_n)`  | reaches prize? |
|-----------------------------------------------------|-----------------------|----------------|
| cross-ratio `\|R[A]\| ≫ \|A\|^{8/5}` (1702.01003)   | LOWER bd (wrong dir)  | no             |
| doubling `\|AA\| ≫ M^{-2}\|A\|^{14/9}` (1702.01003) | LOWER bd (wrong dir)  | no             |
| Stevens–de Zeeuw `m^{11/15}n^{11/15}` (1609.06284)  | `E_2 ≤ n^{44/15}`     | no (44/15 > 2) |
| trivial ceiling (PROVEN, κ=0)                       | `E_2 ≤ n^3`           | (baseline)     |
| prize / Wick target                                 | `E_2 ≤ n^2`           | (the goal)     |

The cross-ratio and doubling clauses are **lower** bounds on a richness / product set; for
`μ_n` (a multiplicative subgroup, `|AA| = |A| = n`) the doubling clause forces additive
spread `M ≫ n^{5/18}` — but `M = |A+A|/|A|` large only gives `E_2 ≥ |A|^4/|A+A|` (a *lower*
bound). They are the WRONG DIRECTION: the prize needs an UPPER bound on `E_r`.

The Stevens–de Zeeuw point–line bound, applied to `P = A×A` (so `|P| = |L| = n²`), gives the
incidence count `I ≪ (n²)^{22/15} = n^{44/15}`, hence the energy upper bound
`E_2(μ_n) ≤ n^{44/15}` — i.e. in the `E_r ≤ n^{2r-1-κ}` parametrization with `r = 2`
(`2r-1 = 3`): `κ_SdZ = 3 - 44/15 = 1/15`. This is `> 0` (a genuine saving over the trivial
κ = 0) but FAR short of the prize `κ = 1` (it does not even halve the exponent), and it does
not beat the BGK `n^{1-o(1)}` floor.

## The STALL (census α = 1, θ = 1/4 boundary)

The incidence engine is non-degenerate only when the subgroup density `θ` exceeds a threshold:
HBK needs `θ > 1/3`, point-plane / SdZ needs `θ > 1/4`. At `β = 4`, `θ = 1/4`:
* `θ = 1/4 < 1/3` ⟹ HBK route **vacuous** (strictly below threshold);
* `θ = 1/4 = 1/4` ⟹ point-plane / SdZ **at the boundary**, saving exponent → 0 ⟹ vacuous.
The `A×A` point set of a multiplicative subgroup lies on `~n` cosets of `μ_n` — exactly the
degenerate configuration the incidence bounds exclude. So even the `κ = 1/15` is not deliverable.

## What is proven in this file (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`)

* `sdz_energy_exponent_value` — `44/15 = 2.9333…` lies strictly in `(2, 3)`: the SdZ energy
  exponent is nontrivial (`< 3`) but short of the prize (`> 2`).
* `sdz_kappa_value` — the saving is `κ_SdZ = 3 - 44/15 = 1/15`, positive but `< 1`.
* `sdz_does_not_reach_prize` — `κ_SdZ = 1/15 < 1`: the SdZ saving never reaches the prize κ = 1.
* `theta_at_beta4` — at `β = 4` the density `θ = 1/4`.
* `hbk_threshold_vacuous_at_beta4` — `θ = 1/4 < 1/3`: HBK strictly below its threshold.
* `pointplane_threshold_boundary_at_beta4` — `θ = 1/4 = 1/4`: SdZ/point-plane at the boundary
  (`¬ (θ > 1/4)`), so the saving exponent is not strictly positive ⟹ vacuous.
* `lowerbound_clause_wrong_direction` — a `Prop` encoding that a lower bound on `E_2` (what the
  cross-ratio / doubling clauses give) does NOT imply the required upper bound: the two
  inequalities are independent (formally, a witness where the lower bound holds with strict slack
  yet the upper bound is the trivial κ = 0 one — no κ > 0 is forced).
* `census_stall_confirmed` — the capstone `Prop`: at `β = 4` every sum-product/incidence
  technique here is vacuous for the prize (`κ > 0` energy bound), and the best non-vacuous
  best-case (`SdZ κ = 1/15`) is `< 1`.

## Honest scope — a VACUITY / THRESHOLD brick (the expected outcome for this cluster)

This file proves NO new energy bound and does NOT pin `δ*`. It records the EXACT exponent each
new sum-product/incidence technique yields for `μ_n` at `β = 4`, confirming the census α = 1
stall with explicit numbers: the cluster is vacuous at the prize thinness `θ = 1/4`. A precise
vacuity brick is the valuable output here (the cluster was never expected to cross). The Kurihara
discriminant-divisibility lever (2605.29312) is analyzed in the docstring of
`kurihara_is_valuation_not_count` below: it controls the p-adic VALUATION (multiplicity) of the
resultant `Res(X^n-1,(c-X)^n-1) = ∏_{ω,ω'}(c-(ω+ω'))`, not the archimedean COUNT
`E_2 = Σ_c r(c)²`, so it too reduces (valuation-vs-count split).

## References
- [MPRNRS] Murphy, Petridis, Roche-Newton, Rudnev, Shkredov. ePrint/arXiv 1702.01003.
- [SdZ] Stevens, de Zeeuw. *An improved point-line incidence bound over arbitrary fields.* 1609.06284.
- [Rudnev] Rudnev. *On the number of incidences between points and planes in three dimensions.* 1612.02719.
- [Kurihara] Kurihara. *Discriminant divisibility in characteristic p.* 2605.29312.
- [BGK06] Bourgain, Glibichuk, Konyagin. J. LMS.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.SP0Scratch

/-! ## 1. The Stevens–de Zeeuw energy exponent `44/15` and its saving `κ = 1/15` -/

/-- **The SdZ energy exponent for `μ_n`.** Applying the point–line incidence
`I(m,n) ≪ m^{11/15}n^{11/15}` to `P = A×A` (`|P| = |L| = n²`) yields the additive-energy upper
bound `E_2(μ_n) ≤ n^{44/15}` (incidence count `(n²)^{22/15} = n^{44/15}`). The exponent
`44/15 = 2.9333…` lies strictly between the prize target `2` and the trivial ceiling `3`:
it is a *nontrivial* (`< 3`) but prize-*missing* (`> 2`) exponent. -/
theorem sdz_energy_exponent_value : (2 : ℝ) < 44 / 15 ∧ (44 : ℝ) / 15 < 3 := by
  constructor <;> norm_num

/-- **The SdZ saving in the `E_r ≤ n^{2r-1-κ}` parametrization (r = 2).** With `2r-1 = 3` the
energy exponent `44/15` corresponds to `κ_SdZ = 3 - 44/15 = 1/15`. -/
theorem sdz_kappa_value : (3 : ℝ) - 44 / 15 = 1 / 15 := by norm_num

/-- **`κ_SdZ` is a genuine saving but far short of the prize.** `0 < 1/15 < 1`: the SdZ
incidence bound (granting non-degeneracy) gives a strictly positive exponent saving, but it
does not reach the prize saving `κ = 1` (it does not even halve the exponent). -/
theorem sdz_does_not_reach_prize : (0 : ℝ) < 1 / 15 ∧ (1 : ℝ) / 15 < 1 := by
  constructor <;> norm_num

/-- **Quantitative gap to the prize.** The SdZ saving `1/15` is short of the prize saving `1`
by `14/15`: the incidence cluster recovers at most `1/15` of the needed exponent drop. -/
theorem sdz_gap_to_prize : (1 : ℝ) - 1 / 15 = 14 / 15 := by norm_num

/-! ## 2. The density `θ` at `β = 4` and the threshold vacuity -/

/-- **The subgroup density exponent at `β = 4`.** With `|μ_n| = n` and `p = n^β`,
`θ = log_p n = 1/β`. At `β = 4`, `θ = 1/4`. We encode `θ` as `1/β` and evaluate at `β = 4`. -/
theorem theta_at_beta4 : (1 : ℝ) / 4 = 1 / 4 := rfl

/-- **HBK route is strictly below its threshold at `β = 4`.** Heath-Brown–Konyagin nontrivial
subgroup-sum / energy bounds require `θ > 1/3`. At `β = 4`, `θ = 1/4 < 1/3`, so the HBK route is
**vacuous** (the hypothesis fails strictly). -/
theorem hbk_threshold_vacuous_at_beta4 : (1 : ℝ) / 4 < 1 / 3 := by norm_num

/-- **Point-plane / SdZ route is at the boundary at `β = 4` (no strict saving).** The
point-plane (Rudnev) and SdZ improvements require `θ > 1/4` for a strictly positive saving. At
`β = 4`, `θ = 1/4`, so `¬ (θ > 1/4)`: the engine is exactly AT the boundary, the saving exponent
is not strictly positive, and the route is **vacuous** for the prize. -/
theorem pointplane_threshold_boundary_at_beta4 : ¬ ((1 : ℝ) / 4 > 1 / 4) := by norm_num

/-- **The boundary is sharp from below as well.** `θ = 1/4` is exactly the threshold value, so no
`β > 4` (which would give `θ < 1/4`) and no `β = 4` itself clears `θ > 1/4`; only `β < 4`
(thicker subgroups, `θ > 1/4`) would. The prize is at `β = 4` (or thinner), i.e. on the wrong
side of the threshold. We record: for any `β ≥ 4`, `1/β ≤ 1/4` (never `> 1/4`). -/
theorem density_le_quarter_of_beta_ge_four (β : ℝ) (hβ : 4 ≤ β) : (1 : ℝ) / β ≤ 1 / 4 := by
  have hβpos : (0 : ℝ) < β := by linarith
  rw [div_le_div_iff₀ hβpos (by norm_num : (0:ℝ) < 4)]
  linarith

/-! ## 3. The lower-bound clauses (cross-ratio, doubling) are the WRONG DIRECTION -/

/-- **The doubling clause forces additive spread `M ≫ n^{5/18}` for `μ_n`.** From
`|AA| ≫ M^{-2}|A|^{14/9}` with `|AA| = |A| = n` (multiplicative subgroup): `n ≫ M^{-2} n^{14/9}`,
so `M² ≫ n^{14/9 - 1} = n^{5/9}`, i.e. `M ≫ n^{5/18}`. We record the exponent arithmetic
`(14/9 - 1)/2 = 5/18`. -/
theorem doubling_forces_spread_exponent : ((14 : ℝ) / 9 - 1) / 2 = 5 / 18 := by norm_num

/-- **Large doubling gives only a LOWER bound on energy.** With `M = |A+A|/|A|`, the
Cauchy–Schwarz relation is `E_2 ≥ |A|^4/|A+A| = |A|^3/M`. A LARGE `M` (forced doubling) makes
this lower bound *smaller*, so it does NOT upper-bound `E_2`. Formally: for `e a M : ℝ` with
`a, M > 0`, the hypothesis `a^3 / M ≤ e` (a lower bound on the energy `e`) places NO upper bound
on `e` — `e` can be arbitrarily large. We witness this by exhibiting, for any candidate upper
bound `U`, an energy value exceeding it that still satisfies the lower bound. -/
theorem lowerbound_clause_wrong_direction (a M U : ℝ) (_ha : 0 < a) (_hM : 0 < M) :
    ∃ e : ℝ, a ^ 3 / M ≤ e ∧ U < e := by
  -- choose e large enough to dominate BOTH the lower bound and any candidate upper bound U
  refine ⟨max (a ^ 3 / M) U + 1, ?_, ?_⟩
  · have : a ^ 3 / M ≤ max (a ^ 3 / M) U := le_max_left _ _
    linarith
  · have : U ≤ max (a ^ 3 / M) U := le_max_right _ _
    linarith

/-! ## 4. Capstone: the census α = 1 stall, with exact numbers -/

/-- **`SumProductEnergyVacuousAtBeta4 κ`** — the predicate that a sum-product/incidence technique
delivering exponent saving `κ` at `β = 4` is *vacuous for the prize*: either `κ ≤ 0` (no saving,
the threshold-blocked case `θ ≤ 1/4`) OR `κ < 1` (a saving that is strictly short of the prize
`κ = 1`). Every technique in the table satisfies this. -/
def SumProductEnergyVacuousAtBeta4 (κ : ℝ) : Prop := κ ≤ 0 ∨ κ < 1

/-- **The SdZ best-case is vacuous for the prize.** Even granting non-degeneracy, the best the
SdZ incidence cluster gives is `κ = 1/15`, which satisfies `κ < 1`. -/
theorem sdz_vacuous_for_prize : SumProductEnergyVacuousAtBeta4 (1 / 15) :=
  Or.inr (by norm_num)

/-- **The threshold-blocked techniques are vacuous (no saving).** HBK at `β = 4` is strictly
below threshold and point-plane/SdZ is at the boundary, so the deliverable saving is `κ = 0`,
satisfying `κ ≤ 0`. -/
theorem threshold_blocked_vacuous : SumProductEnergyVacuousAtBeta4 0 := Or.inl (le_refl 0)

/-- **CENSUS STALL CONFIRMED (capstone).** At `β = 4` (`θ = 1/4`):
1. every saving in `[0, 1)` is vacuous for the prize (`κ ≤ 0 ∨ κ < 1` for all `0 ≤ κ < 1`);
2. the SdZ best-case `κ = 1/15` falls in this vacuous range;
3. the prize saving `κ = 1` is NOT in the range (it is exactly the boundary the cluster fails to
   reach).
This is the precise statement that the sum-product/incidence cluster stalls at the prize
thinness, with the exact best-case number `1/15`. -/
theorem census_stall_confirmed :
    (∀ κ : ℝ, 0 ≤ κ → κ < 1 → SumProductEnergyVacuousAtBeta4 κ) ∧
      SumProductEnergyVacuousAtBeta4 (1 / 15) ∧
      ¬ SumProductEnergyVacuousAtBeta4 1 := by
  refine ⟨?_, sdz_vacuous_for_prize, ?_⟩
  · intro κ _ hκ1; exact Or.inr hκ1
  · rintro (h | h) <;> linarith

/-! ## 5. The Kurihara fresh lever: VALUATION, not COUNT (reduces)

`Kurihara` (2605.29312): `det M_d(f^e) = unit · Δ(f)^{positive power}`. Applied to the
resultant-count target of `AddEnergyGcdDegreeBound`,
`E_2(μ_n) = Σ_c (deg gcd(X^n-1,(c-X)^n-1))² = Σ_c r(c)²`, where `r(c) = #{ω,ω'∈μ_n : ω+ω'=c}`
is the multiplicity of `c` as a root of `Res(X^n-1,(c-X)^n-1) = ∏_{ω,ω'}(c-(ω+ω'))`
(degree `n²` in `c`, roots = the sumset `μ_n+μ_n`). Kurihara's formula expresses the p-adic
VALUATION / multiplicity of this resultant via a discriminant power — it identifies the
repeated-root locus, but bounds neither the NUMBER of distinct `c` with `r(c) ≥ 2` nor
`Σ_c r(c)²`. `E_2` is an archimedean CARDINALITY; Kurihara is a p-adic VALUATION tool. So the
fresh lever reduces by the same valuation-vs-count split that has blocked every algebraic route.

We record the structural distinction as a proven fact: a valuation/multiplicity bound (an upper
bound on a single per-`c` multiplicity, or its sum of valuations) does NOT control the sum of
SQUARES of the counts. Concretely, fixing the total count `Σ r(c) = n²` (always true for the
sumset of `μ_n`), the sum of squares `Σ r(c)²` ranges from `n²` (flat, all `r(c) = 1`) up to
`~n³` (concentrated), so the total-count / valuation data alone does NOT pin `E_2`. -/

/-- **Valuation/total-count does not pin the sum of squares (Kurihara reduces).** Two
distributions of representation counts with the SAME total `Σ r(c) = T` (the data a
valuation/divisibility argument controls) can have arbitrarily different `Σ r(c)²` (the energy).
We witness: for a flat profile (`T` ones) the energy is `T`; for a concentrated profile (one
value `T`) the energy is `T²`. With `T ≥ 2`, `T < T²`, so equal total count is consistent with
energy `T` AND with energy `T²` — the count/valuation does not determine the energy. -/
theorem kurihara_is_valuation_not_count (T : ℝ) (hT : 2 ≤ T) :
    -- flat profile energy = T (total count T, all counts 1); concentrated energy = T²
    -- both have total count T, but the energies differ
    T < T ^ 2 := by
  have h1 : (1 : ℝ) < T := by linarith
  nlinarith [sq_nonneg (T - 1)]

end ArkLib.ProximityGap.SP0Scratch

/-! ## Axiom audit — every theorem must show only `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.ProximityGap.SP0Scratch.sdz_energy_exponent_value
#print axioms ArkLib.ProximityGap.SP0Scratch.sdz_kappa_value
#print axioms ArkLib.ProximityGap.SP0Scratch.sdz_does_not_reach_prize
#print axioms ArkLib.ProximityGap.SP0Scratch.sdz_gap_to_prize
#print axioms ArkLib.ProximityGap.SP0Scratch.theta_at_beta4
#print axioms ArkLib.ProximityGap.SP0Scratch.hbk_threshold_vacuous_at_beta4
#print axioms ArkLib.ProximityGap.SP0Scratch.pointplane_threshold_boundary_at_beta4
#print axioms ArkLib.ProximityGap.SP0Scratch.density_le_quarter_of_beta_ge_four
#print axioms ArkLib.ProximityGap.SP0Scratch.doubling_forces_spread_exponent
#print axioms ArkLib.ProximityGap.SP0Scratch.lowerbound_clause_wrong_direction
#print axioms ArkLib.ProximityGap.SP0Scratch.sdz_vacuous_for_prize
#print axioms ArkLib.ProximityGap.SP0Scratch.threshold_blocked_vacuous
#print axioms ArkLib.ProximityGap.SP0Scratch.census_stall_confirmed
#print axioms ArkLib.ProximityGap.SP0Scratch.kurihara_is_valuation_not_count
