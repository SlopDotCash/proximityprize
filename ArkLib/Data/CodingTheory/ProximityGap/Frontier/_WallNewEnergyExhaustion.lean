/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466, lane W2)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BilinearDFTBeat

/-!
# The exact-energy exponent axis is exhausted at `8/9` good-prime / `n^{1−o(1)}` unconditional
  (#466, lane W2 — the analytic-wall SOTA frontier)

**Result (exponent bookkeeping, axiom-clean).** One more audit of the exact-`μ_n`-energy
landscape for the Gauss-sum sup-norm `M(n,p) = max_{a≠0}|Σ_{y∈μ_n} e_p(ay)|` at aspect
ratio `p = n^β`, `β = 4`, against the THREE candidate energy inputs the campaign's
additive-energy sweep does not isolate (`scripts/probes/probe_466_wall_newenergy.py` /
`_out_466_wall_newenergy.txt`, verified exactly on `F_p` data at `n = 8,16,32`, multiple
primes):

* **(C1) the multiplicative energy `E_×(μ_n) = n³`** — EXACT and UNCONDITIONAL (a subgroup
  has maximal, char-free multiplicative energy; verified `= n³` at every `(n,p)`). The
  additive character sum's `2r`-th moment identity `Σ_a|S(a)|^{2r} = p·T_r(μ_n)` contains
  NO multiplicative energy, so `E_×` feeds a sup-norm bound ONLY via a sum-product transfer
  `E_× = n³ ⟹ T_2 ≤ (bound)`. The sharpest UNCONDITIONAL subgroup transfers are exactly the
  campaign's "generic" menu: the single-application Heath-Brown–Konyagin `t₂ = 5/2` (which
  is **VACUOUS at `β = 4`** — it dies at `β = 3`, the `p^{1/3}` wall), and the MRSS/Rudnev
  point-plane best `t₂ = 49/20, t₃ = 4`, whose best output is the di Benedetto
  `2849/2880 = 1 − 31/2880 = 0.98924` — the SOTA EFFECTIVE unconditional, `n^{1−o(1)}` class.
  **No unconditional power-saving past BGK.**
* **(C2) the exact higher additive energies `T₄, T₆`** (char-0 Wick, good-prime) fed to a
  Rudnev point-line / point-plane finisher. A point-plane finisher IS the trilinear
  Petridis–Shparlinski shape already swept (dominated by the bilinear for `β < 17/3`); and
  among the symmetric bilinears at the LEGAL (mass-floor-forced) energy exponents, the
  optimum sits at fold order `m = β`, giving `7/8` — the family infimum — whose `t₄ = 4`
  good-prime supply is **DEAD** (`D₄` generic K-bad, round 8). Higher fold orders are
  strictly worse (`23/25` at `m=5`, `17/18` at `m=6`). **No gain past the landed `8/9`.**
* **(C3) the exact character second moment** `Σ_{b≠0}|η_b|² = pn − n²` (exact Parseval;
  verified). This is the Parseval FLOOR: it lower-bounds `M ≥ √(n − n²/p) ≈ √n` (in-tree
  `GaussPeriodParsevalFloor`) but its only sup UPPER bound is the trivial
  `M ≤ √(pn) = n^{(β+1)/2} = n^{5/2}`. **No sup-norm upper lever.**

## What is proven here vs named

The **exponent algebra is PROVEN axiom-clean** (exact rationals, plus one real-exponent
bridge welded to `_BilinearDFTBeat`): the symmetric-bilinear exponent law, the `k=β`
optimality among the lattice points, the family infimum `1 − 1/(2β)`, the legal-envelope
moment law `1 − 1/(2k)` and its monotonicity (infimum attained at `k=β`), the mult-energy
HBK vacuity at `β=4`, the unconditional-effective value `2849/2880` and its `n^{1−o(1)}`
placement, and the second-moment triviality. The **analytic content is NAMED** (the same
class as `_BilinearDFTBeat.Leg1PopularSumset` / `Leg2DFTFinisher`): the energy inputs `T_r`
themselves and the sum-product / DFT / incidence finishers live in the char-`p` files. This
file is a **cartography brick**: it prices each candidate and records that the exact-energy
exponent axis is CLOSED.

## ⚠️ Honest scope

* **No new exponent.** This is the SOTA-frontier *record*, not a beat: `8/9` good-prime
  (landed, `_BilinearDFTBeat`) and `n^{1−o(1)}` unconditional stand; the three candidate
  inputs do not move either. A partial result honestly scoped.
* **HIGH side of the BGK wall.** Every value here is `≥ 7/8 ≫ 1/2`; by
  `deltaStar_determination_all_or_nothing` a fixed power law cannot move δ*.
  `isPrizeClosure := false`.

Issue #466, dossier v3 §3 (SOTA table) / §6 (frontier). Axiom-clean
(`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real

namespace ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion

/-! ## The exponent engine (exact rationals)

The di Benedetto pipeline (`probe_466_dibenedetto_half.py`) with a symmetric bilinear
finisher `bilinear(m,m)`, energy exponent `t` at both legs, aspect ratio `β`:
`E = 4m − 2t` (the energy-sum), `κ = 2m²` (the Δ-collapse constant), and — when nonvacuous
(`E > β`) — final sup-norm exponent `θ = 1 − (E − β)/κ = 1 − (4m − 2t − β)/(2m²)`. -/

/-- The energy-sum of the symmetric bilinear finisher `bilinear(m,m)` at leg-energy `t`:
`E = 4m − 2t`. The bound is nonvacuous exactly when `E > β`. -/
def bilinearE (m t : ℚ) : ℚ := 4 * m - 2 * t

/-- The symmetric-bilinear sup-norm exponent `θ(m,t;β) = 1 − (4m − 2t − β)/(2m²)`
(valid where `bilinearE m t > β`). -/
def bilinearSymExp (β m t : ℚ) : ℚ := 1 - (4 * m - 2 * t - β) / (2 * m ^ 2)

/-- The bare moment-method exponent `θ = (β − 1 + t_k)/(2k)` at depth `k`, energy exp `t_k`. -/
def momentExp (β k tk : ℚ) : ℚ := (β - 1 + tk) / (2 * k)

/-- The Cauchy–Schwarz mass-floor LEGAL energy envelope `t_k ≥ max(k, 2k − β)`
(the char-`p` mean-count floor `T_k(μ_n) ≥ n^{2k}/p` forces `t_k ≥ 2k − β`; char-0 Wick
gives `t_k ≥ k`). -/
def legalEnergyExp (β k : ℚ) : ℚ := max k (2 * k - β)

/-- The di Benedetto method-family INFIMUM `1 − 1/(2β)` (over all legal inputs and finishers;
`probe_466_dibenedetto_half.py` (c')). -/
def familyInfimum (β : ℚ) : ℚ := 1 - 1 / (2 * β)

/-! ## The family infimum and the legal-envelope moment law -/

/-- **The family infimum at `β = 4` is `7/8`.** -/
theorem familyInfimum_beta4 : familyInfimum 4 = 7 / 8 := by
  unfold familyInfimum; norm_num

/-- **Legal-envelope moment law:** for depth `k ≥ β` the mass floor forces `t_k = 2k − β`,
and then the moment exponent collapses to `1 − 1/(2k)` (independent of `β`). -/
theorem momentExp_legal_of_ge (β k : ℚ) (hk : 0 < k) (h : β ≤ k) :
    momentExp β k (legalEnergyExp β k) = 1 - 1 / (2 * k) := by
  have hle : k ≤ 2 * k - β := by linarith
  have : legalEnergyExp β k = 2 * k - β := by
    unfold legalEnergyExp; exact max_eq_right hle
  rw [this]; unfold momentExp
  field_simp
  ring

/-- **The infimum is attained at `k = β` from above:** for `0 < β ≤ k` the legal-envelope
moment exponent `1 − 1/(2k)` is `≥` the family infimum `1 − 1/(2β)`, with equality iff `k = β`.
So over the mass-floor-legal depths the moment method cannot beat `1 − 1/(2β)`. -/
theorem momentExp_ge_familyInfimum (β k : ℚ) (hβ : 0 < β) (h : β ≤ k) :
    familyInfimum β ≤ momentExp β k (legalEnergyExp β k) := by
  have hk : 0 < k := lt_of_lt_of_le hβ h
  rw [momentExp_legal_of_ge β k hk h]
  unfold familyInfimum
  have h2β : 0 < 2 * β := by linarith
  have h2k : 0 < 2 * k := by linarith
  have : 1 / (2 * k) ≤ 1 / (2 * β) := by
    apply one_div_le_one_div_of_le h2β; linarith
  linarith

/-! ## (C2) Higher exact additive energies: `k = β` is the bilinear optimum -/

/-- The landed proven-input value: `bilinear(3,3)` at `t₃ = 3` gives `8/9`
(= `BilinearDFTBeat.bilinearTheta 4`). -/
theorem bilinearSymExp_33 : bilinearSymExp 4 3 3 = 8 / 9 := by
  unfold bilinearSymExp; norm_num

/-- The family infimum value: `bilinear(4,4)` at `t₄ = 4` (fold order `= β`) gives `7/8`
(the mass-floor optimum; `t₄ = 4` good-prime supply DEAD, `D₄` round 8). -/
theorem bilinearSymExp_44 : bilinearSymExp 4 4 4 = 7 / 8 := by
  unfold bilinearSymExp; norm_num

/-- `bilinear(5,5)` at the LEGAL `t₅ = max(5, 6) = 6` gives `23/25` — strictly WORSE. -/
theorem bilinearSymExp_55 : bilinearSymExp 4 5 6 = 23 / 25 := by
  unfold bilinearSymExp; norm_num

/-- `bilinear(6,6)` at the LEGAL `t₆ = max(6, 8) = 8` gives `17/18` — strictly WORSE. -/
theorem bilinearSymExp_66 : bilinearSymExp 4 6 8 = 17 / 18 := by
  unfold bilinearSymExp; norm_num

/-- The legal-envelope value used at each fold order is `max(m, 2m − β)`; at `β=4`:
`t₃=3, t₄=4, t₅=6, t₆=8` (the values above). -/
theorem legalEnergyExp_lattice_beta4 :
    legalEnergyExp 4 3 = 3 ∧ legalEnergyExp 4 4 = 4 ∧
    legalEnergyExp 4 5 = 6 ∧ legalEnergyExp 4 6 = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> · unfold legalEnergyExp; norm_num

/-- **`k = β = 4` is the symmetric-bilinear optimum** among the legal lattice points:
`7/8 < 8/9` (infimum below the landed value) and `8/9 < 23/25 < 17/18` (higher fold orders
strictly worse). The landed `8/9` is the best whose good-prime supply survives; `7/8` is the
unreachable floor. -/
theorem bilinear_k_eq_beta_optimal :
    bilinearSymExp 4 4 4 < bilinearSymExp 4 3 3 ∧
    bilinearSymExp 4 3 3 < bilinearSymExp 4 5 6 ∧
    bilinearSymExp 4 5 6 < bilinearSymExp 4 6 8 := by
  rw [bilinearSymExp_44, bilinearSymExp_33, bilinearSymExp_55, bilinearSymExp_66]
  norm_num

/-- The gap between the landed value and the aspirational floor is exactly `1/72`. -/
theorem landed_minus_infimum : bilinearSymExp 4 3 3 - familyInfimum 4 = 1 / 72 := by
  rw [bilinearSymExp_33, familyInfimum_beta4]; norm_num

/-! ## (C1) Multiplicative energy: unconditional, but only via sum-product -/

/-- **The direct Heath-Brown–Konyagin subgroup transfer `t₂ = 5/2` is VACUOUS at `β = 4`.**
The single-application bound `E_× = n³ ⟹ T₂ ≤ n^{5/2}` feeds `bilinear(2,2)` with energy-sum
`E = 4·2 − 2·(5/2) = 3`, and `3 < 4 = β`, so the bound is vacuous. It becomes nonvacuous
exactly for `β < 3` (the classical `H > p^{1/3}` Heath-Brown–Konyagin threshold). -/
theorem multEnergyHBK_E : bilinearE 2 (5 / 2) = 3 := by unfold bilinearE; norm_num

theorem multEnergyHBK_vacuous_at_beta4 : bilinearE 2 (5 / 2) < 4 := by
  rw [multEnergyHBK_E]; norm_num

/-- The HBK route is nonvacuous exactly for `β < 3` (`E = 3 > β ⟺ β < 3`). -/
theorem multEnergyHBK_nonvacuous_iff (β : ℚ) : β < bilinearE 2 (5 / 2) ↔ β < 3 := by
  rw [multEnergyHBK_E]

/-- **The best UNCONDITIONAL sum-product output at `β = 4` (the multiplicative energy's
sharpest transfer, MRSS/Rudnev `t₂ = 49/20, t₃ = 4`) is the di Benedetto
`2849/2880 = 1 − 31/2880`** — the SOTA EFFECTIVE unconditional exponent. -/
def unconditionalEffectiveExp : ℚ := 2849 / 2880

theorem unconditionalEffectiveExp_eq : unconditionalEffectiveExp = 1 - 31 / 2880 := by
  unfold unconditionalEffectiveExp; norm_num

/-- **The unconditional effective exponent is `n^{1−o(1)}` class and strictly WORSE than the
good-prime `8/9`:** `8/9 < 2849/2880 < 1` (and `> 1/2`). So the unconditional multiplicative
energy route buys no power-saving past BGK — its saving `31/2880` is on the `1−o(1)` side. -/
theorem unconditionalEffective_high_and_worse :
    (8 : ℚ) / 9 < unconditionalEffectiveExp ∧
    unconditionalEffectiveExp < 1 ∧
    (1 : ℚ) / 2 < unconditionalEffectiveExp := by
  unfold unconditionalEffectiveExp
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## (C3) Character second moment: the Parseval floor, no sup upper lever -/

/-- The sup exponent obtainable from the exact 2nd moment `Σ_{b≠0}|η_b|² = pn − n²` ALONE:
`M ≤ √(pn) = n^{(β+1)/2}`. -/
def secondMomentSupExp (β : ℚ) : ℚ := (β + 1) / 2

/-- The Parseval-floor LOWER exponent: `M ≥ √(n − n²/p) ≈ n^{1/2}`. -/
def parsevalFloorExp : ℚ := 1 / 2

/-- **The exact second moment is TRIVIAL as a sup upper bound at `β = 4`:**
`secondMomentSupExp 4 = 5/2 > 1` (worse than the trivial `M ≤ n`). Only the `2r`-th moment
at `r ≈ log p` — the OPEN Wick atom — controls the sup; the 2nd moment is the FLOOR. -/
theorem secondMoment_trivial_beta4 :
    secondMomentSupExp 4 = 5 / 2 ∧ (1 : ℚ) < secondMomentSupExp 4 := by
  unfold secondMomentSupExp; norm_num

/-- The 2nd moment brackets `[√n, trivial]`: floor exponent `1/2` below the sup exponent
`(β+1)/2`, gap `β/2` — no upper improvement over trivial. -/
theorem secondMoment_bracket (β : ℚ) (hβ : 0 < β) :
    parsevalFloorExp < secondMomentSupExp β := by
  unfold parsevalFloorExp secondMomentSupExp; linarith

/-! ## The exhaustion verdict -/

/-- **NOT prize closure.** Every exponent here is `≥ 7/8 ≫ 1/2`; a fixed power law cannot
move δ* (`deltaStar_determination_all_or_nothing`), and the good-prime restriction persists. -/
def isPrizeClosure : Bool := false

/-- **The assembled exhaustion statement (exponent bookkeeping).** At `β = 4`, welding to the
landed `_BilinearDFTBeat` value:

* the best PROVEN-input exponent is `8/9` (`BilinearDFTBeat.bilinearTheta 4`, landed);
* the family infimum is `7/8` (`bilinear(4,4)`, `t₄` supply dead), a gap of exactly `1/72`;
* the best UNCONDITIONAL effective exponent is `2849/2880 = 1 − 31/2880` (`n^{1−o(1)}`);
* NONE of the three candidate inputs (mult-energy `n³`, higher exact `T_r`, 2nd moment)
  beats `8/9` good-prime or `n^{1−o(1)}` unconditional: mult-energy routes through
  sum-product (best `2849/2880`, direct HBK vacuous); higher `T_r` optima are `≥ 7/8`
  with dead supply; the 2nd moment is the Parseval floor (sup exponent `5/2`, trivial).

All four clauses proven; this is the SOTA frontier record, not a beat. -/
theorem exact_energy_axis_exhausted :
    BilinearDFTBeat.bilinearTheta 4 = 8 / 9 ∧
    familyInfimum 4 = 7 / 8 ∧
    bilinearSymExp 4 3 3 - familyInfimum 4 = 1 / 72 ∧
    unconditionalEffectiveExp = 1 - 31 / 2880 ∧
    ((8 : ℚ) / 9 < unconditionalEffectiveExp ∧ unconditionalEffectiveExp < 1) ∧
    (1 : ℚ) < secondMomentSupExp 4 := by
  refine ⟨BilinearDFTBeat.bilinearTheta_beta4, familyInfimum_beta4, landed_minus_infimum,
    unconditionalEffectiveExp_eq, ⟨?_, ?_⟩, ?_⟩
  · exact (unconditionalEffective_high_and_worse).1
  · exact (unconditionalEffective_high_and_worse).2.1
  · exact (secondMoment_trivial_beta4).2

/-- **Real-exponent headline (welded to the landed sup-norm extraction).** The best
exact-energy exponent that survives (`8/9`, good-prime) is the one already delivered by
`_BilinearDFTBeat.charSum_beta4`: under the two named analytic legs and the good-prime cubic
energy input, `M ≤ (225·K)^{1/18}·n^{8/9}`. This lane adds no new sup-norm bound — it records
that the three candidate energy inputs cannot improve it. -/
theorem headline_is_the_landed_89 {n M p K : ℝ}
    (hn : 1 ≤ n) (hM : 0 ≤ M) (hK : 1 ≤ K) (hp : 0 ≤ p)
    (hMoment : M ^ 18 ≤ 225 * K * p * n ^ 12)
    (hβ : p ≤ n ^ (4 : ℝ)) :
    M ≤ (225 * K) ^ ((1 : ℝ) / 18) * n ^ ((8 : ℝ) / 9) :=
  BilinearDFTBeat.charSum_beta4 hn hM hK hp hMoment hβ

end ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.familyInfimum_beta4
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.momentExp_legal_of_ge
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.momentExp_ge_familyInfimum
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.bilinearSymExp_33
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.bilinearSymExp_44
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.bilinearSymExp_55
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.bilinearSymExp_66
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.legalEnergyExp_lattice_beta4
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.bilinear_k_eq_beta_optimal
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.landed_minus_infimum
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.multEnergyHBK_E
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.multEnergyHBK_vacuous_at_beta4
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.multEnergyHBK_nonvacuous_iff
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.unconditionalEffectiveExp_eq
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.unconditionalEffective_high_and_worse
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.secondMoment_trivial_beta4
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.secondMoment_bracket
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.exact_energy_axis_exhausted
#print axioms ArkLib.ProximityGap.Frontier.WallNewEnergyExhaustion.headline_is_the_landed_89
