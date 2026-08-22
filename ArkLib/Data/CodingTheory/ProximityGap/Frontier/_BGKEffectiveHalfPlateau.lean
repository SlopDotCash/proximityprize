/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SubgroupExpSumPSavingGate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiBenedettoNearSidonImprovement

/-!
# The effective-BGK 1/2-push at β = 4 is QUANTIFIED-DEAD (#466 Tier-1 item 5)

Dossier v3 §6 Tier-1 item 5 — "di Benedetto sum-product pushed to an **effective 1/2 exponent**
at β = 4" — was announced on the #464 thread (2026-06-27) and never run.  This brick runs it and
lands the verdict: **REFUTED for the entire explicit sum-product corpus, with exact constants.**

The corpus has exactly two explicit mechanisms at the prize aspect ratio `β = 4` (`p = n^β`,
`n = |μ_n| = 2^30`):

1. **The trilinear (depth-3) machinery** (di Benedetto–Garaev–García–González-Sánchez–
   Shparlinski–Trujillo, arXiv:2003.06165 Thm 3.1).  Its saving is
   `diBenedettoSaving t₂ t₃ = (10 − 2t₃ − t₂/2)/72` in the energy exponents, and the in-tree
   ceiling `diBenedettoSaving_le_ceiling` (`_DiBenedettoNearSidonImprovement.lean`) already pins
   its ABSOLUTE input-slot cap at `1/24` (attained by the dyadic Sidon-floor energies
   `t₂ = 2, t₃ = 3`): no legal energy input can do better.

2. **The iterated sum-product** (Bourgain–Glibichuk–Konyagin), whose sharpest EXPLICIT form —
   per Kowalski's exposition arXiv:2401.04756, Remark 1.2(3) — is **Shkredov, "Some remarks on
   the asymmetric sum-product phenomenon" (arXiv:1705.09703, Cor. 16)**:

   > `max_{ξ≠0} |Γ̂(ξ)| ≪ |Γ|·p^{−δ/2^{7+2/δ}}` for `|Γ| ≥ p^δ`, via `k = ⌈2·log p/log|Γ|⌉ + 4`
   > squaring iterations, i.e. a `|Γ|`-exponent saving of exactly `1/2^{k+2}`, under the
   > applicability condition `2^{64k}·C∗⁴ ≤ |Γ|` (droppable per Shkredov Rem. 13 at the cost of a
   > `(C∗ log|Γ|)^{k−1}` multiple, which washes out under the `2^{k+1}`-th root).

   This file pins the arithmetic of that shape at `β = 4`:
   * `k = 2·4 + 4 = 12` iterations (`shkredovIterations`);
   * `n`-exponent saving `1/2^14 = 1/16384` (`shkredovNSaving_at_four`) — the headline
     `δ/2^{7+2/δ}` form evaluates to the safe uniform `p`-saving `2^{−17}`; the exact-`k` value
     at integral β is `p`-saving `1/65536`;
   * the clean Cor. 16 applicability floor at `k = 12` is `|Γ| ≥ 2^{768}·C∗⁴` — the prize scale
     `n = 2^30` sits a factor `2^{738}` BELOW it (`prize_scale_below_cor16Floor`); only the
     Remark-13 variant applies at all, with the same `1/16384` saving;
   * composition with the in-tree gate (`pSaving_misses_prize_beta_four`, requiring `ν ≥ 1/8`):
     `1/65536 < 1/8`, so the explicit bound lands `n^{0.49994}` ABOVE the prize exponent
     (`shkredov_explicit_misses_prize`);
   * the trilinear ceiling dominates the iterated explicit saving by a factor > 682
     (`trilinear_ceiling_dominates`): iteration does not amplify at β = 4 — it collapses;
   * **the shape can NEVER reach saving 1/2 at any aspect ratio and any depth**:
     `1/2^{k+2} ≤ 1/64` for every k in the method's range, and `< 1/2` for every `k : ℕ`
     (`half_unreachable_at_any_depth`) — Shkredov's own Rem. 17 notes constants are improvable
     "but not the constant C in (31)", i.e. the `2^k` collapse is structural;
   * **the depth-inefficiency meter** (`depth_efficiency_gap`): the iterated method consumes
     additive-energy depth `2^k = 4096` (`shkredov_energy_depth`) — 46× the wall depth
     `r ≈ ln q ≈ 89` — and converts it to saving `1/16384`, while the (OPEN) Gaussian/Wick bound
     at that same depth would give `wickSaving 4096 = 4093/8192 ≈ 0.4996`: a conversion
     inefficiency exceeding 4000×.  The sum-product cascade is an L²-energy method squarely
     inside the Meta-Theorem's cap; it pays wall-currency (moment depth) at a doubly-exponential
     exchange rate.

## Verdict

Every explicit mechanism engaging the real object at `β = 4` plateaus at `1/24` (trilinear
ceiling, in-tree) or `1/16384` (iterated explicit, this file) — both `≪ 1/2`.  An effective-1/2
exponent is unreachable inside the corpus's shapes; reaching it means a NEW mechanism, which is
exactly the open CORE (`M(μ_n) ≤ C·√(n·log(p/n))`).  Tier-1 item 5 is hereby CLOSED as a
refutation-with-exact-constants; the residue is (as always) the wall.

**HONESTY (rules 1, 3, 6).**  This is exponent bookkeeping on two cited literature shapes (the
Cor.-16 saving `1/2^{k+2}` with `k = 2β+4`, quoted verbatim above; the in-tree
`diBenedettoSaving`), NOT new analytic content, NOT thinness-essential, and it neither proves
nor disproves CORE.  It quantifies a method plateau; the open core stays open.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate
open ProximityGap.Frontier.DiBenedettoNearSidon

namespace ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau

/-! ## The Shkredov Cor. 16 shape at integral aspect ratio -/

/-- **Shkredov Cor. 16 iteration count** at integral aspect ratio `β = log p / log |Γ|`:
`k = ⌈2·log p/log|Γ|⌉ + 4 = 2β + 4`. -/
def shkredovIterations (β : ℕ) : ℕ := 2 * β + 4

/-- **The `|Γ|`-exponent saving** of the explicit iterated sum-product bound:
`ρ ≪ |Γ|^{1 − 1/2^{k+2}}`, i.e. saving `1/2^{k+2}`. -/
def shkredovNSaving (β : ℕ) : ℚ := 1 / 2 ^ (shkredovIterations β + 2)

/-- **The `p`-exponent saving** `ν` with `|Γ| = p^{1/β}`: `n`-saving `= β·ν`. -/
def shkredovPSaving (β : ℕ) : ℚ := shkredovNSaving β / β

/-- The clean Cor. 16 applicability floor `2^{64k}` (`C∗⁴` omitted — a further factor `> 1`;
droppable entirely per Shkredov Rem. 13). -/
def cor16ApplicabilityFloor (β : ℕ) : ℕ := 2 ^ (64 * shkredovIterations β)

/-- The (OPEN, conditional) Gaussian/Wick moment-route saving at depth `r`, `β = 4`:
`1 − (β + r − 1)/(2r) = (r − 3)/(2r)`.  Used here only as the depth-efficiency meter. -/
def wickSaving (r : ℚ) : ℚ := (r - 3) / (2 * r)

/-! ## The exact values at the prize point β = 4 -/

/-- At `β = 4`: `k = 12` squaring iterations. -/
theorem shkredovIterations_at_four : shkredovIterations 4 = 12 := by
  norm_num [shkredovIterations]

/-- At `β = 4`: the explicit iterated `n`-exponent saving is `1/16384` — the sharpest explicit
BGK bound at the prize aspect ratio is `M ≤ n^{1 − 1/16384}`. -/
theorem shkredovNSaving_at_four : shkredovNSaving 4 = 1 / 16384 := by
  norm_num [shkredovNSaving, shkredovIterations]

/-- At `β = 4`: the explicit `p`-exponent saving is `ν = 1/65536`. -/
theorem shkredovPSaving_at_four : shkredovPSaving 4 = 1 / 65536 := by
  norm_num [shkredovPSaving, shkredovNSaving, shkredovIterations]

/-- The additive-energy depth the iterated method consumes at `β = 4`: `2^k = 4096` — 46× the
wall depth `r ≈ ln q ≈ 89`. -/
theorem shkredov_energy_depth : 2 ^ shkredovIterations 4 = 4096 := by
  norm_num [shkredovIterations]

/-! ## The four kill theorems -/

/-- **Gate composition: the explicit iterated bound MISSES the prize exponent.**  The in-tree
gate requires `p`-saving `ν ≥ 1/8` at `β = 4`; the sharpest explicit value is `1/65536` —
`8192×` short.  The bound lands at `n^{1 − 1/16384}`, i.e. `n^{0.4999+}` above the `√n` target. -/
theorem shkredov_explicit_misses_prize :
    prizeNExponent < nExponentFromPSaving 4 ((1 : ℝ) / 65536) := by
  rw [pSaving_misses_prize_beta_four]
  norm_num

/-- **The trilinear ceiling dominates the iterated explicit route by > 682×** at `β = 4`:
iteration does not amplify the saving — it collapses it (each further squaring halves the
per-depth yield).  Together with the in-tree `diBenedettoSaving_le_ceiling` (`≤ 1/24` for every
legal energy input), the ENTIRE explicit corpus plateaus at `1/24 ≪ 1/2`. -/
theorem trilinear_ceiling_dominates :
    682 * shkredovNSaving 4 < 1 / 24 ∧ shkredovNSaving 4 < 1 / 24 := by
  rw [shkredovNSaving_at_four]
  norm_num

/-- **Saving `1/2` is unreachable at ANY depth**: `1/2^{k+2} < 1/2` for every `k : ℕ`, and
`≤ 1/64` for every `k ≥ 4` (the method's range is `k ≥ 4` by construction, any aspect ratio).
Shkredov Rem. 17: the constants are improvable, "but not the constant C in (31)" — the `2^k`
collapse is the structure, not slack. -/
theorem half_unreachable_at_any_depth :
    (∀ k : ℕ, (1 : ℚ) / 2 ^ (k + 2) < 1 / 2) ∧
    (∀ β : ℕ, shkredovNSaving β ≤ 1 / 64) := by
  constructor
  · intro k
    have h4 : (4 : ℚ) ≤ 2 ^ (k + 2) := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · intro β
    unfold shkredovNSaving shkredovIterations
    have h64 : (64 : ℚ) ≤ 2 ^ (2 * β + 4 + 2) := by
      calc (64 : ℚ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (2 * β + 4 + 2) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

/-- **The prize scale sits `2^{738}` BELOW the clean Cor. 16 applicability floor** at `β = 4`
(`|Γ| ≥ 2^{768}` required vs `n = 2^30` deployed): as stated, the sharpest explicit BGK theorem
does not even apply at the prize point — only the Remark-13 variant (worse constants, same
`1/16384` saving shape) does. -/
theorem prize_scale_below_cor16Floor : 2 ^ 30 < cor16ApplicabilityFloor 4 := by
  unfold cor16ApplicabilityFloor
  rw [shkredovIterations_at_four]
  exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)

/-- **The depth-inefficiency meter.**  At the energy depth `4096` the iterated method already
consumes, the (OPEN) Wick bound would yield saving `4093/8192 ≈ 0.4996 ≈ 1/2`; the method
extracts `1/16384` — a conversion inefficiency exceeding `4000×`.  The cascade pays
wall-currency (moment depth) at a doubly-exponential exchange rate; it is an L²-energy method
strictly inside the Meta-Theorem's cap. -/
theorem depth_efficiency_gap :
    4000 * shkredovNSaving 4 < wickSaving 4096 ∧ wickSaving 4096 < 1 / 2 := by
  rw [shkredovNSaving_at_four]
  unfold wickSaving
  norm_num

/-- The wall-depth Wick saving for calibration: at `r = 89 ≈ ln q`, the (OPEN) moment route
gives `43/89 ≈ 0.483` — the prize-adjacent value.  The explicit corpus reaches `≤ 1/24` at any
depth; the missing factor IS the open core. -/
theorem wickSaving_at_wall_depth : wickSaving 89 = 43 / 89 := by
  unfold wickSaving
  norm_num

end ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau.shkredovNSaving_at_four
#print axioms ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau.shkredov_explicit_misses_prize
#print axioms ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau.trilinear_ceiling_dominates
#print axioms ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau.half_unreachable_at_any_depth
#print axioms ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau.prize_scale_below_cor16Floor
#print axioms ArkLib.ProximityGap.Frontier.BGKEffectiveHalfPlateau.depth_efficiency_gap
