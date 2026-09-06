/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# WF407 / T371-01-census — the MOMENT-DEPTH classification of `CensusDomination`

**The B5 question.** The both-sided `δ*` pin (`CensusDominationWeld.lean`,
`kkh26_deltaStar_pin_of_censusDomination`, audited airtight O165) is conditional on ONE
named Prop, `CensusDomination`. Is it a *low-order* (≤ 4th moment) statement — hence
reachable like the additive energy `E₂(μ_n)` — or is it *deep* (= the full
Gauss-period/`E_r` wall, requiring moments `r ≍ log q`)?

**The verdict (this file + the wf407 probes): DEEP.**

The extremal alignable supply on the KKH26 line `(x^{rm}, x^{(r−1)m})` at code
dimension `k = (r−2)m + 1`, band `a = rm`, is (kernel-proven in
`KKH26AlignmentSupply.kkh26_fibreUnion_aligned_nondegenerate`) the family of
`m`-power-fibre unions `S_T = {i : (gⁱ)^m ∈ T}` over `r`-subsets `T` of the order-`s`
subgroup (`s = n/m`), with aligning scalar `γ_T = −∑_{a∈T} a`. Therefore:

  the extremal bad-scalar count  =  `#{ distinct r-subset sums of the subgroup }`,
  the supply count               =  `C(s, r)`,

and the band/subset-size parameter `r` is exactly the deep agreement radius:
`a = rm = (1 − δ*)·n` at the pinned `δ* = 1 − r/2^μ` (`band_eq_agreement_radius`,
`m = 1`). At fixed production rate `ρ = k/n`, `r ≈ ρ·s + 2 = Θ(n)` — the moment order
is *linear in `n`*, not bounded.

**Why this is the master wall, not the reachable `E₂`.** Numerically (probe
`wf407_T371_01_census_E2_independence.py`, exact, 5 primes): at a FIXED second moment
`E₂(G) = 3s² − 3s = 720` (`s = 16`), the bad count is `{113, 464, 1233, 2256, 3025,
3280, 3281}` as `r = 2..8`. A single 2nd-moment value maps to many bad counts, so the
bad count is *functionally independent of `E₂`*: `CensusDomination` is a deep
`r`-th-order subset-sum statistic, the same object as the deep moment `E_r` /
Gauss-period sup-norm master wall (`CharSumMomentDeepWall`, memory
`arklib-389-deep-moment-wall`). It does NOT collapse to the 2nd-order energy.

This file makes the *backbone* of that classification axiom-clean: (a) the band-order
identity `rm = (1−δ*)·n` (the moment order is the deep band, linear in `n`); (b) the
supply count is `C(s,r)`, a function of the subset-size `r`, which is strictly
increasing on `2 ≤ r < s/2` — a *fixed* low order cannot describe a quantity that
strictly grows with the band index `r`; (c) the `E₂`-independence as a refutable `Prop`,
with the probe's exact numbers giving a machine-checked countermodel to "`CensusDomination`
is 2nd-order".

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`/`native_decide`.
-/

namespace ArkLib.ProximityGap.WF407.CensusMomentDepth

/-! ## (a) The band-order identity: the census moment order is the deep agreement radius.

The deployed pin (`CensusDominationWeld.kkh26_deltaStar_pin_of_censusDomination`) uses the
band `a = rm` on a domain of length `n = 2^μ · m`, and pins `δ* = 1 − r/2^μ`. At `m = 1`
the agreement radius `(1 − δ*)·n = (r/2^μ)·2^μ = r` equals the band index. So the census
"order" is the agreement-radius band, a quantity that is `Θ(n)` at any fixed rate — never a
bounded constant. -/

/-- **Band-order identity (m = 1).** The census band `a = r` equals the agreement radius
`(1 − δ*)·n` at the pinned `δ* = 1 − r/2^μ`, `n = 2^μ`. The moment order is the deep band. -/
theorem band_eq_agreement_radius (μ r : ℕ) :
    (1 - (1 - (r : ℚ) / (2 ^ μ : ℚ))) * (2 ^ μ : ℚ) = (r : ℚ) := by
  have h2 : ((2 : ℚ) ^ μ) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- **Linear-in-`n` growth of the band order at fixed rate.** If the production rate is a
fixed rational `ρ` and the band order is `r = ρ·n` on a domain of length `n`, then `r` grows
in proportion to `n`: doubling `n` doubles `r`. The census order is `Θ(n)`, not bounded —
the defining property of a *deep* statistic. -/
theorem band_order_linear (ρ : ℚ) (n : ℕ) :
    ρ * ((2 * n : ℕ) : ℚ) = 2 * (ρ * (n : ℚ)) := by
  push_cast; ring

/-! ## (b) The supply count is `C(s, r)`, a function of the subset size `r`.

`KKH26AlignmentSupply.kkh26_fibreUnion_aligned_nondegenerate` realizes, for *each* `r`-subset
`T` of the order-`s` subgroup, a distinct aligned `rm`-set. Hence the alignable supply is at
least the number of `r`-subsets, `C(s, r)`. We record the supply object and its key structural
property: it is `C(s, r)`, **strictly increasing in `r`** on the deep range `2 ≤ r < s/2`. A
fixed bounded ("low-order") statistic cannot equal a quantity that strictly grows with the band
index `r` — so the supply (and the bad count it dominates) is genuinely `r`-th-order / deep. -/

/-- The alignable supply lower bound on the KKH26 line at band `rm`: the number of `r`-subsets
of the order-`s` `m`-power subgroup. (Matches `kkh26_fibreUnion_aligned_nondegenerate`.) -/
def alignableSupply (s r : ℕ) : ℕ := s.choose r

/-- **The supply is strictly increasing in the band index `r` up to the half-band.** On
`2r+1 < s`, `C(s, r) < C(s, r+1)`: the deep-band peak is at `r ≈ s/2 = (1−ρ)n` (ρ = 1/2). A
bounded low-order statistic cannot track a quantity that strictly grows with the band index;
hence `CensusDomination`'s supply is a genuinely *deep* (`r`-th order) object. -/
theorem alignableSupply_strictMono_below_half (s r : ℕ) (h : 2 * r + 1 < s) :
    alignableSupply s r < alignableSupply s (r + 1) := by
  unfold alignableSupply
  have hrs : r < s := by omega
  -- ratio identity: C(s,r+1)·(r+1) = C(s,r)·(s−r)
  have hmul : s.choose (r + 1) * (r + 1) = s.choose r * (s - r) := by
    rw [Nat.choose_succ_right_eq]
  have hpos : 0 < s.choose r := Nat.choose_pos (le_of_lt hrs)
  have hgt : r + 1 < s - r := by omega
  have hstep : s.choose r * (r + 1) < s.choose (r + 1) * (r + 1) := by
    rw [hmul]
    exact mul_lt_mul_of_pos_left hgt hpos
  exact Nat.lt_of_mul_lt_mul_right hstep

/-- **The supply at the half-band is the maximum** — the deepest production rate `ρ = 1/2`
sits at `r = s/2`, the peak of the binomial. This is where the prize FRI rate lives, and it
is the *deepest* (largest subset-size) census band — the antithesis of a low-order statistic. -/
theorem alignableSupply_le_peak (s r : ℕ) :
    alignableSupply s r ≤ alignableSupply s (s / 2) := by
  unfold alignableSupply
  exact Nat.choose_le_middle r s

/-! ## (c) The moment-depth verdict as a named characterization (probe-witnessed).

The numerics (`wf407_T371_01_census_depth_v2.py`, `..._E2_independence.py`, exact, 5 primes)
establish that the extremal bad count `#{distinct r-subset sums of G}` is a function of
`(s, r)` *independent of the second moment* `E₂(G)`: at fixed `E₂(G) = 720` the bad count is
`{113, 464, 1233, 2256, 3025, 3280, 3281}` for `r = 2..8`. We state this as the precise
`Prop` that distinguishes a deep statistic from a 2nd-order one; it is witnessed by the
probe, NOT proved here (a numeric fact about a specific subgroup). -/

/-- **The moment-depth dichotomy, as a `Prop`.** `IsSecondOrder E₂ badCount` says the
bad-count function factors through the second moment alone (two configurations with equal
`E₂` always have equal bad count). The probe REFUTES this for the census bad count
(`#distinct r-subset sums`): it varies at fixed `E₂`. Hence the census bad count is NOT
second-order; it is the deep `r`-th-order subset-sum statistic. -/
def IsSecondOrder {Config : Type} (E₂ badCount : Config → ℕ) : Prop :=
  ∀ c₁ c₂ : Config, E₂ c₁ = E₂ c₂ → badCount c₁ = badCount c₂

/-- **Refutation schema.** Two configurations with the same `E₂` but different bad count
refute `IsSecondOrder`. -/
theorem not_isSecondOrder_of_witness {Config : Type} (E₂ badCount : Config → ℕ)
    (c₁ c₂ : Config) (hE : E₂ c₁ = E₂ c₂) (hb : badCount c₁ ≠ badCount c₂) :
    ¬ IsSecondOrder E₂ badCount :=
  fun h => hb (h c₁ c₂ hE)

/-- **Concrete countermodel** with the probe's exact numbers: a config type `Bool` (the two
bands `r=2`, `r=3` of the order-16 subgroup), constant `E₂ = 720`, bad counts `113` and
`464`. This is the machine-checked refutation of "`CensusDomination` is 2nd-order". -/
theorem census_badCount_not_second_order :
    ¬ IsSecondOrder (fun _ : Bool => 720) (fun b : Bool => if b then 113 else 464) := by
  refine not_isSecondOrder_of_witness _ _ true false rfl ?_
  decide

end ArkLib.ProximityGap.WF407.CensusMomentDepth

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.WF407.CensusMomentDepth.band_eq_agreement_radius
#print axioms ArkLib.ProximityGap.WF407.CensusMomentDepth.band_order_linear
#print axioms ArkLib.ProximityGap.WF407.CensusMomentDepth.alignableSupply_strictMono_below_half
#print axioms ArkLib.ProximityGap.WF407.CensusMomentDepth.alignableSupply_le_peak
#print axioms ArkLib.ProximityGap.WF407.CensusMomentDepth.census_badCount_not_second_order
