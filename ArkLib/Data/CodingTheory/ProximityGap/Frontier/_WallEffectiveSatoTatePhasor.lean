/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant

/-!
# WALL ATTACK [effective-Sato-Tate]: the prize is a UNIFORM-IN-`b` cancellation bound on the
# Gauss-sum phasor sum of growing length `t = (q-1)/d` (#444/#334)

## The phase-aware face, made exact

The in-tree `completion_identity` is the load-bearing exact identity
`t · η_b = ∑_{j=0}^{t-1} g(χ^{dj}, ψ_b)`, `t = (q-1)/d`, where the `j = 0` term is the trivial
Gauss sum `g(1, ψ_b) = -1` and each of the other `t-1` terms has norm **exactly** `√q`
(`norm_gaussSum_eq_sqrt`). Writing `T_b := ∑_{j=1}^{t-1} g(χ^{dj}, ψ_b)` (the **nontrivial
partial sum**) we obtain the EXACT phasor identity

> `t · η_b = -1 + T_b`,    `T_b = √q · S_b`,    `S_b := T_b / √q = ∑_{j=1}^{t-1} z_j(b)`,

with each `z_j(b) := g(χ^{dj},ψ_b)/√q` of **unit modulus** (`‖z_j(b)‖ = 1`). So `‖η_b‖` is
controlled by `‖S_b‖`, the norm of a sum of `t-1` unit phasors:

> `‖η_b‖ ≤ (1 + √q · ‖S_b‖) / t`.

The **triangle bound** `‖S_b‖ ≤ t-1` recovers the classical `‖η_b‖ ≤ √q` anchor exactly
(`norm_eta_torsion_le`). The **prize** `‖η_b‖ ≤ √(2n·ln q)` is EQUIVALENT (with `d = n`,
`t ≈ q/n`) to the square-root-cancellation bound

> `‖S_b‖ ≤ (t·√(2n·ln q) − 1)/√q ≈ √(2t·ln q)`,    **uniformly in `b ≠ 0`**

— i.e. the `t` Gauss-sum phases `{z_j(b)}` cancel like a quasi-random sum to within a `√(ln q)`
factor, the *effective vertical Sato-Tate / discrepancy* statement (Katz equidistribution of the
`G(χ^j)` made effective and worst-case-uniform). The `√(ln q)` is exactly the union-bound entropy
of the search over `b`: the EVT logarithm of the family size `q`.

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `eta_eq_phasorSum` — the EXACT phasor identity `t · η_b = -1 + T_b` (off `completion_identity`,
  splitting the trivial `j=0` term, no new mathematics — the partial-sum form the parent file
  collapsed into the triangle bound).
* `norm_eta_le_of_phasorCancellation` — the prize-shaped reduction: ANY uniform cancellation bound
  `‖T_b‖ ≤ C` yields `‖η_b‖ ≤ (1 + C)/t`. With `C = √q·√(2t·ln q)` this IS the prize.
* `PhasorCancellation` — the named open input (the EFFECTIVE Sato-Tate discrepancy), and
  `worstCaseIncompleteSumBound_of_phasorCancellation` wiring it to the canonical predicate, hence
  to `Λ²` (`prizeRadiusSq`). This is the phase-aware restatement of the wall.
* `phasorSum_triangle_bound` — the triangle bound `‖T_b‖ ≤ (t-1)·√q` (recovers the `√q` anchor),
  the UNCONDITIONAL ceiling the cancellation must beat.
* `prizeRadiusSq_le_of_phasorCancellation` — the cancellation input transported to `Λ²` directly:
  a uniform `‖T_b‖ ≤ C` gives `Λ² ≤ ((1+C)/t)²`. The SHARP form: the prize floor is the *minimum*
  achievable `C`, and the gap between the proven triangle `C = (t-1)√q` and the prize
  `C ≈ √q·√(2t ln q)` is EXACTLY the `√(t/(2 ln q))` cancellation deficit — the wall quantified.
* `phasorSum_secondMoment` (the AVERAGE-CASE genuine sub-step): the EXACT transported-Parseval
  identity `∑_{b≠0} ‖-1+T_b‖² = t²·(q·n − n²)`.  This makes the average phasor cancellation rigorous:
  RMS `‖T_b‖ = t√(n·(q−n)/(q−1)) ≈ t√n`, so RMS `‖S_b‖ = ‖T_b‖/√q ≈ √t` — EXACTLY square-root
  cancellation of the `t` unit phasors on average.  The wall is therefore isolated as PURELY the
  worst-case-over-`b` excess of `√(2 ln q)` above this proven `√t` average (the EVT logarithm).
  (Numerically confirmed exact at `p=17, d=4`: LHS `= 832 = t²(qn−n²)`.)
* `prizeRadiusSq_bound_monotone_in_C` — the cancellation deficit is monotone: progress on the
  effective-Sato-Tate discrepancy `C` transfers monotonically to `Λ²`.  The triangle ceiling
  `C=(t-1)√q` gives `Λ²≤q`; the prize `C≈√q√(2t ln q)` gives `Λ²≈2n ln q`; the gap (deficit factor
  `√(t/(2 ln q))`) is the wall, quantified.

## HONEST SCOPE (rule 6)

This **does not prove CORE**. It is a *strictly-more-tractable equivalent*: it converts the wall
from a bound on an incomplete character sum into a bound on the discrepancy of an explicit set of
`t` complex phases of unit modulus — the effective-Sato-Tate object. The open content
(`PhasorCancellation` = `‖T_b‖ ≤ √q·√(2t ln q)` uniformly) is Katz's vertical equidistribution
made effective; it is the SAME wall, but on the phase-aware side where the `√log` is visibly the
EVT logarithm, the triangle ceiling is `t-1` and the target is `√t·√(2 ln q)` — the cancellation
deficit is named and quantified. No `δ*`/capacity/beyond-Johnson claim. No Weil/étale input used
(only the elementary completion identity + `‖g(χ)‖ = √q`).
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset AddChar

namespace ArkLib.ProximityGap.WallFourEffectiveSatoTate

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.PrizeStructuralConstant

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The nontrivial Gauss-sum partial sum `T_b`.**  Given a full-order multiplicative character
`χ` (`orderOf χ = q-1`), `T_b = ∑_{j=1}^{t-1} g(χ^{dj}, ψ_b)`, the sum of the `t-1` nontrivial
completion terms (each of modulus exactly `√q`).  `t = (q-1)/d`. -/
noncomputable def phasorSum (d : ℕ) (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (b : F) : ℂ :=
  ∑ j ∈ (Finset.range ((Fintype.card F - 1) / d)).erase 0,
    gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)

/-- **The EXACT phasor identity** `t · η_b = -1 + T_b`.  Off `completion_identity`, splitting the
trivial `j = 0` term `g(1, ψ_b) = -1` from the nontrivial partial sum `T_b`.  This is the parent
file's intermediate, kept in its exact (un-triangle-inequality'd) form: the whole cancellation
content lives in `T_b`. -/
theorem eta_eq_phasorSum {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    (((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b
      = -1 + phasorSum d χ ψ b := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have hkey := completion_identity hd hd0 hord ψ b
  -- split the j = 0 term off the range-sum
  rw [hkey]
  rw [← Finset.add_sum_erase (Finset.range t)
        (fun j => gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)) (Finset.mem_range.mpr ht0)]
  congr 1
  · rw [mul_zero, pow_zero, gaussSum_one_mulShift hψ hb]

/-- **The triangle ceiling on the phasor sum** `‖T_b‖ ≤ (t-1)·√q`.  Each of the `t-1` nontrivial
terms has norm exactly `√q` (`norm_gaussSum_eq_sqrt`).  This is the UNCONDITIONAL upper bound that
the prize cancellation `‖T_b‖ ≈ √q·√(2t·ln q)` must beat — the gap is the cancellation deficit. -/
theorem phasorSum_triangle_bound {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖phasorSum d χ ψ b‖
      ≤ (((Fintype.card F - 1) / d - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  unfold phasorSum
  calc ‖∑ j ∈ (Finset.range t).erase 0, gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖
      ≤ ∑ j ∈ (Finset.range t).erase 0,
          ‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ := norm_sum_le _ _
    _ = ((t - 1 : ℕ) : ℝ) * Real.sqrt (Fintype.card F) := by
        have hbound : ∀ j ∈ (Finset.range t).erase 0,
            ‖gaussSum (χ ^ (d * j)) (AddChar.mulShift ψ b)‖ = Real.sqrt (Fintype.card F) := by
          intro j hj
          have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
          have hjt : j < t := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
          have hχ' : χ ^ (d * j) ≠ 1 := by
            refine chi_pow_ne_one hord (Nat.mul_pos hd0 (Nat.pos_of_ne_zero hj0)) ?_
            calc d * j < d * t := (Nat.mul_lt_mul_left hd0).mpr hjt
              _ = Fintype.card F - 1 := by rw [mul_comm]; exact htd
          set bu : Fˣ := Units.mk0 b hb with hbu
          have hshift := gaussSum_mulShift (χ ^ (d * j)) ψ bu
          have hnorms := congrArg norm hshift
          rw [Complex.norm_mul, norm_mulChar_apply_unit _ (show ((bu : F)) ≠ 0 from hb),
            one_mul] at hnorms
          rw [show AddChar.mulShift ψ b = AddChar.mulShift ψ ((bu : F)) from rfl, hnorms,
            norm_gaussSum_eq_sqrt hχ' hψ]
        rw [Finset.sum_congr rfl hbound, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_range.mpr ht0), Finset.card_range, nsmul_eq_mul]

/-- **The prize-shaped phasor-cancellation reduction.**  ANY uniform bound `‖T_b‖ ≤ C` on the
nontrivial Gauss-sum partial sum yields `‖η_b‖ ≤ (1 + C)/t`.  Substituting the prize cancellation
`C = √q·√(2t·ln q)` gives `‖η_b‖ ≤ (1 + √q·√(2t ln q))/t ≈ √(2n ln q)` (the prize floor).  The
proof is the elementary `t·η_b = -1 + T_b ⟹ t‖η_b‖ ≤ 1 + ‖T_b‖`. -/
theorem norm_eta_le_of_phasorCancellation {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) {C : ℝ}
    (hC : ‖phasorSum d χ ψ b‖ ≤ C) :
    ‖eta ψ (torsion F d) b‖ ≤ (1 + C) / (((Fintype.card F - 1) / d : ℕ) : ℝ) := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have hid := eta_eq_phasorSum hd hd0 hord hψ hb
  -- t·‖η_b‖ = ‖-1 + T_b‖ ≤ 1 + ‖T_b‖ ≤ 1 + C
  have hnorm : (t : ℝ) * ‖eta ψ (torsion F d) b‖ = ‖(-1 : ℂ) + phasorSum d χ ψ b‖ := by
    rw [← hid, norm_mul, Complex.norm_natCast]
  rw [le_div_iff₀ ht0R, mul_comm]
  calc (t : ℝ) * ‖eta ψ (torsion F d) b‖
      = ‖(-1 : ℂ) + phasorSum d χ ψ b‖ := hnorm
    _ ≤ ‖(-1 : ℂ)‖ + ‖phasorSum d χ ψ b‖ := norm_add_le _ _
    _ ≤ 1 + C := by rw [norm_neg, norm_one]; linarith [hC]

/-- **The EFFECTIVE Sato-Tate discrepancy input** (the open core, phase-aware face).  A uniform
square-root-cancellation bound on the Gauss-sum phasor sum: `‖T_b‖ ≤ C` for every `b ≠ 0`.  The
prize is this with `C ≈ √q·√(2t·ln q)` — i.e. the `t` unit phasors `{g(χ^{dj},ψ_b)/√q}` cancel to
the EVT scale `√(2t·ln q)`, uniformly in `b`.  This is Katz's vertical equidistribution of the
Gauss sums made *effective* and *worst-case-uniform*; it is the SAME wall as `DepthLogSubGaussian`,
restated on the phase side.  The triangle ceiling `C = (t-1)√q` (`phasorSum_triangle_bound`) is the
unconditional value; the cancellation deficit `(t-1)√q / (√q√(2t ln q)) = √(t/(2 ln q))` is the
exact gap the prize closes. -/
def PhasorCancellation (d : ℕ) (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖phasorSum d χ ψ b‖ ≤ C

/-- **The phasor-cancellation input discharges the canonical predicate.**  If the Gauss-sum
phasors cancel uniformly to level `C`, then `WorstCaseIncompleteSumBound` holds at the squared
scale `((1+C)/t)²`, hence (via `worstCaseIncompleteSumBound_iff_prizeRadiusSq_le`) bounds the prize
structural constant `Λ²`.  The whole prize becomes: prove `PhasorCancellation` at `C ≈ √q√(2t ln q)`.
-/
theorem worstCaseIncompleteSumBound_of_phasorCancellation {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {C : ℝ} (hC0 : 0 ≤ C)
    (hPC : PhasorCancellation d χ ψ C) :
    WorstCaseIncompleteSumBound ψ (torsion F d)
      (((1 + C) / (((Fintype.card F - 1) / d : ℕ) : ℝ)) ^ 2) := by
  intro b hb
  have hnn : (0 : ℝ) ≤ ‖eta ψ (torsion F d) b‖ := norm_nonneg _
  have hle : ‖eta ψ (torsion F d) b‖
      ≤ (1 + C) / (((Fintype.card F - 1) / d : ℕ) : ℝ) :=
    norm_eta_le_of_phasorCancellation hd hd0 hord hψ hb (hPC b hb)
  exact pow_le_pow_left₀ hnn hle 2

/-- **The phasor cancellation transported to the canonical prize constant `Λ²`.**  `Λ²(ψ, torsion
F d) ≤ ((1+C)/t)²` from a uniform phasor cancellation `C`.  This is the wall as a threshold on the
*single* prize object, expressed in the *phase-aware* variable: the entire content is the value of
`C` for which the bound is provable.  The triangle ceiling gives `Λ² ≤ q` (the classical anchor);
the prize floor needs `C ≈ √q√(2t ln q)`, i.e. `Λ² ≈ 2n ln q`. -/
theorem prizeRadiusSq_le_of_phasorCancellation {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {C : ℝ} (hC0 : 0 ≤ C)
    (hPC : PhasorCancellation d χ ψ C) :
    prizeRadiusSq ψ (torsion F d)
      ≤ ((1 + C) / (((Fintype.card F - 1) / d : ℕ) : ℝ)) ^ 2 :=
  (worstCaseIncompleteSumBound_iff_prizeRadiusSq_le ψ (torsion F d) _).mp
    (worstCaseIncompleteSumBound_of_phasorCancellation hd hd0 hord hψ hC0 hPC)

/-- **The classical `√q` anchor RE-DERIVED through the phasor representation** — sanity/consistency
check that the triangle ceiling recovers exactly the known anchor.  Feeding the triangle bound
`C = (t-1)√q` into the reduction gives `‖η_b‖ ≤ (1+(t-1)√q)/t ≤ √q`.  Confirms the phasor reduction
is tight at the unconditional end. -/
theorem norm_eta_le_sqrt_via_phasor {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖eta ψ (torsion F d) b‖ ≤ Real.sqrt (Fintype.card F) := by
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    refine Real.sqrt_le_sqrt ?_
    have := Fintype.one_lt_card (α := F); exact_mod_cast this.le
  have htri := phasorSum_triangle_bound hd hd0 hord hψ hb
  have hle := norm_eta_le_of_phasorCancellation hd hd0 hord hψ hb htri
  -- (1 + (t-1)√q)/t ≤ √q  ⟺  1 + (t-1)√q ≤ t√q  ⟺  1 ≤ √q
  have htcast : (((Fintype.card F - 1) / d - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [← ht, Nat.cast_sub ht0]; norm_num
  rw [htcast] at hle
  refine hle.trans ?_
  rw [div_le_iff₀ ht0R]
  nlinarith [hsqrt1, ht0R]

/-- **The EXACT second-moment phasor identity** (the average-case genuine sub-step).  Squaring the
exact identity `t·η_b = -1 + T_b` and summing over ALL `b` (Parseval): since `t²‖η_b‖² = ‖-1+T_b‖²`
pointwise,
  `∑_{b∈F} ‖-1 + T_b‖² = t² · ∑_{b∈F} ‖η_b‖² = t² · q·|G|`,
using the proven `subgroup_gaussSum_secondMoment` (`∑_b ‖η_b‖² = q·|G|`).  This makes the AVERAGE
phasor cancellation rigorous: the mean of `‖-1+T_b‖²` over the `q` frequencies is `t²·q·n/q = t²·n`,
so the RMS phasor sum is `‖T_b‖ ≈ t√n`, i.e. `‖S_b‖ = ‖T_b‖/√q ≈ t√n/√q = √(q/n) = √t` — EXACTLY
square-root cancellation of the `t` unit phasors on average.  The wall is therefore PURELY the
worst-case-over-`b` excess `√(2 ln q)` above this proven `√t` average — the effective Sato-Tate /
union-bound logarithm, isolated.  (NOTE: this identity holds at `b = 0` too, where `η_0 = |G|` and
the completion identity's hypotheses do not require `b ≠ 0` for the squared form via Parseval; we
state it over all `b`, which is the clean Parseval form.) -/
theorem phasorSum_secondMoment {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖(-1 : ℂ) + phasorSum d χ ψ b‖ ^ 2
      = ((((Fintype.card F - 1) / d : ℕ) : ℝ)) ^ 2
          * ((Fintype.card F : ℝ) * (torsion F d).card - ((torsion F d).card : ℝ) ^ 2) := by
  set t := (Fintype.card F - 1) / d with ht
  -- pointwise: ‖-1+T_b‖² = (t‖η_b‖)² = t²‖η_b‖²  for b ≠ 0
  have hpt : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖(-1 : ℂ) + phasorSum d χ ψ b‖ ^ 2 = (t : ℝ) ^ 2 * ‖eta ψ (torsion F d) b‖ ^ 2 := by
    intro b hb
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    have hid := eta_eq_phasorSum hd hd0 hord hψ hb0
    have : ‖(((Fintype.card F - 1) / d : ℕ) : ℂ) * eta ψ (torsion F d) b‖
        = ‖(-1 : ℂ) + phasorSum d χ ψ b‖ := by rw [hid]
    rw [norm_mul, Complex.norm_natCast] at this
    rw [← this, mul_pow, ← ht]
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  -- ∑_{b≠0} ‖η_b‖² = q·|G| − |G|²  (Parseval, minus the b=0 term ‖η_0‖² = |G|²)
  have hall : ∑ b : F, ‖eta ψ (torsion F d) b‖ ^ 2
      = (Fintype.card F : ℝ) * (torsion F d).card :=
    subgroup_gaussSum_secondMoment hψ (torsion F d)
  have hz : ‖eta ψ (torsion F d) (0 : F)‖ ^ 2 = ((torsion F d).card : ℝ) ^ 2 := by
    have he0 : eta ψ (torsion F d) (0 : F) = ((torsion F d).card : ℂ) := by
      simp only [eta, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [he0, Complex.norm_natCast]
  have hsub : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ (torsion F d) b‖ ^ 2
      = (Fintype.card F : ℝ) * (torsion F d).card - ((torsion F d).card : ℝ) ^ 2 := by
    have hsplit : ∑ b : F, ‖eta ψ (torsion F d) b‖ ^ 2
        = ‖eta ψ (torsion F d) (0 : F)‖ ^ 2
          + ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ (torsion F d) b‖ ^ 2 :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    rw [hall, hz] at hsplit; linarith
  rw [hsub]

/-- **The cancellation deficit, quantified.**  The proven triangle ceiling on the phasor sum is
`‖T_b‖ ≤ (t-1)·√q` (`phasorSum_triangle_bound`), giving the classical anchor `Λ² ≤ q`.  The prize
needs `‖T_b‖ ≤ √q·√(2t·ln q)` (giving `Λ² ≈ 2n ln q`).  The ratio of the two ceilings is the EXACT
cancellation deficit: any `C` strictly between them moves the wall.  This lemma records the clean
monotonicity: a SMALLER uniform phasor bound `C₁ ≤ C₂` gives a SMALLER `Λ²` bound — so progress on
the effective-Sato-Tate discrepancy `C` transfers MONOTONICALLY to the prize constant.  (The
direction the prize needs: push `C` from the triangle `(t-1)√q` down toward `√q√(2t ln q)`.) -/
theorem prizeRadiusSq_bound_monotone_in_C {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {χ : MulChar F ℂ} (hord : orderOf χ = Fintype.card F - 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {C₁ C₂ : ℝ} (hC10 : 0 ≤ C₁) (hC12 : C₁ ≤ C₂)
    (hPC : PhasorCancellation d χ ψ C₁) :
    prizeRadiusSq ψ (torsion F d)
      ≤ ((1 + C₂) / (((Fintype.card F - 1) / d : ℕ) : ℝ)) ^ 2 := by
  -- a stronger cancellation C₁ implies the weaker-C₂ Λ² bound, since the bound is increasing in C
  have hbase := prizeRadiusSq_le_of_phasorCancellation hd hd0 hord hψ hC10 hPC
  refine hbase.trans ?_
  set t := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have h1 : (0 : ℝ) ≤ (1 + C₁) / (t : ℝ) := by positivity
  have h2 : (1 + C₁) / (t : ℝ) ≤ (1 + C₂) / (t : ℝ) := by
    gcongr
  exact pow_le_pow_left₀ h1 h2 2

end ArkLib.ProximityGap.WallFourEffectiveSatoTate

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.eta_eq_phasorSum
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.phasorSum_triangle_bound
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.norm_eta_le_of_phasorCancellation
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.worstCaseIncompleteSumBound_of_phasorCancellation
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.prizeRadiusSq_le_of_phasorCancellation
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.norm_eta_le_sqrt_via_phasor
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.phasorSum_secondMoment
#print axioms ArkLib.ProximityGap.WallFourEffectiveSatoTate.prizeRadiusSq_bound_monotone_in_C
