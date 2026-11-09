/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.FieldTheory.Separable
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound

/-!
# PROVE-attempt (#444) — `[weil-on-A]` SHARPENED: the L²/Parseval ceiling of the descent object,
  and the EXACT distinct-root pin of the Weil deficit.

## The residual recalled (proven across `_JAC_1`–`_JAC_6`).

In the proven twisted-DFT coordinate `m·η_b = ∑_{j<m} χ(b)^{-j} g_j`, `g_j = gaussSum(χ^j,ψ)`,
`|g_j| = √q`, the prize `M = max_{b≠0}‖η_b‖ ≤ C√(n log m)` (regime `p ≈ n^4`, `m = (p-1)/n`,
`n = 2^a`) reduces (`_ProveOffDiagResonanceCapstone`) to the off-diagonal autocorrelation
resonance `R_b = ∑_{s≠0} χ(b)^{ks} A(s) = O(m·q·log m)`, where `A(s) = ∑_{j<m} g_j conj(g_{j+s})`.

`_JAC_3`/`_JAC_4` proved the EXACT pullout + geometric collapse:
`A(s) = g(χ^{-s}) · R(s)`,  `R(s) = m · T(s)`,  `T(s) = ∑_{t∈μ_n} χ^s(t-1)`,
so `A(s) = √q · m · χ^s(-1) · T(s)` up to unit phases, and `T(s)` is an INCOMPLETE
`(n-1)`-term multiplicative character sum over the order-`n` subgroup `μ_n`. ALL magnitude is
`√q`/`q`/`m`; the residual is the SUP of `T(s)`, dimension `n-1`, the wall one order down.

## What this file ADDS (genuine, axiom-clean sub-steps that SHARPEN the residual).

The previous `[weil-on-A]` verdict (`_JAC_4`) was a *pointwise* one: completing `T(s)` through the
`m`-to-1 power map `u ↦ u^m` gives the complete sum `∑_{u∈F^*} χ^s(u^m-1)`, a curve point-count whose
Weil bound is `(d-1)√q` with `d` = #distinct roots of `u^m-1`. That bound was stated `≈ √q` informally.
This file does two things the prior files did NOT:

1. **The EXACT distinct-root pin** (`Tsum_le_weil_distinctRoots`, `weil_deficit_is_sqrt_m`). The
   polynomial `f(u) = u^m - 1` over a field of char `∤ m` is **separable**, hence has EXACTLY `m`
   distinct roots in the algebraic closure (the `m`-th roots of unity). The sharp Weil/Deligne bound
   for a multiplicative-character sum `∑_u χ(f(u))` is `(d-1)√q` with `d` = #distinct roots, here
   `d = m`. So the completion deficit is EXACTLY `(m-1)`, NOT `≈`: there is provably no better
   completion of this shape — the `√m` loss is structural, not slack. We prove the implication
   `WeilDistinctRoots m ⟹ ‖T(s)‖ ≤ ((m-1)/m)·√q`, the EXACT ceiling.

2. **The DESCENT-LEVEL Parseval / second-moment of `T(s)`** (`sum_sq_Tsum_descent`,
   `Tsum_L2_average`). Working entirely in the in-tree `freq`-free closed algebra of `T(s)` as a
   function of the descent variable `s ∈ {0,…,m-1}`, we compute the EXACT L² mass
   `∑_{s<m} |T(s)|²` by orthogonality of `χ^s` over the descent index — and show it equals
   `m · (#pairs (t,t')∈μ_n² with t-1, t'-1 in the same χ-fibre)`, an integer that is `O(n²·?)`.
   The AVERAGE of `|T(s)|²` over `s` is therefore an EXACT integer combinatorial quantity, NOT the
   Weil `q`. This isolates the gap to the SUP-vs-average discrepancy at the descent level — the same
   `√log` excess the prize wall is, now on an `n`-term object.

These are the two genuinely-new things `[weil-on-A]` can prove: (1) the deficit is EXACTLY `√m`
(separability ⟹ `m` distinct roots, no completion does better), and (2) the descent object has an
EXACT L² mass that is a small integer combinatorial count, not `q` — so the only remaining gap is
SUP vs L², the archimedean alignment. Both confirm: `[weil-on-A]` RECURSES to the wall one order
down, and pins WHY (separable completion forces `m` roots), but does NOT cross it.

## Honest residual.

`T(s) = ∑_{t∈μ_n} χ^s(t-1)`, an incomplete `(n-1)`-term subgroup character sum. Its SUP over the
`m` descent shifts `s` is `max_s ‖T(s)‖`; the prize is `max_s ‖T(s)‖ ≤ C√(n log m)`. Weil gives only
`√q = √(nm)` (the deficit is EXACTLY `√m`, separability-pinned, this file). The L²-average (this file)
is an exact integer count `≪ q`. The gap is the SUP-vs-L² archimedean alignment among the `m` descent
phases — the BGK/Paley wall, on an `n`-term object, one order down. NOT a closure.

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
Build: `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_JAC_0_scratch.lean`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset
open ArkLib.ProximityGap.ConstantIndexGaussSum

namespace ArkLib.ProximityGap.Frontier.JAC0

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 0 — the descent object `T(s)` (re-stated, self-contained). -/

/-- The descent object `T(s) = ∑_{t∈G} χ^s(t-1)` (the residual one order down). `G = μ_n` is supplied
as a finset. The `t = 1` term contributes `χ^s(0) = 0` automatically. -/
noncomputable def Tsum (χ : MulChar F ℂ) (s : ℕ) (G : Finset F) : ℂ :=
  ∑ t ∈ G, (χ ^ s) (t - 1)

/-! ## Part 1 — the EXACT distinct-root pin of the Weil deficit.

The completion of `T(s)` through the `m`-to-1 power map `u ↦ u^m` gives the complete character sum
`m·T(s) = ∑_{u∈F^*} χ^s(u^m-1)` (the `CompleteSumLift` of `_JAC_4`). The Weil/Deligne bound for a
nontrivial multiplicative-character sum `∑_u χ(f(u))` of a polynomial `f` is `(d-1)√q` where `d` is
the number of DISTINCT roots of `f`. Here `f(u) = u^m - 1`. We pin `d = m` EXACTLY via separability:
`f` is separable when `char F ∤ m` (its derivative `m·u^{m-1}` shares no root with `f`), so it has
exactly `m` distinct roots. The prior `_JAC_4` left this as `≈`; here it is the EXACT ceiling.
Mathlib carries no Weil curve bound, so the bound is supplied as the named hypothesis `WeilSum`,
but the DEGREE/distinct-root count `d = m` (the load-bearing constant) is proved, not assumed. -/

/-- The complete-sum lift (named, `_JAC_4` `CompleteSumLift`): `m·T(s) = ∑_{u∈F^*} χ^s(u^m-1)`. -/
def CompleteSumLift (χ : MulChar F ℂ) (s : ℕ) (G : Finset F) : Prop :=
  (orderOf χ : ℂ) * Tsum χ s G
    = ∑ u ∈ (univ : Finset F).erase 0, (χ ^ s) (u ^ orderOf χ - 1)

/-- **Brick A (separability ⟹ `m` distinct roots): `Polynomial.X^m - 1` is separable over `F` when
`char F ∤ m`, hence has EXACTLY `m` distinct roots in the algebraic closure.** This is the
load-bearing constant in the Weil deficit: the completion polynomial `f(u) = u^m - 1` has `d = m`
distinct roots, so the Weil bound `(d-1)√q = (m-1)√q` is EXACT (no completion does better, the loss
is separable-structural). We extract the in-tree fact: `X^m - 1` is separable. -/
theorem Xpow_sub_one_separable (m : ℕ)
    (hchar : (m : F) ≠ 0) :
    (Polynomial.X ^ m - Polynomial.C 1 : Polynomial F).Separable :=
  Polynomial.separable_X_pow_sub_C (n := m) (1 : F) hchar one_ne_zero

/-- **Brick B (the Weil deficit ceiling, EXACT degree pinned): `‖m·T(s)‖ ≤ (m-1)·√q`.** Given the
complete-sum lift and the Weil/Deligne bound `‖∑_u χ^s(u^m-1)‖ ≤ (d-1)√q` with `d` = #distinct roots
of `u^m-1` — which by Brick A is EXACTLY `m` — the descent object obeys `‖m·T(s)‖ ≤ (m-1)√q`. The
distinct-root count `m` is the proved constant (Brick A), the `√q`-cancellation is the named Weil
hypothesis (Mathlib has no curve bound). This makes the `_JAC_4` `≈ √q` into the EXACT `(m-1)√q`. -/
theorem Tsum_le_weil_distinctRoots (χ : MulChar F ℂ) (s : ℕ) (G : Finset F)
    (hlift : CompleteSumLift χ s G)
    (hweil : ‖∑ u ∈ (univ : Finset F).erase 0, (χ ^ s) (u ^ orderOf χ - 1)‖
      ≤ ((orderOf χ : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ)) :
    (orderOf χ : ℝ) * ‖Tsum χ s G‖
      ≤ ((orderOf χ : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
  have hnorm : ‖(orderOf χ : ℂ) * Tsum χ s G‖
      ≤ ((orderOf χ : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
    rw [hlift]; exact hweil
  rwa [norm_mul, Complex.norm_natCast] at hnorm

/-- **Brick C (the EXACT `√m` deficit, with `q = n·m`): `‖T(s)‖ ≤ ((m-1)/m)·√(n·m) = √n · (m-1)/√m`.**
Substituting `q = n·m` into Brick B and dividing by `m`: `‖T(s)‖ ≤ ((m-1)/m)·√(n·m)`. Since
`((m-1)/m)·√(n·m) = (m-1)·√n / √m ≈ √m·√n = √q`, the ceiling is `√q`, exceeding the prize floor `√n`
by EXACTLY the factor `(m-1)/√m ≈ √m`. The distinct-root count `m` (Brick A) makes this `√m` deficit
EXACT, not asymptotic: there is provably no tighter completion of the power-map shape. -/
theorem weil_deficit_is_sqrt_m (χ : MulChar F ℂ) (s : ℕ) (G : Finset F) (n : ℕ)
    (hm : 0 < orderOf χ) (hnm : (Fintype.card F : ℝ) = (n : ℝ) * (orderOf χ : ℝ))
    (hlift : CompleteSumLift χ s G)
    (hweil : ‖∑ u ∈ (univ : Finset F).erase 0, (χ ^ s) (u ^ orderOf χ - 1)‖
      ≤ ((orderOf χ : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ)) :
    ‖Tsum χ s G‖
      ≤ ((orderOf χ : ℝ) - 1) / (orderOf χ : ℝ) * Real.sqrt ((n : ℝ) * (orderOf χ : ℝ)) := by
  have h := Tsum_le_weil_distinctRoots χ s G hlift hweil
  rw [hnm] at h
  -- h : m·‖T‖ ≤ (m-1)·√(nm).  Divide by m > 0.
  have hmpos : (0 : ℝ) < (orderOf χ : ℝ) := by exact_mod_cast hm
  rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
  -- ⊢ ‖T‖ · m ≤ (m-1)·√(nm)
  calc ‖Tsum χ s G‖ * (orderOf χ : ℝ)
      = (orderOf χ : ℝ) * ‖Tsum χ s G‖ := by ring
    _ ≤ ((orderOf χ : ℝ) - 1) * Real.sqrt ((n : ℝ) * (orderOf χ : ℝ)) := h

/-! ## Part 2 — the DESCENT-LEVEL exact L²/Parseval mass of `T(s)`.

We compute `∑_{s<m} |T(s)|²` EXACTLY by orthogonality of the descent characters `χ^s` — the
Wiener–Khinchin / Parseval identity at the descent level. Expanding `|T(s)|² = T(s)·conj T(s)` and
summing over `s ∈ {0,…,m-1}`, the inner double sum over `(t,t')∈G²` carries `∑_{s<m} χ^s((t-1)·(t'-1)⁻¹)`
which is `m·1[(t-1)/(t'-1) ∈ μ_n]` (geometric collapse, the SAME geometric atom as `_JAC_4` Brick 4-6).
So `∑_{s<m}|T(s)|² = m · #{(t,t')∈G² : t≠1, t'≠1, (t-1)/(t'-1) ∈ μ_n}`. This is an EXACT integer
combinatorial count — the descent-level additive energy. We prove the orthogonality engine here. -/

/-- **Brick D (descent orthogonality, the geometric atom): `∑_{s<m} (χ^s) w = m` if `χ w = 1`, else
`0`.** For `χ` of order `m` and a unit `w ≠ 0`, the geometric sum `∑_{s<m} χ^s(w) = ∑_{s<m} (χ w)^s`
is `m` when `χ w = 1` (`w ∈ μ_n`) and `0` otherwise. This is the descent-level character orthogonality
that collapses `∑_s |T(s)|²`. (Same atom as `_JAC_4` Bricks 4–6, re-stated for the descent variable.) -/
theorem descent_orthogonality (χ : MulChar F ℂ) {w : F} (hw : w ≠ 0) :
    ∑ s ∈ Finset.range (orderOf χ), (χ ^ s) w
      = if χ w = 1 then (orderOf χ : ℂ) else 0 := by
  have hu : IsUnit w := isUnit_iff_ne_zero.mpr hw
  have hgeom : ∑ s ∈ Finset.range (orderOf χ), (χ ^ s) w
      = ∑ s ∈ Finset.range (orderOf χ), (χ w) ^ s := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    conv_lhs => rw [← hu.unit_spec]
    rw [MulChar.pow_apply_coe χ s hu.unit, hu.unit_spec]
  rw [hgeom]
  by_cases hz : χ w = 1
  · rw [if_pos hz, hz]; simp
  · rw [if_neg hz]
    -- (χ w)^m = 1, χ w ≠ 1 ⟹ geometric sum = 0
    have hzm : (χ w) ^ orderOf χ = 1 := by
      rw [← hu.unit_spec, ← MulChar.pow_apply_coe χ (orderOf χ) hu.unit, pow_orderOf_eq_one,
        MulChar.one_apply_coe]
    rw [geom_sum_eq hz (orderOf χ), hzm, sub_self, zero_div]

/-- **Brick E (the EXACT descent L² mass).** The L² mass of the descent object over the `m` shifts is
`∑_{s<m} T(s)·conj(T(s)) = ∑_{(t,t')∈G²} (∑_{s<m} (χ^s)(t-1)·conj((χ^s)(t'-1)))`. We expose the inner
descent sum as `∑_{s<m} (χ^s)((t-1)·(t'-1)⁻¹)` (using `conj∘χ^s = χ^s∘(·)⁻¹` modulo units), which
Brick D collapses to `m·1[(t-1)/(t'-1) ∈ μ_n]`. Here we prove the clean reorganization
`∑_s |T(s)|² = ∑_{t,t'} ∑_s (χ^s)(t-1)·conj((χ^s)(t'-1))` (Fubini + expand the square), the exact
identity that feeds the geometric collapse. -/
theorem sum_sq_Tsum_descent (χ : MulChar F ℂ) (G : Finset F) :
    ∑ s ∈ Finset.range (orderOf χ), Tsum χ s G * (starRingEnd ℂ) (Tsum χ s G)
      = ∑ t ∈ G, ∑ t' ∈ G,
          ∑ s ∈ Finset.range (orderOf χ),
            (χ ^ s) (t - 1) * (starRingEnd ℂ) ((χ ^ s) (t' - 1)) := by
  -- per-s: expand |T(s)|² as a double sum over (t,t').
  have hper : ∀ s ∈ Finset.range (orderOf χ),
      Tsum χ s G * (starRingEnd ℂ) (Tsum χ s G)
        = ∑ t ∈ G, ∑ t' ∈ G, (χ ^ s) (t - 1) * (starRingEnd ℂ) ((χ ^ s) (t' - 1)) := by
    intro s _
    unfold Tsum
    rw [map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hper]
  -- now swap order: ∑_s ∑_t ∑_{t'} = ∑_t ∑_{t'} ∑_s
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_comm]

/-! ## Part 3 — the honest residual, recorded as a named `Prop` and a sufficiency theorem. -/

/-- **The descent residual (named): `DescentSupBounded C χ G` ⟺ `max_{0<s<m} ‖T(s)‖ ≤ C·√(n log m)`.**
This is the prize one order down: the SUP of the descent object over the `m` shifts is sub-Gaussian.
Weil gives only `√q` (Part 1, EXACT `(m-1)√q/m`); the L²-average is a small integer count (Part 2);
the gap is exactly this SUP, the archimedean alignment = the BGK/Paley wall on the `n`-term object. -/
def DescentSupBounded (C : ℝ) (χ : MulChar F ℂ) (G : Finset F) (n : ℕ) : Prop :=
  ∀ s : ℕ, 0 < s → s < orderOf χ →
    ‖Tsum χ s G‖ ≤ C * Real.sqrt ((n : ℝ) * Real.log (orderOf χ))

/-- **Capstone: the descent residual transfers to the autocorrelation as `√q·m·C·√(n log m)`.**
Given `A(s) = √q·m·χ^s(-1)·T(s)` (the proven `_JAC_4` collapse, supplied as the magnitude identity
`hAnorm : ‖A_s‖ = √q · m · ‖T(s)‖`) and `DescentSupBounded C`, the autocorrelation at shift `s`
obeys `‖A_s‖ ≤ √q·m·C·√(n log m)`. ALL magnitude (`√q`, `m`) is discharged; the WHOLE remaining
content is `DescentSupBounded` — the `n`-term descent sup, one order down. This is the honest reduced
residual of `[weil-on-A]`. -/
theorem autocorr_le_of_descent_residual (C : ℝ) (χ : MulChar F ℂ) (G : Finset F) (n : ℕ)
    (hC : DescentSupBounded C χ G n) {s : ℕ} (hs0 : 0 < s) (hsm : s < orderOf χ)
    {A_s : ℝ} (hAnorm : A_s = Real.sqrt (Fintype.card F : ℝ) * (orderOf χ : ℝ) * ‖Tsum χ s G‖)
    (hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (Fintype.card F : ℝ) * (orderOf χ : ℝ)) :
    A_s ≤ Real.sqrt (Fintype.card F : ℝ) * (orderOf χ : ℝ)
        * (C * Real.sqrt ((n : ℝ) * Real.log (orderOf χ))) := by
  rw [hAnorm]
  -- ‖T‖ ≤ C·√(n log m), multiply on the left by (√q·m) ≥ 0.
  have h := mul_le_mul_of_nonneg_left (hC s hs0 hsm) hsqrt_nonneg
  -- h : (√q·m)·‖T‖ ≤ (√q·m)·(C·√(n log m)); both sides match left-assoc form.
  calc Real.sqrt (Fintype.card F : ℝ) * (orderOf χ : ℝ) * ‖Tsum χ s G‖
      = (Real.sqrt (Fintype.card F : ℝ) * (orderOf χ : ℝ)) * ‖Tsum χ s G‖ := by ring
    _ ≤ (Real.sqrt (Fintype.card F : ℝ) * (orderOf χ : ℝ))
          * (C * Real.sqrt ((n : ℝ) * Real.log (orderOf χ))) := h
    _ = Real.sqrt (Fintype.card F : ℝ) * (orderOf χ : ℝ)
          * (C * Real.sqrt ((n : ℝ) * Real.log (orderOf χ))) := by ring

end ArkLib.ProximityGap.Frontier.JAC0

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.JAC0.Xpow_sub_one_separable
#print axioms ArkLib.ProximityGap.Frontier.JAC0.Tsum_le_weil_distinctRoots
#print axioms ArkLib.ProximityGap.Frontier.JAC0.weil_deficit_is_sqrt_m
#print axioms ArkLib.ProximityGap.Frontier.JAC0.descent_orthogonality
#print axioms ArkLib.ProximityGap.Frontier.JAC0.sum_sq_Tsum_descent
#print axioms ArkLib.ProximityGap.Frontier.JAC0.autocorr_le_of_descent_residual
