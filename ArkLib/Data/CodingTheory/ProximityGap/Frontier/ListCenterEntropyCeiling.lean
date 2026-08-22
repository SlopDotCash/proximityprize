/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26EntropyForm
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The list-center entropy ceiling constant `c(ρ) = H₂(ρ)` (issue #444)

The in-tree [KKH26] asymptotic ceiling (`KKH26AsymptoticCeiling.lean`) phrases the gap below
capacity as `Θ_ρ(1/log n)`, and Route 2 (`docs/kb/deltastar-444-route2-closed-crho-H2-…`)
pins the constant to the **binary entropy** `c(ρ) = H₂(ρ)`.  This file grounds that constant
**in tree**, axiom-clean, and proves that it is the *binding* (larger) constant against the
in-tree line-family rate `Φ(ρ) = ρ + ½H₂(2ρ)`.

## The math ([KKH26] Appendix A / Remark 5, list-center family)

A single deep-hole-type received word `u = x^{rm}` has a large list of close RS codewords:
the codewords correspond to the vanishing polynomials `v_S(X^m)` over `r`-subsets `S` of a
size-`s` subgroup `G ⊆ μ_n`.  Remark 5 — *"different subsets give different vanishing
polynomials"* — makes the list size **exactly** `C(s, r)` (a binomial; no additive
combinatorics).  With `r = ρ·s`, the method of types gives
`log₂ C(s, ρs) = s·H₂(ρ)·(1 − o(1))`, so the per-symbol exponent is `H₂(ρ)`, **strictly
larger** than the dyadic line-family rate `Φ(ρ) = ρ + ½H₂(2ρ)` (they agree only as `ρ → 0`).
The larger constant **binds** (smaller `δ*`), so `c(ρ) = max(H₂, Φ) = H₂(ρ)`.

Crossover at the prize budget `2^{c(ρ)/η} = ε*·|F| ≈ n = 2^μ` gives the cushion
`η* = c(ρ)/log₂ n` and the closed ceiling value `δ*_ceiling = (1 − ρ) − H₂(ρ)/log₂ n`.

## Main results

* `listCenterRate ρ := H₂(ρ)` (`= binEntropy ρ / log 2`) — the per-symbol list-center
  exponent.  `lineRate ρ := ρ + ½H₂(2ρ)` — the in-tree dyadic line-family exponent.
* `listCenterRate_gt_lineRate` — **the binding comparison**: `H₂(ρ) > Φ(ρ)` for every
  `ρ ∈ (0, 1/2]` (general; proved from strict convexity of `x ↦ x log x` — no `norm_num`,
  covers all four prize rates `1/2, 1/4, 1/8, 1/16` as instances).  Plus
  `listCenterRate_gt_lineRate_half`, the clean `ρ = 1/2` value `1 > 1/2`.
* `listCenter_count_ge` — **the unconditional combinatorial count**: the list size
  `C(s, r) ≥ 2^{s·H₂(r/s)}/(s+1)` (reusing `choose_ge_two_rpow_entropy_div`); the entropy
  exponent `s·H₂(r/s)` is exactly `s·listCenterRate (r/s)`.
* `deltaStarCeilingEntropy ρ n := (1 − ρ) − H₂(ρ)/log₂ n` — the closed-form ceiling **value**.
* `deltaStar_ceiling_entropy_of_TZ` — **the conditional ceiling**: under the named
  Thorner–Zaman supply `TZPrimeSupply` (the cited [TZ24] analytic input — never proved here,
  the §6 modularity convention, exactly as `kkh26_mcaDeltaStar_le_of_TZ`), the formal MCA
  threshold of the explicit list-center code is `≤ 1 − r/2^μ`, the finite-parameter form of
  the entropy ceiling at polynomial field size.

## Honest status

* The combinatorial count (`listCenter_count_ge`) and the binding comparison
  (`listCenterRate_gt_lineRate`) are **unconditional and axiom-clean**.
* The prize-scale ceiling (`deltaStar_ceiling_entropy_of_TZ`) is **conditional** on the named
  `TZPrimeSupply` hypothesis (and the numeric budget), inherited verbatim from
  `kkh26_mcaDeltaStar_le_of_TZ`.
* The **floor** — that the worst-window list *reaches* `2^{s·H₂(ρ)}` at the prize prime, so
  the ceiling is *tight* and the conjecture `δ* = (1−ρ) − H₂(ρ)/log₂ n` is an *equality* — is
  the recognized open prize and is **NOT** claimed here.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782 (Appendix A, Remark 5; Lemma 2; Theorem 1).
* [TZ24] J. Thorner, A. Zaman, *Refinements to the prime number theorem in arithmetic
  progressions*, Cor 3.1.  Issue #334, #444.
-/

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ## The two per-symbol rates: list-center `H₂(ρ)` vs line-family `Φ(ρ)` -/

/-- The **list-center per-symbol exponent** `c(ρ) = H₂(ρ)` ([KKH26] Appendix A / Remark 5):
the base-2 binary entropy, `H₂(ρ) = binEntropy ρ / log 2`.  This is the exponential rate of
the exact list size `C(s, ρs)` (method of types). -/
noncomputable def listCenterRate (ρ : ℝ) : ℝ := Real.binEntropy ρ / Real.log 2

/-- The in-tree **dyadic line-family per-symbol exponent** `Φ(ρ) = ρ + ½H₂(2ρ)` (the rate of
the half-domain sign-free count `2^r·C(s/2, r)` of `KKH26WitnessSpread.lean`). -/
noncomputable def lineRate (ρ : ℝ) : ℝ := ρ + Real.binEntropy (2 * ρ) / (2 * Real.log 2)

/-- `H₂` in bits at `1/2` is exactly `1`: `binEntropy (1/2) = log 2`. -/
lemma listCenterRate_half : listCenterRate (1 / 2) = 1 := by
  unfold listCenterRate
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
    Real.binEntropy_eq_log_two.mpr rfl]
  exact div_self (Real.log_pos one_lt_two).ne'

/-- `Φ` at `1/2` is exactly `1/2`: `binEntropy (2·(1/2)) = binEntropy 1 = 0`. -/
lemma lineRate_half : lineRate (1 / 2) = 1 / 2 := by
  unfold lineRate
  rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num,
    Real.binEntropy_eq_zero.mpr (Or.inr rfl)]
  norm_num

/-! ## The binding comparison `H₂(ρ) > Φ(ρ)` on `(0, 1/2]`

The difference, cleared of `log 2`, is
`(H₂(ρ) − Φ(ρ))·log 2 = ½[ (1−2ρ)·log(1−2ρ) − (2−2ρ)·log((1−ρ)) ]` (after the substitution
`a = 1−2ρ`, `1−ρ = (1+a)/2`).  Writing `g(x) = x·log x`, this is `½[g(a) − 2·g((1+a)/2)]`,
which is positive by **strict convexity of `g` at the midpoint of `a < 1`**:
`g((a+1)/2) < ½g(a) + ½g(1) = ½g(a)` (since `g(1) = 0`). -/

/-- **The strict-convexity midpoint step** for `g(x) = x·log x` at `a < 1` (`0 ≤ a`):
`((1 + a)/2)·log((1 + a)/2) < (a·log a)/2`.  Pure analysis; the engine of the comparison. -/
private lemma mul_log_midpoint_lt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((1 + t) / 2) * Real.log ((1 + t) / 2) < t * Real.log t / 2 := by
  have hconv := Real.strictConvexOn_mul_log
  have hxs : t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr ht0
  have hys : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr zero_le_one
  have hne : t ≠ 1 := ne_of_lt ht1
  have h := hconv.2 hxs hys hne (show (0:ℝ) < 1 / 2 by norm_num)
    (show (0:ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at h
  rw [Real.log_one, mul_zero] at h
  -- h : (1/2 * t + 1/2 * 1) * log (1/2 * t + 1/2 * 1) < 1/2 * (t * log t) + 1/2 * 0
  have harg : (1 / 2 : ℝ) * t + 1 / 2 * 1 = (1 + t) / 2 := by ring
  rw [harg] at h
  calc ((1 + t) / 2) * Real.log ((1 + t) / 2)
      < 1 / 2 * (t * Real.log t) + 1 / 2 * 0 := h
    _ = t * Real.log t / 2 := by ring

/-- **The binding comparison** ([KKH26] Appendix A): the list-center rate strictly exceeds the
line-family rate, `H₂(ρ) > Φ(ρ)`, for every `ρ ∈ (0, 1/2]`.  Hence the *binding* (smaller
`δ*`) constant is `c(ρ) = max(H₂, Φ) = H₂(ρ)`.  This is general (no `norm_num`); the four
prize rates `1/2, 1/4, 1/8, 1/16 ∈ (0, 1/2]` are instances. -/
theorem listCenterRate_gt_lineRate {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    lineRate ρ < listCenterRate ρ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [lineRate, listCenterRate, ← sub_pos]
  -- reduce to a positivity statement cleared of `log 2`:
  -- `binEntropy ρ/log2 − (ρ + binEntropy(2ρ)/(2 log2))
  --    = (binEntropy ρ − ρ·log2 − binEntropy(2ρ)/2)/log2`.
  rw [show Real.binEntropy ρ / Real.log 2 - (ρ + Real.binEntropy (2 * ρ) / (2 * Real.log 2))
        = (Real.binEntropy ρ - ρ * Real.log 2 - Real.binEntropy (2 * ρ) / 2) / Real.log 2 by
      field_simp; ring]
  apply div_pos _ hlog2
  -- bounds on the relevant arguments
  set a : ℝ := 1 - 2 * ρ with ha
  have h12ρ0 : 0 ≤ a := by rw [ha]; linarith
  have h12ρ1 : a < 1 := by rw [ha]; linarith
  have ha0 : 0 < 1 - a := by rw [ha]; linarith
  have ha1 : 0 < 1 + a := by rw [ha]; linarith
  -- `binEntropy x = -(x log x) - (1-x) log (1-x)` (negMulLog form, valid on all of ℝ here)
  have hbE : ∀ x : ℝ, Real.binEntropy x
      = -(x * Real.log x) - (1 - x) * Real.log (1 - x) := by
    intro x
    rw [Real.binEntropy]
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp
    rcases eq_or_ne (1 - x) 0 with hx1 | hx1
    · rw [hx1]; simp [Real.log_inv]
    · rw [Real.log_inv, Real.log_inv]; ring
  -- Express the cleared numerator exactly as `½·a·log a − ((1+a)/2)·log((1+a)/2)`.
  -- All `binEntropy` log-atoms are quotient logs; split via `log_div`, then it is a
  -- polynomial identity in the four atoms `{log(1-a), log(1+a), log a, log 2}`.
  have hkey : Real.binEntropy ρ - ρ * Real.log 2 - Real.binEntropy (2 * ρ) / 2
      = a * Real.log a / 2 - (1 + a) / 2 * Real.log ((1 + a) / 2) := by
    have hρa : ρ = (1 - a) / 2 := by rw [ha]; ring
    rw [hbE ρ, hbE (2 * ρ), hρa]
    -- the four log atoms appearing in the goal, each a quotient/affine log
    have l1 : Real.log ((1 - a) / 2) = Real.log (1 - a) - Real.log 2 := by
      rw [Real.log_div ha0.ne' two_ne_zero]
    have l2 : Real.log (1 - (1 - a) / 2) = Real.log (1 + a) - Real.log 2 := by
      rw [show (1 : ℝ) - (1 - a) / 2 = (1 + a) / 2 by ring,
        Real.log_div ha1.ne' two_ne_zero]
    have l3 : Real.log (2 * ((1 - a) / 2)) = Real.log (1 - a) := by
      rw [show (2 : ℝ) * ((1 - a) / 2) = 1 - a by ring]
    have l4 : Real.log (1 - 2 * ((1 - a) / 2)) = Real.log a := by
      rw [show (1 : ℝ) - 2 * ((1 - a) / 2) = a by ring]
    have l5 : Real.log ((1 + a) / 2) = Real.log (1 + a) - Real.log 2 := by
      rw [Real.log_div ha1.ne' two_ne_zero]
    rw [l1, l2, l3, l4, l5]
    ring
  rw [hkey]
  -- the convexity midpoint gap, the engine of positivity
  have hgap := mul_log_midpoint_lt h12ρ0 h12ρ1
  linarith [hgap]

/-- The binding comparison at the rate `ρ = 1/2` in closed value form: `Φ(1/2) = 1/2 < 1 =
H₂(1/2)`. -/
theorem listCenterRate_gt_lineRate_half : lineRate (1 / 2) < listCenterRate (1 / 2) := by
  rw [lineRate_half, listCenterRate_half]; norm_num

/-! ## The unconditional combinatorial list-size count (method of types)

The list size of the [KKH26] list-center family is **exactly** `C(s, r)` (Remark 5, distinct
vanishing polynomials).  Its entropy lower bound is the reused `choose_ge_two_rpow_entropy_div`
(axiom-clean, `KKH26EntropyForm.lean`); the exponent `s·H₂(r/s)` is `s·listCenterRate (r/s)`. -/

/-- **The list-center count is `≥ 2^{s·H₂(r/s)}/(s+1)`** (method of types, unconditional).
The list size `C(s, r)` of the [KKH26] list-center family satisfies
`C(s, r) ≥ 2^{s·listCenterRate (r/s)}/(s+1)` for `0 < r < s` — directly the reused
`choose_ge_two_rpow_entropy_div`, written with the per-symbol rate `listCenterRate (r/s) =
H₂(r/s)`. -/
theorem listCenter_count_ge {s r : ℕ} (hr0 : 0 < r) (hrs : r < s) :
    (2 : ℝ) ^ ((s : ℝ) * listCenterRate ((r : ℝ) / (s : ℝ))) / ((s : ℝ) + 1)
      ≤ (s.choose r : ℝ) := by
  have h := choose_ge_two_rpow_entropy_div (n := s) (k := r) hr0 hrs
  -- `(s:ℝ) * binEntropy (r/s) / log 2 = (s:ℝ) * (binEntropy (r/s) / log 2)`
  have hrw : (s : ℝ) * listCenterRate ((r : ℝ) / (s : ℝ))
      = (s : ℝ) * Real.binEntropy ((r : ℝ) / (s : ℝ)) / Real.log 2 := by
    unfold listCenterRate; ring
  rwa [hrw]

/-! ## The closed-form ceiling value -/

/-- The **closed-form `δ*` ceiling value** `(1 − ρ) − H₂(ρ)/log₂ n` (Route 2, [KKH26]
Appendix A): capacity `1 − ρ` minus the list-center cushion `H₂(ρ)/log₂ n`.  No undetermined
quantity — a definite function of `ρ` and `n`. -/
noncomputable def deltaStarCeilingEntropy (ρ : ℝ) (n : ℕ) : ℝ :=
  (1 - ρ) - listCenterRate ρ / Real.logb 2 (n : ℝ)

/-- The ceiling value, unfolded with the explicit entropy: `(1−ρ) − (binEntropy ρ / log 2)/log₂ n`. -/
lemma deltaStarCeilingEntropy_eq (ρ : ℝ) (n : ℕ) :
    deltaStarCeilingEntropy ρ n
      = (1 - ρ) - (Real.binEntropy ρ / Real.log 2) / Real.logb 2 (n : ℝ) := rfl

/-! ## The conditional ceiling, packaged on the named Thorner–Zaman supply

The finite-parameter form of the ceiling at polynomial field size is exactly the in-tree
`kkh26_mcaDeltaStar_le_of_TZ` (conditional on the named `TZPrimeSupply`).  We restate it as
the **list-center** ceiling, recording the closed constant alongside the threshold bound.  The
combinatorial entropy count above is unconditional; *only* the prime-existence input
`TZPrimeSupply` is the named hypothesis (the §6 modularity convention). -/

/-- **The conditional list-center entropy ceiling at polynomial field size** (issue #444).
Under the named Thorner–Zaman supply `TZPrimeSupply n β supply` (the cited [TZ24] input — not
proved here) and the bad-prime budget inequality, there is a prime `p = Θ(n^β)` and a smooth
domain `⟨g⟩ ⊆ F_p^×` of order `n` such that the formal MCA threshold of the explicit
list-center code satisfies, for every `ε*` below the list budget,

  `mcaDeltaStar(C, ε*) ≤ 1 − r/2^μ`,

the finite-parameter form of the entropy ceiling `δ* ≤ (1 − ρ) − H₂(ρ)/log₂ n`.  This is a
verbatim re-export of `kkh26_mcaDeltaStar_le_of_TZ`: the *only* unproven input is `hTZ` (plus
the numeric budget `hcount`).  The matching **floor** (tightness — that the conjecture is an
*equality*) is the recognized open prize and is NOT asserted. -/
theorem deltaStar_ceiling_entropy_of_TZ {n : ℕ} {β : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : TZPrimeSupply n β supply) {μ m r : ℕ}
    (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ μ : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hcount : ((collisionPairs μ r).card : ℝ) *
        (Real.log (((((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  kkh26_mcaDeltaStar_le_of_TZ hTZ hμ hm hn hr2 hr hx hpl hcount

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.listCenterRate_half
#print axioms ArkLib.ProximityGap.KKH26.lineRate_half
#print axioms ArkLib.ProximityGap.KKH26.listCenterRate_gt_lineRate
#print axioms ArkLib.ProximityGap.KKH26.listCenterRate_gt_lineRate_half
#print axioms ArkLib.ProximityGap.KKH26.listCenter_count_ge
#print axioms ArkLib.ProximityGap.KKH26.deltaStar_ceiling_entropy_of_TZ
