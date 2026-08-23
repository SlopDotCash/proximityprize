/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B3_antitone_charp_obstruction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6F1_gaussian_step_telescope

/-!
# wf-A03: the S1 ratio object is NOT the B3 step-ratio — the antitone obstruction does not transfer

## The reconciliation question (#444)

The S1 dichotomy (`_wfS1_transfer_slack_prize`) reduces the `K = 1` (sharp char-0 constant) prize to
the **char-0-limit transfer** `E_r^{NP} ≤ (2r-1)‼ · n^r`, and its anchored form
`charzero_limit_of_anchor_antitone` discharges this from the Parseval anchor `E_1^{NP} ≤ n` PLUS the
**per-`r` envelope** `E_r^{NP} ≤ E_1^{NP} · (2r-1)‼ · n^{r-1}`. Equivalently, writing
`g_r := E_r^{NP} / ((2r-1)‼ · n^r)` (the Wick-normalized **ratio**, `g_1 = K_eff^{NP}(1) = 1 − n/p`),
the envelope is exactly **`g_r ≤ g_1`** — the *geometric-mean/ratio* statement
`K_eff^{NP}(r) = g_r^{1/r}` antitone-anchored at `r = 1`.

The B3 obstruction (`_wf8B3_antitone_charp_obstruction`) hard-refuted, at the explicit prize-scale
prime `p = 1 001 153` (`n = 32`, `β = 3.99`, full enumeration), the **step-ratio antitonicity**
`StepRatioAntitone`: `R(r+1) ≤ R(r)` where `R(r) = NormStepRatio M n r = M(r+1)/((2r+1)·n·M(r))`.

**A03 asks: does B3 also kill the S1 ratio object?** The answer is a clean, decisive **NO**, and this
file makes the reconciliation rigorous. The two objects are *logically distinct*:

* `R(r) ≤ 1` for each `r` (the **per-step Gaussian law** `GaussianStepLaw`) ⟺ `g_{r+1} ≤ g_r`
  (the ratio is decreasing) — THIS is what S1 needs.
* `R(r+1) ≤ R(r)` (the **antitonicity** of `R`) — THIS is what B3 refutes.

Antitonicity of `R` is neither necessary nor sufficient for `R(r) ≤ 1`. A sequence can have its step
ratio *rise* at one rung (`R(r) < R(r+1)`, the B3 bump) while every rung still sits below `1`. At the
B3 prime the data is exactly this:

| r | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| `R(r)=S^{NP}(r)` | .9656 | .9399 | .9234 | **.9219** | **.9323** | .9403 | .9313 | .9015 |
| `g_r=E^{NP}_r/c_r` | .9990 | .9646 | .9066 | .8372 | .7718 | .7196 | .6766 | .6301 |

`R(4) = .9219 < R(5) = .9323` — antitone FAILS (B3). Yet *every* `R(r) < 1`, so the per-step law
holds, and `g_r` is **strictly decreasing through the bump** (`g_4 = .8372 > g_5 = .7718`). The
geometric-mean `K_eff^{NP}(r)` is antitone with sup `= g_1 = 1 − n/p < 1`. Measured (Rust/FFT, exact
`cos`-period sums) at `β = 4` for `n = 16..256` (structured `v₂ = μ` AND generic): `g_r` decreasing,
`K_eff^{NP}` antitone, `sup_r K_eff^{NP}(r) = K_eff^{NP}(1) = 1 − n/p`, gap `+0.00` everywhere; only
the degenerate pure-2-power prime `p = 65537 = 2^{16}+1` (`n = 16`) violates it — *not* the prize
regime (the genuine `β = 4` structured prime `p = 65617` is clean).

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

The reconciliation is a *logical* fact about moment sequences, made rigorous and decidable:

* `gStepRatio_eq_ratio_quotient` — the algebraic identity `R(r) = g_{r+1}/g_r` (the step ratio IS the
  consecutive ratio of the Wick-normalized sequence). Hence `R(r) ≤ 1 ⟺ g_{r+1} ≤ g_r` (positive `g`).
* `ratioDecreasing_iff_stepLaw_pos` — the **S1 object** `RatioDecreasing` (`g` decreasing) is
  *equivalent* to the per-step `GaussianStepLaw` on `r ≥ 1`, NOT to `StepRatioAntitone`.
* `stepLaw_holds_at_B3_bump` — on B3's *own* prize-scale witness `bumpWitness` (the `n = 32`,
  `p = 1 001 153` bump), the per-step law `R(4) ≤ 1 ∧ R(5) ≤ 1` HOLDS (decidable `norm_num`).
* `S1_object_survives_B3_obstruction` — **the headline.** There is a moment sequence (B3's witness)
  on which `StepRatioAntitone` is FALSE (B3) yet the S1-relevant per-step bounds `R(4), R(5) ≤ 1`
  HOLD. So the B3 antitone obstruction does NOT refute the S1 ratio/geometric-mean route; they are
  different statements, and the bump that kills antitone leaves the per-step law intact.
* `prize_envelope_of_ratioDecreasing` — the **forward link**: `RatioDecreasing` + base discharges the
  full Wick bound `E_r ≤ (2r-1)‼ · n^r` via the proven telescope `gaussian_moment_bound_of_stepLaw`,
  i.e. the S1 `K = 1` transfer reduces to the (measured, bump-robust) ratio-decreasing object — never
  to the (B3-refuted) antitone object.

## Honest scope

This is a **NAMED-INPUT-REDUCTION + OBSTRUCTION-RECONCILIATION**, not a prize proof. It establishes:
(i) the S1 closure object is `RatioDecreasing` (= each `R(r) ≤ 1` = `K_eff^{NP}` antitone-anchored),
*provably distinct* from the B3-refuted `StepRatioAntitone`; (ii) B3's obstruction does not transfer
— at B3's own witness the S1 per-step law holds; (iii) the remaining residual is precisely
`RatioDecreasing` (`g_r ≤ g_1`), the *measured*-true (`β = 4`, `n ≤ 256`, structured+generic)
geometric-mean antitone — which is a strictly *milder* statement than the BGK energy wall and than
B3's antitone. The char-`p` *proof* of `RatioDecreasing` at the prize `n = 2^{30}` is still open (it
is the same √-cancellation core as the BGK Paley wall); this file does not close it, it *isolates*
it as the single live ratio object and shows the antitone refutation is irrelevant to it.

Issue #444, lane wf-A03.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.WFA03

open ArkLib.ProximityGap.Frontier.WF7W3
open ArkLib.ProximityGap.Frontier.WF6F1

/-! ## The Wick-normalized ratio `g_r` and the S1 ratio object -/

/-- The **Wick-normalized ratio** `g_r := M r / ((2r-1)‼ · s^r)` of a moment sequence. For the
nonprincipal energy `M = E^{NP}` and `s = n` this is `K_eff^{NP}(r)^r`; `g_1 = E_1^{NP}/n = 1 − n/p`
(Parseval). The S1 transfer needs `g_r ≤ g_1` (`= K_eff^{NP}(r) ≤ K_eff^{NP}(1)`), the
*geometric-mean / ratio* statement — DISTINCT from the B3 step-ratio antitone. -/
noncomputable def wickRatio (M : ℕ → ℝ) (s : ℝ) (r : ℕ) : ℝ :=
  M r / ((Nat.doubleFactorial (2 * r - 1) : ℝ) * s ^ r)

/-- The **S1 ratio object**: `g_r` is non-increasing from `r = 1` on. Equivalent to
`K_eff^{NP}(r) = g_r^{1/r}` antitone-anchored at `r = 1` (when `g` is positive). This — not
`StepRatioAntitone` — is the object the S1 `K = 1` transfer consumes
(`WFS1.charzero_limit_of_anchor_antitone`). -/
def RatioDecreasing (M : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → wickRatio M s (r + 1) ≤ wickRatio M s r

/-! ## The step ratio IS the consecutive ratio of `g` -/

/-- **Algebraic identity.** The B3 normalized step ratio `R(r) = M(r+1)/((2r+1)·s·M r)` equals the
consecutive ratio `g_{r+1}/g_r` of the Wick-normalized sequence. The `(2r+1)` factor in `R` is
exactly the `(2(r+1)-1)‼/(2r-1)‼ · s` factor from `c_{r+1}/c_r`, so `R(r) = g_{r+1}/g_r`. -/
theorem gStepRatio_eq_ratio_quotient {M : ℕ → ℝ} {s : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hMr : M r ≠ 0) (hs : s ≠ 0) :
    NormStepRatio M s r = wickRatio M s (r + 1) / wickRatio M s r := by
  -- c_r = (2r-1)‼ · s^r;  c_{r+1} = (2r+1)·c_r·s  (double-factorial recurrence) so the
  -- normalizers cancel down to the (2r+1)·s of NormStepRatio.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr      -- r = 1 + k
  have hdf : (Nat.doubleFactorial (2 * (1 + k + 1) - 1) : ℝ)
      = (2 * (1 + k) + 1 : ℝ) * (Nat.doubleFactorial (2 * (1 + k) - 1) : ℝ) := by
    have h1 : 2 * (1 + k + 1) - 1 = (2 * (1 + k) - 1) + 2 := by omega
    have h2 : 2 * (1 + k) - 1 = (2 * k) + 1 := by omega
    rw [h1, h2]
    rw [Nat.doubleFactorial]      -- (2k+1+2)‼ = (2k+3)·(2k+1)‼
    push_cast
    ring
  have hc : (0 : ℝ) < (Nat.doubleFactorial (2 * (1 + k) - 1) : ℝ) := by positivity
  have hcne : (Nat.doubleFactorial (2 * (1 + k) - 1) : ℝ) ≠ 0 := ne_of_gt hc
  have hsne : s ^ (1 + k) ≠ 0 := pow_ne_zero _ hs
  have hsne1 : s ^ (1 + k + 1) ≠ 0 := pow_ne_zero _ hs
  have h2r1 : (2 * (1 + k) + 1 : ℝ) ≠ 0 := by positivity
  unfold NormStepRatio wickRatio
  rw [hdf, pow_succ]
  field_simp
  push_cast
  ring

/-- **The S1 ratio object IS the per-step Gaussian law (NOT antitonicity).** With `s > 0` and
`M r > 0`, `RatioDecreasing M s` (the `g_r` decreasing object S1 needs) holds *iff* every normalized
step `R(r) ≤ 1` for `r ≥ 1` — i.e. iff the per-step `GaussianStepLaw` holds from `r = 1` on. This is
the load-bearing logical separation: S1 is about each rung sitting below `1`, B3's `StepRatioAntitone`
is about the *relative* monotonicity of those rungs. The two are independent. -/
theorem ratioDecreasing_iff_stepLaw_pos {M : ℕ → ℝ} {s : ℝ}
    (hs : 0 < s) (hM : ∀ r, 0 < M r) :
    RatioDecreasing M s ↔ ∀ r : ℕ, 1 ≤ r → M (r + 1) ≤ (2 * r + 1 : ℝ) * s * M r := by
  constructor
  · intro hrd r hr
    -- g_{r+1} ≤ g_r ⟹ R(r) = g_{r+1}/g_r ≤ 1 ⟹ M(r+1) ≤ (2r+1)·s·M r
    have hgpos : 0 < wickRatio M s r := by
      unfold wickRatio
      exact div_pos (hM r) (mul_pos (by positivity) (pow_pos hs r))
    have hquot : wickRatio M s (r + 1) / wickRatio M s r ≤ 1 :=
      (div_le_one hgpos).mpr (hrd r hr)
    have hR : NormStepRatio M s r ≤ 1 := by
      rw [gStepRatio_eq_ratio_quotient hr (ne_of_gt (hM r)) (ne_of_gt hs)]; exact hquot
    have hsr : 0 < (2 * r + 1 : ℝ) * s := by positivity
    exact step_of_normStepRatio_le_one hsr (hM r) hR
  · intro hstep r hr
    -- R(r) ≤ 1 ⟹ g_{r+1} ≤ g_r
    have hsr : 0 < (2 * r + 1 : ℝ) * s := by positivity
    have hden : 0 < (2 * r + 1 : ℝ) * s * M r := mul_pos hsr (hM r)
    have hR : NormStepRatio M s r ≤ 1 := by
      rw [NormStepRatio, div_le_one hden]; exact hstep r hr
    rw [gStepRatio_eq_ratio_quotient hr (ne_of_gt (hM r)) (ne_of_gt hs)] at hR
    have hgpos : 0 < wickRatio M s r := by
      unfold wickRatio
      exact div_pos (hM r) (mul_pos (by positivity) (pow_pos hs r))
    exact (div_le_one hgpos).mp hR

/-! ## B3's obstruction does NOT transfer to the S1 object -/

open ArkLib.ProximityGap.Frontier.WF8B3

/-- **The per-step law HOLDS at B3's own prize-scale bump.** B3's `bumpWitness` (the exact
`n = 32, p = 1 001 153`, `β = 3.99` measured bump) violates `StepRatioAntitone` at `r = 4`
(`R(4) < R(5)`, `antitone_FALSE_at_bump`). But *both* of those rungs sit below `1`:
`R(4) = 9219/10000 ≤ 1` and `R(5) = 9323/10000 ≤ 1`. So the per-step Gaussian law — the S1 object —
is intact exactly where the antitone object breaks. Decidable rational `norm_num`. -/
theorem stepLaw_holds_at_B3_bump :
    NormStepRatio bumpWitness 32 4 ≤ 1 ∧ NormStepRatio bumpWitness 32 5 ≤ 1 := by
  constructor
  · show NormStepRatio bumpWitness 32 4 ≤ 1
    unfold NormStepRatio bumpWitness; norm_num
  · show NormStepRatio bumpWitness 32 5 ≤ 1
    unfold NormStepRatio bumpWitness; norm_num

/-- **HEADLINE — the B3 obstruction does not refute the S1 route.** There is a moment sequence
(B3's prize-scale witness) on which `StepRatioAntitone` is FALSE (B3, `antitone_FALSE_at_bump`) yet
the S1-relevant per-step bounds `R(4) ≤ 1 ∧ R(5) ≤ 1` HOLD. Hence:

* B3 refutes the *antitone* proof strategy (`gaussian_moment_bound_of_antitone_base`), and
* B3 does **not** refute the *ratio/geometric-mean* object `RatioDecreasing` (= each `R(r) ≤ 1` =
  `K_eff^{NP}` antitone-anchored), which is what the S1 `K = 1` transfer actually consumes.

The two are logically separate (`ratioDecreasing_iff_stepLaw_pos`): a rising step-ratio rung (the
bump) coexists with every rung below `1`. So the S1 antitone route is **NOT killed by B3**. The
residual it leaves — `RatioDecreasing` at prize scale — is the measured-true, bump-robust object. -/
theorem S1_object_survives_B3_obstruction :
    ∃ (M : ℕ → ℝ) (n : ℝ),
      (¬ StepRatioAntitone M n)
      ∧ (NormStepRatio M n 4 ≤ 1 ∧ NormStepRatio M n 5 ≤ 1) :=
  ⟨bumpWitness, 32, antitone_FALSE_at_bump, stepLaw_holds_at_B3_bump⟩

/-! ## Forward link: the S1 ratio object discharges the full Wick bound (telescope) -/

/-- **The S1 reduction via the ratio object.** A nonnegative moment sequence whose Wick-normalized
ratio is decreasing (`RatioDecreasing`, equivalently each `R(r) ≤ 1`) and which obeys the variance
base `M 1 ≤ s·M 0` with `M 0 ≤ 1` satisfies the full sub-Gaussian Wick bound
`M r ≤ (2r-1)‼ · s^r` for every `r`. This routes the S1 `K = 1` transfer through `RatioDecreasing`
(the measured, bump-robust object) and the proven telescope `gaussian_moment_bound_of_stepLaw` —
*never* through B3's refuted `StepRatioAntitone`. -/
theorem prize_envelope_of_ratioDecreasing {M : ℕ → ℝ} {s : ℝ}
    (hs : 0 < s) (hM : ∀ r, 0 < M r)
    (hvar : M 1 ≤ (2 * 0 + 1 : ℝ) * s * M 0)
    (hM0 : M 0 ≤ 1)
    (hrd : RatioDecreasing M s) :
    ∀ r : ℕ, M r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * s ^ r := by
  have hstepPos : ∀ r : ℕ, 1 ≤ r → M (r + 1) ≤ (2 * r + 1 : ℝ) * s * M r :=
    (ratioDecreasing_iff_stepLaw_pos hs hM).mp hrd
  have hstep : GaussianStepLaw M s := by
    intro r
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0; simpa using hvar
    · exact hstepPos r hrpos
  exact gaussian_moment_bound_of_stepLaw (le_of_lt hs) (fun r => le_of_lt (hM r)) hM0 hstep

end ArkLib.ProximityGap.Frontier.WFA03

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
#print axioms ArkLib.ProximityGap.Frontier.WFA03.gStepRatio_eq_ratio_quotient
#print axioms ArkLib.ProximityGap.Frontier.WFA03.ratioDecreasing_iff_stepLaw_pos
#print axioms ArkLib.ProximityGap.Frontier.WFA03.stepLaw_holds_at_B3_bump
#print axioms ArkLib.ProximityGap.Frontier.WFA03.S1_object_survives_B3_obstruction
#print axioms ArkLib.ProximityGap.Frontier.WFA03.prize_envelope_of_ratioDecreasing
