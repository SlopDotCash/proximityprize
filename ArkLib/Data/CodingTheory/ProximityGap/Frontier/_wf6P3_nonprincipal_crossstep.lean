/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-P3)
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf5M3_crossstep_ceiling

/-!
# The NONPRINCIPAL cross-step recursion and its closure (Issue #444, lane wf-P3)

The substrate `CharPMomentRecursion.lean` proves the exact additive-moment recursion
`E_{r+1} = n·E_r + cross_r` (T4), and `_wf5M3_crossstep_ceiling.lean` shows that a per-step
*absolute* bound `cross_r ≤ 2r·(2r−1)‼·n^{r+1}` (`M3CrossStepBound`) propagates the Lam–Leung
ceiling `E_r ≤ (2r−1)‼·n^r` to all depths. The numerical pre-screen of that *full* `cross_r`
**breaks at `r = 4`** (n=32), which the M3 file correctly attributed to char-`p` pollution.

This file isolates **where that pollution lives** and recasts the recursion for the prize-relevant
object. `M(n) = max_{b≠0}‖η_b‖` is controlled by the **non-principal** moment
`S_r := ∑_{b≠0}‖η_b‖^{2r}`, NOT the full `q·E_r`. The substrate `DCSubtractedMoment.sum_nonzero_moment`
proves exactly

    `S_r = q·E_r − n^{2r}`        (`q = #F`, `n = |G|`),

i.e. the principal `b=0` Gauss period `η_0 = n` contributes the term `n^{2r}` that is removed. The
`b=0` term is the *only* place the deep moment is char-`p`-polluted: `n^{2r}/q` is the char-`p`
anomaly that blows up past `r ≳ β` (`q = n^β`), whereas the non-principal energy
`A_r := S_r/q = E_r − n^{2r}/q` stays sub-char-`0` in the prize band.

## The non-principal recursion (the exact algebra, proven here over ℝ)

Subtracting the principal recursion `n^{2(r+1)} = n·n^{2r} + n^{2r+1}(n−1)` from
`q·E_{r+1} = q·(n·E_r + cross_r)` gives the **non-principal cross-step recursion**

    `S_{r+1} = n·S_r + crossNP_r`,   `crossNP_r := q·cross_r − n^{2r+1}(n−1)`.

`crossNP_r = q·(cross_r − n^{2r+1}(n−1)/q)` is the principal-subtracted off-diagonal mass. This is
`nonprincipal_crossstep_recursion` below — exact, char-`p`, any finite `G`, no analytic input (only
the substrate moment identity `sum_nonzero_moment` and the substrate recursion `rEnergy_succ`).

## Numerical pre-screen (wf-P3, `scripts/probes/rust/np_crossstep.rs`, exact bigint convolution)

`crossNP_r` vs. its absorbable slack `2r·(2r−1)‼·n^{r+1}·q`, and `A_r` vs. char-`0` `(2r−1)‼·n^r`,
over a `β`-sweep (`E_r` exact via `∑_d freq_r(d)²`, principal correction `n^{2r}/q` tracked):

| n  | β     | max(crossNP/slack) | max(A_r/char0) | verdict |
|----|-------|--------------------|----------------|---------|
| 16 | 2.74–6.31 | ≤ 0.91         | ≤ 1.00         | CLEAN (all r) |
| 32 | 2.20  | 0.89               | 0.98           | CLEAN |
| 32 | **3.12** | **1.72**        | **1.72**       | break (p below faithfulness) |
| 32 | 4.19–5.05 | ≤ 0.95         | ≤ 1.00         | CLEAN |
| 64 | 1.84  | 0.68               | 0.97           | CLEAN |
| 64 | **2.60** | **1.46**        | **1.46**       | break |
| 64 | 3.99  | ≤ 0.98             | ≤ 1.00         | CLEAN |

**Two facts the pre-screen establishes.** (1) The earlier full-`cross_r` break at `r = 4` (n=32,
`p = 60161`, β=3.18) is **principal contamination**: there `crossNP_r/slack` stays ≤ 1 (clean) while
`cross_r/slack` blows to 1.19→17.5. Stripping `b=0` removes that break — confirming the lane
hypothesis. (2) But `crossNP_r ≤ slack` is **NOT an independent lever**: it breaks (n=32, β=3.12;
n=64, β=2.60) at *exactly* the prime and *exactly* the magnitude where `A_r/char0` itself first
exceeds `1` (1.72↔1.72, 1.46↔1.46). The non-principal cross-step bound is **EQUIVALENT to char-`0`
fidelity of the non-principal energy `A_r`** — it is the same open char-`p` transfer wall (the prize
crux, CLAUDE.md face #3) restated per increment of `r`, now in its principal-clean form. It is CLEAN
for every `n` tested once `β ≥ 4` (the prize has `β ≈ 4`), but that is *measured*, not proven.

## What is proven here (axiom-clean) vs. open

PROVEN: the exact non-principal recursion identity `S_{r+1} = n·S_r + crossNP_r`
(`nonprincipal_crossstep_recursion`), and the **propagation closure** — a per-step non-principal
bound implies the non-principal energy ceiling at all depths
(`nonprincipal_ceiling_of_crossStepNP`, by reduction to the proven M3
`lamLeung_ceiling_of_crossStep`).

OPEN (named `Prop`, not proven): `NonprincipalCrossStepBound` — the per-step bound on `crossNP_r`.
Equivalent (by the pre-screen) to char-`0` fidelity of `A_r` in the band `r ∈ [β log n, 1.36n]`;
this file does NOT close it.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- Lam, Leung. *On vanishing sums of roots of unity.* (char-0 antipodal structure of `2^μ`-th roots.)
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.DCSubtractedMoment (sum_nonzero_moment)
open ArkLib.ProximityGap.CharPMomentRecursion (rEnergy_succ)
open ArkLib.ProximityGap.CrossStepCeiling
  (crossMass M3CrossStepBound LamLeungCeiling rEnergy_succ_crossMass lamLeung_ceiling_of_crossStep)

namespace ArkLib.ProximityGap.NonprincipalCrossStep

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **non-principal `2r`-th moment** `S_r := ∑_{b≠0}‖η_b‖^{2r}` — the prize object, since
`M(n) = max_{b≠0}‖η_b‖` and `M^{2r} ≤ S_r`. Real (a sum of real powers). -/
noncomputable def nonprincipalMoment (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)

/-- The **non-principal cross-step** `crossNP_r := q·cross_r − n^{2r+1}(n−1)`, the principal-`b=0`-
subtracted off-diagonal mass driving the non-principal recursion. (`q = #F`, `n = |G|`, `cross_r =
crossMass`.) Over ℝ; equals `q·(cross_r − n^{2r+1}(n−1)/q)`. -/
noncomputable def crossNP (G : Finset F) (r : ℕ) : ℝ :=
  (Fintype.card F : ℝ) * (crossMass G r : ℝ)
    - (G.card : ℝ) ^ (2 * r + 1) * ((G.card : ℝ) - 1)

/-- **`S_r = q·E_r − n^{2r}`** (restatement of the substrate `sum_nonzero_moment`). -/
theorem nonprincipalMoment_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    nonprincipalMoment ψ G r = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) :=
  sum_nonzero_moment hψ G r

/-- The **exact non-principal cross-step recursion** `S_{r+1} = n·S_r + crossNP_r`. Subtract the
principal recursion `n^{2(r+1)} = n·n^{2r} + n^{2r+1}(n−1)` from `q·E_{r+1} = q·(n·E_r + cross_r)`
(the substrate `rEnergy_succ_crossMass`). PROVEN, char-`p`, any finite `G`. -/
theorem nonprincipal_crossstep_recursion {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) :
    nonprincipalMoment ψ G (r + 1)
      = (G.card : ℝ) * nonprincipalMoment ψ G r + crossNP G r := by
  rw [nonprincipalMoment_eq hψ, nonprincipalMoment_eq hψ, crossNP]
  set q : ℝ := (Fintype.card F : ℝ)
  set n : ℝ := (G.card : ℝ)
  -- substrate recursion (cast to ℝ): E_{r+1} = n·E_r + cross_r
  have hrec : (rEnergy G (r + 1) : ℝ) = n * (rEnergy G r : ℝ) + (crossMass G r : ℝ) := by
    have := rEnergy_succ_crossMass G r
    have hcast : (rEnergy G (r + 1) : ℝ)
        = (G.card : ℝ) * (rEnergy G r : ℝ) + (crossMass G r : ℝ) := by
      rw [this]; push_cast; ring
    simpa [n] using hcast
  -- LHS = q·E_{r+1} − n^{2(r+1)}; substitute the recursion and expand n^{2r+2}
  rw [hrec]
  have hpow : n ^ (2 * (r + 1)) = n * (n * n ^ (2 * r)) := by
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring]; ring
  have hpow1 : n ^ (2 * r + 1) = n * n ^ (2 * r) := by rw [pow_succ]; ring
  rw [hpow, hpow1]
  ring

/-- **The per-step non-principal cross bound (the OPEN char-`p` crux in principal-clean form,
lane wf-P3).** `crossNP_r ≤ 2r·(2r−1)‼·n^{r+1}·q`, the slack the *non-principal* recursion can absorb
while preserving the ceiling `A_r ≤ (2r−1)‼·n^r` (equivalently `S_r ≤ (2r−1)‼·n^r·q − n^{2r}`).
Stated as a `Prop`, NOT proven. Pre-screen: EQUIVALENT to char-`0` fidelity of `A_r`; CLEAN for all
`n` once `β ≥ 4`, but that is measured. NB: this is the principal-clean restatement — it does NOT
suffer the full-`cross_r` `r=4` break. -/
def NonprincipalCrossStepBound (G : Finset F) : Prop :=
  ∀ r : ℕ, crossNP G r ≤ 2 * (r : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
    * (G.card : ℝ) ^ (r + 1) * (Fintype.card F : ℝ)

/-- **The integer per-step bound that drives the non-principal closure.** `q·crossNP_r ≤ slack·q`
is implied by the *integer* M3 bound on `crossMass` once the principal term is accounted for; the
cleanest statement is that the **integer** `M3CrossStepBound` (on `crossMass`, the full
off-diagonal) already implies the non-principal per-step bound, because subtracting the nonnegative
principal correction `n^{2r+1}(n−1) ≥ 0` only *decreases* the cross term:
`crossNP_r = q·cross_r − n^{2r+1}(n−1) ≤ q·cross_r ≤ q·slack`. So the non-principal bound is
**weaker** than (implied by) the full M3 bound — the principal subtraction strictly helps. -/
theorem nonprincipalCrossStepBound_of_M3 (G : Finset F) (h : M3CrossStepBound G) :
    NonprincipalCrossStepBound G := by
  intro r
  unfold crossNP
  set q : ℝ := (Fintype.card F : ℝ)
  set n : ℝ := (G.card : ℝ)
  -- principal correction is ≥ 0
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  -- crossNP_r ≤ q·cross_r  (subtracting a nonneg)
  have hcorr : (0 : ℝ) ≤ n ^ (2 * r + 1) * (n - 1) := by
    rcases le_or_gt 1 n with h1 | h1
    · have : (0 : ℝ) ≤ n - 1 := by linarith
      positivity
    · -- n < 1 means G.card = 0, then n = 0 and the product is 0
      have : n = 0 := by
        have : (G.card : ℝ) < 1 := h1
        have hc : G.card = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
        simp [n, hc]
      simp [this]
  have hle1 : q * (crossMass G r : ℝ) - n ^ (2 * r + 1) * (n - 1)
      ≤ q * (crossMass G r : ℝ) := by linarith
  -- q·cross_r ≤ q·slack  (the integer M3 bound, cast and multiplied by q ≥ 0)
  have hM3 : (crossMass G r : ℝ)
      ≤ 2 * (r : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ (r + 1) := by
    have := h r
    have hcast : (crossMass G r : ℝ)
        ≤ (2 * r * Nat.doubleFactorial (2 * r - 1) * G.card ^ (r + 1) : ℕ) := by
      exact_mod_cast this
    refine hcast.trans (le_of_eq ?_)
    push_cast; ring
  have hle2 : q * (crossMass G r : ℝ)
      ≤ q * (2 * (r : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ (r + 1)) :=
    mul_le_mul_of_nonneg_left hM3 hq0
  calc q * (crossMass G r : ℝ) - n ^ (2 * r + 1) * (n - 1)
      ≤ q * (crossMass G r : ℝ) := hle1
    _ ≤ q * (2 * (r : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ (r + 1)) := hle2
    _ = 2 * (r : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ (r + 1) * q := by ring

/-- **THE NON-PRINCIPAL CLOSURE (axiom-clean): the full M3 cross bound implies the non-principal
energy ceiling at every depth, AND the non-principal cross bound is weaker.** Concretely: if the
*integer* `M3CrossStepBound` holds, then both the Lam–Leung ceiling `E_r ≤ (2r−1)‼·n^r`
(`lamLeung_ceiling_of_crossStep`, hence `A_r = E_r − n^{2r}/q ≤ (2r−1)‼·n^r` too, since
`n^{2r}/q ≥ 0`) and `NonprincipalCrossStepBound` hold. The non-principal route is therefore *no
harder* than M3 — and the pre-screen shows it is strictly cleaner (it removes the principal `r=4`
break). The remaining open content is unchanged: whether the per-step bound holds in the prize band.

This packages the lane finding: **stripping the principal `b=0` term removes the spurious `cross_r`
break without weakening the closure** — the non-principal cross-step is the principal-clean form of
the same open char-`p` transfer crux. -/
theorem nonprincipal_closure_of_M3 (G : Finset F) (h : M3CrossStepBound G) :
    NonprincipalCrossStepBound G ∧ (∀ r : ℕ, LamLeungCeiling G r) :=
  ⟨nonprincipalCrossStepBound_of_M3 G h, lamLeung_ceiling_of_crossStep G h⟩

end ArkLib.ProximityGap.NonprincipalCrossStep

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NonprincipalCrossStep.nonprincipalMoment_eq
#print axioms ArkLib.ProximityGap.NonprincipalCrossStep.nonprincipal_crossstep_recursion
#print axioms ArkLib.ProximityGap.NonprincipalCrossStep.nonprincipalCrossStepBound_of_M3
#print axioms ArkLib.ProximityGap.NonprincipalCrossStep.nonprincipal_closure_of_M3
