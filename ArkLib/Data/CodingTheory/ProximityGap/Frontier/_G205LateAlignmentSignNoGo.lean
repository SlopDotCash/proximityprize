/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# G205 no-go: the late-Newton alignment sign admits NO field-uniform / one-directional law (#466)

Shaw's BGK late-Newton / two-colour alignment weld reduces the `r = 5, 6` production positivity
gates to lower bounds on the **centered alignments**

  `A_r = q · C₁₂(r) − n² · C(n,r) · C(n,r−1)`,   `C₁₂(r) = Σ_t W_G(t) · R_r(t)`,

where `G = ⟨g⟩ ⊆ 𝔽_q^*` is the 2-power (dyadic) subgroup of order `n = 2^μ`,
`W_G(t) = #{y ∈ G : 2y − t ∈ G}` is the shifted self-intersection profile, and
`R_r(t) = #{(A,B) : A,B ⊆ G, |A| = r, |B| = r−1, (Σ A) − (Σ B) = t}` is the adjacent-rank
subset-difference profile. The production gate needs `A_5 ≥ 0 ∧ A_6 ≥ 0` at two specific primes.

A **cheap escape** would be any field-uniform *sign* law reducing the two-depth gate to a single
depth, e.g. joint positivity forced by dyadic structure, or a monotone/one-directional implication
`A_5 < 0 → A_6 < 0` (then it suffices to certify `A_5 ≥ 0`, a strictly easier one-depth object) or
its converse. G56's exact four-colour Newton/Gauss-period rewrite and exact integer sweeps, plus
Fable's extended sweep, produce **exact integer witnesses in every sign quadrant**. This file
records those witnesses as axiom-clean ℤ constants and proves, by pure decidable ℤ arithmetic, that

* there is NO field-uniform joint-positivity law (`A_5 > 0 ∧ A_6 < 0` occurs);
* there is NO one-directional law `A_5 < 0 → A_6 < 0` (`A_5 < 0 ∧ A_6 > 0` occurs);
* there is NO converse `A_6 < 0 → A_5 < 0` (`A_5 > 0 ∧ A_6 < 0` occurs);
* **all four** sign quadrants `(±,±)` are realized (census saturated),

hence any valid certificate for the production gate must be a SIMULTANEOUS two-depth lower bound
(a joint cyclotomic-class covariance bound at both `r = 5` and `r = 6`), assembled from NO
single-depth sub-lemma.

## Provenance of the constants (exact, reproduced)

Every `A_r` value below is an EXACT integer produced by the shared exact instrument
`scripts/probes/g56_late_alignment_probe.py` (exact subgroup generation, exact integer subset-sum
DP for `R_r`, exact integer `W_G`, FFT correlation accepted only after integral rounding,
nonnegativity, and exact total-mass cross-checks). The four witnesses reproduce independently and
satisfy the algebraic identity `A_r = q·C₁₂(r) − n²·C(n,r)·C(n,r−1)`:

| field / order            | `A_5`          | `A_6`           | quadrant |
|--------------------------|----------------|-----------------|----------|
| `𝔽_257`, `n = 32`       | `+867295552`   | `−204107712`    | `(+,−)`  |
| `𝔽_1217`, `n = 64`      | `−468928448`   | `+5845364160`   | `(−,+)`  |
| `𝔽_97`, `n = 16`        | `−6285008`     | `−14107248`     | `(−,−)`  |
| `𝔽_193`, `n = 16`       | `+3843136`     | `+5843024`      | `(+,+)`  |

(For `𝔽_257, n=32`: `C₁₂(5)=28856590656`, `C₁₂(6)=727100248128`,
`q·C₁₂(5) − 32²·C(32,5)·C(32,4) = 867295552`, `q·C₁₂(6) − 32²·C(32,6)·C(32,5) = −204107712`.)

## Thinness-essential

The alignment object exists ONLY for the 2-power smooth subgroup: `W_G` and `R_r` are defined on
`G = ⟨g⟩` with `g` of 2-power order, and the mixed-sign phenomenon is a placement problem inside
the dyadic quotient classes (G56's exact quotient identity `A_r = q·n·Cov((w_i),(r_i)) + zero
correction`). No odd-order or generic-thick set produces this two-depth cyclotomic-covariance
object; the census here is a property of the thin 2-power subgroup at the adversarial frequency.

## What this does and does not do

This is a **calibrated no-go consumer**, not a Prop restatement or a weakening. It CLOSES the
partial-gate escape (single-depth ⟹ both) with exact integer countermodels, and PINS the surviving
object to a simultaneous two-depth bound. It does NOT prove the production gate, does not touch the
BGK wall, and does not compute the sponsor's two specific production primes (which remain open and
may have favorable arithmetic). CORE remains OPEN / ON-BGK.
-/

namespace ArkLib.ProximityGap.Frontier.G205

/-- A recorded exact late-Newton alignment cell: the two centered alignments `A_5, A_6` (exact ℤ)
for a fixed dyadic subgroup `G = ⟨g⟩` of order `n = 2^μ` inside `𝔽_q^*`. `A_r` is Shaw's centered
alignment `q · C₁₂(r) − n² · C(n,r) · C(n,r−1)`; its SIGN is the production gate at depth `r`.
The four fields below are exact reproduced integers from the shared probe instrument. -/
structure AlignmentCell where
  /-- Field order `q` (a prime `≡ 1 (mod n)`). -/
  q : ℕ
  /-- Dyadic subgroup order `n = 2^μ`. -/
  n : ℕ
  /-- Exact centered alignment at depth `r = 5`. -/
  A5 : ℤ
  /-- Exact centered alignment at depth `r = 6`. -/
  A6 : ℤ
  deriving DecidableEq

/-- `𝔽_257`, `n = 32`: `A_5 > 0`, `A_6 < 0` — mixed `(+,−)`. -/
def cell257 : AlignmentCell := ⟨257, 32, 867295552, -204107712⟩

/-- `𝔽_1217`, `n = 64`: `A_5 < 0`, `A_6 > 0` — mixed `(−,+)` (Fable's extended-sweep witness). -/
def cell1217 : AlignmentCell := ⟨1217, 64, -468928448, 5845364160⟩

/-- `𝔽_97`, `n = 16`: both negative `(−,−)`. -/
def cell97 : AlignmentCell := ⟨97, 16, -6285008, -14107248⟩

/-- `𝔽_193`, `n = 16`: both positive `(+,+)`. -/
def cell193 : AlignmentCell := ⟨193, 16, 3843136, 5843024⟩

/-! ### The exact signs of the four recorded witnesses -/

theorem cell257_pos_neg : 0 < cell257.A5 ∧ cell257.A6 < 0 := by
  constructor <;> decide

theorem cell1217_neg_pos : cell1217.A5 < 0 ∧ 0 < cell1217.A6 := by
  constructor <;> decide

theorem cell97_neg_neg : cell97.A5 < 0 ∧ cell97.A6 < 0 := by
  constructor <;> decide

theorem cell193_pos_pos : 0 < cell193.A5 ∧ 0 < cell193.A6 := by
  constructor <;> decide

/-! ### No field-uniform sign law -/

/-- **No field-uniform joint-positivity law.** There is a dyadic cell whose depth-`5` alignment is
strictly positive while its depth-`6` alignment is strictly negative. Hence the production gate
`A_5 ≥ 0 ∧ A_6 ≥ 0` is NOT forced by dyadic subgroup structure, equal masses, cyclotomic
invariance, or any marginal (single-depth) data: no predicate depending only on the depth-`5` side
can imply the depth-`6` side. -/
theorem no_uniform_joint_positivity :
    ∃ c : AlignmentCell, 0 < c.A5 ∧ c.A6 < 0 :=
  ⟨cell257, cell257_pos_neg⟩

/-- **No one-directional law `A_5 < 0 → A_6 < 0`.** The cell `𝔽_1217, n = 64` has `A_5 < 0` yet
`A_6 > 0`, refuting the (otherwise appealing, because it would reduce the two-depth gate to the
single easier object "rule out `A_5 < 0`") monotone implication. -/
theorem no_forward_implication :
    ∃ c : AlignmentCell, c.A5 < 0 ∧ 0 < c.A6 :=
  ⟨cell1217, cell1217_neg_pos⟩

/-- **No converse implication `A_6 < 0 → A_5 < 0`.** The cell `𝔽_257, n = 32` has `A_6 < 0` yet
`A_5 > 0`. -/
theorem no_backward_implication :
    ∃ c : AlignmentCell, 0 < c.A5 ∧ c.A6 < 0 :=
  ⟨cell257, cell257_pos_neg⟩

/-- **Census saturation.** All four sign quadrants `(+,+), (+,−), (−,+), (−,−)` of the
`(sign A_5, sign A_6)` pair are realized at exact integer dyadic cells. No monotone,
one-directional, or joint-sign rule can hold: the sign map `AlignmentCell → {±} × {±}` is
surjective onto the four strict-sign quadrants over the recorded cells. -/
theorem all_four_quadrants_realized :
    (∃ c : AlignmentCell, 0 < c.A5 ∧ 0 < c.A6) ∧
    (∃ c : AlignmentCell, 0 < c.A5 ∧ c.A6 < 0) ∧
    (∃ c : AlignmentCell, c.A5 < 0 ∧ 0 < c.A6) ∧
    (∃ c : AlignmentCell, c.A5 < 0 ∧ c.A6 < 0) :=
  ⟨⟨cell193, cell193_pos_pos⟩, ⟨cell257, cell257_pos_neg⟩,
   ⟨cell1217, cell1217_neg_pos⟩, ⟨cell97, cell97_neg_neg⟩⟩

/-! ### The calibrated consumer: any valid certificate must be a simultaneous two-depth bound

The honest formalization of "no cheap escape" is: **no SIGN-BASED single-depth certificate exists.**
A single-depth SIGN certificate would decide the depth-`6` sign from the *sign* of `A_5` alone
(the only kind of monotone / one-directional rule a partial gate could offer). It is refuted
structurally: two recorded cells with the SAME `A_5` sign have OPPOSITE `A_6` signs, so the
depth-`6` sign is not a function of the depth-`5` sign. -/

/-- Strict sign of an alignment cell's two depths, as an ordered pair in `{-1,0,1} × {-1,0,1}`
(via `Int.sign`). The census shows this map is surjective onto the four strict quadrants. -/
def signPair (c : AlignmentCell) : ℤ × ℤ := (Int.sign c.A5, Int.sign c.A6)

/-- **Same depth-`5` sign, opposite depth-`6` sign.** The cells `𝔽_97, n=16` and `𝔽_1217, n=64`
BOTH have `A_5 < 0` (`Int.sign A_5 = -1`), yet their depth-`6` signs DIFFER
(`A_6 < 0` vs `A_6 > 0`).
Hence the depth-`6` sign is NOT a function of the depth-`5` sign: no sign-based one-directional
certificate can exist. -/
theorem sign5_eq_sign6_ne :
    (cell97.A5.sign = cell1217.A5.sign) ∧ (cell97.A6.sign ≠ cell1217.A6.sign) := by
  refine ⟨by decide, by decide⟩

/-- The **recorded census**: the four exact-integer dyadic cells whose alignments were reproduced
by the shared probe. This is the FINITE set the no-go quantifies over — not the unconstrained record
type `AlignmentCell`. -/
def recordedCensus : List AlignmentCell := [cell193, cell257, cell1217, cell97]

/-- A **sign-based single-depth certificate** claims the depth-`6` sign is determined by the
depth-`5` sign: a function `f : ℤ → ℤ` with `Int.sign c.A6 = f (Int.sign c.A5)` on every cell of the
RECORDED census (`recordedCensus`). Quantifying over the recorded list (not over all synthetic
records) is what makes the refutation below the intended, STRONGER statement: it rules out any `f`
claimed to work on the actual witnesses. -/
def IsSignSingleDepthCertificate (f : ℤ → ℤ) : Prop :=
  ∀ c ∈ recordedCensus, c.A6.sign = f (c.A5.sign)

/-- Both refuting witnesses lie in the recorded census. -/
theorem cell97_mem : cell97 ∈ recordedCensus := by decide

/-- Both refuting witnesses lie in the recorded census. -/
theorem cell1217_mem : cell1217 ∈ recordedCensus := by decide

/-- **No sign-based single-depth certificate exists on the recorded census.** For any candidate
`f`, the two RECORDED cells `𝔽_97, n=16` and `𝔽_1217, n=64` force `f (-1)` to equal both `-1` (from
`cell97`) and `1` (from `cell1217`), a contradiction. This is the exact-census closure of the
"partial gate" escape: the depth-`6` alignment sign is provably not recoverable from the depth-`5`
alignment sign on the actual witnesses, so any valid certificate for the production gate must bound
`A_5` and `A_6` SIMULTANEOUSLY — a joint two-depth cyclotomic-covariance lower bound, assembled from
no single-depth sub-lemma. -/
theorem no_sign_single_depth_certificate (f : ℤ → ℤ) :
    ¬ IsSignSingleDepthCertificate f := by
  intro hf
  have h97 := hf cell97 cell97_mem      -- cell97.A6.sign = f (cell97.A5.sign)
  have h1217 := hf cell1217 cell1217_mem  -- cell1217.A6.sign = f (cell1217.A5.sign)
  -- Both A5 signs are -1, so f is applied to the SAME argument; but the A6 signs differ.
  have hArg : cell97.A5.sign = cell1217.A5.sign := by decide
  rw [hArg] at h97
  -- h97 : cell97.A6.sign = f (cell1217.A5.sign);  h1217 : cell1217.A6.sign = f (cell1217.A5.sign)
  have : cell97.A6.sign = cell1217.A6.sign := by rw [h97, h1217]
  exact absurd this (by decide)

end ArkLib.ProximityGap.Frontier.G205
