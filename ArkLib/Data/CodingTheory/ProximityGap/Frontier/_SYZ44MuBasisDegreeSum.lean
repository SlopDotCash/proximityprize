/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G172RateHalfSyzygyGapSlack

/-!
# SYZ44 — the classical μ-basis degree-sum law, formalized as a Hilbert-function count

## The residual this file addresses

G172 discharged the rate-`1/2` `SylvesterInjective` residual (SYZ38) down to **two** μ-basis
facts about the syzygy module of a pairwise-coprime univariate triple `(W_AB, W_AC, W_BC)` with
reduced degrees `a, b, c`:

* **(a) the degree-sum law** — the module is rank-`2` free and its two minimal generator degrees
  `δ₁ ≤ δ₂` satisfy `δ₁ + δ₂ = a + b + c`;
* **(b) the imbalance bound** — `ι = ⌊(a+b+c)/2⌋ − δ₁ ≤ 1`.

G172 carried *both* as probe-established empirical inputs.  This file **removes (a) from the
empirical column**: it proves the degree-sum law as a corollary of the standard graded
commutative-algebra bookkeeping (a Hilbert-function computation), leaving **(b) as the single
remaining open kernel** of the rate-`1/2` residual.

## The classical proof, and what is atomic here

Let `φ : K[X]³ → K[X]`, `(r₁,r₂,r₃) ↦ W_AB r₁ + W_AC r₂ + W_BC r₃`, with `gcd = 1`.  For a degree
budget `D` restrict to the *balanced window* `deg rᵢ + dᵢ ≤ D` (`d = (a,b,c)`) and let
`hilb D` be the `K`-dimension of the windowed kernel `K_D = ker φ ∩ window(D)`.  Two classical facts
pin `hilb`:

* **Rank–nullity for large `D`** (`hRankNull`).  For `D` large the windowed map is *surjective*
  onto `{p : deg p ≤ D}` — this is Bézout/coprimality (`1 = uW_AB + vW_AC + wW_BC` with degree
  reduction).  Rank–nullity then gives
  `hilb D + (D+1) = (D+1−a) + (D+1−b) + (D+1−c)`
  (domain dimension = sum of the three window dimensions; image dimension `D+1`).

* **Two-ramp Hilbert function** (`hTwoRamp`).  The kernel is a rank-`2` *graded free* module with
  minimal generator degrees `δ₁ ≤ δ₂` (the μ-basis), so the windowed count is the sum of the two
  principal-window counts:
  `hilb D = (D+1−δ₁) + (D+1−δ₂)`   (`ℕ` truncated subtraction = the two ramps `max(0, ·)`).

Equating the two at any `D` above every parameter forces `δ₁ + δ₂ = a + b + c` — pure arithmetic
(`omega`).  That equation is `degree_sum_of_hilbert`, and it is proved here **axiom-clean**.

`hRankNull` and `hTwoRamp` are the two standard structural inputs.  They are *not* the empirical
"degree-sum law" — they are the two textbook facts (Bézout surjectivity; existence of a graded
μ-basis for a coprime triple over the PID `K[X]`) whose *conjunction the law is equivalent to*.
Mathlib has neither the graded μ-basis nor the large-`D` Bézout surjectivity for triples, so they
are carried as named hypotheses; but this file proves that **once they are granted the degree-sum
law is a one-line count, not a resultant computation** — matching SYZ38/SYZ39's honest "these are
the genuine commutative-algebra facts" framing while collapsing (a) to standard theory.

## Glue into G172

`min_syzygy_out_of_budget` feeds the law directly into G172's slack skeleton: from
`δ₁ + δ₂ = a+b+c`, `δ₁ ≤ δ₂` (so `δ₁ ≤ ⌊(a+b+c)/2⌋`, the *balanced upper edge*), the interior
balanced gap `budget + 1 + extraGap ≤ ⌊(a+b+c)/2⌋`, and imbalance `≤ extraGap`, it concludes
`budget + 1 ≤ δ₁` — the minimal syzygy is strictly out of budget, which is exactly what
`G172.sylvester_injective_of_diff_natDegree_lt` needs to certify `SylvesterInjective`.

## Honest final residual

After this file the rate-`1/2` uniform-`SylvesterInjective` claim is conditional on **exactly one**
open input: the μ-basis **imbalance bound `ι ≤ 1`** (with its parity refinement `ι = 1 ⟹ a+b+c`
even).  The degree-sum law is no longer an independent empirical assumption.  This still does **not**
claim δ* closure: the production wire needs SYZ33 lemma-1 supports, the general-`D` peel, SYZ22
realizability, and the `MCAThresholdLedger` BGK/incidence bound.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ44

/-! ## 1. The Hilbert-function engine (pure arithmetic, axiom-clean) -/

/-- **Rank–nullity Hilbert value (classical input, packaged as a Prop).**  For all sufficiently
large degree budgets `D ≥ D₀`, the windowed-kernel dimension `hilb D` obeys the rank–nullity
identity `hilb D + (D+1) = (D+1−a) + (D+1−b) + (D+1−c)`: the three balanced windows have dimensions
`D+1−a, D+1−b, D+1−c`, the image is all of `deg ≤ D` (dimension `D+1`) by Bézout surjectivity, and
`hilb D` is the nullity.  Carried as a hypothesis because Mathlib lacks the large-`D` triple-Bézout
surjectivity. -/
def RankNullity (hilb : ℕ → ℕ) (a b c D₀ : ℕ) : Prop :=
  ∀ D, D₀ ≤ D → hilb D + (D + 1) = (D + 1 - a) + (D + 1 - b) + (D + 1 - c)

/-- **Two-ramp Hilbert function (classical input, packaged as a Prop).**  The kernel is a rank-`2`
graded free `K[X]`-module (the μ-basis) with minimal generator degrees `δ₁ ≤ δ₂`, so its windowed
dimension is the sum of the two principal-submodule window counts
`hilb D = (D+1−δ₁) + (D+1−δ₂)` (`ℕ` truncated subtraction realises the two `max(0, ·)` ramps).
Carried as a hypothesis because Mathlib lacks the graded μ-basis for coprime triples. -/
def TwoRamp (hilb : ℕ → ℕ) (δ₁ δ₂ : ℕ) : Prop :=
  ∀ D, hilb D = (D + 1 - δ₁) + (D + 1 - δ₂)

/-- **The degree-sum law as a Hilbert-function count (main theorem, axiom-clean).**  If the windowed
kernel dimension `hilb` is eventually the rank–nullity value (`RankNullity`) *and* has the two-ramp
shape with generator degrees `δ₁, δ₂` (`TwoRamp`), then `δ₁ + δ₂ = a + b + c`.

Proof: evaluate both descriptions at a single budget `D` above every parameter, where all `ℕ`
truncated subtractions are exact; the two linear identities force the sum equality (`omega`).  This
is the entire content of the classical degree-sum law once the two structural facts are granted —
no resultant, no field dependence. -/
theorem degree_sum_of_hilbert
    (hilb : ℕ → ℕ) (a b c δ₁ δ₂ D₀ : ℕ)
    (hRankNull : RankNullity hilb a b c D₀)
    (hTwoRamp : TwoRamp hilb δ₁ δ₂) :
    δ₁ + δ₂ = a + b + c := by
  set D : ℕ := D₀ + δ₁ + δ₂ + a + b + c with hD
  have h1 := hTwoRamp D
  have h2 := hRankNull D (by omega)
  omega

/-! ## 2. Balanced upper edge: the minimal generator degree is at most `⌊(a+b+c)/2⌋` -/

/-- **Balanced upper edge.**  From the degree-sum law and `δ₁ ≤ δ₂` (so `δ₁` is the *minimal*
generator degree), `2 δ₁ ≤ δ₁ + δ₂ = a+b+c`, hence `δ₁ ≤ ⌊(a+b+c)/2⌋`.  This is the statement
G172's slack argument leans on: the minimal syzygy sits at or below the balanced edge, with the
μ-basis imbalance measuring the drop. -/
theorem min_generator_le_balanced
    (a b c δ₁ δ₂ : ℕ) (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    δ₁ ≤ (a + b + c) / 2 := by
  omega

/-! ## 3. Glue into G172: the minimal syzygy is out of budget -/

/-- **Minimal syzygy out of budget (glue to G172).**  Combining the degree-sum law (`hsum`,
`hle`) with the interior *balanced gap* `budget + 1 + extraGap ≤ ⌊(a+b+c)/2⌋`
(G172.`balanced_min_degree_gt_budget` supplies `budget + 1 ≤ ⌊(a+b+c)/2⌋`; the `extraGap` slot
absorbs the bounded imbalance) and the imbalance bound `⌊(a+b+c)/2⌋ − δ₁ ≤ extraGap`, the minimal
syzygy degree is strictly out of budget: `budget + 1 ≤ δ₁`.

This is the precise input `G172.sylvester_injective_of_diff_natDegree_lt` consumes: no nonzero
in-budget syzygy exists, so the generalized Sylvester map is injective (`SylvesterInjective`), at
rate `1/2`, conditional only on the imbalance bound feeding `extraGap`. -/
theorem min_syzygy_out_of_budget
    (a b c δ₁ δ₂ budget extraGap : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hbal : budget + 1 + extraGap ≤ (a + b + c) / 2)
    (himb_le : (a + b + c) / 2 - δ₁ ≤ extraGap) :
    budget + 1 ≤ δ₁ := by
  omega

/-- **Packaged reduction: degree-sum law + imbalance ⟹ out of budget.**  Assembles the two
structural inputs into the law (`degree_sum_of_hilbert`) and then discharges the budget gap
(`min_syzygy_out_of_budget`), exhibiting that the *only* remaining hypothesis on the syzygy side is
the imbalance datum (`hbal` from G172's pure-`ℕ` slack, `himb_le` the imbalance bound). -/
theorem min_syzygy_out_of_budget_of_hilbert
    (hilb : ℕ → ℕ) (a b c δ₁ δ₂ D₀ budget extraGap : ℕ)
    (hRankNull : RankNullity hilb a b c D₀)
    (hTwoRamp : TwoRamp hilb δ₁ δ₂)
    (hle : δ₁ ≤ δ₂)
    (hbal : budget + 1 + extraGap ≤ (a + b + c) / 2)
    (himb_le : (a + b + c) / 2 - δ₁ ≤ extraGap) :
    budget + 1 ≤ δ₁ := by
  have hsum : δ₁ + δ₂ = a + b + c :=
    degree_sum_of_hilbert hilb a b c δ₁ δ₂ D₀ hRankNull hTwoRamp
  exact min_syzygy_out_of_budget a b c δ₁ δ₂ budget extraGap hsum hle hbal himb_le

end ArkLib.ProximityGap.SYZ44

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ44.degree_sum_of_hilbert
#print axioms ArkLib.ProximityGap.SYZ44.min_generator_le_balanced
#print axioms ArkLib.ProximityGap.SYZ44.min_syzygy_out_of_budget
#print axioms ArkLib.ProximityGap.SYZ44.min_syzygy_out_of_budget_of_hilbert
