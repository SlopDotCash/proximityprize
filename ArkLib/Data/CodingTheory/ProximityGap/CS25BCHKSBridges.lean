/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.ToMathlib.Bridge2BCHKS25
import ArkLib.ToMathlib.Bridge2BGKS20
import ArkLib.ToMathlib.CS25JointFar

/-!
# CS25/BCHKS/BGKS upper-witness bridges (issue #22)

SILVER reductions: MCAUpperWitness.ofBadLineBCHKS25 / ofBadLineBCHKS25AllButOne / ofSeparationBGKS20
construct Grand-MCA upper witnesses from BadLineWitness / NearCertainBadLine via the proven Fact 4.5
epsCA_le_epsMCA bridge. The bad-line CONSTRUCTIONS from the named papers are the isolated inputs.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ProximityGap.GrandChallenges.Issue22

open scoped NNReal ENNReal BigOperators
open ProximityGap ProximityGap.GrandChallenges CodingTheory CodingTheory.Bridge Polynomial

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-!
================================================================================
§A. BCHKS25 bad-line ⟹ Grand-MCA upper witness  (SILVER REDUCTION)
================================================================================

ABF26 Theorem 5.2 / BCHKS25 Theorem 1.9. The geometric residual `BadLineWitness`
(external: the affine-shift interpolation construction) yields `epsCA(C,δ,δ) ≥ 1/(2n)`.
We connect it to the Grand-MCA `MCAUpperWitness` framework: any threshold
`ε* < ofReal(1/(2n))` is then forced strictly below `epsCA`, hence below `epsMCA`.

The ONLY external input is `BadLineWitness` (the paper's bad-line construction). Everything
else — the epsCA(δ_fld,δ_int)→epsCA(δ,δ) instantiation, the strict-comparison chaining, and
the `ofEpsCAGt` edge through `epsCA ≤ epsMCA` — is proven below.
-/

/-- **BCHKS25 bad-line ⟹ MCA upper witness (the in-tree-proven half).**

From a `BadLineWitness` for the RS code at a *single* radius `δ` (so `δ_fld = δ_int = δ`,
the shape `ofEpsCAGt` consumes) and a threshold strictly below `ofReal(1/(2n))`, build a
Grand-MCA upper witness at radius `δ`.

`hε` is the Phase-5 numeric check `ε* < 1/(2n)` (read in `ENNReal` via `ofReal`); for the prize
regime `ε* = 2^(−128)` and `n` polynomial in the security parameter this holds with enormous
margin. The bad-line construction itself stays the single named external residual `hBadLine`. -/
noncomputable def MCAUpperWitness.ofBadLineBCHKS25
    (domain : ι ↪ F) (k : ℕ) (δ ε_star : ℝ≥0)
    (hBadLine : BadLineWitness (F := F)
      ((ReedSolomon.code domain k : Set (ι → F))) δ δ)
    (hε : (ε_star : ENNReal) < ENNReal.ofReal (1 / (2 * Fintype.card ι))) :
    MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  -- `ReedSolomon.code domain k` is a `Submodule F (ι → F)`, so `ofEpsCAGt` applies with `MC := code`.
  MCAUpperWitness.ofEpsCAGt (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ) <|
    -- Goal: `(ε_star : ENNReal) < epsCA (code) δ δ`.
    -- `epsCA_badLine_bridge_of_residual` (proven) gives `ofReal(1/(2n)) ≤ epsCA (code) δ δ`.
    lt_of_lt_of_le hε
      (CodingTheory.Bridge.epsCA_badLine_bridge_of_residual
        ((ReedSolomon.code domain k : Set (ι → F))) δ δ hBadLine)

/-- **All-but-one front door for the BCHKS25 Grand-MCA witness.**

Same conclusion, but the bad-line residual is supplied in the "all scalars but one make the
combining line close" form (`Bridge.badLineWitness_of_allButOne`, proven). This is the precise
shape several paper statements assert. The single distinguished bad scalar `γ_bad` is the
external content; everything else is proven. -/
noncomputable def MCAUpperWitness.ofBadLineBCHKS25AllButOne
    (domain : ι ↪ F) (k : ℕ) (δ ε_star : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι) (γ_bad : F)
    (hjp : ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)
    (hgood : ∀ γ : F, γ ≠ γ_bad →
      δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)
    (hε : (ε_star : ENNReal) < ENNReal.ofReal (1 / (2 * Fintype.card ι))) :
    MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  MCAUpperWitness.ofBadLineBCHKS25 domain k δ ε_star
    (CodingTheory.Bridge.badLineWitness_of_allButOne
      ((ReedSolomon.code domain k : Set (ι → F))) δ δ u γ_bad hjp hgood)
    hε

/-!
================================================================================
§B. BGKS20 char-2 separation ⟹ Grand-MCA upper witness  (SILVER REDUCTION)
================================================================================

ABF26 Theorem 5.4 / BGKS20 Lemma 3.3. The geometric residual `NearCertainBadLine`
(external: the explicit rate-1/8 char-2 stack whose line is close for all-but-one scalar)
yields `epsCA(C,δ,δ) ≥ 1 − 1/|F|`. We connect it to the Grand-MCA framework: any threshold
`ε* < ofReal(1 − 1/|F|)` is forced strictly below `epsMCA`.

This is the strongest of the three lower bounds: `1 − 1/|F|` is essentially `1`, so for any
prize threshold `ε* = 2^(−128) < 1 − 1/|F|` the witness lands trivially (the threshold
hypothesis is far weaker than the BCHKS `1/(2n)` one). Only `NearCertainBadLine` is external.
-/

/-- **BGKS20 separation ⟹ MCA upper witness (the in-tree-proven half).**

From a `NearCertainBadLine` residual for the RS code at a single radius `δ` and a threshold
strictly below `ofReal(1 − 1/|F|)`, build a Grand-MCA upper witness at radius `δ`. The char-2
near-certain-bad-line construction is the single named external residual. -/
noncomputable def MCAUpperWitness.ofSeparationBGKS20
    (domain : ι ↪ F) (k : ℕ) (δ ε_star : ℝ≥0)
    (hSep : NearCertainBadLine (F := F)
      ((ReedSolomon.code domain k : Set (ι → F))) δ δ)
    (hε : (ε_star : ENNReal) < ENNReal.ofReal (1 - 1 / Fintype.card F)) :
    MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  MCAUpperWitness.ofEpsCAGt (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ) <|
    -- Goal: `(ε_star : ENNReal) < epsCA (code) δ δ`.
    -- `epsCA_separation_bridge_of_residual` (proven) gives `ofReal(1 − 1/|F|) ≤ epsCA (code) δ δ`.
    lt_of_lt_of_le hε
      (CodingTheory.Bridge.epsCA_separation_bridge_of_residual
        ((ReedSolomon.code domain k : Set (ι → F))) δ δ hSep)

/-!
================================================================================
§C. Deep-hole probability input  (FULL PROOF, reduced to mathlib counting)
================================================================================

The issue asks specifically to "prove the deep-hole Pr[random point δ-close] computations
that reduce to mathlib counting". The relevant statement is:

  Pr_{γ ← $ᵖ F}[deep-hole line at γ is δ-close to RS[k]] ≥ numDistinct(p, a) / |F|.

In-tree (`CS25DeepHoleFinish2.numDistinct_div_card_le_pr`) this is already proven, and it
reduces exactly to two mathlib counting facts:

  (i)  numDistinct(p,a) ≤ |{γ : line δ-close}|        -- injection of distinct values into good γ
  (ii) Pr[uniform γ ∈ filter] = |filter| / |F|        -- `prob_uniform_eq_card_filter_div_card`

Step (i) is `numDistinct_le_card_caGood`; it is the genuine "counting" content. Below I give
an INDEPENDENT, self-contained re-derivation of the abstract counting core of (i): for ANY
finite list of polynomials `p : Fin L → F[X]`, ANY point `a`, and ANY predicate `Good : F → Prop`
that holds at every value `−(p j)(a)`, the number of distinct values `numDistinct p a` is at most
the number of `Good` scalars. This is the mathlib-only kernel that the deep-hole argument plugs
the closeness predicate into; it is provable purely from `Finset.card_image_of_injective`,
`Finset.card_le_card`, and `neg_injective` — no coding theory, no probability. -/

/-- **Deep-hole counting kernel (mathlib-only).**

`numDistinct p a` counts distinct values `(p j)(a)`. The map `j ↦ −(p j)(a)` has image of the
same cardinality (negation is injective), and if every such negated value satisfies a predicate
`Good`, that image embeds into the `Good`-filter. Hence `numDistinct p a ≤ |{γ : Good γ}|`.

This is the abstract heart of `numDistinct_le_card_caGood`: in the deep-hole instance,
`Good γ := caCloseEvent domain u a k δ γ` and the hypothesis `hGood` is supplied by
`deepHoleLine_relClose_of_mem_ball` (the proven closeness-transfer lemma). The probability
statement (ii) then follows by `prob_uniform_eq_card_filter_div_card`. -/
theorem numDistinct_le_card_good_kernel
    {L : ℕ} (p : Fin L → F[X]) (a : F) (Good : F → Prop) [DecidablePred Good]
    (hGood : ∀ j : Fin L, Good (-(p j).eval a)) :
    CodingTheory.CS25.numDistinct p a ≤ (Finset.univ.filter Good).card := by
  classical
  -- The negated-value image has the same cardinality as `numDistinct` (negation injective).
  have hcard_eq :
      (Finset.univ.image (fun j : Fin L => -(p j).eval a)).card
        = CodingTheory.CS25.numDistinct p a := by
    rw [CodingTheory.CS25.numDistinct]
    -- `numDistinct = |image (j ↦ (p j)(a))|`; precompose with `(· ↦ −·)` and use injectivity.
    rw [show (fun j : Fin L => -(p j).eval a)
          = (fun x : F => -x) ∘ (fun j : Fin L => (p j).eval a) from rfl,
      ← Finset.image_image]
    exact Finset.card_image_of_injective _ neg_injective
  -- The negated-value image is contained in the `Good`-filter.
  have hsub :
      (Finset.univ.image (fun j : Fin L => -(p j).eval a)) ⊆ Finset.univ.filter Good := by
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨j, -, rfl⟩ := hγ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hGood j⟩
  calc CodingTheory.CS25.numDistinct p a
        = (Finset.univ.image (fun j : Fin L => -(p j).eval a)).card := hcard_eq.symm
    _ ≤ (Finset.univ.filter Good).card := Finset.card_le_card hsub

/-!
The probability lower bound itself is in-tree as `numDistinct_div_card_le_pr`. For completeness,
the clean "Pr ≥ numDistinct/q" deep-hole statement specialises the kernel above with
`Good γ := caCloseEvent domain u a k δ γ`, whose `hGood` is exactly
`CS25.DeepHole.deepHoleLine_relClose_of_mem_ball`. We restate the consumed in-tree fact so the
dependency is explicit; its proof body is the in-tree one (NOT reproved here — it depends on the
proven `prob_uniform_eq_card_filter_div_card` and the kernel above):

  CS25.DeepHole.numDistinct_div_card_le_pr :
    ((numDistinct p a : ℝ≥0) / (Fintype.card F : ℝ≥0))
      ≤ (Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ]).toNNReal

Conclusion for §C: the deep-hole `Pr[δ-close] ≥ numDistinct/q` input is ALREADY fully proven
in-tree and bottoms out in mathlib counting (the kernel above) + the proven uniform-PMF counting
lemma. There is NO residual probability input remaining for the CS25 deep-hole path; the only
genuine hypothesis is the arithmetic rate condition `k < n − ⌊δ·n⌋` (joint-far), itself proven.
-/

/-!
================================================================================
§D. CS25 capacity-side qEntropy ball-count breakdown — DISPOSITION (no new math)
================================================================================

The CS25 (qEntropy / ball-count) epsCA LOWER bound is the *complete breakdown* regime
`epsCA(RS, δ, δ) = 1`, already connected to a Grand-MCA upper witness in-tree via
`GrandChallenges.MCAUpperWitness.ofRSBreakdownCS25` and the count-budget form
`MCAUpperWitness.ofRSBreakdownCS25Counts`. Those consume

  `CodingTheory.rs_epsCA_breakdown_cs25{,_of_counts}`

whose residual is the qEntropy ball-count inequality `hsum` (the CS25 §Cor-1 covering count:
far-lines + jointly-close stacks < total stacks). That `hsum` is the irreducible paper input
(a ball-count over `WordStack F (Fin 2) ι`); the connector to `ε* < 1 ⟹ MCAUpperWitness` is the
proven plumbing. No additional SILVER reduction is extractable here beyond what already exists:
the §A/§B connectors above are the missing pieces; the CS25 breakdown connector already lands.

================================================================================
SUMMARY (Issue #22)
================================================================================

  PROVEN (new, this file):
    * MCAUpperWitness.ofBadLineBCHKS25            (BCHKS25 epsCA≥1/(2n) → Grand-MCA witness)
    * MCAUpperWitness.ofBadLineBCHKS25AllButOne   (all-but-one front door)
    * MCAUpperWitness.ofSeparationBGKS20          (BGKS20 epsCA≥1−1/|F| → Grand-MCA witness)
    * numDistinct_le_card_good_kernel             (mathlib-only deep-hole counting kernel)

  EXTERNAL RESIDUALS (isolated, named, irreducible paper-lemma content):
    * BadLineWitness (BCHKS25 affine-shift interpolation: |F| codewords ⟹ bad line)
    * NearCertainBadLine (BGKS20 char-2 rate-1/8 explicit stack construction)
    * the qEntropy ball-count `hsum` for CS25 breakdown (already isolated upstream)

  ALREADY-CLOSED IN-TREE (verified, not re-proved):
    * CS25 deep-hole joint-far + Pr[δ-close]≥numDistinct/q  (down to rate condition only)
    * the ε-arithmetic plumbing in Bridge2BCHKS25 / Bridge2BGKS20
    * the CS25 complete-breakdown Grand-MCA connector (ofRSBreakdownCS25)
-/

end ProximityGap.GrandChallenges.Issue22
