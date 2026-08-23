/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Line decoding (ABF26 §4.4)

Line decoding is a structural strengthening of list decoding that lifts a fiberwise
"line is close to *some* codeword" statement into an aligned "line is close to a *single*
affine pair `u₁ + γ·u₂`". Definition 4.20 of *Open Problems in List Decoding and Correlated
Agreement* (Arnon, Boneh, Fenzi; April 8, 2026) formalises this; the immediate downstream
fact is Theorem 4.21, which converts a line-decoding bound into a mutual correlated
agreement (MCA) bound.

## Main definitions

- `CodingTheory.LineDecodable` — ABF26 Definition 4.20: `(δ, a, b)`-line-decodability of
  an `F`-additive code `C`.

## Main statements

- `CodingTheory.lineDecodable_imp_epsMCA_le_target` — the black-box theorem shape once
  considered for ABF26 Theorem 4.21 [GG25 Thm 3.5]. It is kept only as a named target
  proposition because the unconstrained black-box statement is formally refuted in
  `LineDecodingRefutation.lean`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §4.4.
- [GG25] Guo, Gerbush. Definition 3.1 / Theorem 3.5 (original source).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open ProximityGap

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **ABF26 Definition 4.20 [GG25 Def 3.1].** A code `C ⊆ A^ι` is `(δ, a, b)`-**line-decodable**
when every `γ`-indexed family of codewords that aligns with a random line `f₁ + γ·f₂` on at
least an `a/|F|` fraction of `γ`'s is itself induced (on at least a `b/|F|` fraction of `γ`'s)
by a single affine pair `(u₁, u₂)` of codewords.

In formula:

  `∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ, U γ ∈ C) →`
  `  Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ] ≥ a / |F| →`
  `  ∃ u₁ u₂ ∈ C, Pr_γ [U γ = u₁ + γ • u₂] ≥ b / |F|`

The hypothesis pins each `U γ` inside `C`; ABF26 writes this as `U : F → C` but Lean is
cleaner with a function into the ambient space plus a side condition. The probabilities
are read in `ENNReal`, matching the convention in
[`ProximityGap.Errors`](ProximityGap.Errors.lean). -/
def LineDecodable (C : Set (ι → A)) (δ : ℝ≥0) (a b : ℝ≥0) : Prop :=
  ∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ : F, U γ ∈ C) →
    (a : ENNReal) / (Fintype.card F : ENNReal)
        ≤ Pr_{let γ ← $ᵖ F}[δᵣ(f₁ + γ • f₂, U γ) ≤ δ] →
    ∃ u₁ ∈ C, ∃ u₂ ∈ C,
      (b : ENNReal) / (Fintype.card F : ENNReal)
          ≤ Pr_{let γ ← $ᵖ F}[U γ = u₁ + γ • u₂]

/- **ABF26 Theorem 4.21 [GG25 Thm 3.5].** If `C` is `(δ, a, n+1)`-line-decodable, then its
mutual correlated agreement error is bounded by `a / |F|`:

  `LineDecodable (F := F) C δ a (n+1) → ε_mca(C, δ) ≤ a / |F|`

where `n = |ι|`. The proof in [GG25] proceeds by taking the line-decoder's witness
pair `(u₁, u₂)` and showing that the `Δ_S = 0` witness set of the MCA event must coincide
with the `γ`-set on which `U γ = u₁ + γ • u₂`, which has measure `≥ (n+1)/|F|`. Because
that pair has at most `n` exceptional positions on every fold, the alignment lifts to a
joint-pair witness, contradicting the `¬ pairJointAgreesOn` clause of `mcaEvent` when the
fraction of γ-aligned points exceeds `n/|F|`.

## Status (2026-06): U-construction realised in-tree; residual is the multi-γ coverage count

The statement is reduced here, via `iSup_le`, to the **per-stack** bound
`Pr_γ[mcaEvent C δ (u 0) (u 1) γ] ≤ a / |F|` for every word stack `u`, then attacked by
contradiction. The **GG25 U-construction is now fully formalised in-tree** (no longer a
black-box): fixing `f₁ := u 0`, `f₂ := u 1`, the proof builds
`U : F → ι → A`, `U γ := if mcaEvent fires then the event's witness codeword `w_γ` else `0``
(`0 ∈ C` as `C` is a submodule), proves `∀ γ, U γ ∈ C` (`hU_mem`) and that on the
`mcaEvent`-set the line is `δ`-close to `U γ` (`hU_close`, agreement on the size-`≥(1-δ)n`
witness set `S_γ`; cf. `ProximityGap.mcaEvent_imp_relCloseToCode`). Under the negated goal
`Pr_γ[mcaEvent] > a/|F|`, event-domination (`Pr_le_Pr_of_implies`) lifts this to
`a/|F| ≤ Pr_γ[δᵣ(f₁+γ·f₂, U γ) ≤ δ]`, so **line-decodability fires in-tree** and yields a
single affine pair `(u₁, u₂) ∈ C` with `Pr_γ[U γ = u₁ + γ·u₂] ≥ (n+1)/|F|`.

**Residual (the only remaining `sorry`): the GG25 multi-γ overlap/coverage extraction.**
The aligned set `G := {γ : U γ = u₁ + γ·u₂}` has `> n` elements. For `γ ∈ G` with `mcaEvent`
firing, `U γ = w_γ` agrees with the line on `S_γ`, so the affine-in-γ word
`D(γ) := (u₁ - f₁) + γ·(u₂ - f₂)` vanishes on `S_γ`. To contradict `¬ pairJointAgreesOn C
S_{γ₀} f₁ f₂` for a fixed bad `γ₀` one must show `(u₁, u₂)` agrees with `(f₁, f₂)` on **all**
of `S_{γ₀}`, i.e. for **every** `i ∈ S_{γ₀}` a *second* aligned-mcaEvent `γ ≠ γ₀` with
`i ∈ S_γ` (two zeros of the affine `g_i(γ) := (u₁-f₁) i + γ·(u₂-f₂) i` pin `u₁ i = f₁ i`,
`u₂ i = f₂ i`). Note `pairJointAgreesOn` is **antitone** in `S`, so the easy 2-γ argument —
which only yields agreement on the *intersection* `S_γ ∩ S_{γ'} ⊆ S_{γ₀}` — does **not**
contradict `¬ pairJointAgreesOn` on the larger `S_{γ₀}` (wrong direction).

## WALL (2026-06-04): the counting reduction is mathematically FALSE; only the
## Guruswami–Sudan bivariate route closes it, and that route is unavailable for a black-box `a`.

Exact residual goal (via `extract_goal`): `False`, with the hypotheses
`hgt : a/|F| < Pr_γ[mcaEvent C δ f₁ f₂ γ]`, the U-construction facts (`hU_mem`, `hU_close`,
`hPr_close`), and the line-decoder output `u₁ u₂ ∈ C`,
`hPr_align : (n+1)/|F| ≤ Pr_γ[U γ = u₁ + γ·u₂]`.

The reduction of this `False` to a **pure-Nat double-coverage count** is:
let `H := {γ ∈ G : mcaEvent fires}` (`|H| ≥ n+1` after clearing the `|F|` denominators),
each `S_γ` (`γ ∈ H`) missing `≤ m := ⌊δ·n⌋` positions of `T := S_{γ₀}`; the target is
`∀ i ∈ T, 2 ≤ |{γ ∈ H : i ∈ S_γ}|` (per-position double coverage of the *full* `T`).
**This target is false whenever `m ≥ 1`** (i.e. `δ ≥ 1/n`, the only non-degenerate regime):
take every `γ ∈ H` to miss the **same** position `i₀ ∈ T` and cover `T \ {i₀}` — each then
misses exactly `1 ≤ m` position of `T`, `|H|` may be arbitrarily large, yet `i₀` is covered
`0 < 2` times, so the affine `g_{i₀}` gets only one equation and `(u₁ u₂)` is unpinned at `i₀`.
A kernel-checked counterexample to the reduction target lives at
`ArkLib/Data/CodingTheory/ProximityGap/LineDecodingCounting.lean`
(`double_coverage_counterexample`, axioms `[propext, Classical.choice, Quot.sound]`;
the constant-`S` fiber is beta-reduced before `decide`, since a free `γ` blocks the kernel
decision procedure — the earlier `intro γ _; decide` form did *not* compile).
Equivalently: the docstring's earlier claim that "the `n+1`-point budget closes the cover"
is **wrong** — the per-position miss is *not* bounded by the per-γ total miss `δn`, so the
`n+1`-budget bounds the *average* coverage, never the *minimum*. Averaging gives double
coverage of *most* of `T`, but `pairJointAgreesOn` is antitone and needs *all* of `T`.

Five genuinely-different skeletons, all dying at the same one-linear-equation obstruction:
  S1 (per-position counting on `T`): false, see counterexample above.
  S2 (global probability count): `|mcaEvent set| > a` and `|H| ≥ n+1` are facts about
     distinct overlapping γ-sets with no structural link; no contradiction.
  S3 (single-γ codeword-forcing / UDR): under `2δn < d_min`, `mcaEvent` at `γ` forces the
     witness `w_γ = combined`, but only the *combined* equation on `S_γ \ S'` (cf. the
     letter-exact analysis at `Errors.lean` L609–645,
     `mcaEvent_witness_eq_combined_of_jointProximity_udr`); the per-coordinate split is
     exactly what is missing — UDR does not shortcut it.
  S4 (aligned∩mcaEvent direct at a single γ): for `γ ∈ H` with `mcaEvent`, `(u₁,u₂)` is a
     joint-pair candidate but agrees with `(f₁,f₂)` on `S_γ` only via the combined equation
     `u₁+γu₂ = f₁+γf₂`; identical obstruction to S3.
  S5 (re-instantiate line-decodability at a perturbed `(f₁',f₂')`): no second instance
     produces the missing per-coordinate datum.

The genuine [GG25 Thm 2 / eprint 2025/2110; BCIKS20 Thm 5.1] proof routes through the
Guruswami–Sudan list decoder of `f₀ + Z·f₁` over the rational-function field `F(Z)`: the
aligned γ's are the roots of a single bivariate interpolation polynomial `Q(X,Y)` whose
`Y`-degree `ℓ` is the list size, and `a = |E| ≤ ℓ⁷·(ρn)²/3` is *defined by* that polynomial.
That is the in-tree `WeightedAgreement.list_agreement_on_curve_implies_correlated_agreement_bound`
machinery (the `badCoord_match_card_le` degree-`l+1` fiber bound, `sum_filter_sum_eq`
double-counting). Importing it here would require `a` to carry the GS degree structure; the
present statement abstracts `a` as a *free* `ℝ≥0`, severing that link. Closing this `sorry`
faithfully therefore requires **strengthening the statement** to expose the GS interpolation
(an `a := ℓ⁷(ρn)²/3`-shaped hypothesis with a `ReedSolomon.code`/Johnson-bound side condition),
i.e. a documented statement REPAIR, *not* a leaf proof of the present black-box form.

This repair has now landed: `LineDecodingCoverage.lean` provides the faithful
repaired theorem `lineDecodable_imp_epsMCA_le_target` which explicitly consumes the
`MCAForallDoubleCover` overlap-coverage data rather than the refuted black-box
line-decodability implication.

-/

end

end CodingTheory
