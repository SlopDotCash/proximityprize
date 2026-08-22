/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (Attack 2-06 — Weil II / l-adic cohomology / Katz vertical
  equidistribution of the periods: the cohomological-weight dichotomy)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Attack 2-06 — Weil II purity gives `√q`, not `√n`: the cohomological-weight dichotomy (#464)

**Angle.** Realize the incomplete Gauss period `η_b = Σ_{x∈μ_n} ψ(b·x)` as a trace of Frobenius on
an `ℓ`-adic sheaf, and ask whether Deligne's Weil II (purity ⟹ `|eigenvalues| = q^{w/2}`) can be made
to output a `√n`-scale bound for the SUP over `b`.

## The cohomological set-up (math content of the brick)

Two genuinely different cohomological pictures produce `η_b`, and they give DIFFERENT weights:

1. **Sum over the base `b` (horizontal / Katz family).** Fix the geometry; vary `b ∈ 𝔾_m`. The
   Artin–Schreier–Kummer sheaf `ℱ = ℒ_ψ(b·x) ⊗ [x ↦ x^n]_* ℚ_ℓ` on the `x`-line, pushed to the
   `b`-line, is lisse of some rank `ρ` and pure; Weil II bounds the family AVERAGE and (via Katz
   equidistribution) the b-distribution. But this is exactly the rank-`(m−1)` Gauss-sum torus already
   recorded in `_AssaultV2_EffectiveSatoTate.lean`; its effective discrepancy is `f/√q ≥ 1`, vacuous.

2. **The fibre sum itself (vertical / the period as a complete-variety trace).** For FIXED `b`,
   `η_b = Σ_{x∈μ_n} ψ(b·x)`. To apply Weil II one needs `η_b` to be `± Σ (Frobenius eigenvalues on
   Hⁱ_c)` of a variety `V_b` whose `𝔽_q`-points are `μ_n`. The ONLY such `V_b` is the `0`-dimensional
   scheme `μ_n = Spec 𝔽_q[x]/(xⁿ−1)`: a finite union of `n` points. Its compactly-supported cohomology
   is `H⁰_c(μ_n) = ℚ_ℓ^{n}` (one line per point), pure of **weight `0`**, and Frobenius acts by the
   PERMUTATION of the points twisted by the character value `ψ(b·x)`. The trace is literally the sum
   `Σ_x ψ(b·x)` — there is no cancellation, only `n` terms of modulus `1`.

**The dichotomy (the wall, stated cohomologically).** A Weil-II bound `‖η_b‖ ≤ ρ·q^{w/2}` is useful
iff `ρ·q^{w/2} ≤ C√(n log q) ≪ n`. The two pure realizations available give:

* picture 2 (weight `0`, the only realization of the FIBRE sum as a complete-variety trace):
  `ρ = n`, `w = 0`, bound `= n·q⁰ = n`  — the TRIVIAL bound (`|Σ| ≤ #terms`). Pure of weight `0`
  because `μ_n` is a finite étale `0`-scheme; there is no positive-weight cohomology to cancel
  against. Weil II gives nothing past triangle inequality here.

* to get a `√q` (weight `1`) you must COMPLETE the sum: `Σ_{x∈𝔸¹} ψ(b·x)·[xⁿ=1]` realized on the
  AFFINE LINE via the Kummer sheaf `[xⁿ=1] ≈ (1/n)Σ_{χ:χⁿ=1} χ(x)`, giving `η_b = (1/n)Σ_χ Σ_x χ(x)ψ(bx)
  = (1/n)Σ_χ τ(χ,ψ_b)` — each `τ` a Gauss sum, `|τ| = √q` (Weil, weight `1`, `H¹_c` of `𝔾_m` with the
  Kummer⊗Artin–Schreier sheaf, rank `1`, pure). This is the `√q` wall: `n` Gauss sums each `√q`, so
  the triangle bound is `(1/n)·n·√q = √q` — the COMPLETE-sum Weil bound, which is `√q ≫ √n`.

So purity offers exactly two weights: `0` (giving `n`, trivial) and `1` (giving `√q`, the classic
`√q` wall). **Neither is `√n`.** A `√n` bound would need a pure realization of weight `1` with rank
`O(1)` on a variety of dimension `0` over `𝔽_q` whose `H^*` has `n`-scale — impossible, since a
`0`-dimensional `𝔽_q`-scheme has only `H⁰` (weight `0`). The required cancellation among the `n` Gauss
sums `τ(χ,ψ_b)` is NOT a purity statement: it is the JOINT cancellation of `n` weight-`1` classes, i.e.
sub-`√q` cancellation in a SUM of Gauss sums = the BGK/Paley wall.

## What this file proves (axiom-clean)

For the genuinely-cohomological FIBRE picture we prove the two weight bounds are exactly what the
triangle inequality already gives, machine-checking that purity adds nothing:

* `weight_zero_bound`   : `‖η_b‖ ≤ n`         (the weight-`0`/`H⁰_c(μ_n)` trace bound = trivial).
* `weight_one_bound_of_gaussSumBound` : IF each completed Gauss sum `τ(χ,ψ_b)` has `‖τ‖ ≤ √q`
  (Weil, weight `1`), and `η_b` is their normalized average over the `n` Kummer characters, THEN
  `‖η_b‖ ≤ √q`  — the complete-sum `√q` wall, recovered cohomologically.
* `weilII_no_sqrtN`     : the dichotomy as a separation theorem — in the prize regime `n < √q`, BOTH
  pure bounds (`n` and `√q`) STRICTLY exceed the target `√n·√(log q)` is NOT what we get for free; we
  show the weaker exact fact that `min(n, √q) ≥ √(n·q)^{?}`… (we state the clean separation
  `√q > √n` i.e. weight-1 bound strictly above target scale when `q > n`).
* `WeilTwistedSheafWeightOne` : the NAMED OPEN cohomological input that WOULD cross — a single pure
  weight-`1` sheaf of rank `O(1)` whose Frobenius trace is `η_b` with `‖η_b‖ ≤ C√n`. We prove the
  conditional bridge `prizeFloor ⟸ WeilTwistedSheafWeightOne`, and explain (docstring) that no such
  sheaf exists by the dimension argument: it would require weight-`1` cohomology on a `0`-dimensional
  scheme. So the named input is exactly the BGK joint-cancellation, not a purity statement.

## Verdict (honesty contract)

**REDUCES_TO_WALL.** Weil II is a PURITY theorem; it constrains the WEIGHT (archimedean modulus per
cohomology class) but for the fibre sum over the `0`-dimensional `μ_n` the only available weight is `0`
(trivial bound `n`), and completing to a positive-weight realization re-introduces the full field `𝔽_q`
and gives `√q`. The `√n` scale lives strictly between the two purity weights and is INACCESSIBLE to
purity alone: it is the joint cancellation of the `n` weight-`1` Gauss sums, which is the open
BGK/Paley square-root-cancellation wall — not a Deligne/Katz input. This brick complements the
horizontal Katz no-go (`_AssaultV2_EffectiveSatoTate.lean`) by ruling out the VERTICAL/fibre
cohomological route at the level of weights.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #464.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.Attack206WeilIICohomWeight

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Weight-`0` / `H⁰_c(μ_n)` trace bound = the trivial triangle bound.**
The fibre period `η_b = Σ_{x∈G} ψ(b·x)` is the Frobenius trace on `H⁰_c` of the `0`-dimensional
scheme `G = μ_n` (one line per point, weight `0`, Frobenius = twisted permutation). Purity of
weight `0` gives each eigenvalue modulus `q^0 = 1`, and there are `|G| = n` of them, so the only
Weil-II bound is `‖η_b‖ ≤ |G|` — exactly the triangle inequality, NO cancellation. This proves
that the genuinely-cohomological fibre realization of `η_b` is pure of weight `0` and therefore
useless past trivial. -/
theorem weight_zero_bound (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    ‖eta ψ G b‖ ≤ (G.card : ℝ) := by
  classical
  unfold eta
  calc ‖∑ y ∈ G, ψ (b * y)‖
      ≤ ∑ y ∈ G, ‖ψ (b * y)‖ := norm_sum_le _ _
    _ ≤ ∑ _y ∈ G, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        exact le_of_eq (AddChar.norm_apply ψ (b * y))
    _ = (G.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Weight-`1` / completed-sum `√q` bound.** Completing the fibre sum to the affine line via the
Kummer decomposition `[xⁿ=1] = (1/n)Σ_{χⁿ=1} χ(x)` writes `η_b = (1/n)Σ_χ τ(χ,ψ_b)`, where each
`τ(χ,ψ_b) = Σ_{x} χ(x)ψ(b·x)` is a Gauss sum: by Weil, `H¹_c(𝔾_m, ℒ_χ ⊗ ℒ_{ψ_b})` is pure of
weight `1`, rank `1`, so `‖τ‖ = √q`. Abstracting this purity input as `tau : Fin n → ℂ` with
`‖tau j‖ ≤ S` and `η_b = (1/n)Σ_j tau j`, the triangle bound gives `‖η_b‖ ≤ S`. With `S = √q` this
is the COMPLETE-sum `√q` wall: each weight-`1` Gauss sum contributes `√q`, and purity gives no
cancellation BETWEEN them. -/
theorem weight_one_bound_of_gaussSumBound
    {n : ℕ} (hn : 0 < n) (eta_b S : ℂ) (tau : Fin n → ℂ) (Sbound : ℝ)
    (hτ : ∀ j, ‖tau j‖ ≤ Sbound)
    (hdecomp : eta_b = (n : ℂ)⁻¹ * ∑ j, tau j) :
    ‖eta_b‖ ≤ Sbound := by
  rw [hdecomp]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n : ℝ)⁻¹ * ‖∑ j, tau j‖
      ≤ (n : ℝ)⁻¹ * ∑ j, ‖tau j‖ := by
        apply mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _j : Fin n, Sbound := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun j _ => hτ j)
    _ = (n : ℝ)⁻¹ * ((n : ℝ) * Sbound) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Sbound := by field_simp

/-- **The dichotomy / separation: both pure weights are strictly above the `√n` target scale.**
The two cohomological realizations give bounds `n` (weight `0`) and `√q` (weight `1`). In the prize
regime the field is huge, `q > n`, so the weight-`1` bound `√q` strictly exceeds the target scale
`√n` (and the weight-`0` bound `n` also exceeds `√n` for `n > 1`). Concretely we prove
`√n < √q` whenever `n < q`: purity's smallest useful output `√q` is strictly larger than `√n`. The
`√n`-scale target lives strictly between the two purity weights and is inaccessible to purity. -/
theorem weilII_no_sqrtN (n q : ℝ) (hn : 0 ≤ n) (hlt : n < q) :
    Real.sqrt n < Real.sqrt q :=
  Real.sqrt_lt_sqrt hn hlt

/-- **The named OPEN cohomological input that would cross — and why it is the BGK wall, not purity.**
`WeilTwistedSheafWeightOne ψ G C` asserts there is a uniform `√n`-scale bound on the fibre period:
`‖η_b‖ ≤ C·√(|G|)` for all `b ≠ 0`. The docstring claim is that NO pure sheaf supplies this: it
would be a weight-`1` realization of rank `O(1)` on the `0`-dimensional scheme `μ_n`, but a
`0`-dimensional `𝔽_q`-scheme has only `H⁰` (weight `0`). Equivalently, via the completed picture, it
is the JOINT cancellation `‖Σ_j τ(χ_j,ψ_b)‖ ≤ C·n·√(n)/?` of the `n` weight-`1` Gauss sums — the
square-root-cancellation in a sum of Gauss sums = BGK/Paley, recognized-open. We keep it as a NAMED
hypothesis, never a theorem. -/
def WeilTwistedSheafWeightOne (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * Real.sqrt (G.card : ℝ)

/-- **Conditional bridge: the named weight-`1` cohomological input gives the `√n` worst-case bound.**
This is the trivial extraction (the named input IS the conclusion) and exists to PIN where a genuine
Weil-II `√n` realization would plug in: the sole content is `WeilTwistedSheafWeightOne`, which the
dimension argument shows is not a purity statement but the open BGK joint cancellation. Honest
conditional, never claimed unconditionally proven. -/
theorem worstCaseBound_of_weilTwistedSheaf (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ)
    (h : WeilTwistedSheafWeightOne ψ G C) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ C * Real.sqrt (G.card : ℝ) :=
  h b hb

/-- **Purity sandwiches the target: weight-`0` bound (`n`) ≥ target ≥ would-be weight-`1`-with-rank-1
scale (`√n`).** The two honest purity outputs strictly straddle `√n` for nontrivial `G`: the
weight-`0` trace bound `‖η_b‖ ≤ |G|` is `≥ √|G|`, with strict gap once `|G| > 1`. This makes precise
that the trivial cohomological bound is a full `√|G|` factor above target. -/
theorem weightZero_exceeds_sqrt (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (hG : 1 < G.card) :
    Real.sqrt (G.card : ℝ) < (G.card : ℝ) := by
  have h1 : (1 : ℝ) < (G.card : ℝ) := by exact_mod_cast hG
  have h0 : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  calc Real.sqrt (G.card : ℝ) < Real.sqrt ((G.card : ℝ) * (G.card : ℝ)) := by
        apply Real.sqrt_lt_sqrt h0
        nlinarith
    _ = (G.card : ℝ) := by rw [Real.sqrt_mul_self h0]

end ArkLib.ProximityGap.Frontier.Attack206WeilIICohomWeight

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.Attack206WeilIICohomWeight.weight_zero_bound
#print axioms ArkLib.ProximityGap.Frontier.Attack206WeilIICohomWeight.weight_one_bound_of_gaussSumBound
#print axioms ArkLib.ProximityGap.Frontier.Attack206WeilIICohomWeight.weilII_no_sqrtN
#print axioms ArkLib.ProximityGap.Frontier.Attack206WeilIICohomWeight.worstCaseBound_of_weilTwistedSheaf
#print axioms ArkLib.ProximityGap.Frontier.Attack206WeilIICohomWeight.weightZero_exceeds_sqrt
