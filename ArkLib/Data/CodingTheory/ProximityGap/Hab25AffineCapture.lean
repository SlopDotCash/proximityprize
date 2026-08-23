/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonNumericBridge

/-!
# Hab25 §3 — the affine-capture cover: per-stack algebraic data from captured bad scalars

This file builds the per-stack `Hab25JohnsonAlgebraicData` bundle — the input the in-tree
S11 bridge (`JohnsonNumericBound.of_algebraic_cover_nat`) consumes — from a single,
precisely-named hypothesis per bad scalar: **affine capture**.

A bad scalar `γ` (one triggering the `mcaEvent`) is *affine-captured* by a pair
`(a, b) ∈ F[X]²` when some `mcaEvent` witness set `S` certifies the closeness of the fold
with the **affine codeword** `a + γ·b` itself (`AffineCaptured`). This is exactly what the
proven S6 kernel produces for the `K = F(Z)`-decoded list (`affine_pair_of_hammingDist`:
every `K`-decoded codeword *is* an affine pair, and its `Z := γ` specialization is a
codeword agreeing with the fold).

The mathematical content here is the **improvement lemma** (`affineCaptured_improve`),
Hab25's "from the proof of Lemma 1" step upgraded to the mutual setting: if `γ` is
affine-captured by `(a, b)`, then because the `mcaEvent` forbids *joint* agreement on the
witness set `S`, the pair `(a, b)` must disagree with `(f₀, f₁)` somewhere **on `S`** —
and at such a coordinate `x` the fold agreement forces the affine functional
`(a(x) − f₀ x) + γ·(b(x) − f₁ x)` to vanish. That is precisely the `hImprove` obligation
of the bundle, with difference vectors `d₀ = a∘D − f₀`, `d₁ = b∘D − f₁`.

Capstones:

* `exists_algebraicData_of_affine_capture` — a finite pair list of size `≤ L` capturing
  all bad scalars assembles into a full `Hab25JohnsonAlgebraicData` bundle with
  `Edis = hab25McaBadScalars` and `ℓ = L`;
* `johnsonNumericBound_of_affine_capture` — composed with the in-tree S11 bridge: per-stack
  capture lists + the closed-form inequality `L·n/|F| ≤ johnsonBoundReal` imply the
  previously-atomic `JohnsonNumericBound` residual.

**What remains after this file** (the honest residual, now a single named Prop): *every*
bad scalar is affine-captured by a list of `≤ L` pairs — i.e. the per-`z` decoded codewords
all arise from the `K`-level affine pairs. Its divisibility skeleton is the proven
S10 bridge (`GSIntegerRepresentative` / `GSSpecializedConditions`: both per-`z` decoded
codewords and affine-pair specializations divide the same `Q₀|_{Z:=z}`); the open kernel is
the factor-matching step (no per-`z` codeword hides in a non-affine factor — the deep
BCIKS20 §5 Hensel content).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory Polynomial

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Affine capture.** The bad scalar `γ` is captured by the pair `(a, b)` when some
`mcaEvent`-shaped witness set `S` (large, no joint agreement) certifies the fold's closeness
with the affine codeword `a + γ·b` itself. The `K = F(Z)`-decoded list supplies exactly such
pairs via the proven S6 kernel (`affine_pair_of_hammingDist`). -/
def AffineCaptured (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) ι₀) (γ : F₀) (ab : F₀[X] × F₀[X]) : Prop :=
  ∃ S : Finset ι₀, ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀) ∧
    (∀ i ∈ S, (ab.1 + Polynomial.C γ * ab.2).eval (domain i) = u 0 i + γ • u 1 i) ∧
    ¬ pairJointAgreesOn ((ReedSolomon.code domain k : Set (ι₀ → F₀))) S (u 0) (u 1)

/-- **The improvement lemma (Hab25 "from the proof of Lemma 1", mutual form).** If `γ` is
affine-captured by `(a, b)` (with the degree bounds making the pair's rows codewords), then
the pair disagrees with `(f₀, f₁)` at some coordinate of the witness set — forbidden joint
agreement — and there the fold agreement forces the affine functional to vanish:

  `∃ x ∈ disagreeSet (a∘D − f₀) (b∘D − f₁), affineGap … γ x = 0`.

This is exactly the `hImprove` obligation of `Hab25JohnsonAlgebraicData`. -/
theorem affineCaptured_improve {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀} {ab : F₀[X] × F₀[X]}
    (hdeg₀ : ab.1.natDegree < k) (hdeg₁ : ab.2.natDegree < k)
    (hcap : AffineCaptured domain k δ u γ ab) :
    ∃ x ∈ disagreeSet (fun i => ab.1.eval (domain i) - u 0 i)
        (fun i => ab.2.eval (domain i) - u 1 i),
      affineGap (fun i => ab.1.eval (domain i) - u 0 i)
        (fun i => ab.2.eval (domain i) - u 1 i) γ x = 0 := by
  classical
  obtain ⟨S, _hScard, hagree, hnjp⟩ := hcap
  -- the pair's rows are Reed–Solomon codewords
  have hv₀ : (fun i => ab.1.eval (domain i)) ∈
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) :=
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval ab.1 hdeg₀ fun i => rfl
  have hv₁ : (fun i => ab.2.eval (domain i)) ∈
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) :=
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval ab.2 hdeg₁ fun i => rfl
  -- forbidden joint agreement ⇒ a disagreement coordinate on `S`
  have hdis : ¬ ∀ i ∈ S, ab.1.eval (domain i) = u 0 i ∧ ab.2.eval (domain i) = u 1 i := by
    intro hall
    exact hnjp ⟨_, hv₀, _, hv₁, hall⟩
  push Not at hdis
  obtain ⟨x, hxS, hxne⟩ := hdis
  refine ⟨x, ?_, ?_⟩
  · -- the coordinate lies in the disagreement set
    rw [disagreeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hxne (sub_eq_zero.mp hcon.1) (sub_eq_zero.mp hcon.2)
  · -- the fold agreement at `x` kills the affine functional
    have h := hagree x hxS
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul] at h
    show (ab.1.eval (domain x) - u 0 x) + γ * (ab.2.eval (domain x) - u 1 x) = 0
    linear_combination h

/-- **Per-stack algebraic data from an affine-capture list.** A finite list of `≤ L` pairs
capturing every bad scalar of the stack `u` assembles into a complete
`Hab25JohnsonAlgebraicData` bundle: the factor index is the pair list, the difference
vectors are `(a∘D − f₀, b∘D − f₁)`, the per-factor exceptional sets are the captured
scalars, the cover is the capture hypothesis, and `hImprove` is the proven improvement
lemma. The bundle's `Edis` is exactly `hab25McaBadScalars` and `ℓ = L`. -/
theorem exists_algebraicData_of_affine_capture
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (hη : 0 < η)
    (hδ : InJohnsonRange domain k η δ)
    (u : WordStack F₀ (Fin 2) ι₀) (pairs : Finset (F₀[X] × F₀[X])) (L : ℕ)
    (hL : pairs.card ≤ L)
    (hdeg : ∀ ab ∈ pairs, ab.1.natDegree < k ∧ ab.2.natDegree < k)
    (hcap : ∀ γ ∈ hab25McaBadScalars domain k δ u,
      ∃ ab ∈ pairs, AffineCaptured domain k δ u γ ab) :
    ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
      hab25McaBadScalars domain k δ u ⊆ A.Edis ∧ A.ℓ = L := by
  classical
  refine ⟨{
    Idx := F₀[X] × F₀[X]
    decIdx := inferInstance
    Index := pairs
    ℓ := L
    hYbound := hL
    d₀ := fun ab i => ab.1.eval (domain i) - u 0 i
    d₁ := fun ab i => ab.2.eval (domain i) - u 1 i
    Edis := hab25McaBadScalars domain k δ u
    Efactor := fun ab => (hab25McaBadScalars domain k δ u).filter
      (fun γ => AffineCaptured domain k δ u γ ab)
    hcover := ?_
    hImprove := ?_ }, subset_rfl, rfl⟩
  · intro γ hγ
    obtain ⟨ab, habp, hcapγ⟩ := hcap γ hγ
    exact Finset.mem_biUnion.mpr ⟨ab, habp, Finset.mem_filter.mpr ⟨hγ, hcapγ⟩⟩
  · intro ab habp γ hγ
    exact affineCaptured_improve (hdeg ab habp).1 (hdeg ab habp).2
      (Finset.mem_filter.mp hγ).2

/-- **The Johnson numeric residual from per-stack affine capture.** Per-stack capture lists
of size `≤ L` plus the closed-form parameter inequality `L·n/|F| ≤ johnsonBoundReal`
discharge the previously-atomic `JohnsonNumericBound` residual, through the in-tree S11
bridge `JohnsonNumericBound.of_algebraic_cover_nat`. The only remaining mathematical input
is the capture hypothesis itself. -/
theorem johnsonNumericBound_of_affine_capture
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ pairs : Finset (F₀[X] × F₀[X]), pairs.card ≤ L ∧
        (∀ ab ∈ pairs, ab.1.natDegree < k ∧ ab.2.natDegree < k) ∧
        ∀ γ ∈ hab25McaBadScalars domain k δ u,
          ∃ ab ∈ pairs, AffineCaptured domain k δ u γ ab)
    (hreal : ((L * Fintype.card ι₀ : ℕ) : ℝ) / (Fintype.card F₀ : ℝ) ≤
      johnsonBoundReal domain k η δ) :
    JohnsonNumericBound domain k η δ := by
  refine JohnsonNumericBound.of_algebraic_cover_nat domain k η δ
    (L * Fintype.card ι₀) hη hδ hreal ?_
  intro u
  obtain ⟨pairs, hL, hdeg, hcap⟩ := hdata u
  obtain ⟨A, hsub, hℓ⟩ :=
    exists_algebraicData_of_affine_capture domain k η δ hη hδ u pairs L hL hdeg hcap
  exact ⟨A, hsub, by rw [hℓ]⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.affineCaptured_improve
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_algebraicData_of_affine_capture
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_affine_capture
