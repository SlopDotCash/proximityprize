/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MCAJohnsonMutualExtract
import Mathlib.Algebra.Polynomial.Roots

/-! # Uniqueness of the extracted codeword pair (toward MCA Johnson)

If the mutual agreement set has at least `deg` points, the pair `(p₀, p₁)`
extracted by `affineLine_mutual_extract` is THE unique low-degree pair — two
degree-`<deg` polynomials agreeing on `≥ deg` domain points coincide. Hence all
good slopes whose agreement sets pairwise overlap in `≥ deg` points extract one
and the same global codeword pair: the bridge from pairwise extraction to a
single joint (interleaved-code) proximate. -/

namespace MCAJohnson

open Polynomial

variable {F : Type*} [Field F] {ι : Type*} (domain : ι ↪ F)

/-- A degree-`<deg` polynomial is determined by its values on any `deg` domain
points: two such polynomials agreeing on a set `S` with `deg ≤ |S|` are equal. -/
theorem degreeLT_eq_of_agree_on_card {deg : ℕ} [NeZero deg]
    {p q : F[X]} (hp : p ∈ Polynomial.degreeLT F deg) (hq : q ∈ Polynomial.degreeLT F deg)
    {S : Finset ι} (hcard : deg ≤ S.card)
    (h : ∀ x ∈ S, p.eval (domain x) = q.eval (domain x)) : p = q := by
  classical
  have hpd : p.natDegree < deg := ReedSolomon.natDegree_lt_of_mem_degreeLT hp
  have hqd : q.natDegree < deg := ReedSolomon.natDegree_lt_of_mem_degreeLT hq
  -- work over the image Finset of S under the (injective) domain embedding
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p q (S.image domain) ?_ ?_
  · intro y hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
    exact h x hxS
  · rw [Finset.card_image_of_injective _ domain.injective]
    omega

/-- **Consensus of large-overlap proximates.** If two collinear proximate pairs
(at slopes `γ≠γ'` and `γ≠γ''`, sharing the same first codeword `c` and slope `γ`)
both extract on a common large set, the extracted slope/intercept polynomials are
forced equal. Concretely: two degree-`<deg` interpolants of `f₁` on a `≥deg` set
coincide — so the joint codeword pair is globally well-defined. -/
theorem extracted_pair_unique {deg : ℕ} [NeZero deg]
    {p₁ p₁' : F[X]} (hp₁ : p₁ ∈ Polynomial.degreeLT F deg)
    (hp₁' : p₁' ∈ Polynomial.degreeLT F deg)
    {f₁ : ι → F} {S : Finset ι} (hcard : deg ≤ S.card)
    (h : ∀ x ∈ S, p₁.eval (domain x) = f₁ x)
    (h' : ∀ x ∈ S, p₁'.eval (domain x) = f₁ x) : p₁ = p₁' :=
  degreeLT_eq_of_agree_on_card domain hp₁ hp₁' hcard
    (fun x hx => by rw [h x hx, h' x hx])

/-- **Full consensus of the extracted pair.** If two low-degree pairs both
interpolate `(f₀, f₁)` on a common set of at least `deg` domain points, then
both the slope and intercept polynomials coincide. -/
theorem extracted_pair_unique_full {deg : ℕ} [NeZero deg]
    {p₀ p₁ p₀' p₁' : F[X]}
    (hp₀ : p₀ ∈ Polynomial.degreeLT F deg) (hp₁ : p₁ ∈ Polynomial.degreeLT F deg)
    (hp₀' : p₀' ∈ Polynomial.degreeLT F deg) (hp₁' : p₁' ∈ Polynomial.degreeLT F deg)
    {f₀ f₁ : ι → F} {S : Finset ι} (hcard : deg ≤ S.card)
    (h : ∀ x ∈ S, p₁.eval (domain x) = f₁ x ∧ p₀.eval (domain x) = f₀ x)
    (h' : ∀ x ∈ S, p₁'.eval (domain x) = f₁ x ∧ p₀'.eval (domain x) = f₀ x) :
    p₀ = p₀' ∧ p₁ = p₁' := by
  refine ⟨?_, ?_⟩
  · exact degreeLT_eq_of_agree_on_card domain hp₀ hp₀' hcard
      (fun x hx => by rw [(h x hx).2, (h' x hx).2])
  · exact degreeLT_eq_of_agree_on_card domain hp₁ hp₁' hcard
      (fun x hx => by rw [(h x hx).1, (h' x hx).1])

end MCAJohnson
