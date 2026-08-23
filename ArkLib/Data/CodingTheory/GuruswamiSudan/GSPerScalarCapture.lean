/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSpecializedConditions
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorDegreeOverRatFunc

/-!
# Per-scalar capture by the generic GS interpolant (BCHKS25 §3 / S10 brick)

The uniformization half-step of the mutual-disagreement cover (issues #302/#304/#301): at
**every** scalar `z` (with nonzero specialization of the integer representative `Q₀`), the
δ-close codewords of the scalar fold `f₀ + z·f₁` within the Guruswami–Sudan Johnson radius are
**`Y`-roots of the one specialized generic object `Q₀(z)`**, hence number at most its `Y`-degree
— bounded by the `Y`-degree of the single generic interpolant, uniformly in `z`:

* `scalar_close_codeword_isRoot` — each close codeword polynomial is a root of `Q₀(z)`
  (composes the proven `scalar_fold_decoded_divides_specialization`).
* `scalar_close_codewords_card_le` — the per-scalar close-codeword count is `≤ natDegree (Q₀(z))`
  (distinct codewords give distinct roots; root-count ≤ degree).

What remains of the full S10 cover after this brick is exactly the **branch organization**: the
roots of `Q₀(z)` as `z` varies organize into the branches of the generic factors, and the
close-root branches are affine in `z` (the Hensel/branch-rigidity step S6 — see
`HenselBranchRigidity` and `GSAffinePair.affine_pair_of_hammingDist` for the proven local and
rational-case inputs). This file pins the cover's carrier as the specialization of one uniform
algebraic family, replacing the previous per-`z` ad-hoc lists. Axiom-clean.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- **Per-scalar capture by the specialized generic interpolant.** For every scalar `z` where the
integer representative `Q₀` specializes nonzero, every Reed–Solomon codeword within the
Guruswami–Sudan Johnson radius of the scalar fold `f₀ + z·f₁` is a `Y`-root of the specialized
bivariate `Q₀(z) ∈ F[X][Y]`. Hence the close-codeword list of EVERY scalar fold embeds in the
root set of a single uniform algebraic family — the specialization of one generic object. -/
theorem scalar_close_codeword_isRoot {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (p : ReedSolomon.code ωs k)
    (h_dist :
      (hammingDist (fun i => f₀ i + z * f₁ i)
          (fun i => (ReedSolomon.codewordToPoly p).eval (ωs i)) : ℝ) / n <
        gs_johnson k n m) :
    (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).IsRoot
      (ReedSolomon.codewordToPoly p) := by
  rw [← Polynomial.dvd_iff_isRoot]
  exact scalar_fold_decoded_divides_specialization ωs f₀ f₁ hQ hrep z hz hk hm p h_dist

/-- **The per-scalar close-codeword count is bounded by the generic `Y`-degree.** At every scalar
`z` with nonzero specialization, the number of distinct degree-`<k` codeword polynomials within
the Johnson radius of the fold `f₀ + z·f₁` is at most `natDegree_Y (Q₀(z))` — which is bounded by
the `Y`-degree of the single generic interpolant, uniformly in `z`. -/
theorem scalar_close_codewords_card_le {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (genericFold f₀ f₁) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (S : Finset (ReedSolomon.code ωs k))
    (hS : ∀ p ∈ S,
      (hammingDist (fun i => f₀ i + z * f₁ i)
          (fun i => (ReedSolomon.codewordToPoly p).eval (ωs i)) : ℝ) / n <
        gs_johnson k n m)
    (hinj : Set.InjOn (fun p : ReedSolomon.code ωs k => ReedSolomon.codewordToPoly p) S) :
    S.card ≤ (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).natDegree := by
  classical
  set Qz := Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) with hQz
  -- map each close codeword to its polynomial, a root of `Qz`
  have hroots : ∀ p ∈ S, (ReedSolomon.codewordToPoly p) ∈ Qz.roots := by
    intro p hp
    rw [Polynomial.mem_roots hz]
    exact scalar_close_codeword_isRoot ωs f₀ f₁ hQ hrep z hz hk hm p (hS p hp)
  -- distinct codewords give distinct roots, so the count is bounded by the root multiset card
  have hcard : S.card ≤ Multiset.card Qz.roots := by
    have himg : S.image (fun p => ReedSolomon.codewordToPoly p) ⊆ Qz.roots.toFinset := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [Multiset.mem_toFinset]
      exact hroots p hp
    calc S.card = (S.image (fun p => ReedSolomon.codewordToPoly p)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ Qz.roots.toFinset.card := Finset.card_le_card himg
      _ ≤ Multiset.card Qz.roots := Multiset.toFinset_card_le _
  exact le_trans hcard (Polynomial.card_roots' Qz)

end GuruswamiSudan.OverRatFunc

#print axioms GuruswamiSudan.OverRatFunc.scalar_close_codeword_isRoot
#print axioms GuruswamiSudan.OverRatFunc.scalar_close_codewords_card_le
