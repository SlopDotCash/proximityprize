/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSimplexBound
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound

/-!
# The explicit Reed–Solomon Johnson list-decoding bound (verified, composed)

This file composes two independently-proven, `sorry`-free bricks into the **Reed–Solomon-specific**
Johnson list-size bound — the second row of the ABF26 proximity table (Issue #232 §3, the "up to the
Johnson radius `1 − √ρ`" regime) instantiated for the *explicit* RS codes the prize fixes:

* `ArkLib.CodingTheory.JohnsonSimplex.johnson_simplex_bound` — the honest second-moment/Gram Johnson
  bound (a list of words pairwise agreeing on `≤ b` coordinates, each agreeing with `w` on `≥ a`, has
  `|L|·(a² − n·b) ≤ n²`). This file keeps the RS composition on the self-contained simplex route;
  the parallel `ArkLib.JohnsonList`/`ArkLib.Coverage` route is also axiom-clean in the current tree.
* `ArkLib.CodingTheory.UniqueDecoding.agreement_card_le` — distinct degree-`<k` polynomials on an
  injective domain agree on `≤ k − 1` coordinates (root counting).

Plugging `b = k − 1` (the RS pairwise-agreement bound) into the Johnson bound gives:

`reedSolomon_johnson_list_bound` — a list `L` of Reed–Solomon codewords of degree-`<k` polynomials,
each agreeing with a received word `w` on `≥ a` of the `n = |ι|` coordinates, has
`|L| · (a² − n·(k−1)) ≤ n²`. When `n·(k−1) < a²` (the RS Johnson gap), this caps `|L|`; with the
substitution `a = n − e`, `d = n − k + 1` this is exactly the Johnson radius
`e < n − √(n(k−1)) = n(1 − √((k−1)/n)) ≈ n(1 − √ρ)`, the lower edge of the prize gap `[1−√ρ, 1−ρ]`.
`reedSolomon_johnson_list_card_le_div` is the natural-number form `|L| ≤ ⌊n² / (a² − n·(k−1))⌋`
under that gap.

`sorry`-free, axiom-clean, and a genuine *composition* on a clean foundation. Not the open prize apex
(the interior of `(1−√ρ, 1−ρ)`).
-/

open Polynomial Finset

namespace ArkLib.CodingTheory.ReedSolomonJohnson

open ArkLib.CodingTheory.JohnsonSimplex ArkLib.CodingTheory.UniqueDecoding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Reed–Solomon Johnson list-decoding bound.** A list `L` of words, each of which is the
evaluation `i ↦ p(D i)` of some polynomial `p` of degree `< k` on an injective domain `D`, with each
agreeing with the received word `w` on at least `a` coordinates, satisfies
`|L| · (a² − n·(k−1)) ≤ n²` (`n = |ι|`).

Proof: distinct degree-`<k` polynomials agree on `≤ k − 1` coordinates (`agreement_card_le`), so the
codewords pairwise agree on `≤ k − 1`; apply the (self-contained, axiom-clean) Johnson second-moment
bound with `b = k − 1`. -/
theorem reedSolomon_johnson_list_bound (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w) :
    (L.card : ℝ) * ((a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ))
      ≤ (Fintype.card ι : ℝ) ^ 2 := by
  refine johnson_simplex_bound L w (a : ℝ) ((k - 1 : ℕ) : ℝ) (by positivity) (by positivity)
    (fun c hc => by exact_mod_cast hclose c hc) ?_
  intro c hc c' hc' hne
  obtain ⟨p, hp, rfl⟩ := hpoly c hc
  obtain ⟨q, hq, rfl⟩ := hpoly c' hc'
  have hpq : p ≠ q := fun h => hne (by rw [h])
  have e : agree (fun i => p.eval (D i)) (fun i => q.eval (D i)) ≤ k - 1 :=
    agreement_card_le hp hq hpq
  exact_mod_cast e

/-- **Natural-number form of the Reed–Solomon Johnson list bound.**  Under the RS Johnson gap
`n·(k−1) < a²` (`n = |ι|`), a list `L` of degree-`<k` evaluation codewords each agreeing with `w`
on at least `a` coordinates has `|L| ≤ ⌊n² / (a² − n·(k−1))⌋`.  This is the single shared
`ℝ → ℕ` conversion of `reedSolomon_johnson_list_bound`. -/
theorem reedSolomon_johnson_list_card_le_div (D : ι ↪ F) (k : ℕ) (w : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ agree c w)
    (hgap : Fintype.card ι * (k - 1) < a ^ 2) :
    L.card ≤ Fintype.card ι ^ 2 / (a ^ 2 - Fintype.card ι * (k - 1)) := by
  have hreal := reedSolomon_johnson_list_bound D k w L a hpoly hclose
  have hsub : ((a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ)) =
      ((a ^ 2 - Fintype.card ι * (k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hgap)]; push_cast; ring
  rw [hsub] at hreal
  have hnat : L.card * (a ^ 2 - Fintype.card ι * (k - 1)) ≤ Fintype.card ι ^ 2 := by
    exact_mod_cast hreal
  exact (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hgap)).2 hnat

end ArkLib.CodingTheory.ReedSolomonJohnson
