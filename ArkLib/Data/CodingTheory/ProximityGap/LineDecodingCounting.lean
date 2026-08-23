/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Card

/-!
# Refutation of the double-coverage counting reduction (GG25 / ABF26 Thm 4.21 wall)

`ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean` documents that the target proposition
`lineDecodable_imp_epsMCA_le_target` would need a **pure-`Nat` double-coverage count** in the
black-box route: an aligned-and-
`mcaEvent` index finset `H` with `|H| ≥ n+1`, a per-index witness set `S γ` each missing at
most `m := ⌊δ·n⌋` positions of a fixed target set `T := S_{γ₀}`, should force *every* position
of `T` to be covered by `≥ 2` indices of `H` (two distinct zeros of the affine
`g_i(γ) = (u₁-f₁) i + γ·(u₂-f₂) i` pin `u₁ i = f₁ i`, `u₂ i = f₂ i`, giving
`pairJointAgreesOn` on all of `T`).

`pairJointAgreesOn` is **antitone** in its set argument, so the contradiction genuinely needs
double coverage of the *full* `T`, not merely most of it.

This file proves that reduction target is **false** for every `m ≥ 1` (equivalently `δ ≥ 1/n`,
the only non-degenerate proximity regime): a single shared missed position defeats it for an
arbitrarily large `H`. Hence the black-box target is blocked by a precisely-characterized wall,
not a missing leaf proof; the faithful route requires exposing the Guruswami–Sudan
interpolation degree in the statement of `LineDecodable` (a documented statement repair), per
the in-file analysis in `LineDecoding.lean`.

This is a refutation artifact, not a closure of the target theorem.
-/

namespace CodingTheory.ProximityGap.LineDecodingCounting

open Finset

/-- **The double-coverage counting reduction of GG25 / ABF26 Thm 4.21 is false for `m ≥ 1`.**

There exist a finite index type `Φ` (the field-element / `γ` index), a finite domain `ι`, an
index finset `H ⊆ Φ`, per-index witness sets `S : Φ → Finset ι`, a target set `T ⊆ ι`, a
position `i₀ ∈ T`, and a miss budget `m ≥ 1`, such that:

* every `γ ∈ H` misses at most `m` positions of `T` (`((univ \ S γ) ∩ T).card ≤ m`);
* the index budget is met, `n + 1 ≤ |H|` (here even with room to spare, `|H| = 5 ≥ 3`);
* `i₀ ∈ T`;

yet `i₀` is **not** double-covered: `|{γ ∈ H : i₀ ∈ S γ}| < 2`.

Witnesses: `Φ = Fin 5`, `ι = Fin 3` (so `n = 3` here — the bound `n+1 ≤ |H|` is `4 ≤ 5`),
`T = {0,1,2} = univ`, `m = 1`, and `S γ = {1,2}` for every `γ` — every index misses exactly the
single position `0 = i₀`. The shared miss makes `i₀` covered `0 < 2` times while `|H|` is free.
The affine `g_{i₀}` then receives only one linear equation, so `(u₁,u₂)` is unpinned at `i₀`
and `pairJointAgreesOn` on the full `T` cannot be derived. -/
theorem double_coverage_counterexample :
    ∃ (Φ : Type) (_ : Fintype Φ) (_ : DecidableEq Φ)
      (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (H : Finset Φ) (S : Φ → Finset ι) (T : Finset ι) (i₀ : ι) (n m : ℕ),
        1 ≤ m ∧
        n + 1 ≤ H.card ∧
        i₀ ∈ T ∧
        (∀ γ ∈ H, ((Finset.univ \ S γ) ∩ T).card ≤ m) ∧
        (H.filter (fun γ => i₀ ∈ S γ)).card < 2 := by
  refine ⟨Fin 5, inferInstance, inferInstance, Fin 3, inferInstance, inferInstance,
    Finset.univ, fun _ => ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3)),
    (0 : Fin 3), 3, 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_refl 1
  · decide
  · decide
  · intro γ _
    -- `S γ = {1,2}` is constant in `γ`; beta-reduce before `decide` (no free `γ` remains).
    simp only
    decide
  · decide

/-- The same obstruction persists with an arbitrarily large aligned index set.

For every requested size `q ≥ 4`, take `Φ = Fin q`, `H = univ`, and keep the same
three-position target with a single shared missed position.  Thus increasing the
number of aligned `γ`'s alone cannot repair the failed double-coverage reduction:
the bad position can remain uncovered by every aligned index. -/
theorem double_coverage_counterexample_arbitrarily_large (q : ℕ) (hq : 4 ≤ q) :
    ∃ (Φ : Type) (_ : Fintype Φ) (_ : DecidableEq Φ)
      (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (H : Finset Φ) (S : Φ → Finset ι) (T : Finset ι) (i₀ : ι) (n m : ℕ),
        1 ≤ m ∧
        n + 1 ≤ H.card ∧
        q ≤ H.card ∧
        i₀ ∈ T ∧
        (∀ γ ∈ H, ((Finset.univ \ S γ) ∩ T).card ≤ m) ∧
        (H.filter (fun γ => i₀ ∈ S γ)).card < 2 := by
  refine ⟨Fin q, inferInstance, inferInstance, Fin 3, inferInstance, inferInstance,
    Finset.univ, fun _ => ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3)),
    (0 : Fin 3), 3, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_refl 1
  · simpa using hq
  · simp
  · decide
  · intro γ _
    simp only
    decide
  · simp

end CodingTheory.ProximityGap.LineDecodingCounting
