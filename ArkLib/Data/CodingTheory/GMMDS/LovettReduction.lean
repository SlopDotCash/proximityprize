/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettBaseCase
import ArkLib.Data.CodingTheory.GMMDS.LovettInduction

/-!
# Lovett's GM-MDS proof: the coordinate-reduction step (#389, layer 5)

The inductive-step engine of Lovett (arXiv:1803.02523, Lemma 2.2 / the `P(k,V) =
(x − aⱼ)·P(k−1,V')` reduction).  If a *whole* indexed family of shifted polynomials has a
coordinate `j` with `vᵢ(j) ≥ 1` everywhere, then each element factors out `(x − aⱼ)`, so
the family equals `(x − aⱼ)·`(the reduced family).  Multiplication by the nonzero
`(x − aⱼ)` preserves independence; hence:

> **`pFam_family_indep_of_reduced`** — if the reduced family `{ pFam (vᵢ − eⱼ) eᵢ }` is
> linearly independent over `F[a]`, so is the original `{ pFam vᵢ eᵢ }`.

This is exactly the step "minimality gives `P(k−1,V')` independent ⟹ `P(k,V)` independent"
that drives the minimal-counterexample induction (Lemmas 2.2, 2.4).

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- **The coordinate-reduction step.**  If every member of an indexed shifted-polynomial
family has `vᵢ(j) ≥ 1`, then independence of the reduced family (coordinate `j` lowered by
one) implies independence of the original family — because the original is `(x − aⱼ)` times
the reduced, and multiplication by the nonzero `(x − aⱼ)` preserves independence. -/
theorem pFam_family_indep_of_reduced {ι : Type*} {vi : ι → (Fin n → ℕ)} {ei : ι → ℕ}
    {j : Fin n} (hj : ∀ p, 1 ≤ vi p j)
    (hred : LinearIndependent (MvPolynomial (Fin n) F)
      (fun p => pFam (F := F) (Function.update (vi p) j (vi p j - 1)) (ei p))) :
    LinearIndependent (MvPolynomial (Fin n) F) (fun p => pFam (F := F) (vi p) (ei p)) := by
  have heq : (fun p => pFam (F := F) (vi p) (ei p))
      = (LinearMap.mulLeft (MvPolynomial (Fin n) F) (xSubA j))
        ∘ (fun p => pFam (F := F) (Function.update (vi p) j (vi p j - 1)) (ei p)) := by
    funext p
    rw [Function.comp_apply, LinearMap.mulLeft_apply, ← pFam_factor (hj p)]
  rw [heq]
  refine hred.map' _ (LinearMap.ker_eq_bot.mpr (fun x y h => ?_))
  simp only [LinearMap.mulLeft_apply] at h
  exact mul_left_cancel₀ (xSubA_monic (F := F) j).ne_zero h

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.pFam_family_indep_of_reduced
