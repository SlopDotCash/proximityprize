/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettPolynomial
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Lovett's GM-MDS proof: induction engine (#389, layer 3)

The two engine pieces that drive Lovett's minimal-counterexample induction
(arXiv:1803.02523):

* `pFam_factor` — the family-level coordinate peeling
  `pFam v e = (x − aⱼ) · pFam (v − eⱼ) e` (from `pVanish_factor`); this realises the
  bijection `P(k,v) ↔ (x − aⱼ)·P(k−1, v−eⱼ)` used in Lemmas 2.2/2.4.
* `linearIndependent_mul_left` — multiplication by a nonzero element of a domain `K`-algebra
  preserves linear independence over `K`.  Composed with `pFam_factor`, this is exactly the
  step "minimality gives `P(k−1,V')` independent ⟹ `P(k,V)` independent": multiplying an
  independent family by `(x − aⱼ)` keeps it independent.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- **Family-level coordinate peeling.**  If `v(j) ≥ 1`, every shifted family element factors
out one `(x − aⱼ)`. -/
theorem pFam_factor {v : Fin n → ℕ} {j : Fin n} (hj : 1 ≤ v j) (e : ℕ) :
    pFam (F := F) v e = xSubA j * pFam (Function.update v j (v j - 1)) e := by
  rw [pFam, pVanish_factor hj, pFam, mul_assoc]

/-- **Multiplication preserves linear independence.**  In a domain `K`-algebra `A`, scaling a
linearly-independent family by a nonzero `c` keeps it linearly independent over `K`. -/
theorem linearIndependent_mul_left {K A ι : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] {f : ι → A} (hf : LinearIndependent K f) {c : A} (hc : c ≠ 0) :
    LinearIndependent K (fun i => c * f i) := by
  have hcomp : (fun i => c * f i) = (LinearMap.mulLeft K c) ∘ f := rfl
  rw [hcomp]
  exact hf.map' (LinearMap.mulLeft K c)
    (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hc))

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.pFam_factor
#print axioms ArkLib.GMMDS.linearIndependent_mul_left
