/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettBaseCase
import ArkLib.Data.CodingTheory.GMMDS.LovettReduction
import Mathlib.Data.Fintype.Sigma

/-!
# Lovett's GM-MDS proof: the union family `P(k,V)` (#389, layer 6)

The full object of Lovett's Theorem 1.7 (arXiv:1803.02523): `P(k,V) = ⋃ᵢ P(k,vᵢ)`, the
multiset (here, `Sigma`-indexed family) of all shifted polynomials `pFam vᵢ e`,
`e < k − |vᵢ|`.  Theorem 1.7 asserts its linear independence over `F[a]` under `V*(k)`.

* `pFamUnion` — the `Σ`-indexed family.
* `card_pFamUnion_index` — `|P(k,V)| = Σᵢ (k − |vᵢ|)`, the induction measure `d`.
* `LovettThm17` — the target statement (a `Prop` to be discharged by the
  minimal-counterexample induction over `(n,k,m,d)`).

All engine pieces (Lemma 2.1, `pVanish_factor`, base case `m=1`, the coordinate-reduction
step) are proven in layers 1–5; the remaining content is the induction assembly.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-- The union family `P(k,V) = ⋃ᵢ P(k,vᵢ)`, `Σ`-indexed by `(i, e)` with `e < k − |vᵢ|`. -/
noncomputable def pFamUnion (V : Fin m → (Fin n → ℕ)) (k : ℕ) :
    (Σ i : Fin m, Fin (k - vAbs (V i))) → (MvPolynomial (Fin n) F)[X] :=
  fun p => pFam (F := F) (V p.1) (p.2 : ℕ)

/-- The size of `P(k,V)` is `Σᵢ (k − |vᵢ|)` — the induction measure `d`. -/
theorem card_pFamUnion_index (V : Fin m → (Fin n → ℕ)) (k : ℕ) :
    Fintype.card (Σ i : Fin m, Fin (k - vAbs (V i))) = ∑ i, (k - vAbs (V i)) := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => Fintype.card_fin _)

/-- **Lovett's Theorem 1.7** (target): under `V*(k)`, the family `P(k,V)` is linearly
independent over `F[a]`.  Discharged by minimal-counterexample induction on `(n,k,m,d)`;
the engine (Lemmas 2.1/2.2, base case, coordinate reduction) is proven in layers 1–5. -/
def LovettThm17 (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∀ {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
    LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k)

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.card_pFamUnion_index
