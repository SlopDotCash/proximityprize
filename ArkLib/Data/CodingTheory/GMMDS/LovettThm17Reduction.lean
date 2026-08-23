/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettUnion
import ArkLib.Data.CodingTheory.GMMDS.LovettReduction
import ArkLib.Data.CodingTheory.GMMDS.LovettVStarReduce

/-!
# Lovett's GM-MDS proof: reducing Theorem 1.7 to the primitive case (#389)

The minimal-counterexample induction of Lovett (arXiv:1803.02523) splits on whether the
system has a *globally peelable* coordinate.  This file performs that split, isolating the
entire remaining content of Theorem 1.7 to **one** named open `Prop` — the primitive case —
exactly the project's modularity convention.

* **reducible** (`∃ j, ∀ i, Vᵢ(j) ≥ 1`): the whole union family `P(k,V)` peels `(x − aⱼ)`,
  so independence of `P(k−1, vReduce V j)` (the induction hypothesis, via the now-`V*(k−1)`
  reduced system — `isVStar_reduce`) transfers up by `pFam_family_indep_of_reduced`.  This
  step needs a `Σ`-`Fin` index transport (the reduced family is indexed by
  `Σ i, Fin ((k−1) − |vReduce Vᵢ|)`, equal cardinality-wise to `Σ i, Fin (k − |Vᵢ|)` but not
  definitionally).  It is captured as the named **`LovettReducibleStep`** — a purely
  *Lean-technical* residual (provable by the explicit reindexing `Equiv`; not a mathematical
  gap), held separate because the dependent-cast transport hits an elaboration wall.
* **primitive** (`∀ j, ∃ i, Vᵢ(j) = 0`): no global peel; this is Lovett's polynomial-method
  core (the matrix of leading coefficients is nonsingular by the `V*(k)` structure), named
  **`LovettPrimitiveCase`** — the genuine open *mathematical* obligation.

`lovettThm17_of_steps` then closes Theorem 1.7 by strong induction on `k`, modulo those two
named pieces.  The induction skeleton itself (the well-founded recursion, the reducible /
primitive dichotomy, the `V*(k−1)` preservation via `isVStar_reduce`, the empty-family base)
is fully proven here.

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- **The reducible step** (Lean-technical residual; provable by index reindexing).  If a
coordinate `j` is `≥ 1` in every vector (the whole family peels `(x − aⱼ)`) and the reduced
union family `P(k−1, vReduce V j)` is independent, then so is `P(k, V)`.  Mathematically
immediate from `pFam_family_indep_of_reduced` after the `Σ`-`Fin` index transport
(`k − |Vᵢ| = (k−1) − |vReduce Vᵢ|`); named separately only because that dependent-cast
transport hits a `whnf` elaboration wall. -/
def LovettReducibleStep (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∀ {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ) (j : Fin n), 1 ≤ k → IsVStar V k →
    (∀ i, 1 ≤ V i j) →
    LinearIndependent (MvPolynomial (Fin n) F)
      (pFamUnion (F := F) (fun i => Function.update (V i) j (V i j - 1)) (k - 1)) →
    LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k)

/-- **The primitive case of Lovett's Theorem 1.7** (the open *mathematical* obligation): when
no coordinate is globally peelable (`∀ j, ∃ i, Vᵢ(j) = 0`), the union family `P(k,V)` is
independent.  This is Lovett's polynomial-method core (nonsingularity of the
leading-coefficient matrix from the `V*(k)` structure), left as a named `Prop`. -/
def LovettPrimitiveCase (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∀ {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
    (∀ j : Fin n, ∃ i, V i j = 0) →
    LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k)

/-- **Theorem 1.7 modulo the reducible step and the primitive case.**  The
minimal-counterexample induction: strong induction on `k`, splitting reducible (peel, via
`LovettReducibleStep` and the `V*(k−1)` preservation `isVStar_reduce`) vs primitive (via
`LovettPrimitiveCase`).  The induction skeleton — well-founded recursion, the dichotomy, the
`V*(k)`→`V*(k−1)` step, the empty-family base — is fully proven; discharging the two named
pieces closes the algebraic GM-MDS conjecture (Theorem 1.7), and with it the in-tree floor
`AGL24.GMMDSDualZeroPatternTheorem`. -/
theorem lovettThm17_of_steps (hstep : LovettReducibleStep F n)
    (hprim : LovettPrimitiveCase F n) : LovettThm17 F n := by
  intro m V k
  induction k using Nat.strong_induction_on generalizing V with
  | _ k IH =>
    intro hk hV
    by_cases hred : ∃ j : Fin n, ∀ i, 1 ≤ V i j
    · obtain ⟨j, hjj⟩ := hred
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- empty family is trivially independent
        subst hm0
        haveI : IsEmpty (Σ i : Fin 0, Fin (k - vAbs (V i))) := by
          constructor; rintro ⟨i, _⟩; exact i.elim0
        exact linearIndependent_empty_type
      · -- reducible: peel and use the induction hypothesis at k-1
        have i₀ : Fin m := ⟨0, hmpos⟩
        have hk2 : 2 ≤ k := by
          have hwi := hV.weight_le i₀
          have hji := hjj i₀
          have hjle : V i₀ j ≤ vAbs (V i₀) :=
            Finset.single_le_sum (f := V i₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          omega
        have hV' : IsVStar (fun i => Function.update (V i) j (V i j - 1)) (k - 1) :=
          isVStar_reduce hk hV hjj
        have hIH : LinearIndependent (MvPolynomial (Fin n) F)
            (pFamUnion (F := F) (fun i => Function.update (V i) j (V i j - 1)) (k - 1)) :=
          IH (k - 1) (by omega) (fun i => Function.update (V i) j (V i j - 1)) (by omega) hV'
        exact hstep V k j hk hV hjj hIH
    · -- primitive: no globally peelable coordinate
      push_neg at hred
      refine hprim V k hk hV (fun j => ?_)
      obtain ⟨i, hi⟩ := hred j
      exact ⟨i, by omega⟩

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.lovettThm17_of_steps
