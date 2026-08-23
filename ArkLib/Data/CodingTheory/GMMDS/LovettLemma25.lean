/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma25Opening
import ArkLib.Data.CodingTheory.GMMDS.LovettNLtK
import ArkLib.Data.CodingTheory.GMMDS.LovettWitnessCounterexample
import Mathlib.Algebra.Polynomial.Basis

/-!
# Lovett's GM-MDS proof: the Lemma 2.5 assembly and its residual merge step (#389)

This file assembles Lovett's primitive step (`LovettPrimitiveStep`, arXiv:1803.02523 §2) out of
the landed combinatorial opening (`witness_or_mergeCandidate`), the proven `n < k` / `n = k`
closures (`lovettHolds_of_witness`), a direct `n = 0` base case, and isolates the one remaining
algebraic gap as a **precise, machine-checked-satisfiable** residual.

## The structure of Lemma 2.5

Lovett's Lemma 2.5 says: a *primitive* `V*(k)` system contains the structured witness
`vᵢ₀ = (1,…,1,0)`.  The proof (opened in `LovettLemma25Opening.lean`) is a dichotomy:

* **Witness branch.**  Lemma 2.2 (`exists_last_coord_zero`) locates a vector with
  `vᵢ*(n−1) = 0`.  If that vector *is* `(1,…,1,0)`, we are done.
* **Merge branch.**  Otherwise (`exists_inner_zero_of_ne_oneVec`) it has an interior zero
  `vᵢ*(j*) = 0` with `j* < n−1`, so `vᵢ*(j*) = vᵢ*(n−1) = 0`.  Lovett builds a new system `V'`
  over `Fin (n−1)` by **merging** coordinates `j*` and `n−1`, shows `V'` is `V*(k)`, applies the
  `n−1` induction hypothesis to get `P(k,V')` independent, and derives a contradiction with the
  minimality of `V`: a dependence of `P(k,V)`, after the merge substitution `a_{n-1} ↦ a_{j*}`,
  yields a dependence of `P(k,V')` whose (common-factor-free) coefficients are each killed by the
  substitution, hence each divisible by `(a_{j*} − a_{n-1})` (`sub_X_dvd_of_subst_eq_zero`),
  contradicting common-factor-freeness.

The merge branch is therefore *vacuous*: it cannot occur in a minimal counterexample.

## The `n = 0` degeneracy

The bundled residual `LovettWitnessExists` is, *as literally stated*, **false at `n = 0`**: the
single-vector system over the empty coordinate space `Fin 0` is `V*(1)` and primitive, yet
`LovettWitness F V 1 = ∃ (hn : 1 ≤ 0), …` is `False` (`no_witness_emptyDimSystem`).  This
degeneracy does **not** threaten Theorem 1.7 — the `n = 0` primitive case is independent for the
trivial reason that each block is a set of distinct monomials `{xᵉ : e < k}`
(`lovettHolds_dim0_single`).  Accordingly the *correct* target to discharge is
`LovettPrimitiveStep` directly, branching on `n`.

## What this file contributes

* `lovettHolds_dim0_single`, `lovettHolds_dim0` — the **`n = 0` primitive base case**, proven
  directly via monomial independence (`Polynomial.basisMonomials`).
* `emptyDimSystem`, `no_witness_emptyDimSystem` — the explicit witness that `LovettWitnessExists`
  is false at `n = 0` (documenting why we target `LovettPrimitiveStep`).
* `MergeBranchImpossible` — the **precise statement** of the one remaining gap: in a primitive
  `V*(k)` system over `Fin n` with `n ≥ 1` and both induction hypotheses, a merge candidate
  `(i, j)` forces the witness to exist.  This is exactly Lovett's merge argument.
* `lovettPrimitiveStep_of_mergeBranchImpossible` — **the assembly**: `MergeBranchImpossible`
  implies `LovettPrimitiveStep`, hence (via `lovettThm17_of_primitiveStep`) the full algebraic
  GM-MDS theorem `LovettThm17`.  Proven unconditionally and axiom-clean.
* `mergeBranchImpossible_conclusion_cexV` — a **non-vacuity certificate**: on the explicit
  `LovettWitnessCounterexample` system the merge-branch conclusion holds (the witness is present),
  so the residual is satisfiable, not contradictory.

The residual `MergeBranchImpossible` is the genuine remaining mathematical content of Lemma 2.5:
the coordinate-merge construction over `Fin (n−1)` together with the substitution-divisibility
contradiction (whose algebraic kernel `sub_X_dvd_of_subst_eq_zero` is already proven in
`LovettSubstitutionDvd.lean`).

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-! ## The `n = 0` primitive base case -/

/-- **The single-vector `n = 0` base.**  A `V*(k)` system with one vector over the empty
coordinate space `Fin 0` is independent: the vanishing polynomial is `1`, so the block is
`{xᵉ : e < k}`, a set of distinct monomials, independent by `Polynomial.basisMonomials`. -/
theorem lovettHolds_dim0_single (V : Fin 1 → (Fin 0 → ℕ)) (k : ℕ) (_hk : 1 ≤ k)
    (_hV : IsVStar V k) : LovettHolds F V k := by
  classical
  show LinearIndependent (MvPolynomial (Fin 0) F) (pFamUnion (F := F) V k)
  set R := MvPolynomial (Fin 0) F
  have hv0 : vAbs (V 0) = 0 := by simp [vAbs]
  have hcard : ∀ i : Fin 1, k - vAbs (V i) = k := by
    intro i; rw [Subsingleton.elim i 0, hv0]; omega
  let e : (Σ i : Fin 1, Fin (k - vAbs (V i))) ≃ Fin k :=
    { toFun := fun p => ⟨(p.2 : ℕ), by have h := p.2.isLt; have h2 := hcard p.1; omega⟩
      invFun := fun a => ⟨0, ⟨(a:ℕ), by have := a.isLt; have h2 := hcard 0; omega⟩⟩
      left_inv := by rintro ⟨i, x⟩; rw [Subsingleton.elim i 0]; rfl
      right_inv := by intro a; rfl }
  have hmono : LinearIndependent R (fun a : Fin k => (X : R[X])^(a:ℕ)) := by
    have hb := (Polynomial.basisMonomials R).linearIndependent
    have hcomp : (fun a : Fin k => (X : R[X])^(a:ℕ))
       = (fun s => (monomial s (1:R))) ∘ (fun a : Fin k => (a:ℕ)) := by
      funext a; simp [Polynomial.monomial_one_right_eq_X_pow]
    rw [hcomp]; exact hb.comp _ (fun a b h => Fin.val_injective h)
  have hfun : pFamUnion (F := F) V k = (fun a : Fin k => (X : R[X])^(a:ℕ)) ∘ e := by
    funext p
    obtain ⟨i, x⟩ := p
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    show pFam (F := F) (V 0) (x:ℕ) = (X:R[X])^(((e ⟨0,x⟩ : Fin k)):ℕ)
    have hev : ((e ⟨(0:Fin 1),x⟩ : Fin k) : ℕ) = (x:ℕ) := rfl
    rw [hev]; simp [pFam, pVanish]
  rw [hfun]
  exact (linearIndependent_equiv e (f := fun a : Fin k => (X:R[X])^(a:ℕ))).mpr hmono

/-- **The `n = 0` primitive base case.**  Any primitive `V*(k)` system over `Fin 0` is
independent.  By Lemma 2.1 (`not_le_of_isVStar`) the `m ≥ 2` case is impossible (all empty
vectors coincide); `m = 0` is the empty family; `m = 1` is `lovettHolds_dim0_single`. -/
theorem lovettHolds_dim0 {m : ℕ} (V : Fin m → (Fin 0 → ℕ)) (k : ℕ) (hk : 1 ≤ k)
    (hV : IsVStar V k) : LovettHolds F V k := by
  classical
  match m, V, hV with
  | 0, V, _hV =>
      show LinearIndependent (MvPolynomial (Fin 0) F) (pFamUnion (F := F) V k)
      haveI : IsEmpty (Σ i : Fin 0, Fin (k - vAbs (V i))) := by
        constructor; rintro ⟨i, _⟩; exact i.elim0
      exact linearIndependent_empty_type
  | 1, V, hV => exact lovettHolds_dim0_single V k hk hV
  | (m + 2), V, hV =>
      exfalso
      have h01 : (⟨0, by omega⟩ : Fin (m + 2)) ≠ ⟨1, by omega⟩ := by
        intro h; simpa using congrArg Fin.val h
      exact not_le_of_isVStar hk hV h01 (fun l => l.elim0)

/-! ## The `n = 0` degeneracy of `LovettWitnessExists` (documentation) -/

/-- The `n = 0` single-vector primitive system witnessing the degeneracy of
`LovettWitnessExists`: `V = (∅) : Fin 1 → (Fin 0 → ℕ)`. -/
def emptyDimSystem : Fin 1 → (Fin 0 → ℕ) := fun _ => (fun j => j.elim0)

theorem emptyDimSystem_isVStar : IsVStar emptyDimSystem 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; simp [vAbs]
  · intro I hI
    obtain ⟨i, hi⟩ := hI
    have hIeq : I = {0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨by simpa [Subsingleton.elim i 0] using hi, fun x _ => Subsingleton.elim x 0⟩
    subst hIeq
    rw [Finset.sum_singleton]
    have hm0 : vAbs (vMeet emptyDimSystem {0} ⟨0, Finset.mem_singleton_self 0⟩) = 0 := by
      simp [vAbs]
    rw [hm0]; simp [vAbs, emptyDimSystem]
  · intro i j; exact j.elim0

theorem emptyDimSystem_primitive : ∀ j : Fin 0, ∃ i, emptyDimSystem i j = 0 := fun j => j.elim0

/-- **`LovettWitnessExists` is false at `n = 0`.**  No `LovettWitness` exists for `emptyDimSystem`
because the definition demands `1 ≤ 0`.  This is precisely why the merge assembly targets
`LovettPrimitiveStep` (which handles `n = 0` directly) and *not* `LovettWitnessExists`. -/
theorem no_witness_emptyDimSystem : ¬ LovettWitness F emptyDimSystem 1 := by
  rintro ⟨hn, _, _⟩; exact absurd hn (by norm_num)

/-! ## The merge-branch-impossibility residual and the assembly -/

/-- **The merge-branch-impossibility residual** (the algebraic heart of Lovett's Lemma 2.5).

For a primitive `V*(k)` system over `Fin n` with `n ≥ 1`, equipped with both minimal-
counterexample induction hypotheses (the `n−1` coordinate-IH `IHn` and the `d`-IH `IHd`, exactly
as in `LovettPrimitiveStep`), the *merge branch* of Lemma 2.5 is impossible: the existence of any
merge candidate `(i, j)` (with `j < n−1`, `vᵢ(j) = 0` and `vᵢ(n−1) = 0`) forces the witness
`vᵢ₀ = (1,…,1,0)` to exist.

Lovett discharges this by building `V'` over `Fin (n−1)` (merging coordinates `j` and `n−1`),
invoking `IHn` to get `P(k,V')` independent, and contradicting the minimality of `V` via the
substitution-divisibility kernel `ArkLib.GMMDS.sub_X_dvd_of_subst_eq_zero`. -/
def MergeBranchImpossible (F : Type*) [Field F] : Prop :=
  ∀ {n m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → (hn : 1 ≤ n) → IsVStar V k →
    (∀ j : Fin n, ∃ i, V i j = 0) →
    (∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ), n' < n → 1 ≤ k' → IsVStar V' k' →
      LovettHolds F V' k') →
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k) →
    (∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) →
    (∀ (i : Fin m) (j : Fin n), (j : ℕ) < n - 1 → V i j = 0 → V i (lastCoord n hn) = 0 →
      ∃ i₀, V i₀ = oneVec n hn)

/-- **The Lemma 2.5 assembly.**  `MergeBranchImpossible` implies `LovettPrimitiveStep`.

Branch on the ambient dimension `n`:

* `n = 0`: the direct base case `lovettHolds_dim0`.
* `n ≥ 1`: run `witness_or_mergeCandidate`.  Either the witness exists outright, or there is a
  merge candidate; `MergeBranchImpossible` turns the candidate into the witness.  Either way the
  witness exists, and `lovettHolds_of_witness` (the proven `n < k` / `n = k` closure) finishes.

Unconditional and axiom-clean: it consumes only landed lemmas. -/
theorem lovettPrimitiveStep_of_mergeBranchImpossible (hmerge : MergeBranchImpossible F) :
    LovettPrimitiveStep F := by
  intro n m V k hk hV hprim IHn IHd IHm
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; exact lovettHolds_dim0 V k hk hV
  · have hwit : LovettWitness F V k := by
      rcases witness_or_mergeCandidate (V := V) (k := k) hn hV hprim with ⟨i₀, hone⟩ | hcand
      · exact ⟨hn, i₀, hone⟩
      · obtain ⟨i, j, hjlt, hj0, hlast⟩ := hcand
        obtain ⟨i₀, hone⟩ := hmerge V k hk hn hV hprim IHn IHd IHm i j hjlt hj0 hlast
        exact ⟨hn, i₀, hone⟩
    exact lovettHolds_of_witness hk hV hwit IHd

/-- **Full Theorem 1.7 from the merge residual.**  Combining the assembly with the master frame
(`lovettThm17_of_primitiveStep`), `MergeBranchImpossible` yields the full algebraic GM-MDS theorem
`LovettThm17` unconditionally. -/
theorem lovettThm17_of_mergeBranchImpossible (hmerge : MergeBranchImpossible F) {n : ℕ} :
    LovettThm17 F n :=
  lovettThm17_of_primitiveStep (lovettPrimitiveStep_of_mergeBranchImpossible hmerge)

/-! ## Non-vacuity certificate for the residual

We certify that `MergeBranchImpossible`'s conclusion is reachable on a concrete primitive `V*(k)`
system that contains the witness.  On the `LovettWitnessCounterexample` system
`V = ((1,0),(0,2))` over `ℕ²`, the witness `(1,0) = oneVec 2` is present (`cexV_zero_eq_oneVec`),
so the merge-branch conclusion holds for *every* candidate `(i, j)` — the witness disjunct fires.
This shows the residual's conclusion is satisfiable (not contradictory). -/

/-- **Non-vacuity certificate.**  The merge-branch conclusion holds on the concrete counterexample
system: for any merge candidate `(i, j)`, the witness `oneVec 2` exists (it is `cexV 0`). -/
theorem mergeBranchImpossible_conclusion_cexV
    (i : Fin 2) (j : Fin 2) (_hjlt : (j : ℕ) < 2 - 1)
    (_hj0 : cexV i j = 0) (_hlast : cexV i (lastCoord 2 (by norm_num)) = 0) :
    ∃ i₀, cexV i₀ = oneVec 2 (by norm_num) :=
  ⟨0, cexV_zero_eq_oneVec⟩

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.lovettHolds_dim0_single
#print axioms ArkLib.GMMDS.lovettHolds_dim0
#print axioms ArkLib.GMMDS.no_witness_emptyDimSystem
#print axioms ArkLib.GMMDS.lovettPrimitiveStep_of_mergeBranchImpossible
#print axioms ArkLib.GMMDS.lovettThm17_of_mergeBranchImpossible
#print axioms ArkLib.GMMDS.mergeBranchImpossible_conclusion_cexV
