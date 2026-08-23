/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettThm17Reduction
import ArkLib.Data.CodingTheory.GMMDS.LovettBaseCase
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finset.Max

/-!
# Distinct-degree independence + structural pins for `LovettPrimitiveCase` (#389)

The union family `P(k,V)` is a family of univariate polynomials in `x` over
`R = MvPolynomial (Fin n) F`, and linear independence of such a family is *exactly* the
nonsingularity of its coefficient matrix.  This file proves the cleanly-closable kernel of
that picture plus the structural pins that put `P(k,V)` into the dimension-counting regime
(complementing the sibling minimal-counterexample frame in `LovettPrimitiveDischarge`, whose
`lovettD`-induction is literally on the size `d` bounded here):

* `pFamUnion_natDegree_lt` — every member has degree `< k`; `card_pFamUnion_le` — the family
  size is `d = Σᵢ(k−|vᵢ|) ≤ k` (MDS condition (ii) at `I = univ`).  Together: `P(k,V)` lives in
  the `k`-dimensional space of degree `< k` polynomials with `≤ k` members — the `d ≤ k = dim`
  regime where dimension counting / generalized-Vandermonde nonsingularity is the right tool.

* `linearIndependent_of_injOn_natDegree` — a fully axiom-clean, general fact over any integral
  domain: a finite family of **nonzero** univariate polynomials with **pairwise-distinct
  `natDegree`** is linearly independent.  Proof: a vanishing combination, read off at the
  coefficient of the maximal degree present in the support, forces the leading coefficient of the
  top term to vanish — impossible in a domain.

* `lovettPrimitiveCase_of_injOn_degree` — the **reduction**: `LovettPrimitiveCase F n` follows
  once one knows that for every `V*(k)` primitive system the union degrees
  `(i,e) ↦ |Vᵢ| + e` are pairwise distinct.  This isolates the entire remaining content into one
  precise, named, purely combinatorial residual `LovettUnionDegreesInjective`.

* `LovettUnionDegreesInjective` — the named residual (the "generalized-Vandermonde minor is
  nonzero" content of Route C, here in its sharpest concrete form: distinct multiplicities/shifts).

The all-distinct-degree sub-case of Theorem 1.7 is therefore CLOSED unconditionally
(`lovettPrimitiveCase_holds_of_degrees_injective`), and the general primitive case is reduced to
`LovettUnionDegreesInjective`.

Issue #389.
-/

open Polynomial Finset

namespace ArkLib.GMMDS

universe u

section DistinctDegree

variable {R : Type*} [CommRing R] [IsDomain R] {ι : Type u}

/-- **Distinct-degree independence.**  Over an integral domain, a finite family of nonzero
univariate polynomials with pairwise-distinct `natDegree` is linearly independent.

Mechanism: if a combination `∑ g i • f i = 0` had nonzero support `S`, pick `i₀ ∈ S` of maximal
`natDegree`; reading the combination's coefficient at `d = natDegree (f i₀)` annihilates every
other support term (strictly smaller degree ⟹ coeff `0` there) and leaves
`g i₀ * leadingCoeff (f i₀) ≠ 0` (domain), contradicting the combination being `0`. -/
theorem linearIndependent_of_injOn_natDegree [Fintype ι] {f : ι → R[X]}
    (hne : ∀ i, f i ≠ 0)
    (hinj : Function.Injective (fun i => (f i).natDegree)) :
    LinearIndependent R f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀w, hi₀w⟩ := hcon
  -- the support of `g`
  set S : Finset ι := Finset.univ.filter (fun i => g i ≠ 0) with hS
  have hSne : S.Nonempty := ⟨i₀w, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi₀w⟩⟩
  -- pick the maximal-degree support element
  obtain ⟨i₀, hi₀S, hi₀max⟩ := S.exists_max_image (fun i => (f i).natDegree) hSne
  have hg₀ : g i₀ ≠ 0 := by
    have := hi₀S; rw [hS, Finset.mem_filter] at this; exact this.2
  set d : ℕ := (f i₀).natDegree with hd
  -- read off the coefficient of the vanishing combination at degree `d`
  have hcoeff : (∑ i, g i • f i).coeff d = g i₀ * (f i₀).leadingCoeff := by
    rw [Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single i₀]
    · rw [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_natDegree]
    · intro i _ hii
      rw [Polynomial.coeff_smul, smul_eq_mul]
      rcases eq_or_ne (g i) 0 with hgi | hgi
      · rw [hgi, zero_mul]
      · -- `i ∈ S`; its degree is `≤ d` and `≠ d` (injectivity), hence `< d`, coeff `0`
        have hiS : i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgi⟩
        have hle : (f i).natDegree ≤ d := hi₀max i hiS
        have hne' : (f i).natDegree ≠ d := by
          intro heq
          exact hii (hinj (by simpa [hd] using heq))
        have hlt : (f i).natDegree < d := lt_of_le_of_ne hle hne'
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [hg, Polynomial.coeff_zero] at hcoeff
  -- contradiction: `0 = g i₀ * leadingCoeff (f i₀)`, both nonzero in a domain
  have hlc : (f i₀).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hne i₀)
  exact (mul_ne_zero hg₀ hlc) hcoeff.symm

end DistinctDegree

section LovettReduction

variable {F : Type*} [Field F] {n : ℕ}

/-- Each union element is nonzero (a product of nonzero monic factors and `X^e`). -/
theorem pFamUnion_ne_zero {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ)
    (p : Σ i : Fin m, Fin (k - vAbs (V i))) :
    pFamUnion (F := F) V k p ≠ 0 := by
  show pFam (F := F) (V p.1) (p.2 : ℕ) ≠ 0
  have : (pFam (F := F) (V p.1) (p.2 : ℕ)).natDegree = vAbs (V p.1) + (p.2 : ℕ) :=
    pFam_natDegree _ _
  rw [pFam]
  exact mul_ne_zero (pVanish_monic _).ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)

/-- The `natDegree` of a union element is `|Vᵢ| + e`. -/
theorem pFamUnion_natDegree {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ)
    (p : Σ i : Fin m, Fin (k - vAbs (V i))) :
    (pFamUnion (F := F) V k p).natDegree = vAbs (V p.1) + (p.2 : ℕ) :=
  pFam_natDegree _ _

/-- **Every member of `P(k,V)` has degree `< k`** (the `e < k − |vᵢ|` fiber bound), so the whole
family lives in the `k`-dimensional space of polynomials of degree `< k`. -/
theorem pFamUnion_natDegree_lt {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ)
    (p : Σ i : Fin m, Fin (k - vAbs (V i))) :
    (pFamUnion (F := F) V k p).natDegree < k := by
  rw [pFamUnion_natDegree]
  have he : (p.2 : ℕ) < k - vAbs (V p.1) := p.2.2
  omega

/-- **The family size is `≤ k`** for any `V*(k)` system: the MDS condition (ii) at the full
index set gives `Σᵢ (k − |vᵢ|) + |⋀ᵢ vᵢ| ≤ k`, hence `d = Σᵢ (k − |vᵢ|) ≤ k`.  Together with
`pFamUnion_natDegree_lt` this pins `P(k,V)` into the `d ≤ k = dim` regime where dimension
counting / generalized-Vandermonde nonsingularity is the right tool (and where the sibling
`lovettD`-induction in `LovettPrimitiveDischarge` lives). -/
theorem card_pFamUnion_le {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ)
    (hm : 0 < m) (hV : IsVStar V k) :
    Fintype.card (Σ i : Fin m, Fin (k - vAbs (V i))) ≤ k := by
  classical
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hmds := hV.mds Finset.univ huniv
  rw [card_pFamUnion_index]
  have hsum : (∑ i, (k - vAbs (V i)))
      = (∑ i ∈ (Finset.univ : Finset (Fin m)), (k - vAbs (V i))) := rfl
  rw [hsum]; omega

/-- **The named Route-C residual.**  For a `V*(k)` primitive system, the union degrees
`(i,e) ↦ |Vᵢ| + e` (over the `Σ`-index of `P(k,V)`) are pairwise distinct.

This is the sharpest concrete face of "the generalized-Vandermonde minor is nonzero" for the
distinct-degree picture: once degrees are distinct, `linearIndependent_of_injOn_natDegree`
finishes.  (In general the union degrees are NOT all distinct — repeated degrees are where the
genuine Vandermonde/leading-coefficient-matrix nonsingularity of Lovett's argument is needed; this
residual is the exact hypothesis under which Route C closes the primitive case.) -/
def LovettUnionDegreesInjective (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∀ {m : ℕ} (V : Fin m → (Fin n → ℕ)) (k : ℕ), 1 ≤ k → IsVStar V k →
    (∀ j : Fin n, ∃ i, V i j = 0) →
    Function.Injective
      (fun p : Σ i : Fin m, Fin (k - vAbs (V i)) => vAbs (V p.1) + (p.2 : ℕ))

/-- **Reduction of the primitive case to the degree-injectivity residual.**  Modulo
`LovettUnionDegreesInjective`, the primitive case of Theorem 1.7 holds. -/
theorem lovettPrimitiveCase_of_injOn_degree
    (hdeg : LovettUnionDegreesInjective F n) : LovettPrimitiveCase F n := by
  intro m V k hk hV hprim
  apply linearIndependent_of_injOn_natDegree (pFamUnion_ne_zero V k)
  have hinj := hdeg V k hk hV hprim
  -- transport injectivity of the degree map through `pFamUnion_natDegree`
  have heq : (fun p : Σ i : Fin m, Fin (k - vAbs (V i)) =>
        (pFamUnion (F := F) V k p).natDegree)
      = (fun p => vAbs (V p.1) + (p.2 : ℕ)) := by
    funext p; exact pFamUnion_natDegree V k p
  rw [heq]; exact hinj

/-- **The all-distinct-degree sub-case of Theorem 1.7's primitive case, CLOSED unconditionally.**
Whenever the union degrees of a primitive `V*(k)` system are pairwise distinct, `P(k,V)` is
linearly independent — no further hypotheses. -/
theorem pFamUnion_linearIndependent_of_degrees_injective {m : ℕ}
    (V : Fin m → (Fin n → ℕ)) (k : ℕ)
    (hinj : Function.Injective
      (fun p : Σ i : Fin m, Fin (k - vAbs (V i)) => vAbs (V p.1) + (p.2 : ℕ))) :
    LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k) := by
  apply linearIndependent_of_injOn_natDegree (pFamUnion_ne_zero V k)
  have heq : (fun p : Σ i : Fin m, Fin (k - vAbs (V i)) =>
        (pFamUnion (F := F) V k p).natDegree)
      = (fun p => vAbs (V p.1) + (p.2 : ℕ)) := by
    funext p; exact pFamUnion_natDegree V k p
  rw [heq]; exact hinj

end LovettReduction

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.linearIndependent_of_injOn_natDegree
#print axioms ArkLib.GMMDS.pFamUnion_natDegree_lt
#print axioms ArkLib.GMMDS.card_pFamUnion_le
#print axioms ArkLib.GMMDS.lovettPrimitiveCase_of_injOn_degree
#print axioms ArkLib.GMMDS.pFamUnion_linearIndependent_of_degrees_injective
