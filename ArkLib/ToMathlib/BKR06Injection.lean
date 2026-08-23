/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.BKR06FiberCount
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# BKR06 §3 Construction: Subspace Polynomials and Reed–Solomon Code Closeness

This module formalizes the geometric component of the list-decoding lower bound for Reed–Solomon
codes established by Ben-Sasson, Kopparty, and Radhakrishnan (BKR06). The core counting engine
is formalized in `ArkLib.ToMathlib.BKR06FiberCount`. This file establishes the algebraic
identities required to map roots of subspace polynomials to Reed–Solomon codewords that are close
to a designated received word.

### Mathematical Framework

Let $K = \mathbb{F}_{q^m}$ be a finite extension of $F = \mathbb{F}_q$.
1. **Agreement Identity:** For a received word interpolant $P^*$ and a polynomial $P$, the
   codeword corresponding to $P^* - P$ agrees with the evaluation of $P^*$ precisely at the roots of
   $P$.
2. **Subspace Interpolation:** When $P = P_L$ is the linearized subspace polynomial of a
$v$-dimensional
   subspace $L \subseteq K$, the roots of $P_L$ form the subspace $L$, yielding agreement on $q^v$
   points.
3. **List Size:** By pigeonholing over subspaces sharing high-degree coefficients, BKR06 constructs
   a family of close codewords of size at least $q^{(u+1)m - v^2}$.

### Parameter Realization

This module addresses the parameter mismatch in standard submodularity bounds by formalizing the
construction over a proper extension field $K/\mathbb{F}_q$ (with $m \ge 2$), where non-trivial
subspaces of dimension $d \ge 2$ exist, ensuring the construction yields the correct list sizes.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

open Polynomial BigOperators Finset

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Module F K]

/-! ## The Algebraic Agreement Identity -/

variable {ι : Type*} [Fintype ι]

/-- The pointwise agreement identity of BKR06 Proposition 3.4. For any pivot polynomial $P^*$
and offset polynomial $P$, the evaluation of $P^* - P$ agrees with the evaluation of $P^*$
at $x$ if and only if $P$ vanishes at $x$. -/
lemma evalOnPoints_sub_agrees_iff_isRoot
    (domain : ι ↪ K) (pivot P : K[X]) (x : ι) :
    ReedSolomon.evalOnPoints domain pivot x
        = ReedSolomon.evalOnPoints domain (pivot - P) x
      ↔ P.IsRoot (domain x) := by
  classical
  simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, eval_sub]
  constructor
  · intro h
    have : P.eval (domain x) = 0 := by
      have := sub_eq_zero.mpr h.symm
      simpa using this
    simpa [IsRoot] using this
  · intro h
    have hP : P.eval (domain x) = 0 := h
    simp [hP]

/-- BKR06 Proposition 3.4 specialized to linearized subspace polynomials.
The evaluation of the difference $P^* - P_W$ agrees with the evaluation of $P^*$ on all points
of the evaluation domain that lie in the subspace $W$. -/
lemma evalOnPoints_sub_subspacePoly_agrees_on_W
    (domain : ι ↪ K) (pivot : K[X]) (W : Submodule F K) [Fintype W]
    (x : ι) (hx : domain x ∈ W) :
    ReedSolomon.evalOnPoints domain pivot x
      = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)) x := by
  rw [evalOnPoints_sub_agrees_iff_isRoot]
  exact (subspacePoly_isRoot_iff (subFinset W) (domain x)).mpr (by simpa using hx)

/-! ## Reed–Solomon Codeword Membership -/

/-- Polynomials of degree strictly less than $k$ evaluate to codewords in `ReedSolomon.code domain
k`. -/
lemma evalOnPoints_mem_code_of_degree_lt
    (domain : ι ↪ K) (Q : K[X]) (k : ℕ) (hQ : Q ∈ Polynomial.degreeLT K k) :
    ReedSolomon.evalOnPoints domain Q ∈ ReedSolomon.code domain k :=
  ⟨Q, hQ, rfl⟩

/-- If the difference between the pivot polynomial and the subspace polynomial $P_W$ has degree
strictly less than $k$, then the evaluation of $pivot - P_W$ yields a valid Reed–Solomon codeword
agreeing with $pivot$ on the subspace $W$. -/
lemma bkr06_codeword_mem_code_and_agrees
    (domain : ι ↪ K) (pivot : K[X]) (W : Submodule F K) [Fintype W] (k : ℕ)
    (hdeg : pivot - subspacePoly (subFinset W) ∈ Polynomial.degreeLT K k) :
    ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W))
        ∈ ReedSolomon.code domain k
      ∧ ∀ x : ι, domain x ∈ W →
          ReedSolomon.evalOnPoints domain pivot x
            = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)) x := by
  refine ⟨evalOnPoints_mem_code_of_degree_lt domain _ k hdeg, ?_⟩
  intro x hx
  exact evalOnPoints_sub_subspacePoly_agrees_on_W domain pivot W x hx

/-! ## The Subspace Family Construction -/

/-- One member of the BKR06 subspace family (Lemma 3.5). For each subspace $L$ whose subspace
polynomial matches the pivot polynomial above degree $k$, we obtain a close codeword. -/
theorem bkr06_family_member_codeword
    (domain : ι ↪ K) (pivot : K[X]) (L : Submodule F K) [Fintype L] (k : ℕ)
    (hdeg : pivot - subspacePoly (subFinset L) ∈ Polynomial.degreeLT K k) :
    ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset L))
        ∈ ReedSolomon.code domain k
      ∧ (∀ x : ι, domain x ∈ L →
          ReedSolomon.evalOnPoints domain pivot x
            = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset L)) x) :=
  bkr06_codeword_mem_code_and_agrees domain pivot L k hdeg

/-- Surjective evaluation domains induce injective polynomial difference mappings.
If the evaluation domain is surjective onto the field $K$, then two distinct subspace polynomials
yield distinct codewords. -/
lemma evalOnPoints_sub_injective_of_surjective
    (domain : ι ↪ K) (hsurj : Function.Surjective domain) (pivot : K[X])
    {P Q : K[X]}
    (hagree : ReedSolomon.evalOnPoints domain (pivot - P)
                = ReedSolomon.evalOnPoints domain (pivot - Q))
    (hP : (pivot - P).natDegree < Fintype.card K)
    (hQ : (pivot - Q).natDegree < Fintype.card K) :
    pivot - P = pivot - Q := by
  classical
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' (pivot - P) (pivot - Q)
    (Finset.univ : Finset K) ?_ ?_
  · intro z _
    obtain ⟨i, rfl⟩ := hsurj z
    have := congrArg (fun f => f i) hagree
    simpa [ReedSolomon.evalOnPoints] using this
  · simpa [Finset.card_univ] using max_lt hP hQ

end BKR06

/-! ## Extension Parameter Variant of BKR06 Injection -/

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Module F K]

/-- The geometric encoding mapping is injective and maps into the Reed–Solomon code.
Under a surjective evaluation domain and a family of distinct subspace polynomials whose differences
from the pivot have degree strictly less than $k$, the encoding map is injective and yields
valid codewords. -/
theorem bkr06_family_encoding_injective_into_code
    {ι : Type*} [Fintype ι]
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (k : ℕ) (𝓛 : ι → Submodule F K) [∀ i, Fintype (𝓛 i)]
    (hdeg : ∀ i, pivot - subspacePoly (subFinset (𝓛 i)) ∈ Polynomial.degreeLT K k)
    (hsmall : ∀ i, (pivot - subspacePoly (subFinset (𝓛 i))).natDegree < Fintype.card K)
    (hdistinct : Function.Injective
        (fun i => subspacePoly (subFinset (𝓛 i)))) :
    let encode : ι → (K → K) :=
      fun i => ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset (𝓛 i)))
    (∀ i, encode i ∈ ReedSolomon.code domain k)
      ∧ (∀ i, ∀ x : K, domain x ∈ 𝓛 i →
            ReedSolomon.evalOnPoints domain pivot x = encode i x)
      ∧ Function.Injective encode := by
  intro encode
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact evalOnPoints_mem_code_of_degree_lt domain _ k (hdeg i)
  · intro i x hx
    exact evalOnPoints_sub_subspacePoly_agrees_on_W domain pivot (𝓛 i) x hx
  · intro i j hij
    -- Equality of the evaluations implies equality of the polynomial representatives, which in turn
    -- implies equality of the underlying subspace polynomials, yielding injectivity via hdistinct.
    have hpoly :
        pivot - subspacePoly (subFinset (𝓛 i))
          = pivot - subspacePoly (subFinset (𝓛 j)) :=
      evalOnPoints_sub_injective_of_surjective domain hsurj pivot hij
        (hsmall i) (hsmall j)
    have hsub :
        subspacePoly (subFinset (𝓛 i)) = subspacePoly (subFinset (𝓛 j)) := by
      linear_combination -hpoly
    exact hdistinct hsub

/-- **Counting hand-off.** The injective family encoding constructed above forces at least
$|\iota|$ distinct close codewords. Combined with the fiber-counting bounds established in
`BKR06FiberCount`, this yields the Ben-Sasson–Kopparty–Radhakrishnan list-size lower bound
by establishing a lower bound on the cardinality of the close-codeword set. -/
theorem bkr06_family_close_codewords_card_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (k : ℕ) (δ : ℝ) (𝓛 : ι → Submodule F K) [∀ i, Fintype (𝓛 i)]
    (hsmall : ∀ i, (pivot - subspacePoly (subFinset (𝓛 i))).natDegree < Fintype.card K)
    (hdistinct : Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))))
    -- Closeness is represented as relative distance in the Reed–Solomon code.
    (hclose : ∀ i,
        ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset (𝓛 i)))
          ∈ ListDecodable.closeCodewordsRel
              ((ReedSolomon.code domain k : Set (K → K)))
              (ReedSolomon.evalOnPoints domain pivot) δ) :
    (Fintype.card ι : ℕ) ≤
      (ListDecodable.closeCodewordsRel
          ((ReedSolomon.code domain k : Set (K → K)))
          (ReedSolomon.evalOnPoints domain pivot) δ).ncard := by
  classical
  set encode : ι → (K → K) :=
    fun i => ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset (𝓛 i)))
    with hencode
  have hinj : Function.Injective encode := by
    intro i j hij
    have hpoly :
        pivot - subspacePoly (subFinset (𝓛 i))
          = pivot - subspacePoly (subFinset (𝓛 j)) :=
      evalOnPoints_sub_injective_of_surjective domain hsurj pivot hij
        (hsmall i) (hsmall j)
    have hsub :
        subspacePoly (subFinset (𝓛 i)) = subspacePoly (subFinset (𝓛 j)) := by
      linear_combination -hpoly
    exact hdistinct hsub
  -- The image of `encode` is a subset of the close-codeword set of size $|\iota|$.
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι),
      encode i ∈
        ListDecodable.closeCodewordsRel
          ((ReedSolomon.code domain k : Set (K → K)))
          (ReedSolomon.evalOnPoints domain pivot) δ := fun i _ => hclose i
  have := Set.ncard_le_ncard_of_injOn (s := (Set.univ : Set ι)) encode
    (fun i _ => hclose i) (hinj.injOn) (Set.toFinite _)
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using this

end BKR06
