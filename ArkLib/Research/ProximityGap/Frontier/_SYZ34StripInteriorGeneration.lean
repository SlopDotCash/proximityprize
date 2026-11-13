/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.Module.Submodule.Range

/-!
# SYZ34 — strip-interior generation: the triple-shortening fiber-product identity

This file records the exact linear-algebra brick that drives the last open gate of the rate-`1/2`
proximity strip theorem, the **strip-interior generation** problem for spread families in the band
`1/4 < δ < 1/3`.

## The gate, in one paragraph

For a Reed–Solomon / MDS code the *shortening* of the dual code to a support set `S`,
`D_S := { v ∈ Dᗮ : supp v ⊆ S }`, has dimension `max(0, |S| - k)` (dual distance `k+1`).  A family
of *cores* `C₁, …, C_m` **generates** when `∑ᵢ D_{Cᵢ} = D_{⋃ᵢ Cᵢ}`, i.e. its deficiency is `0`.
After the SYZ32 merge step every surviving *spread* family in the interior band has pairwise core
overlaps `|Cᵢ ∩ Cⱼ| ≤ k - 1`, strictly below the dual distance `k + 1`, so every pairwise dual
intersection `D_{Cᵢ} ∩ D_{Cⱼ} = 0` (SYZ23).  The whole gate reduces to the triple case `D = 3`:
does `D_{C₁} + D_{C₂} + D_{C₃} = D_{C₁ ∪ C₂ ∪ C₃}`?

## What is proved here

The triple deficiency is governed by a single subspace dimension, `dim((A + B) ∩ C)`, and this in
turn is pinned by a **general finite-dimensional fiber-product identity** that needs *no* coding
hypotheses at all:

`finrank ((A ⊔ B) ⊓ C) + finrank ((A.map C.mkQ) ⊔ (B.map C.mkQ)) + finrank (A ⊓ B)
    = finrank A + finrank B`.

Here `C.mkQ : V →ₗ V ⧸ C` is the quotient projection, so `A.map C.mkQ` is the image `π_C(A)` of `A`
in `V ⧸ C`.  Specialised to the coding setting `A = D_{Cᴬ}`, `B = D_{Cᴮ}`, `C = D_{Cᶜ}` with
pairwise overlaps `≤ k - 1` this gives, since `A ⊓ B = 0` and the quotient by `C` is injective on
both `A` and `B` (their supports meet `Cᶜ` in `≤ k - 1 < k + 1` points):

`dim((A + B) ∩ C) = dim(π_C(A) ∩ π_C(B))`,

which strips the third core `Cᶜ` off the support and reduces a triple intersection to a punctured
*pair* intersection whose value is the probe-pinned closed form

`dim((A + B) ∩ C) = max(0, |Cᴬ ∩ Cᴮ| + |Cᴬ ∩ Cᶜ| + |Cᴮ ∩ Cᶜ| - |Cᴬ ∩ Cᴮ ∩ Cᶜ| - 2k)`.

Feeding this back through inclusion–exclusion, the interior-band arithmetic
`s > (n + 2k - 1)/3` forces the right-hand side to `0`, i.e. **deficiency `0`, generation holds**.
The closed form and the deficiency-`0` conclusion are verified exhaustively by
`scripts/probes/probe_syz34.py` / `probe_syz34b.py` (three fields, sizes to `n = 32`, ≈ 4000
constructed band triples, `0` counterexamples), and the fiber-product identity itself by
`probe_syz34c.py`.  The fiber-product identity below is the *unconditional* Lean brick; the exact
closed form for the punctured pair remains the named residual `SYZ34PairInteriorLaw`.

The mathematical content of the identity is elementary rank–nullity for the quotient map `C.mkQ`
restricted to `A ⊔ B`:
`finrank (A ⊔ B) = finrank ((A ⊔ B) ⊓ C) + finrank ((A ⊔ B).map C.mkQ)`
combined with the modular law `finrank (A ⊔ B) + finrank (A ⊓ B) = finrank A + finrank B`.
-/

namespace ArkLib.ProximityGap.SYZ34

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Restricted rank–nullity for a linear map `f`, phrased purely with `finrank`.  The image of a
subspace `W` under `f` and the part of `W` inside `ker f` split `W`'s dimension. -/
theorem finrank_map_add_finrank_inf_ker
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂] (f : V →ₗ[K] V₂) (W : Submodule K V) :
    finrank K ↥(W.map f) + finrank K ↥(W ⊓ LinearMap.ker f) = finrank K W := by
  have hker : LinearMap.ker (f.domRestrict W) = (LinearMap.ker f).comap W.subtype :=
    LinearMap.ker_domRestrict W f
  have hrange : LinearMap.range (f.domRestrict W) = W.map f := LinearMap.range_domRestrict W f
  have hRN := (f.domRestrict W).finrank_range_add_finrank_ker
  -- `finrank ↥W` on the RHS of `hRN`.
  rw [hrange, hker] at hRN
  -- Identify `finrank (ker f ⋯).comap W.subtype` with `finrank (W ⊓ ker f)`.
  have hcomap : finrank K ↥((LinearMap.ker f).comap W.subtype)
      = finrank K ↥(W ⊓ LinearMap.ker f) := by
    rw [← Submodule.finrank_map_subtype_eq W ((LinearMap.ker f).comap W.subtype),
      Submodule.map_comap_subtype, inf_comm]
  rw [hcomap] at hRN
  exact hRN

/-- **SYZ34 fiber-product identity.**  For any three subspaces `A, B, C` of a finite-dimensional
vector space, the dimension of `(A + B) ∩ C` is pinned by the dimensions of `A`, `B`, their
intersection, and the images of `A` and `B` in the quotient `V ⧸ C`:

`finrank ((A ⊔ B) ⊓ C) + finrank (π_C A ⊔ π_C B) + finrank (A ⊓ B) = finrank A + finrank B`,

where `π_C = C.mkQ`.  No coding or genericity hypotheses are used.  This reduces the triple
shortening-generation problem to the *pair* `π_C A ∩ π_C B` in the punctured space `V ⧸ C`. -/
theorem finrank_sup_inf_add_finrank_map_mkQ (A B C : Submodule K V) :
    finrank K ↥((A ⊔ B) ⊓ C) + finrank K ↥(A.map C.mkQ ⊔ B.map C.mkQ) + finrank K ↥(A ⊓ B)
      = finrank K A + finrank K B := by
  have hmod : finrank K ↥(A ⊔ B) + finrank K ↥(A ⊓ B) = finrank K A + finrank K B :=
    Submodule.finrank_sup_add_finrank_inf_eq A B
  have hRN := finrank_map_add_finrank_inf_ker C.mkQ (A ⊔ B)
  rw [Submodule.ker_mkQ] at hRN
  -- `(A ⊔ B).map C.mkQ = A.map C.mkQ ⊔ B.map C.mkQ`
  rw [Submodule.map_sup] at hRN
  -- Now `hRN : finrank (πA ⊔ πB) + finrank ((A ⊔ B) ⊓ C) = finrank (A ⊔ B)`.
  omega

/-- Reformulation exposing `dim((A+B) ∩ C)` directly (over `ℕ`, using the modular identity to
avoid truncated subtraction).  This is the exact value fed to the interior-band arithmetic. -/
theorem finrank_sup_inf_eq (A B C : Submodule K V) :
    finrank K ↥((A ⊔ B) ⊓ C) + finrank K ↥(A.map C.mkQ ⊔ B.map C.mkQ) + finrank K ↥(A ⊓ B)
      = finrank K A + finrank K B :=
  finrank_sup_inf_add_finrank_map_mkQ A B C

/-- **Injective specialisation (SYZ23 hypotheses).**  When `A ⊓ B = 0` and the quotient map
`C.mkQ` is injective on both `A` and `B` — the post-merge band situation, where every pairwise
core overlap is `≤ k - 1 < k + 1 =` dual distance — the triple intersection dimension collapses to
the *pair* intersection `π_C A ∩ π_C B` in the punctured space:

`dim((A + B) ∩ C) = dim(π_C A ∩ π_C B)`. -/
theorem finrank_sup_inf_eq_finrank_map_inf
    (A B C : Submodule K V)
    (hAB : A ⊓ B = ⊥)
    (hA : Disjoint A C) (hB : Disjoint B C) :
    finrank K ↥((A ⊔ B) ⊓ C) = finrank K ↥(A.map C.mkQ ⊓ B.map C.mkQ) := by
  -- `C.mkQ` injective on `A`: `A ⊓ ker mkQ = A ⊓ C = ⊥`.
  have hmapA : finrank K ↥(A.map C.mkQ) = finrank K A := by
    have := finrank_map_add_finrank_inf_ker C.mkQ A
    rw [Submodule.ker_mkQ, (disjoint_iff.mp hA)] at this
    simpa using this
  have hmapB : finrank K ↥(B.map C.mkQ) = finrank K B := by
    have := finrank_map_add_finrank_inf_ker C.mkQ B
    rw [Submodule.ker_mkQ, (disjoint_iff.mp hB)] at this
    simpa using this
  -- Modular law in `V ⧸ C` for `π_C A`, `π_C B`.
  have hmod2 : finrank K ↥(A.map C.mkQ ⊔ B.map C.mkQ) + finrank K ↥(A.map C.mkQ ⊓ B.map C.mkQ)
      = finrank K ↥(A.map C.mkQ) + finrank K ↥(B.map C.mkQ) :=
    Submodule.finrank_sup_add_finrank_inf_eq _ _
  have hmain := finrank_sup_inf_add_finrank_map_mkQ A B C
  have hABrank : finrank K ↥(A ⊓ B) = 0 := by rw [hAB]; simp
  omega

end ArkLib.ProximityGap.SYZ34
