/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HigherOrderMDS

/-!
# Higher-order MDS for a frame: the column-span bridge (#389, layer 2)

`HigherOrderMDS.lean` (layer 1) is the abstract generic-intersection calculus.  This
file connects it to a *code* through its generator columns.

A Reed–Solomon (or any MDS) generator presents its `n` columns as a **frame**
`v : ι → V` in the `k`-dimensional message space `V` (for RS, `v ζ = (1,ζ,…,ζ^{k-1})`,
the Vandermonde column).  For an index set `J`, `frameSpan K v J = span{v ζ : ζ ∈ J}`.
Roth (2022) / Brakensiek–Gopi–Makam (2023): the code is **higher-order MDS of order
`ℓ`** when, for every `ℓ` **pairwise disjoint** index sets, the column-spans meet
generically (`IsGenericInter` of the `frameSpan`s).  Disjointness matters: overlapping
sets force shared columns, so the abstract `min(k, Σ codim)` value only applies disjointly.

## Results

* `IsMDSFrame` — every `≤ k` columns are linearly independent (the ordinary MDS
  condition on the frame; for RS this is the Vandermonde determinant).
* `finrank_frameSpan` — under `IsMDSFrame`, `finrank (frameSpan K v J) = |J|` for
  `|J| ≤ k`, so `codim (frameSpan K v J) = k − |J|`.
* `IsHigherMDS` — higher-order MDS of order `ℓ`: all `ℓ`-families of **pairwise disjoint**
  `≤ k`-column index sets have generic-position column-spans (disjointness is essential —
  see the def; overlapping sets share columns and are never generic).
* (generic value `dim(⋂ᵢ frameSpan K v Jᵢ) = max(0, Σ|Jᵢ| − (ℓ−1)k)` follows directly
  from layer-1 `finrank_iInf_of_generic` applied to the MDS(ℓ) hypothesis.)
* `not_higherMDS_of_not_generic` — **the failure certificate**: a *disjoint* `ℓ`-family
  whose column-spans intersect in *more* than the generic dimension witnesses
  `¬ IsHigherMDS` — the tool for the explicit smooth-domain (negative) question.

Issue #389.
-/

open Finset Module ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type*} [DecidableEq ι]

/-- The span of the frame columns indexed by `J`. -/
noncomputable def frameSpan (K : Type*) [Field K] [Module K V] (v : ι → V)
    (J : Finset ι) : Submodule K V :=
  Submodule.span K (v '' (J : Set ι))

/-- An **MDS frame**: the columns are distinct and every `≤ finrank V` of them are
linearly independent.  (For a Reed–Solomon generator this is the Vandermonde
nonvanishing; equivalently the code is ordinary MDS.) -/
def IsMDSFrame (K : Type*) [Field K] [Module K V] (v : ι → V) : Prop :=
  Function.Injective v ∧
    ∀ J : Finset ι, J.card ≤ finrank K V →
      LinearIndependent K (fun i : J => v i)

/-- Under an MDS frame, a `≤ k`-column span has dimension exactly its index count. -/
theorem finrank_frameSpan {v : ι → V} (hv : IsMDSFrame K v) {J : Finset ι}
    (hJ : J.card ≤ finrank K V) :
    finrank K ↥(frameSpan K v J) = J.card := by
  classical
  have hli : LinearIndependent K (fun i : J => v i) := hv.2 J hJ
  have himg : (Set.range (fun i : J => v i)) = v '' (J : Set ι) := by
    ext x; constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  have : frameSpan K v J = Submodule.span K (Set.range (fun i : J => v i)) := by
    rw [frameSpan, himg]
  rw [this, finrank_span_eq_card hli, Fintype.card_coe]

/-- Codimension of a `≤ k`-column span: `k − |J|`. -/
theorem codim_frameSpan {v : ι → V} (hv : IsMDSFrame K v) {J : Finset ι}
    (hJ : J.card ≤ finrank K V) :
    codim (frameSpan K v J) = finrank K V - J.card := by
  rw [codim, finrank_frameSpan hv hJ]

/-- **Higher-order MDS of order `ℓ`** for a frame: every family of `ℓ` **pairwise
disjoint** `≤ k`-column index sets has its column-spans in generic intersection position.
Disjointness is essential: column-spans from *overlapping* index sets share the common
columns, so they are never in generic position in the abstract `min(k, Σ codim)` sense
(`span{v₁,v₂} ∩ span{v₂,v₃} ⊇ ⟨v₂⟩`); the genuine higher-order content lives in disjoint
configurations with `Σ|Jᵢ| > k`, where generic points achieve the bound and special
points (e.g. `μ_n`) can fail it.  The precise *code-level* GM-MDS notion is the dual
generic-zero-pattern object (`AGL24.GMMDSDualZeroPatternTheorem`). -/
def IsHigherMDS (K : Type*) [Field K] [Module K V] (ℓ : ℕ) (v : ι → V) : Prop :=
  ∀ J : Fin ℓ → Finset ι, (∀ i, (J i).card ≤ finrank K V) →
    (∀ i j, i ≠ j → Disjoint (J i) (J j)) →
    IsGenericInter (fun i => frameSpan K v (J i))

/-- **The failure certificate.**  A single `ℓ`-family of `≤ k`-column-spans that is not
in generic position witnesses that the frame is *not* higher-order MDS of order `ℓ`.
Combined with `not_generic_of_finrank_iInf_gt` (layer 1), an `ℓ`-family whose spans
intersect in strictly more than `max(0, Σ|Jᵢ| − (ℓ−1)k)` dimensions certifies the
failure — the tool for the explicit smooth-domain (negative) question. -/
theorem not_higherMDS_of_not_generic {ℓ : ℕ} {v : ι → V}
    {J : Fin ℓ → Finset ι} (hJ : ∀ i, (J i).card ≤ finrank K V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (J i) (J j))
    (hbad : ¬ IsGenericInter (fun i => frameSpan K v (J i))) :
    ¬ IsHigherMDS K ℓ v := by
  intro hmds
  exact hbad (hmds J hJ hdisj)

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.finrank_frameSpan
#print axioms ArkLib.HigherOrderMDS.not_higherMDS_of_not_generic
