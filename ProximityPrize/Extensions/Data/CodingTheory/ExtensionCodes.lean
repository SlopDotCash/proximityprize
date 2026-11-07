/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ExtensionCodes

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
import ProximityPrize.Extensions.Data.CodingTheory.InterleavedCode
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Extension fields and extension codes (ABF26 §2.6)

Definitions and the in-tree extension-code list-size bridge from ABF26 §2.6
(Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated Agreement*,
2026, page 11): extension-field presentations, extension codes obtained by
base-change, and the relation `|Λ(C_F, δ)| = |Λ(C_B^e, δ)|` between the list
size of an extension code and the list size of the corresponding interleaved
base code.

## Main definitions

- `ExtensionFieldPresentation` (D2.19): a thin wrapper around Mathlib's
  `[Algebra B F]` + a finite `B`-basis `basis : Basis (Fin e) B F` of `F`.
  All the paper's structure (`ψ : B ↪ F`, `φ : F ≃ B^e`, the coordinate maps,
  and the systematic property) is derived from these two ingredients —
  no parallel implementation.
- `CodingTheory.extensionCode` (D2.20): the extension code `C_F : F^k → F^n`
  obtained from a `B`-linear code `C_B : B^k → B^n` via an `ExtensionFieldPresentation`.

## Main statements

- `extensionCode_add_mem`, `extensionCode_smul_mem` — closure of
  `extensionCode P C_B` under addition and `F`-scalar multiplication (when
  `C_B` is `B`-linear). Together they package `extensionCode P C_B` as a
  full `F`-`Submodule` (B-linear closure was always present; the F-scalar
  closure is what the structural refactor delivers).
- `lambda_extensionCode_eq_lambda_interleaved` (L2.21, [BCFW25 Lem D.3]):
  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`. Proved in-tree via the coordinate isometry
  `extensionCoordEquiv` (the per-position basis bijection `F ≃ (Fin e → B)`).

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [BCFW25] Bordage-Chiesa-Fenzi-Wahby. Lemma D.3.

(The distance equality `δ_min(C_F) = δ_min(C_B)`, referenced in the L2.21 paragraph
context, is from Dao-Petrov 2025 (Theorem 3.2 in their paper). The knowledge-base
citation key for this paper is not yet registered, so we mention it in prose only.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory

open scoped NNReal
open ListDecodable Module

namespace ExtensionFieldPresentation

variable {B F : Type} [Field B] [Field F] [Algebra B F]

/-- The base-field embedding `ψ : B ↪ F`, derived from `[Algebra B F]`. -/
@[reducible]
def ψ (_P : ExtensionFieldPresentation B F) : B →+* F := algebraMap B F

/-- Injectivity of `ψ` — automatic since the algebra map between fields is
always injective. -/
lemma ψ_injective (P : ExtensionFieldPresentation B F) : Function.Injective P.ψ :=
  FaithfulSMul.algebraMap_injective B F

/-- The `B`-linear coordinate isomorphism `φ : F ≃ₗ[B] (Fin e → B)`, derived
from the basis. -/
noncomputable def φ (P : ExtensionFieldPresentation B F) : F ≃ₗ[B] (Fin P.e → B) :=
  P.basis.equivFun

/-- The `j`-th coordinate map is the `j`-th component of `φ`. Holds by definition
(`coord j = proj j ∘ φ`), recorded as a `simp` lemma for the list-size argument. -/
@[simp]
lemma coord_apply (P : ExtensionFieldPresentation B F) (j : Fin P.e) (x : F) :
    P.coord j x = P.φ x j := rfl

/-- Each coordinate `P.coord j` is additive — direct consequence of being a
`LinearMap`. -/
lemma coord_add (P : ExtensionFieldPresentation B F) (j : Fin P.e) (x y : F) :
    P.coord j (x + y) = P.coord j x + P.coord j y :=
  (P.coord j).map_add x y

/-- Each coordinate `P.coord j` respects the `B`-action — direct consequence of
being a `B`-linear map. The `algebraMap`-based smul (`ψ b * x = b • x`) folds
into ordinary `B`-scalar multiplication via `Algebra.smul_def`. -/
lemma coord_psi_smul (P : ExtensionFieldPresentation B F)
    (j : Fin P.e) (b : B) (x : F) :
    P.coord j (P.ψ b * x) = b * P.coord j x := by
  change P.coord j ((algebraMap B F) b * x) = b * P.coord j x
  rw [← Algebra.smul_def, (P.coord j).map_smul, smul_eq_mul]

end ExtensionFieldPresentation

/-- The coordinate isometry `Φ : (ι → F) ≃ (ι → (Fin e → B))` induced by applying the
basis isomorphism `φ : F ≃ (Fin e → B)` at every position. -/
noncomputable def extensionCoordEquiv
    {ι : Type} {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) :
    (ι → F) ≃ (ι → (Fin P.e → B)) :=
  Equiv.piCongrRight (fun _ : ι ↦ (P.φ : F ≃ₗ[B] (Fin P.e → B)).toEquiv)

@[simp]
lemma extensionCoordEquiv_apply
    {ι : Type} {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) (v : ι → F) (i : ι) :
    extensionCoordEquiv (ι := ι) P v i = P.φ (v i) := rfl

/-- The isometry carries the extension code onto the interleaved base code:
`v ∈ extensionCode P C_B ↔ Φ v ∈ interleavedCodeSet (Fin e) C_B`. The interleaved
membership condition `∀ k, (Φ v).transpose k ∈ C_B` unfolds, position-by-position,
to `(Φ v) i k = φ (v i) k = coord k (v i)`, i.e. exactly the extension-code
condition `∀ k, (fun i ↦ coord k (v i)) ∈ C_B`. -/
lemma mem_extensionCode_iff_image_mem_interleaved
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (v : ι → F) :
    v ∈ extensionCode P C_B ↔
      extensionCoordEquiv (ι := ι) P v ∈ Code.interleavedCodeSet (κ := Fin P.e) C_B := by
  rfl

/-- The coordinate isometry preserves relative Hamming distance: `δᵣ(Φ u, Φ v) = δᵣ(u, v)`.
Both sides are `hammingDist / Fintype.card ι`, and `hammingDist (Φ u) (Φ v) = hammingDist u v`
because `Φ` applies the injective bijection `φ` independently at each position
(`Mathlib.hammingDist_comp`). -/
lemma extensionCoordEquiv_relHammingDist
    {ι : Type} [Fintype ι] [Nonempty ι]
    {B F : Type} [Field B] [DecidableEq B] [Field F] [DecidableEq F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) (u v : ι → F) :
    δᵣ(extensionCoordEquiv (ι := ι) P u, extensionCoordEquiv (ι := ι) P v) = δᵣ(u, v) := by
  unfold Code.relHammingDist
  have hHam : Δ₀(extensionCoordEquiv (ι := ι) P u, extensionCoordEquiv (ι := ι) P v)
      = Δ₀(u, v) :=
    hammingDist_comp (fun _ : ι ↦ (P.φ : F → (Fin P.e → B)))
      (fun _ ↦ (P.φ : F ≃ₗ[B] (Fin P.e → B)).injective)
  rw [hHam]

/-- Membership-in-the-relative-ball transfers along the coordinate isometry `Φ`:
`Φ v ∈ relHammingBall (Φ f) δ ↔ v ∈ relHammingBall f δ`. Both balls are stated with
the `relHammingBall` defining instances (the `open Classical` decidability baked into
that definition), so the `DecidableEq`-instance mismatch that would arise from writing
`δᵣ` directly is avoided. The `Code.relHammingDist`-value equality itself is
instance-irrelevant (a `Subsingleton`), supplied by `hammingDist_comp`. -/
lemma relHammingBall_image_mem_iff
    {ι : Type} [Fintype ι] [Nonempty ι]
    {B F : Type} [Field B] [DecidableEq B] [Field F] [DecidableEq F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) (f v : ι → F) {δ : ℝ} :
    extensionCoordEquiv (ι := ι) P v ∈
        ListDecodable.relHammingBall (extensionCoordEquiv (ι := ι) P f) δ ↔
      v ∈ ListDecodable.relHammingBall f δ := by
  simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq]
  -- Reduce both `relHammingDist`s to `hammingDist`, where instance choice is irrelevant
  -- (`hammingDist`'s value does not depend on the `DecidableEq` witness), and apply
  -- the per-position injectivity of `φ` via `hammingDist_comp`.
  have hHam :
      Δ₀(extensionCoordEquiv (ι := ι) P f, extensionCoordEquiv (ι := ι) P v) = Δ₀(f, v) :=
    hammingDist_comp (fun _ : ι ↦ (P.φ : F → (Fin P.e → B)))
      (fun _ ↦ (P.φ : F ≃ₗ[B] (Fin P.e → B)).injective)
  have h₁ : (Code.relHammingDist (extensionCoordEquiv (ι := ι) P f)
          (extensionCoordEquiv (ι := ι) P v) : ℚ≥0)
        = Code.relHammingDist f v := by
    unfold Code.relHammingDist; rw [hHam]
  -- The two `δᵣ` terms in the goal carry the `relHammingBall`-defining (`Classical`)
  -- `DecidableEq` instances, which differ syntactically from `h₁`'s canonical ones but
  -- are propositionally equal (`DecidableEq` is a `Subsingleton`); `convert` bridges them.
  have hcast : ((Code.relHammingDist (extensionCoordEquiv (ι := ι) P f)
          (extensionCoordEquiv (ι := ι) P v) : ℚ≥0) : ℝ)
        = ((Code.relHammingDist f v : ℚ≥0) : ℝ) := by exact_mod_cast h₁
  constructor
  · intro h
    refine le_of_eq_of_le ?_ h
    convert hcast.symm using 3
  · intro h
    refine le_of_eq_of_le ?_ h
    convert hcast using 3

end CodingTheory
