/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Ring-Switching Profile

The `RingSwitchingProfile` abstraction captures the packing-layer data that every ring-switching
reduction needs, so that the protocol skeleton can be written once and instantiated by Binius
(DP24), Hachi (NOZ26 / ePrint 2026/156), and future small-ring/large-ring PCS work.

It is a `structure` passed **explicitly** (not a `class`): distinct profiles may share the same
carriers `(B, L, κ)` (e.g. with different bases), so instance resolution would be ambiguous.

It is stated over `CommRing` (not `Field`): Hachi's carrier `L = R_q` is not a field. The
`Field`-only steps (Schwartz–Zippel over `|L|`) stay at the soundness use-sites in the
ring-switching files, not here.

This file holds only the abstract structure (no Binius dependency), so `Prelude.lean` can import it
and parameterize the protocol over it; the Binius instance `binaryTowerProfile` lives in
`Prelude.lean`, after the tensor-algebra definitions it is built from.

## Fields and their two instantiations

| field | Binius (DP24) | Hachi (ePrint 2026/156) |
|---|---|---|
| `B`, `L` | small field `K`, tower field `L` | `R_q^H ≅ F_{q^k}`, `R_q` |
| `basis` | binary `K`-basis of `L`, rank `2^κ` | `ψ` of Theorem 2, rank `d/k = 2^κ` |
| `A` | tensor algebra `L ⊗[K] L` | `R_q` itself (`= L`) |
| `φ₀`, `φ₁` | `α ↦ α ⊗ 1`, `α ↦ 1 ⊗ α` | `id`, the automorphism `σ₋₁` |
| `decomposeRows`/`Columns` | `L`-coords of `ŝ` in `L ⊗_K L` | coords of `Y ∈ R_q` via `ψ` |

The only structural difference — Hachi has no separate tensor object (`A = L`, `φ₀ = id`,
`φ₁ = σ₋₁`) while Binius has `A = L ⊗_K L` — is absorbed by `A`, `φ₀`, `φ₁` being explicit fields.
The eq̃/trace inner-product law (DP24 §2.5 / Hachi Theorem 2) is carried as the two `Prop`-valued
fields `decomposeRows_spec` / `decomposeColumns_spec` below: it is exactly what the completeness and
soundness proofs consume, and stating it as part of the data keeps those theorems true for *every*
profile (a law-free structure would make the generic statements vacuously false — e.g.
`decomposeColumns ≡ 0`). Each instance discharges the laws from its own algebra (Binius: tensor
`Basis.sum_repr`; Hachi: Theorem 2).

See also: the KB concept page `docs/kb/concepts/ring-switching.md` and the blueprint section
`blueprint/src/proof_systems/ring_switching.tex` for the protocol, phases, and security statements.
-/

namespace RingSwitching

open Module

/-- The packing-layer data a ring-switching reduction abstracts over. `L` is free of rank `2^κ`
over the small ring `B` (via `basis`); `A` is the pack/trace carrier where the folded element `ŝ`
lives (and which the batching phase sends on the wire). See the module docstring for the Binius and
Hachi instantiations of each field. -/
structure RingSwitchingProfile (B L : Type*) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- pack/trace carrier; Binius `L ⊗[K] L`, Hachi `R_q` (`= L`). The batching wire type. -/
  A : Type*
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- column embedding `L → A`; Binius `α ↦ α ⊗ 1`, Hachi `id`. -/
  φ₀ : L →+* A
  /-- row embedding `L → A`; Binius `α ↦ 1 ⊗ α`, Hachi the automorphism `σ₋₁`. -/
  φ₁ : L →+* A
  /-- The `2^κ` `L`-valued "row" coordinates of an `A`-element (Binius:
  `β.baseChange L`-coords of `ŝ ∈ L ⊗_K L`; used in step 5 / `compute_s0`).
  The algebraic law relating it to `φ₀`/`φ₁` and `A`'s multiplication is an
  instance-internal lemma (used in soundness proofs), not a field here. -/
  decomposeRows : A → (Fin κ → Fin 2) → L
  /-- The `2^κ` `L`-valued "column" coordinates of an `A`-element (Binius: `baseChangeRight`-coords;
  used in step 2 / `performCheckOriginalEvaluation`). NOTE: in the Binius instance this uses the
  *right* `L`-module structure on `A`, distinct from `algLA` (the left/`φ₀` action). -/
  decomposeColumns : A → (Fin κ → Fin 2) → L
  /-- **Row reconstruction law** (the eq̃/trace structural identity, DP24 §2.5 / Hachi Theorem 2):
  every `A`-element is recovered from its row coordinates via the `φ₀`-image of those coordinates
  weighted by the `φ₁`-image of the basis. This is the algebraic law tying `decomposeRows` to
  `φ₀`/`φ₁`/`basis`; it is what the batching/sumcheck completeness and soundness
  proofs depend on, and what rules out degenerate profiles (e.g. `decomposeRows ≡ 0`).
  For Binius (`A = L ⊗_K L`) it is `Basis.sum_repr` for `β.baseChange L`; for Hachi
  it is Theorem 2. -/
  decomposeRows_spec : ∀ z : A, z = ∑ u, φ₀ (decomposeRows z u) * φ₁ (basis u)
  /-- **Column reconstruction law**: the right/`φ₁`-action dual of `decomposeRows_spec`. -/
  decomposeColumns_spec : ∀ z : A, z = ∑ v, φ₁ (decomposeColumns z v) * φ₀ (basis v)
  /-- **Row additivity**: row coordinates are additive. Together with
  `decomposeRows_φ₀_mul_φ₁` this is the *extraction* direction (rows of a reconstruction
  recover the coordinates), which `decomposeRows_spec` alone does not imply — two distinct
  coordinate vectors could reconstruct the same element without it. Binius: linearity of
  `(β.baseChange L).repr`. -/
  decomposeRows_add : ∀ z w : A, ∀ u, decomposeRows (z + w) u = decomposeRows z u + decomposeRows w u
  /-- **Row atomic extraction**: the row coordinates of a pure `φ₀ a * φ₁ b` element are the
  basis coordinates of `b` scaled into `a`. Binius: `Basis.baseChange_repr_tmul`. -/
  decomposeRows_φ₀_mul_φ₁ : ∀ (a b : L) (u : Fin κ → Fin 2),
    decomposeRows (φ₀ a * φ₁ b) u = basis.repr b u • a
  /-- **Column additivity**: the column-side dual of `decomposeRows_add`. -/
  decomposeColumns_add : ∀ z w : A, ∀ v,
    decomposeColumns (z + w) v = decomposeColumns z v + decomposeColumns w v
  /-- **Column atomic extraction**: the column coordinates of a pure `φ₀ a * φ₁ b` element are
  the basis coordinates of `a` scaled into `b` — the dual of `decomposeRows_φ₀_mul_φ₁`.
  Binius: `Basis.baseChangeRight_repr_tmul`. -/
  decomposeColumns_φ₀_mul_φ₁ : ∀ (a b : L) (v : Fin κ → Fin 2),
    decomposeColumns (φ₀ a * φ₁ b) v = basis.repr a v • b

attribute [instance] RingSwitchingProfile.commRingA RingSwitchingProfile.algLA

end RingSwitching
