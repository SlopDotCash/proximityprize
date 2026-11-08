/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# PromotedHypothesesA

An **abstract, law-free sketch** of a group of promoted clustering hypotheses (Group A) about
the closest-codeword centers `c z` of a line bundle `u₀ + z·u₁`.

Scope caveats (audit PG-041):

* The local class `PromotedHypothesesA.Field` below is *not* Mathlib's `Field`: it only names
  five operations (`add`, `zero`, `mul`, `one`, `neg`) and imposes **no field laws**
  (no associativity, distributivity, inverses, finiteness, ...). `vector_add` / `vector_smul`
  are therefore pointwise applications of uninterpreted operations, not a vector-space
  structure.
* The code `C : (ι → F) → Prop` is an arbitrary predicate; no linearity or closure under sums is
  assumed.
* Consequently the `H*` definitions are uninterpreted propositions recording the *shape* of each
  hypothesis; they are neither proved nor assumed anywhere. In particular `H7_BarycentricCenter`
  takes an arbitrary target word `sum_c` that is **not** related to `c` (there is no finite sum
  over `F`), so it does not express the barycentric claim "the sum of all centers lies in `C`";
  as stated it is false in general even over a genuine field (zero code, all `c z = 0`, and a
  nonzero `sum_c`).
* The only theorem in this file is `refute_H2_TriangleCluster`: a constant bundle has a single
  center, so it never satisfies `centers_form_triangle`.

A faithful coding-theory version would use Mathlib's `Field`/`Fintype`, a linear code, and the
actual finite sum `∑ z, c z`; that is not done here.
-/

-- Abstract shapes of promoted hypotheses (Group A), plus one trivial refutation (H2).

namespace ProximityGap.PromotedHypothesesA

/-- A bare signature of five operations with **no axioms**; deliberately not Mathlib's `Field`.
Nothing in this file uses field laws. -/
class Field (F : Type) where
  add : F → F → F
  zero : F
  mul : F → F → F
  one : F
  neg : F → F

variable {ι : Type} [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

def vector_add (v w : ι → F) : ι → F := fun i => Field.add (v i) (w i)
def vector_smul (scalar : F) (v : ι → F) : ι → F := fun i => Field.mul scalar (v i)

variable (C : (ι → F) → Prop)
variable (e : Nat)
variable (u₀ u₁ : ι → F)
variable (c : F → ι → F)

-- H1: There exist w₁, w₂ such that the centers lie on an affine line.
def H1_LineCluster : Prop :=
  ∃ w₁ w₂ : ι → F, ∀ z : F, ∃ t : F, c z = vector_add w₁ (vector_smul t w₂)

-- H2: The centers form a triangle (exactly 3 distinct codewords).
-- A trivial constant bundle gives exactly 1 center, refuting the claim that ALL bundles form a triangle.
def centers_form_triangle (c : F → ι → F) (z₁ z₂ z₃ : F) : Prop :=
  c z₁ ≠ c z₂ ∧ c z₂ ≠ c z₃ ∧ c z₁ ≠ c z₃ ∧ (∀ z, c z = c z₁ ∨ c z = c z₂ ∨ c z = c z₃)

theorem refute_H2_TriangleCluster (z₁ z₂ z₃ : F) (c0 : ι → F) :
    ¬ centers_form_triangle (fun _ => c0) z₁ z₂ z₃ := by
  intro h
  have h1 : (fun _ => c0) z₁ ≠ (fun _ => c0) z₂ := h.1
  have h2 : c0 = c0 := rfl
  exact h1 h2

-- H5: If the bundle has exactly 3 distinct closest codewords, those 3 codewords are collinear.
def H5_CollinearCenters (z₁ z₂ z₃ : F) : Prop :=
  centers_form_triangle c z₁ z₂ z₃ → H1_LineCluster c

-- H7 (shape only): if every center `c z` satisfies `C`, then the given word `sum_c` satisfies
-- `C`. `sum_c` is an arbitrary parameter, NOT the sum of the centers (no finite sum over `F`
-- exists in this law-free sketch), so this is not the barycentric statement and is false for
-- general `sum_c` (zero code, all `c z = 0`, nonzero `sum_c`). Unproved and unused.
def H7_BarycentricCenter (sum_c : ι → F) : Prop :=
  (∀ z, C (c z)) → C sum_c

-- H8: Shifting the bundle by c' preserves the clustering radius.
def H8_TranslationInvariance (dist : (ι → F) → (ι → F) → Nat) (c' : ι → F) : Prop :=
  ∀ z, dist (vector_add (vector_add u₀ c') (vector_smul z u₁)) (vector_add (c z) c') =
       dist (vector_add u₀ (vector_smul z u₁)) (c z)

-- H9: The minimal radius required to enclose all centers in a 1-dimensional affine space is <= e-1.
def H9_AffineShiftRadius (dist : (ι → F) → (ι → F) → Nat) : Prop :=
  ∃ w₁ w₂ : ι → F, ∀ z, ∃ t, dist (c z) (vector_add w₁ (vector_smul t w₂)) ≤ e - 1

end ProximityGap.PromotedHypothesesA
