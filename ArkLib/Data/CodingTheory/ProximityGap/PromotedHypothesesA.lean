-- Formalization and Proofs/Refutations of Promoted Hypotheses (Group A)

namespace ProximityGap.PromotedHypothesesA

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

-- H7: The sum of all closest codewords over F is in C.
-- We state it as a general property if the sum exists.
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
