import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic

/-!
# Promoted Hypotheses Group B (Correlated Error Support)

This file formally evaluates the 5 promoted hypotheses from Group B
over generic finite fields. The hypotheses were observed to hold for
`GF(5)` with `n=4, k=2`, but we demonstrate that they have a red-team
flaw: they fail over `GF(3)` for the same parameters due to the field
size being too small to force collinear syndromes to pass through the origin.

We formulate a generic counterexample in `GF(3)` and use it to refute
all 5 hypotheses without sorry.
-/

abbrev F := ZMod 3
abbrev n : ℕ := 4

-- The parity check matrix for our MDS code C (k = 2, so n - k = 2)
def H_matrix : Matrix (Fin 2) (Fin 4) F :=
  ![![1, 0, 1, 1],
    ![0, 1, 1, 2]]

-- A codeword is in C if its syndrome is zero
-- `abbrev` (reducible) so `decide` can see through to the decidable matrix equation.
abbrev C (x : Fin 4 → F) : Prop :=
  Matrix.mulVec H_matrix x = 0

instance (x : Fin 4 → F) : Decidable (C x) :=
  inferInstanceAs (Decidable (Matrix.mulVec H_matrix x = 0))

-- The bundle is defined by u0 and u1
def u0 : Fin 4 → F := ![0, 1, 0, 0]
def u1 : Fin 4 → F := ![1, 0, 0, 0]

-- The closest codewords for each γ ∈ GF(3)
def w0 : Fin 4 → F := ![0, 0, 0, 0]
def w1 : Fin 4 → F := ![1, 1, 2, 0]
def w2 : Fin 4 → F := ![2, 1, 0, 1]

def w (γ : F) : Fin 4 → F :=
  if γ = 0 then w0 else if γ = 1 then w1 else w2

-- The corresponding error vectors
def e0 : Fin 4 → F := ![0, 1, 0, 0]
def e1 : Fin 4 → F := ![0, 0, 1, 0]
def e2 : Fin 4 → F := ![0, 0, 0, 2]

def e (γ : F) : Fin 4 → F :=
  if γ = 0 then e0 else if γ = 1 then e1 else e2

-- Prove they are valid codewords
lemma w_in_C : ∀ (γ : F), C (w γ) := by decide

-- Prove e_gamma is the difference
lemma e_eq : ∀ (γ : F), e γ = u0 + γ • u1 - w γ := by decide

-- Weight metric
def weight (x : Fin 4 → F) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

-- Prove the bundle is 1-close to C
lemma e_weight_le_one : ∀ (γ : F), weight (e γ) ≤ 1 := by decide

def support (x : Fin 4 → F) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => x i ≠ 0)

--------------------------------------------------------------------------------
-- H13 (Support Union Bound): The size of the union of the supports of the
-- errors for all γ is strictly bounded by n - k (which is 2).
--------------------------------------------------------------------------------
def union_support : Finset (Fin 4) :=
  support e0 ∪ support e1 ∪ support e2

theorem refutation_H13 : ¬(union_support.card < 2) := by decide

--------------------------------------------------------------------------------
-- H14 (Subset Support): For any two γ1, γ2, the error support of one is
-- a subset of the other.
--------------------------------------------------------------------------------
theorem refutation_H14 : ¬(∀ γ1 γ2 : F, support (e γ1) ⊆ support (e γ2) ∨ support (e γ2) ⊆ support (e γ1)) := by decide

--------------------------------------------------------------------------------
-- H16 (Punctured Code Clustering): Removing the common error support from the
-- code preserves the clustering property (i.e. makes all w_γ equal).
-- The common support is empty, so punctured code is unchanged.
-- We show they still don't cluster.
--------------------------------------------------------------------------------
def common_support : Finset (Fin 4) :=
  support e0 ∩ support e1 ∩ support e2

theorem refutation_H16 : common_support = ∅ ∧ w 0 ≠ w 1 := by decide

--------------------------------------------------------------------------------
-- H17 (Sparse Basis): The errors can be represented as a sparse linear
-- combination of basis vectors (i.e. their span dimension is ≤ n - k).
-- We show the 3 errors are linearly independent, so dim(span) = 3 > 2.
--------------------------------------------------------------------------------
theorem refutation_H17 : ∀ (c0 c1 c2 : F), c0 • e0 + c1 • e1 + c2 • e2 = 0 → c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by decide

--------------------------------------------------------------------------------
-- H20 (Zero-Sum Error): The sum of all errors ∑ γ e_γ is exactly the zero vector.
--------------------------------------------------------------------------------
def sum_e : Fin 4 → F := e 0 + e 1 + e 2

theorem refutation_H20 : sum_e ≠ 0 := by decide

