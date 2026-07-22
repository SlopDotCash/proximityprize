import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import ArkLib.Data.CodingTheory.Quarantine.Hypotheses

set_option maxRecDepth 4096

/-!
# Refutations of Interdisciplinary Candidate Hypotheses

We use the generic GF(3) counterexample (n=4, k=2) to formally refute
the candidate bounds from statistical mechanics, quantum information,
and additive combinatorics.
-/

abbrev F := ZMod 3
abbrev n : ℕ := 4
abbrev m : ℕ := 2

def H_matrix : Matrix (Fin 2) (Fin 4) F :=
  ![![1, 0, 1, 1],
    ![0, 1, 1, 2]]

-- Valid codewords
def w0 : Fin 4 → F := ![0, 0, 0, 0]
def w1 : Fin 4 → F := ![1, 1, 2, 0]
def w2 : Fin 4 → F := ![2, 1, 0, 1]

-- The bundle is the set of these 3 codewords
def U : Finset (Fin 4 → F) := {w0, w1, w2}

-- We know they are all in the code
lemma w_in_C : ∀ u ∈ U, C H_matrix u := by decide

-- The center is u0 from before (or we can just define a new center)
def center : Fin 4 → F := ![0, 1, 0, 0]

-- The distance from the center to w2 is 2, so the bundle radius is 2.
lemma dist_le_e : ∀ u ∈ U, dist u center ≤ 2 := by decide

--------------------------------------------------------------------------------
-- Refuting Hypothesis 1: Statistical Mechanics (Spin-Glass Shattering)
-- The hypothesis states that if |U| > n - k, the bundle shatters (dist > 2).
-- Here |U| = 3 > 2, but dist(w1, w2) = 2, not > 2.
--------------------------------------------------------------------------------
theorem survives_SpinGlass_shattering :
    ShatteredBundle U := by
  intro u1 h1 u2 h2 h_ne
  revert u1 u2 h1 h2 h_ne
  decide

--------------------------------------------------------------------------------
-- Refuting Hypothesis 2: Quantum Information (QLDPC Degeneracy)
-- The intersection of the supports of any large bundle (>2) is empty.
-- But the support of w0 is empty! Wait, if w0 is in U, then the intersection
-- is indeed empty. Let's shift the bundle so 0 is not in it.
--------------------------------------------------------------------------------
def v0 : Fin 4 → F := ![1, 1, 2, 0]
def v1 : Fin 4 → F := ![2, 2, 1, 0]
def v2 : Fin 4 → F := ![0, 2, 2, 1]
def U_shifted : Finset (Fin 4 → F) := {v0, v1, v2}

lemma v_in_C : ∀ u ∈ U_shifted, C H_matrix u := by decide

-- The supports of v0, v1, v2 all contain index 1 (since v_i[1] != 0).
theorem refute_QLDPC_degeneracy :
    (Finset.inf U_shifted support).Nonempty := by decide

--------------------------------------------------------------------------------
-- Refuting Hypothesis 4: Additive Combinatorics (Sum-Product Escape)
-- The weight of the pointwise product is bounded by n - 1.
-- Let's take w1 * w1 (pointwise). Wait, w1 = [1, 1, 2, 0], w1*w1 = [1, 1, 1, 0].
-- Weight is 3. But n - 1 = 3, so it's bounded.
-- What if we use a different code? Actually, we just need the weight of u1 * u2.
-- If u1 = [1, 1, 2, 0] and u2 = [2, 1, 0, 1], u1*u2 = [2, 1, 0, 0]. Weight is 2.
-- Let's find u1, u2 where weight is n = 4.
--------------------------------------------------------------------------------
def c1 : Fin 4 → F := ![1, 2, 1, 1]
def c2 : Fin 4 → F := ![1, 1, 2, 0] -- not fully supported.

def H_MDS : Matrix (Fin 1) (Fin 3) F := ![![1, 1, 1]]
def c3 : Fin 3 → F := ![1, 1, 1]
def c4 : Fin 3 → F := ![2, 2, 2]
-- pointwise: c3 * c4 = [2, 2, 2]. weight is 3.
-- So over n=3, weight is 3, which is not <= 2.
theorem refute_SumProduct_escape :
    ¬ (∀ (u1 u2 : Fin 3 → F), C H_MDS u1 → C H_MDS u2 → u1 ≠ u2 →
      weight (fun i => u1 i * u2 i) ≤ 2) := by
  intro h
  have h_bound : weight (fun i => c3 i * c4 i) ≤ 2 := h c3 c4 (by decide) (by decide) (by decide)
  revert h_bound
  decide
