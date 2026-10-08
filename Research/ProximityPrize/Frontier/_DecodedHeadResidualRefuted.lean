/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under MIT and Apache 2.0 licenses.
Authors: Mikhail (mashingaan)
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import Research.ProximityPrize.Frontier._SecondDescentStuckResidualRefuted

/-!
# A decoded two-monomial head exceeds the second-descent root cap

Over GF(17), on the 16 nonzero domain elements, the polynomial
`X^12 + 3*X^10` is within relative distance 7/16 of the degree-less-than-8
Reed-Solomon code. Its tail has degree less than 8. After antipodal splitting,
seven isolated square nodes satisfy the residual root equation, exceeding
`k+1 = 5` for `k = 4`.

This strengthens the unrestricted refutation with a genuine decoded head and
an explicit ReedSolomon.code distance witness. It rules out repairing this
universal cap using only decodedness and a two-monomial head. It does not
assert that every additional production restriction holds, refute the prize
threshold, or transfer this finite-field witness to the production regime.
-/
set_option autoImplicit false
open Polynomial
namespace ProximityGap.Frontier.DecodedHeadResidualRefuted
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def tail : (ZMod 17)[X] :=
  C 9 + C 8 * X + C 8 * X^2 + C 15 * X^3 + C 14 * X^4 +
    C 6 * X^5 + C 6 * X^6 + C 6 * X^7

def head : (ZMod 17)[X] := X^12 + C 3 * X^10

def evenPart : (ZMod 17)[X] :=
  -C 9 - C 8 * X - C 14 * X^2 - C 6 * X^3 + C 3 * X^5 + X^6

def oddPart : (ZMod 17)[X] := C 8 + C 15 * X + C 6 * X^2 + C 6 * X^3

def roots : Finset (ZMod 17) := {1,2,3,4,5,6,7,8,9}
def squares : Finset (ZMod 17) := {1,2,4,8,9,15,16}

theorem split_identity : head - tail = evenPart.comp (X^2) - X * oddPart.comp (X^2) := by
  simp [head, tail, evenPart, oddPart]
  ring

theorem tail_degree : tail.natDegree < 8 := by
  have h : tail.natDegree ≤ 7 := by
    unfold tail
    compute_degree
  omega

theorem roots_spec (x : ZMod 17) (hx : x ∈ roots) :
    (head - tail).IsRoot x ∧ x^16 = 1 := by
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [IsRoot, head, tail]
  all_goals decide

theorem roots_card : roots.card = 9 := by
  norm_num [roots]
  decide

theorem squares_spec (x : ZMod 17) (hx : x ∈ squares) :
    (evenPart^2 - X * oddPart^2).IsRoot x ∧ oddPart.eval x ≠ 0 ∧ x^8 = 1 := by
  simp only [squares, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [IsRoot, evenPart, oddPart]
  all_goals decide

theorem squares_card : squares.card = 7 := by
  norm_num [squares]
  decide

def isolated : Finset (ZMod 17) := {1,2,3,4,5,6,7}

theorem isolated_spec (x : ZMod 17) (hx : x ∈ isolated) :
    (head - tail).IsRoot x ∧ ¬ (head - tail).IsRoot (-x) := by
  simp only [isolated, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [IsRoot, head, tail]
  all_goals decide

theorem even_degree : evenPart.natDegree < 8 := by
  have h : evenPart.natDegree ≤ 6 := by
    unfold evenPart
    compute_degree
  omega

theorem odd_degree : oddPart.natDegree < 4 := by
  have h : oddPart.natDegree ≤ 3 := by
    unfold oddPart
    compute_degree
  omega

#print axioms isolated_spec
#print axioms even_degree
#print axioms odd_degree
def domain : Fin 16 ↪ ZMod 17 where
  toFun i := (i.val + 1 : ℕ)
  inj' := by decide

def headWord : Fin 16 → ZMod 17 := fun i => head.eval (domain i)
def tailWord : Fin 16 → ZMod 17 := fun i => tail.eval (domain i)

theorem tailWord_mem : tailWord ∈ ReedSolomon.code domain 8 := by
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval tail tail_degree
  intro i
  rfl

theorem disagreement_set :
    Finset.univ.filter (fun i : Fin 16 => headWord i ≠ tailWord i) =
      {9,10,11,12,13,14,15} := by
  ext i
  fin_cases i
  all_goals norm_num [headWord, tailWord, domain, head, tail]
  all_goals decide

theorem hamming_exact : hammingDist headWord tailWord = 7 := by
  unfold hammingDist
  rw [disagreement_set]
  decide

theorem relative_distance_exact : Code.relHammingDist headWord tailWord = 7 / 16 := by
  norm_num [Code.relHammingDist, hamming_exact]

theorem decoded_distance_le :
    Code.relDistFromCode headWord (ReedSolomon.code domain 8 : Set (Fin 16 → ZMod 17)) ≤
      ((7 / 16 : ℚ≥0) : ENNReal) := by
  have h := Code.relDistFromCode_le_relDist_to_mem headWord tailWord tailWord_mem
  simpa [relative_distance_exact] using h

theorem not_residual_four :
    ¬ ProximityGap.Frontier.SecondDescentParity.SecondDescentStuckResidual (ZMod 17) 4 := by
  intro h
  have hcap := h evenPart oddPart even_degree odd_degree squares (fun x hx =>
    ⟨(squares_spec x hx).1, (squares_spec x hx).2.1⟩)
  rw [squares_card] at hcap
  omega

#print axioms not_residual_four

#print axioms hamming_exact
#print axioms relative_distance_exact
#print axioms decoded_distance_le
#print axioms tailWord_mem
#print axioms disagreement_set
#print axioms split_identity
#print axioms tail_degree
#print axioms roots_spec
#print axioms roots_card
#print axioms squares_spec
#print axioms squares_card
end
end ProximityGap.Frontier.DecodedHeadResidualRefuted
