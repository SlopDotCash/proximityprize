import Mathlib.LinearAlgebra.Lagrange

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- H30: Any vector must agree with some codeword on `k` coordinates.
    Since we can interpolate on any set `S` of size `k`, there is always
    a polynomial of degree `< k` matching those `k` points. -/
theorem h30_agreement_lower_bound (f : F → F) (S : Finset F) :
    ∃ p : Polynomial F, p.degree < (S.card : WithBot ℕ) ∧ ∀ x ∈ S, p.eval x = f x := by
  classical
  use Lagrange.interpolate S id f
  constructor
  · exact Lagrange.degree_interpolate_lt f (fun _ _ _ _ h => h)
  · intro x hx
    exact Lagrange.eval_interpolate_at_node f (fun _ _ _ _ h => h) hx
