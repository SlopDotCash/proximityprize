/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.MvPolynomial.Multilinear

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.CharP.Basic

import CompPoly.Data.MvPolynomial.Notation
import ProximityPrize.Extensions.Data.MvPolynomial.Interpolation

/-!
  # Multilinear Polynomials

  This is the special case of polynomial interpolation, when we consider multilinear polynomials and
  evaluation on the hypercube `σ → Fin 2`.
-/

noncomputable section

namespace MvPolynomial

open BigOperators Fintype Finset

universe u

variable {σ : Type*} {R : Type*}

variable [CommRing R]

variable [Fintype σ]

/-- **The equality kernel is symmetric.**  `eqTilde r r' = eqTilde r' r` — immediate from
`eqPolynomial_symm`, recorded directly on `eqTilde`. -/
theorem eqTilde_symm (r r' : σ → R) : eqTilde r r' = eqTilde r' r :=
  eqPolynomial_symm r r'

-- @[simp]
variable [DecidableEq σ]

@[simp]
theorem MLE'_eval_zeroOne {n : ℕ} (x : Fin n → Fin 2) (evals : Fin (2 ^ n) → R) :
    MvPolynomial.eval (x : Fin n → R) (MLE' evals) = evals (finFunctionFinEquiv x) := by
  simp [MLE', MLE_eval_zeroOne]

section DegreeOf

/-- **Total degree of a multilinear polynomial.**  A polynomial with `degreeOf i ≤ 1` in each of
its `|σ|` variables has total degree at most `|σ|` — each monomial's exponents sum over the `≤ 1`
per-variable degrees.  This is the degree fact underlying multilinear Schwartz–Zippel / sum-check
round soundness (a nonzero multilinear polynomial has at most `|σ|/|F|` of its points as zeros). -/
theorem totalDegree_le_card_of_mem_restrictDegree_one {p : MvPolynomial σ R}
    (hp : p ∈ R⦃≤ 1⦄[X σ]) : p.totalDegree ≤ Fintype.card σ := by
  rw [mem_restrictDegree_iff_degreeOf_le] at hp
  apply Finset.sup_le
  intro m hm
  calc (m.sum fun _ e => e)
      = ∑ i ∈ m.support, m i := rfl
    _ ≤ ∑ i : σ, m i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ _i : σ, 1 :=
        Finset.sum_le_sum fun i _ => le_trans (monomial_le_degreeOf i hm) (hp i)
    _ = Fintype.card σ := by simp [Finset.card_univ]

/-- The multilinear extension of any evaluation function has total degree at most `|σ|`. -/
theorem MLE_totalDegree_le (evals : (σ → Fin 2) → R) : (MLE evals).totalDegree ≤ Fintype.card σ :=
  totalDegree_le_card_of_mem_restrictDegree_one (MLE_mem_restrictDegree evals)

end DegreeOf

/-! ### Linearity of the multilinear extension in the evaluation function

`MLE evals = ∑ x, eqPolynomial x * C (evals x)` is manifestly `R`-linear in `evals`.  These
lemmas record additivity, scalar homogeneity, and commutation with finite sums — the algebraic
foundation behind sum-check-style reductions, where the multilinear extension of a *linear
combination* of evaluation vectors (e.g. a matrix-vector product `M *ᵥ z = ∑ⱼ zⱼ • colⱼ`) splits
as the same combination of the column extensions. -/
section Linearity

/-- **MLE is additive in the evaluation function.** -/
theorem MLE_add (f g : (σ → Fin 2) → R) : MLE (f + g) = MLE f + MLE g := by
  unfold MLE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.add_apply, map_add, mul_add]

/-- **MLE is scalar-homogeneous in the evaluation function.** -/
theorem MLE_smul (c : R) (f : (σ → Fin 2) → R) : MLE (c • f) = C c * MLE f := by
  unfold MLE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- **MLE commutes with finite sums of evaluation functions.** -/
theorem MLE_sum {ι : Type*} (s : Finset ι) (f : ι → (σ → Fin 2) → R) :
    MLE (∑ j ∈ s, f j) = ∑ j ∈ s, MLE (f j) := by
  unfold MLE
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_apply, map_sum, Finset.mul_sum]

/-- **Pointwise form of `MLE_sum`.**  The multilinear extension of a pointwise finite sum of
evaluation functions is the sum of their extensions — the shape that arises when an evaluation
vector is written as a linear combination, `evals x = ∑ⱼ g j x`. -/
theorem MLE_sum_pointwise {ι : Type*} (s : Finset ι) (g : ι → (σ → Fin 2) → R) :
    MLE (fun x => ∑ j ∈ s, g j x) = ∑ j ∈ s, MLE (g j) := by
  rw [← MLE_sum]
  congr 1
  funext x
  exact (Finset.sum_apply x s g).symm

/-- **MLE of a scaled-sum (matrix-vector) evaluation vector.**  When the evaluation function is a
linear combination `evals x = ∑ⱼ z j * g j x` (the shape of a matrix-vector product
`(M *ᵥ z) i = ∑ⱼ M i j * z j`, with `g j` the `j`-th column evaluations and `z j` the scalars),
its extension splits as `∑ⱼ z j • MLE (g j)`.  This is the algebraic identity underlying the
sum-check decomposition `MLE(M *ᵥ z)(r) = ∑ⱼ z j · MLE(colⱼ)(r)`. -/
theorem MLE_scaled_sum {ι : Type*} (s : Finset ι) (z : ι → R) (g : ι → (σ → Fin 2) → R) :
    MLE (fun x => ∑ j ∈ s, z j * g j x) = ∑ j ∈ s, C (z j) * MLE (g j) := by
  rw [show (fun x => ∑ j ∈ s, z j * g j x) = ∑ j ∈ s, z j • g j by
        funext x; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => rfl]
  rw [MLE_sum]
  exact Finset.sum_congr rfl fun j _ => MLE_smul (z j) (g j)

/-- **MLE evaluation as an eq-weighted sum over the hypercube.**  Evaluating the multilinear
extension at any point `r` is the `eqTilde`-weighted sum of the hypercube evaluations:
`eval r (MLE f) = ∑_{x ∈ {0,1}^σ} eqTilde r x · f x`, where `eqTilde r x = eval x (eqPolynomial r)`
is the multilinear equality kernel.  This is the fundamental identity underlying sum-check folding
(the general-ring analogue of the specialized `MLE_eval_eq_sum_eqTilde` in `RingSwitching/Prelude`). -/
theorem MLE_eval_eq_sum_eqTilde (f : (σ → Fin 2) → R) (r : σ → R) :
    eval r (MLE f) = ∑ x : σ → Fin 2, eqTilde r (x : σ → R) * f x := by
  unfold MLE
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [eval_mul, eval_C]
  simp only [eqTilde]
  rw [eqPolynomial_symm]

/-- **Evaluation form of `MLE_scaled_sum`.**  Evaluating the multilinear extension of a
matrix-vector evaluation vector at a point `r` splits as the scalar combination of the column
extensions evaluated at `r`:
`eval r (MLE (fun x => ∑ⱼ z j * g j x)) = ∑ⱼ z j * eval r (MLE (g j))`.
This is the directly-usable sum-check decomposition (e.g. Spartan's `evalClaimValue idx`
`= ∑ⱼ 𝕫 j * eval r_x (MLE colⱼ)`). -/
theorem MLE_eval_scaled_sum {ι : Type*} (s : Finset ι) (z : ι → R) (g : ι → (σ → Fin 2) → R)
    (r : σ → R) :
    eval r (MLE (fun x => ∑ j ∈ s, z j * g j x))
      = ∑ j ∈ s, z j * eval r (MLE (g j)) := by
  rw [MLE_scaled_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [eval_mul, eval_C]

end Linearity

-- Note: add lemmas about the uniqueness of multilinear polynomials up to evaluations on hypercube

variable [DecidableEq R] [IsDomain R]

omit [DecidableEq R] in
/-- **Direct uniqueness of the multilinear extension.**  A multilinear polynomial `p` that agrees
with `evals` on the Boolean hypercube *is* the multilinear extension `MLE evals`.  This is the
most directly-usable form of MLE uniqueness: it discharges interpolation arguments where one has
exhibited a multilinear `p` and checked its hypercube values. -/
theorem eq_MLE_of_isMultilinear_of_eval_eq {p : MvPolynomial σ R} (evals : (σ → Fin 2) → R)
    (hp : p ∈ R⦃≤ 1⦄[X σ]) (heval : ∀ x : σ → Fin 2, eval (x : σ → R) p = evals x) :
    p = MLE evals := by
  have hte : p.toEvalsZeroOne = evals := funext heval
  rw [← hte]
  exact (is_multilinear_iff_eq_evals_zeroOne.mp hp).symm

end MvPolynomial

end
