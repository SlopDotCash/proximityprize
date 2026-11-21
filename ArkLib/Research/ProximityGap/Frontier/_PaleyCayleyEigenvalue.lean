/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Additive characters of the generalized Paley Cayley operator

For the graph on the additive group of a prime field with multiplicative connection
set `μ_n`, convolution has the subgroup periods as eigenvalues. An independent upper
bound on the absolute nonprincipal spectrum would therefore bound these periods.
The classical Paley discrepancy conjecture concerns multiplicative character sums
over arbitrary pairs of vertex sets. Its precise statement appears in
Kim–Yip–Yoo, Conjecture 2.12, and the distinction is recorded in
`_wf9B7_PrizeBGKReductionDirections.lean`.

## The math

Fix the additive character `ψ = e_p` over `F_p` and the connection set `G = μ_n` (the order-`n`
multiplicative subgroup). The **Cayley adjacency / convolution operator** is

> `(A f)(y) = Σ_{x∈G} f(y + x)`   (`cayley`).

Adjacency on the abelian Cayley graph `Cay(F, G)` is **diagonalized by the additive characters**.
For each frequency `b ∈ F` the character `χ_b(y) = ψ(b·y)` (`chi`) is an **eigenvector**:

> `cayley_eigenvalue_eq_eta` :  `(A χ_b)(y) = η_b · χ_b(y)`,   `η_b = Σ_{x∈G} ψ(b·x)`.

Proof: `χ_b(y + x) = ψ(b·(y+x)) = ψ(b·y)·ψ(b·x) = χ_b(y)·ψ(b·x)` by additive-character
multiplicativity (`AddChar.map_add_eq_mul`); pulling the `y`-only factor out of the `Σ_{x∈G}` leaves
exactly `η_b`. (Only character additivity is needed — not primitivity of `ψ`.)

For a primitive additive character on a finite field, the **entire spectrum** of `A` is `{η_b : b ∈ F}`. The trivial eigenvalue is at the
principal frequency `b = 0` (where `η_0 = |G| = n`, the graph degree). The **second eigenvalue** is

> `secondEigenvalue ψ G := max_{b≠0} ‖η_b‖`   (`secondEigenvalue`),

which is — verbatim, `rfl` after unfolding — the prize sup-norm `M(n)` (`secondEigenvalue_eq_M`).
`spectralGap_circular` identifies the two expressions for the absolute spectral gap.
Estimating either expression still requires a bound on the largest nonprincipal period.

## References
- Liu–Zhou, *Eigenvalues of Cayley graphs*, for the character description of the spectrum.
- Kim–Yip–Yoo, *Diophantine tuples and multiplicative structure of shifted multiplicative
  subgroups*, [§2.4](https://arxiv.org/html/2309.09124v3#S2.SS4), for classical discrepancy.
- In-tree substrate: `SubgroupGaussSumSecondMoment.eta`, `Frontier/_CoherenceIdentity` (`M`).
-/

set_option linter.style.longLine false


open Finset AddChar

namespace ProximityGap.Frontier.PaleyCayleyEigenvalue

variable {F : Type*} [Field F]

/-- The incomplete subgroup Gauss sum at frequency `b`: `η_b = Σ_{x∈G} ψ(b·x)` (matches the in-tree
`SubgroupGaussSumSecondMoment.eta` and `Frontier/_CoherenceIdentity.eta`). When `G = μ_n` and `b ≠ 0`
its supremum is the prize quantity `M(n)`. -/
noncomputable def eta (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℂ := ∑ x ∈ G, ψ (b * x)

/-- The additive character `χ_b(y) = ψ(b·y)` — the candidate eigenvector at frequency `b`. -/
noncomputable def chi (ψ : AddChar F ℂ) (b : F) : F → ℂ := fun y => ψ (b * y)

/-- The **Cayley adjacency / convolution operator** with connection set `G`:
`(A f)(y) = Σ_{x∈G} f(y + x)`. For `G = μ_n` over `F_p` this is the adjacency operator of the
generalized Paley graph `Cay(F_p, μ_n)` (up to the symmetric-set convention). -/
noncomputable def cayley (ψ : AddChar F ℂ) (G : Finset F) (f : F → ℂ) : F → ℂ :=
  fun y => ∑ x ∈ G, f (y + x)

/-- **The Cayley eigen-equation: `χ_b` is an eigenvector with eigenvalue `η_b`.**

`(A χ_b)(y) = Σ_{x∈G} χ_b(y + x) = Σ_{x∈G} ψ(b·(y+x)) = Σ_{x∈G} ψ(b·y)·ψ(b·x)
            = ψ(b·y) · Σ_{x∈G} ψ(b·x) = η_b · χ_b(y).`

The single load-bearing step is additive-character multiplicativity
`AddChar.map_add_eq_mul`; the rest is pulling the `x`-free factor `χ_b(y)` out of the finite sum.
For a primitive additive character on a finite field, these eigenvectors form the full character basis. -/
theorem cayley_eigenvalue_eq_eta (ψ : AddChar F ℂ) (G : Finset F) (b y : F) :
    cayley ψ G (chi ψ b) y = eta ψ G b * chi ψ b y := by
  unfold cayley chi eta
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  -- χ_b(y + x) = ψ(b·(y+x)) = ψ(b·y + b·x) = ψ(b·y)·ψ(b·x) = ψ(b·x)·χ_b(y)
  -- χ_b(y + x) = ψ(b·(y+x)) = ψ(b·y + b·x) = ψ(b·y)·ψ(b·x), matching the pulled-out factor.
  have harg : b * (y + x) = b * y + b * x := by ring
  rw [harg, AddChar.map_add_eq_mul, mul_comm]

/-- The **principal eigenvalue** sits at frequency `b = 0`: `η_0 = |G|` (the graph degree). The
character `χ_0 ≡ 1` is the constant (trivial) eigenvector, eigenvalue the degree `n = |G|`. -/
theorem eta_zero_eq_degree (ψ : AddChar F ℂ) (G : Finset F) :
    eta ψ G 0 = (G.card : ℂ) := by
  unfold eta
  simp [AddChar.map_zero_eq_one]

variable [Fintype F] [DecidableEq F]

/-- The prize **sup-norm** `M(n) = max_{b≠0}‖η_b‖`, over the (nonempty) nonzero frequencies.
Matches `Frontier/_CoherenceIdentity.M`. -/
noncomputable def M (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) : ℝ :=
  (Finset.univ.filter (fun b : F => b ≠ 0)).sup' hb (fun b => ‖eta ψ G b‖)

/-- The largest period magnitude over nonzero frequencies. For a primitive character
this gives the absolute nonprincipal spectral radius of the Cayley operator. -/
noncomputable def secondEigenvalue (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) : ℝ :=
  (Finset.univ.filter (fun b : F => b ≠ 0)).sup' hb (fun b => ‖eta ψ G b‖)

/-- **`λ₂ = M(n)` definitionally.** The second eigenvalue of the Cayley/Paley operator and the prize
sup-norm are literally the same `Finset.sup'`. -/
theorem secondEigenvalue_eq_M (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) :
    secondEigenvalue ψ G hb = M ψ G hb := rfl

/-- The degree minus the largest period magnitude equals the degree minus the
absolute nonprincipal spectral radius when the base character is primitive. -/
theorem spectralGap_circular (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) :
    -- the (degree − second eigenvalue) spectral gap is exactly (degree − prize sup-norm):
    ((G.card : ℝ) - secondEigenvalue ψ G hb) = ((G.card : ℝ) - M ψ G hb) := by
  rw [secondEigenvalue_eq_M]

/-- Eigenvalue-magnitude packaging: the magnitude of the Cayley eigenvalue at any nonzero frequency
is dominated by `λ₂ = M(n)`. (Sup-bound over the nonzero-frequency index set; the witness side of
`spectralGap_circular`: there is no Cayley eigenvalue magnitude exceeding the prize quantity, so the
prize is *exactly* the spectral radius on the non-principal subspace.) -/
theorem eigenvalue_norm_le_secondEigenvalue (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) {b : F} (hbne : b ≠ 0) :
    ‖eta ψ G b‖ ≤ secondEigenvalue ψ G hb := by
  unfold secondEigenvalue
  refine Finset.le_sup' (fun b => ‖eta ψ G b‖) ?_
  simp [hbne]

end ProximityGap.Frontier.PaleyCayleyEigenvalue

/-! ## Axiom audit — kernel-clean (`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`). -/
#print axioms ProximityGap.Frontier.PaleyCayleyEigenvalue.cayley_eigenvalue_eq_eta
#print axioms ProximityGap.Frontier.PaleyCayleyEigenvalue.eta_zero_eq_degree
#print axioms ProximityGap.Frontier.PaleyCayleyEigenvalue.secondEigenvalue_eq_M
#print axioms ProximityGap.Frontier.PaleyCayleyEigenvalue.spectralGap_circular
#print axioms ProximityGap.Frontier.PaleyCayleyEigenvalue.eigenvalue_norm_le_secondEigenvalue
