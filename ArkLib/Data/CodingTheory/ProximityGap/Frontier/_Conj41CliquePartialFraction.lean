/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange

/-!
# The clique partial-fraction identity behind the Conjecture 41 counterexample (#444)

ePrint 2026/858 (Chai–Fan), Conjecture 41 ("Open-Set Rank Lemma", §7.6) asserts a **universal
worst-case** list-size bound `max_{s₁,s₂} M_true(s₁,s₂) ≤ ⌊(2D−1)/c⌋` (`c ≥ 3`, `D = n−k`,
`w = D − c`).  A `ℚ`-exact counterexample (verified in
`scripts/probes/probe_conj41_exact_Q_proof.py` and
`scripts/probes/probe_conj41_clique_counterexample.py`) is the **`(w+1)`-clique line**: for the
clique support `S = {a₀,…,a_w}` (distinct nodes), the `w+1` punctured supports `Eᵢ = S \ {aᵢ}`
are simultaneously decodable, giving `M_true = w+1 > ⌊(2D−1)/c⌋` at the paper's exact Remark-42
parameters (`n20,c5: 6>3`; `n24,c5: 8>4`; `n28,c6: 9>4`).

This counterexample is **off the prize critical path** — it refines `OP2`, leaving `δ*` and the
FRI-soundness theorem untouched — but it is a genuine novel result whose mechanism is
*characteristic-0*, hence robust mod every large prime.

## The load-bearing identity (extracted from the probes)

The mechanism that makes the clique rank-deficient over `ℚ` (hence at all large `p`, not a small-`p`
artifact) is the **Lagrange partition-of-unity / partial-fraction identity**.  Write, for distinct
nodes `S = {a₀,…,a_w}`:

* `Λ_S(x)  = ∏_j (x − a_j)`                              (the nodal polynomial, `degree w+1`);
* `Λ_{Eᵢ}(x) = ∏_{j≠i} (x − a_j) = Λ_S(x)/(x − aᵢ)`     (the cofactor / punctured support, `degree w`);
* `Λ_S′(aᵢ) = Λ_{Eᵢ}(aᵢ) = ∏_{j≠i} (aᵢ − a_j)`          (the derivative at the node).

Then the load-bearing fact is the **polynomial identity**

> `Σ_{i=0}^{w} Λ_{Eᵢ}(x) / Λ_S′(aᵢ) = 1`     (the constant polynomial `1`).

Equivalently, in power-sum / residue form (the form that directly produces the linear dependence
among the `Λ_{Eᵢ}` rows used to build the rank-deficient matrix `A = stack[N_{Eᵢ} ∣ γᵢ N_{Eᵢ}]`):

> `Σ_{i=0}^{w} aᵢ^r / Λ_S′(aᵢ) = 0`  for `0 ≤ r < w`,  and  `= 1`  for `r = w`.

Both are verified over `ℚ` in exact `Fraction` arithmetic in the probes.  The polynomial form is the
*strong* statement: it exhibits the constant `1` as a `ℚ`-linear combination of the `degree-w`
polynomials `Λ_{Eᵢ}`, which is precisely the source of the rank drop the counterexample exploits.

## What this file proves

The identity above is **Lagrange interpolation of the constant function `1`**, and is already
available in Mathlib as `Lagrange.sum_basis` once we recognize that

> `Lagrange.basis s v i = C (Λ_S′(aᵢ))⁻¹ · Λ_{Eᵢ}`

via `Lagrange.basis_eq_prod_sub_inv_mul_nodal_div` (`nodalWeight s v i = (Λ_S′(aᵢ))⁻¹`,
`nodal (s.erase i) v = Λ_{Eᵢ}`).  This file:

1. names the explicit clique objects (`nodalS`, `cofactor`, `derivAtNode`) in terms of Mathlib's
   `Lagrange.nodal` / `Lagrange.nodalWeight`;
2. proves the bridge `cliqueBasis_eq` : the `i`-th Lagrange basis polynomial is the normalized
   cofactor `(Λ_S′(aᵢ))⁻¹ • Λ_{Eᵢ}`;
3. proves the **polynomial identity** `clique_partialFraction_poly`:
   `Σ_i (Λ_S′(aᵢ))⁻¹ • Λ_{Eᵢ} = 1`;
4. derives the **scalar evaluation corollary** `clique_partialFraction_eval`:
   `Σ_i (Λ_S′(aᵢ))⁻¹ · Λ_{Eᵢ}(aⱼ) = 1` for every node `aⱼ` (the per-node residue);
5. derives the **power-sum / residue identity** `clique_powerSum_residue`:
   `Σ_i aᵢ^r / Λ_S′(aᵢ) = 0` for `r < w` and `= 1` for `r = w` (`w = #S − 1`).

All statements are over an arbitrary `Field F` (so they specialize to `ℚ` and to every `F_p` with
`p` large; the characteristic-0 robustness the probes claim is exactly the absence of any
characteristic hypothesis here).  **No `sorry`, axiom-clean** (verified by `pg-iterate`).

## References
- [CF26] Chai, Fan. *(ePrint 2026/858)*, Conjecture 41 / Open-Set Rank Lemma (§7.6, Remark 42). #444.
- Mathlib `Mathlib/LinearAlgebra/Lagrange.lean` — `nodal`, `nodalWeight`, `Lagrange.basis`,
  `Lagrange.sum_basis`, `Lagrange.basis_eq_prod_sub_inv_mul_nodal_div`.
- Probes: `scripts/probes/probe_conj41_exact_Q_proof.py`,
  `scripts/probes/probe_conj41_clique_counterexample.py` (mechanism in `ℚ`).
-/

namespace ProximityGap.Frontier.Conj41Clique

open Polynomial Finset Lagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable (s : Finset ι) (v : ι → F)

/-- The clique nodal polynomial `Λ_S(x) = ∏_{j∈s} (x − v j)`. -/
noncomputable def nodalS : F[X] := Lagrange.nodal s v

/-- The punctured cofactor `Λ_{Eᵢ}(x) = ∏_{j∈s, j≠i} (x − v j) = Λ_S(x)/(x − v i)`,
the error-locator for the support `Eᵢ = S \ {i}`. -/
noncomputable def cofactor (i : ι) : F[X] := Lagrange.nodal (s.erase i) v

/-- The derivative of the clique nodal polynomial evaluated at the node `v i`,
`Λ_S′(v i) = ∏_{j∈s, j≠i} (v i − v j)`.  Equal to `Λ_{Eᵢ}(v i)`. -/
noncomputable def derivAtNode (i : ι) : F := ∏ j ∈ s.erase i, (v i - v j)

/-- `derivAtNode` is indeed `eval (v i) (Λ_S′)` — i.e. the genuine derivative-at-node, matching the
probes' `Λ_S′(aᵢ)`. -/
theorem derivAtNode_eq_eval_derivative {i : ι} (hi : i ∈ s) :
    derivAtNode s v i = eval (v i) (derivative (Lagrange.nodal s v)) := by
  rw [derivAtNode, eval_nodal_derivative_eval_node_eq hi, eval_nodal]

/-- `derivAtNode` is `Λ_{Eᵢ}(v i) = eval (v i) (cofactor)`. -/
theorem derivAtNode_eq_eval_cofactor (i : ι) :
    derivAtNode s v i = eval (v i) (cofactor s v i) := by
  rw [derivAtNode, cofactor, eval_nodal]

/-- `derivAtNode s v i = (nodalWeight s v i)⁻¹`: the Mathlib nodal weight is exactly
`(Λ_S′(aᵢ))⁻¹`. -/
theorem derivAtNode_eq_inv_nodalWeight (i : ι) :
    derivAtNode s v i = (nodalWeight s v i)⁻¹ := by
  rw [derivAtNode, nodalWeight, prod_inv_distrib, inv_inv]

/-- `derivAtNode s v i ≠ 0` when `v` is injective on `s` and `i ∈ s` (distinct nodes). -/
theorem derivAtNode_ne_zero (hvs : Set.InjOn v s) {i : ι} (hi : i ∈ s) :
    derivAtNode s v i ≠ 0 := by
  rw [derivAtNode_eq_inv_nodalWeight]
  exact inv_ne_zero (nodalWeight_ne_zero hvs hi)

/-- **Bridge to Mathlib's Lagrange basis.**  The `i`-th Lagrange basis polynomial is the
*normalized cofactor* `(Λ_S′(aᵢ))⁻¹ • Λ_{Eᵢ}`.  This is the explicit form of the clique
basis polynomials underlying the counterexample. -/
theorem cliqueBasis_eq {i : ι} (hi : i ∈ s) :
    Lagrange.basis s v i = C (derivAtNode s v i)⁻¹ * cofactor s v i := by
  rw [basis_eq_prod_sub_inv_mul_nodal_div hi, cofactor,
    nodal_erase_eq_nodal_div hi, derivAtNode_eq_inv_nodalWeight, inv_inv]

/-- **The load-bearing partial-fraction identity (polynomial form).**

For distinct nodes `S = {aⱼ}_{j∈s}`, the normalized cofactors sum to the constant polynomial `1`:

`Σ_{i∈s} (Λ_S′(aᵢ))⁻¹ • Λ_{Eᵢ}(x) = 1`.

This is the Lagrange partition of unity (`= Lagrange.sum_basis`), and is the characteristic-free
algebraic kernel of the Conj 41 `(w+1)`-clique counterexample: it exhibits the constant `1` as a
linear combination of the `degree-w` cofactors `Λ_{Eᵢ}`, the rank dependence the construction
exploits. -/
theorem clique_partialFraction_poly (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ∑ i ∈ s, C (derivAtNode s v i)⁻¹ * cofactor s v i = 1 := by
  rw [← Lagrange.sum_basis hvs hs]
  exact Finset.sum_congr rfl fun i hi => (cliqueBasis_eq s v hi).symm

/-- **Scalar evaluation corollary (per-node residue form).**

Evaluating the partial-fraction identity at any point `v j` gives `1`.  At a node (`j ∈ s`),
`Λ_{Eᵢ}(v j) = 0` for `i ≠ j` and `= Λ_S′(v j)` for `i = j`, so the sum collapses to the single
surviving term — this is the scalar form `Σᵢ Λ_{Eᵢ}(aⱼ)/Λ_S′(aᵢ) = 1` recorded in the probes. -/
theorem clique_partialFraction_eval (hvs : Set.InjOn v s) (hs : s.Nonempty) (j : ι) :
    ∑ i ∈ s, (derivAtNode s v i)⁻¹ * eval (v j) (cofactor s v i) = 1 := by
  have h := congrArg (eval (v j)) (clique_partialFraction_poly s v hvs hs)
  rw [eval_finset_sum, eval_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]

/-- **Power-sum / residue identity.**

For distinct nodes and `0 ≤ r < #s` (i.e. `r ≤ w` with `w = #s − 1`), the residue sum of
`x^r / Λ_S(x)`:

`Σ_{i∈s} (v i)^r / Λ_S′(v i) = 0`  if `r < #s − 1`,  and  `= 1`  if `r = #s − 1`.

This is the direct power-sum form the probes verify (`r < w → 0`, `r = w → 1`, with `w = #s − 1`).
It is `Lagrange.coeff_eq_sum` specialized to the monomial `P = X^r`: the residue sum equals
`(X^r).coeff (#s − 1)`, which is `1` exactly when `r = #s − 1` and `0` otherwise.

(The hypothesis `r < #s` is essential and matches the probes' verified range: for `r ≥ #s` the
power sum is a genuine higher power-sum, generally nonzero — e.g. `r = w+1` gives the elementary
symmetric data, not `0`.) -/
theorem clique_powerSum_residue (hvs : Set.InjOn v s) {r : ℕ} (hr : r < #s) :
    ∑ i ∈ s, (v i) ^ r / derivAtNode s v i =
      if r = #s - 1 then 1 else 0 := by
  -- `derivAtNode s v i = ∏ j ∈ s.erase i, (v i − v j)`, the denominator in `coeff_eq_sum`.
  have hdeg : (X ^ r : F[X]).degree < #s := by
    rw [degree_X_pow]; exact_mod_cast hr
  have hcoeff := Lagrange.coeff_eq_sum (P := (X ^ r : F[X])) hvs hdeg
  -- RHS of `coeff_eq_sum` is exactly our residue sum (eval (v i) (X^r) = (v i)^r).
  have hsum : ∑ i ∈ s, (v i) ^ r / derivAtNode s v i
      = (X ^ r : F[X]).coeff (#s - 1) := by
    rw [hcoeff]
    exact Finset.sum_congr rfl fun i _ => by rw [derivAtNode, eval_pow, eval_X]
  rw [hsum, coeff_X_pow]
  -- `(if #s-1 = r then 1 else 0) = (if r = #s-1 then 1 else 0)`.
  exact if_congr eq_comm rfl rfl

end ProximityGap.Frontier.Conj41Clique

-- Axiom audit: all four load-bearing results are axiom-clean (no `sorryAx`).
#print axioms ProximityGap.Frontier.Conj41Clique.cliqueBasis_eq
#print axioms ProximityGap.Frontier.Conj41Clique.clique_partialFraction_poly
#print axioms ProximityGap.Frontier.Conj41Clique.clique_partialFraction_eval
#print axioms ProximityGap.Frontier.Conj41Clique.clique_powerSum_residue
