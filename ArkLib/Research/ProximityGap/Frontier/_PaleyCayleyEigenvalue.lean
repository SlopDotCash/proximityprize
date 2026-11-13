/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Cayley / circulant spectral-gap NO-GO (N17) — the prize is the eigenvalue (#407/#444)

**Negative guardrail (exotic-math sweep).** This file proves the route *"bound the prize sup-norm
`M(n) = max_{b≠0}‖η_b‖` by a spectral-gap / Poincaré / log-Sobolev (LSI) constant of the
generalized Paley graph `Cay(F_p, μ_n)`"* is **structurally circular**: that constant *is itself a
function of the prize quantity*. The additive characters are the eigenvectors of the Cayley
adjacency operator, their eigenvalues are exactly the incomplete subgroup character sums `η_b`, and
the second-largest eigenvalue `λ₂` is *by definition* `M(n)`. So any spectral-gap statement
**consumes** `M(n)` as an input; it cannot **produce** the `√(log)` cancellation. It does **not**
close the prize — the `L^∞` / `√(log)` core (the BGK / Paley-graph wall) survives. See #407, #444,
and the ~22-lens + 18-domain exotic sweep (all reduce to BGK).

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

Consequently the **entire spectrum** of `A` is `{η_b : b ∈ F}`. The trivial eigenvalue is at the
principal frequency `b = 0` (where `η_0 = |G| = n`, the graph degree). The **second eigenvalue** is

> `secondEigenvalue ψ G := max_{b≠0} ‖η_b‖`   (`secondEigenvalue`),

which is — verbatim, `rfl` after unfolding — the prize sup-norm `M(n)` (`secondEigenvalue_eq_M`).
Hence (`spectralGap_circular`): `M(n)` and `λ₂` are the **same number**. Any Cheeger / Poincaré /
LSI / mixing-time constant is a function of the spectral gap `n − λ₂`, i.e. a function of `M(n)`;
proving the prize *via* such a constant therefore requires knowing `M(n)` first — circular.

## Honesty (project §6)

This is a **NEGATIVE** brick. The genuine content is the **eigen-equation**
`cayley_eigenvalue_eq_eta` (the additive characters diagonalize the Cayley operator with eigenvalue
the incomplete subgroup sum — exact, axiom-clean) and the definitional identification of `λ₂` with
the prize `M(n)`. It records that the spectral-gap route consumes the prize; it proves nothing about
the size of `M(n)`. The `√(n log(p/n))` core is untouched and OPEN.

## References
- #407 / #444 — the Proximity Prize sup-norm `M(n)` grand challenge.
- The exotic-math sweep (RMT / matrix-Bernstein, pseudospectrum, …): all reduce to BGK.
- Liu–Zhou, *generalized Paley graphs*: `B = max_{b≠0}‖η_b‖` IS the non-principal eigenvalue of
  `Cay(F_q, μ_n)`; `B ≤ 2√n ⟺ Ramanujan` = the (open) Paley Graph Conjecture.
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
This diagonalizes the Cayley operator: the spectrum of `A` is exactly `{η_b : b ∈ F}`, so every
eigenvalue of the Paley graph IS an incomplete subgroup character sum. -/
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

/-- The **second eigenvalue** `λ₂` of the Cayley / Paley adjacency operator: the largest
eigenvalue magnitude over the **non**-principal frequencies `b ≠ 0`. Since the spectrum is
`{η_b}` (`cayley_eigenvalue_eq_eta`) and the principal eigenvalue is at `b = 0`
(`eta_zero_eq_degree`), this is the standard `λ₂` controlling every spectral-gap / mixing constant. -/
noncomputable def secondEigenvalue (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) : ℝ :=
  (Finset.univ.filter (fun b : F => b ≠ 0)).sup' hb (fun b => ‖eta ψ G b‖)

/-- **`λ₂ = M(n)` definitionally.** The second eigenvalue of the Cayley/Paley operator and the prize
sup-norm are literally the same `Finset.sup'`. -/
theorem secondEigenvalue_eq_M (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) :
    secondEigenvalue ψ G hb = M ψ G hb := rfl

/-- **The spectral-gap circularity (N17).** The Cayley / Paley second eigenvalue `λ₂` *equals* the
prize quantity `M(n)`. Any spectral-gap / Poincaré / LSI / mixing-time constant is a function of the
gap `n − λ₂` (degree minus second eigenvalue) = `n − M(n)`; hence proving `M(n) ≤ C√(n log(p/n))`
*via* such a constant first requires knowing `M(n)`. The route **consumes** the prize — it cannot
produce the cancellation. (The principal eigenvalue `η_0 = n` is recorded in `eta_zero_eq_degree`.)

This is the identity at the heart of the no-go: `λ₂` and `M(n)` are not merely comparable, they are
the *same number*, so the spectral gap `n − λ₂` is a relabelling of the prize, not a tool to bound
it. -/
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
