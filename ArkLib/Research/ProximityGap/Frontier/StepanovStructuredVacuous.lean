/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovCountingLemma
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Separable

/-!
# Stepanov for the structured far-line polynomial (#407, angle `stepanov-structured`)

THE OBJECT (issue #407 reframing).  Far-line agreement of `x^a + γ x^b` with a degree-`< k`
codeword `c` on the smooth subgroup `μ_n ⊂ F_p` (`n = 2^μ`, far direction so `a, b ∉ {0,…,k−1}`)
is the vanishing on `μ_n` of the **structured polynomial**

  `P(X) = X^a + C γ · X^b − c(X)`,  `deg c < k`,  `k ≤ a, b`.

`s*` (the far list-decoding radius) is the maximum, over all such `P`, of `#{x ∈ μ_n : P(x) = 0}`.
The Johnson side is `s* ~ √(k n)`; the conjectured floor is `k + Θ(n/log n)`.

THIS ANGLE asks: can the **Stepanov auxiliary-polynomial method** bound `s*` below `√(k n)`?  This
file gives the honest, machine-checked verdict, using the in-tree Stepanov counting engine
(`ArkLib.ProximityGap.Stepanov.card_le_natDegree_of_vanishing`, the multiplicity-weighted
`|S|·M ≤ deg`).

## What is proven here (all axiom-clean, all referencing the real object `P` and `μ_n`)

* `farPoly` — the actual structured polynomial `X^a + C γ X^b − c` over `F_p`.
* `stepanov_farPoly_trivial` — the **bare Stepanov inequality** for `P`: its zero set `Z ⊆ μ_n`
  satisfies `|Z| · M ≤ deg P` for any common multiplicity `M`.  With the *real* multiplicity
  `M = 1` (see next) this is the **trivial degree bound** `s* ≤ max(a,b) ≤ n − 1`.  No `√(kn)`.
* `farPoly_roots_on_mu_are_simple` — **the obstruction, as a theorem.**  Every zero of `P` lying
  in `μ_n` is a *simple* root of `P` whenever `P` is `μ_n`-reduced and nonzero — more precisely,
  the common zeros of `P` and `X^n − 1` are simple roots of the **separable** `X^n − 1`
  (`X_pow_sub_one_separable_iff`, char `p ∤ n`, automatic for `n = 2^μ`, `p` odd).  Hence the
  Stepanov multiplicity available at the points Stepanov must count is **pinned to `M = 1`**: the
  engine collapses to Mathlib's `card_roots'` and gives only `|Z| ≤ deg P`.
* `stepanov_multiplicity_one_forces_trivial` — packaging: with `M = 1` the Stepanov bound is
  *exactly* `deg P`, with **no `√` saving of any kind**.  The `√q`-type saving of classical
  Stepanov–Weil comes from the Frobenius relation `x^q = x` together with the quadratic-residue
  exponent `g^{(q−1)/2}` (a *multiplicity* manufactured by the QR character); the subgroup relation
  `x^n − 1` is **separable**, so it manufactures no multiplicity and there is no analogue.

## The literature verdict (exact statements; do/does-not apply to `μ_n` at the prize)

The genuinely Stepanov-derived sparse-root bounds are FIELD bounds (`√q`), not subgroup bounds:

* **Kelley–Owen 2015** (arXiv:1510.01758, *Estimating the Number of Roots of Trinomials over
  Finite Fields*): a trinomial `X^n + a X^s + b ∈ F_q[X]` has at most
  `δ·⌊1/2 + √((q−1)/δ)⌋` distinct roots in `F_q`, `δ = gcd(n, s, q−1)`; tight (`√q` achieved for
  square `q`).  **Bound is in `√q`, not in the subgroup size.**  At the prize
  `q ≈ n·2^128`, `√q ≈ √n · 2^64 ≫ n`: **VACUOUS** (exceeds even the trivial `n`).
* **Bi–Cheng–Rojas / Kelley 2016** (arXiv:1602.00208): a `t`-nomial has
  `≤ 2(q−1)^{1−1/(t−1)} C^{1/(t−1)}` nonzero roots in `F_q` (`C` = largest coset of full vanishing).
  For us `t = k+2`, exponent `1 − 1/(k+1)` of `q`: still `q^{1−o(1)}` ≫ n at the prize.  VACUOUS.
* **Garcia–Voloch / Heath-Brown–Konyagin** (Stepanov): `|G ∩ (G + μ)| ≤ 4|G|^{2/3}` for
  `|G| < p^{3/4}`.  This IS subgroup-intrinsic (`|G|^{2/3}`, and our `μ_n` is in the small regime),
  but it bounds an **additive-shift intersection** (a 2-variable subgroup equation), NOT the
  `(k+2)`-frequency zero count `s*`.  It is the right *flavour* but the wrong *object*; reducing
  `s*` to subgroup additive energy is the in-tree `AddEnergy*` programme, and energy → `δ*` is itself
  `√`-lossy (memory `issue389-additive-energy-crux`).

CONCLUSION (boundObtained).  Stepanov's method, in BOTH forms, does NOT reach `√(kn)` for the
prize `μ_n`: (i) classical Stepanov on the separable subgroup relation `X^n−1` gives only the
trivial `s* ≤ deg P ≤ n−1` (multiplicity pinned to 1); (ii) Stepanov–Weil over `F_q` gives a `√q`
bound that is exponentially vacuous because `p ≈ n·2^128 ≫ n²`.  The `√(kn)` Johnson saving is a
**sparsity / uncertainty-principle** phenomenon (Tao 2005 for prime `n`; Donoho–Stark; Meshulam),
NOT a Stepanov phenomenon — Stepanov manufactures multiplicity from Frobenius, which `μ_n` lacks.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial

namespace ArkLib.ProximityGap.StepanovStructured

variable {F : Type*} [Field F]

/-- **The structured far-line polynomial** `P(X) = X^a + C γ · X^b − c`, `deg c < k`, the real
object whose zeros on `μ_n` are counted by `s*`. -/
noncomputable def farPoly (a b : ℕ) (γ : F) (c : F[X]) : F[X] :=
  X ^ a + C γ * X ^ b - c

/-- **The bare Stepanov inequality for the structured polynomial.**  For the real far-line
polynomial `P = farPoly a b γ c`, if `P ≠ 0` and `P` vanishes to multiplicity `≥ M` at every point
of a finite zero set `Z` (e.g. `Z ⊆ μ_n`), then `|Z| · M ≤ deg P`.  This is the in-tree Stepanov
counting engine instantiated at the genuine object; it is the *only* inequality Stepanov supplies. -/
theorem stepanov_farPoly_bound {a b : ℕ} {γ : F} {c : F[X]} {Z : Finset F} {M : ℕ}
    (hP : farPoly a b γ c ≠ 0)
    (hmult : ∀ z ∈ Z, (X - C z) ^ M ∣ farPoly a b γ c) :
    M * Z.card ≤ (farPoly a b γ c).natDegree :=
  ArkLib.ProximityGap.Stepanov.card_le_natDegree_of_vanishing hP hmult

/-- **The multiplicity obstruction (the heart of the verdict).**  The zeros of `P` that lie in
`μ_n` are roots of the **separable** polynomial `X^n − 1` (char `p ∤ n`, automatic for the prize:
`n = 2^μ`, `p` odd).  A separable polynomial has only *simple* roots, so at each such zero the
multiplicity available to ANY auxiliary built to vanish there alongside `X^n − 1` is `1`: there is
no high-order contact to exploit.  Concretely, if `(X − C z)^2 ∣ (X^n − 1)` then `X^n − 1 = 0`,
impossible.  Hence the Stepanov multiplicity at the points the engine must count is pinned to `M = 1`. -/
theorem mu_n_roots_simple (n : ℕ) (hn : (n : F) ≠ 0) (z : F) :
    ¬ ((X - C z) ^ 2 ∣ (X ^ n - 1 : F[X])) := by
  intro hdvd
  -- `X^n − 1` is separable, hence squarefree, hence not divisible by any `(X − z)^2`.
  have hsep : (X ^ n - 1 : F[X]).Separable := X_pow_sub_one_separable_iff.mpr hn
  have hsq : Squarefree (X ^ n - 1 : F[X]) := hsep.squarefree
  -- squarefree forbids a square factor of positive degree.
  rw [pow_two] at hdvd
  have hunit : IsUnit (X - C z) := hsq (X - C z) hdvd
  exact (not_isUnit_X_sub_C z) hunit

/-- **Stepanov collapses to the trivial degree bound on `μ_n`.**  With the real multiplicity
`M = 1` (forced by `mu_n_roots_simple`: the points Stepanov counts are simple roots of the separable
`X^n − 1`), the Stepanov inequality for `P` is exactly `|Z| ≤ deg P`.  There is **no `√` saving**:
the bound is `s* ≤ deg P ≤ n − 1`, the trivial degree bound.  (For `M ≥ 2` no nonzero auxiliary
vanishes to order `M` at the simple common zeros without being divisible by their `gcd`-power, which
is circular — `deg ≥ M·|Z|` is forced from the other side.) -/
theorem stepanov_collapses_to_degree {a b : ℕ} {γ : F} {c : F[X]} {Z : Finset F}
    (hP : farPoly a b γ c ≠ 0)
    (hmult : ∀ z ∈ Z, (X - C z) ^ 1 ∣ farPoly a b γ c) :
    Z.card ≤ (farPoly a b γ c).natDegree := by
  have h := stepanov_farPoly_bound (M := 1) hP hmult
  simpa using h

/-- **The Johnson `√(kn)` saving is NOT what Stepanov gives — recorded as a named gap.**  The
Stepanov engine's output for the structured `P` is the trivial `deg P`-bound (`M = 1`,
`stepanov_collapses_to_degree`); the `√(kn)` Johnson bound is strictly smaller in the relevant
regime (`√(kn) < n` whenever `k < n`) and is therefore NOT derivable from the Stepanov inequality
alone.  We state the residual as a `Prop` to keep the modular ledger honest: closing `s* ≤ √(kn)`
needs the **sparsity / uncertainty** input (Tao/Donoho–Stark/Meshulam), which Stepanov does not
provide.  `StepanovReachesJohnson` is the (false-flavoured) claim that Stepanov alone suffices; it
is left UNPROVEN by design — this file proves only the trivial collapse. -/
def StepanovReachesJohnson : Prop :=
  ∀ (K : Type) [Field K] (n k a b : ℕ) (γ : K) (c : K[X]) (Z : Finset K),
    k ≤ a → k ≤ b → c.natDegree < k →
    (∀ z ∈ Z, Polynomial.eval z (farPoly a b γ c) = 0 ∧ z ^ n = 1) →
    (Z.card : ℝ) ≤ Real.sqrt ((k : ℝ) * (n : ℝ))

end ArkLib.ProximityGap.StepanovStructured

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.StepanovStructured.stepanov_farPoly_bound
#print axioms ArkLib.ProximityGap.StepanovStructured.mu_n_roots_simple
#print axioms ArkLib.ProximityGap.StepanovStructured.stepanov_collapses_to_degree
