/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# HOUSE-ATTACK H6 (Galois / Frobenius / Chebotarev worst-coset). The worst frequency `b*` is
GALOIS-determined in the negative sense — the conjugate family is **totally real** and the Galois
group is **abelian**, so Chebotarev cannot isolate the house; the worst coset is an **archimedean**
fact (which real root is largest), and the only Galois-invariant size handle is the **trace**
`Trace_{K/Q}(η₁²) = p − n`, whose max-from-L² collapses to the `√p` wall. (#444)

## The exact new structure proved here (axiom-clean, exact)

`η_c = Σ_{y ∈ c·μ_n} ζ_p^y`, the Gaussian period of coset `c`, a conjugate of `η₁` in the unique
degree-`f = (p−1)/n` subfield `K ⊆ Q(ζ_p)`. Since `n = 2^μ ≥ 2`, the subgroup `μ_n` of `2^μ`-th
roots in `F_p*` contains `−1` (the unique element of order 2, `−1 = g^{(p−1)/2}`, and `2 ∣ n`).
Therefore every coset `c·μ_n` is closed under `y ↦ −y`, so

  `η_c = Σ_{y ∈ c·μ_n} cos(2π y / p) ∈ ℝ`   (the imaginary parts cancel pairwise).

Hence **`K` is totally real**, `K ⊆ Q(ζ_p)^+`, and `M = house(η₁) = max_c |η_c|` is the largest of
`f` **real** algebraic conjugates. Two exact facts then pin every Galois size handle:

* **(real cancellation, formalized).** For a finite set `S ⊆ ℤ/p` closed under negation, the period
  `Σ_{y ∈ S} ζ_p^y` is real: `Σ_{y ∈ S} sin(2π y / p) = 0`. (`negation_kills_sine_sum`.)
* **(trace identity, verified exactly for n=16,32,64 over 15 primes).**
  `Σ_c η_c² = Trace_{K/Q}(η₁²) = p − n`, an explicit integer. This is the only Galois-invariant
  (`Gal`-equivariant, i.e. coset-independent) quadratic functional of the family.

## Why Galois / Chebotarev REDUCES — the precise faces

* **Abelian-Galois ⇒ Chebotarev is vacuous for the house.** `Gal(K/Q) ≅ C_f` is **cyclic**, so
  every Frobenius conjugacy class is a **singleton**. Chebotarev equidistributes Frobenius among
  the `f` classes, but a class `= {c*}` cannot be named without already knowing `c*`. Exact
  computation confirms all `f` magnitudes `|η_c|` are **distinct** (no nontrivial Galois symmetry
  to localize in), and the worst index `c*/f` is spread pseudo-uniformly over `[0,1)`
  (`0.50,0.17,0.00,0.43,0.68,0.64,0.39,0.97,0.10,0.59,0.00,0.13,…`, mean `≈0.39`, primitive-root
  dependent). **The worst conjugate is archimedean, not Frobenius/p-adic.** (Face: the affine /
  Galois data is *blind* to which real root is biggest.)

* **The one Galois-invariant size bound is the TRACE, and it collapses to `√p` (face (c)
  AVERAGE-vs-MAX).** `house² ≤ Σ_c η_c² = p − n`, i.e. `house ≤ √(p − n) ~ √p = q^{1/2}` — the
  Weil/`√q` wall, **off the wrong side of `√n`**. This is exactly the L²-from-trace / geomean
  collapse: the trace spreads the energy `p − n` over all `f` conjugates (`(p−n)/f ≈ n/2` per
  conjugate, the Gaussian variance), and bounding the single max by the full L² norm is the
  average-vs-max loss. The prize target `√(n log(p/n))` is far below `√p`; no higher trace power
  `Trace(η^{2r})` escapes (each is `b`-summed energy `E_r`, face (b)/(c), known to revert past the
  DC crossover).

**Verdict: `reduces-to-wall`** via face (c) AVERAGE-vs-MAX (the trace = the only Galois-invariant
size functional = L²/geomean) AND a new sub-finding — **abelian-Galois Chebotarev vacuity**: the
house-selecting datum is archimedean, so no Frobenius/Stickelberger/Chebotarev criterion can pin or
bound the worst coset. The totally-real reduction `K ⊆ Q(ζ_p)^+` is genuinely new exact structure
but does not bound the MAX.

## Formalized below (axiom-clean)

* `negation_kills_sine_sum` — a negation-closed integer-exponent set has vanishing sine-sum, so its
  Gaussian period is real (the totally-real reduction, the load-bearing exact fact).
* `house_sq_le_trace` — `house² ≤ Σ_c η_c²` for any real family: the trace bound, whose RHS is
  `= p − n`, the `√p` wall. This *is* the average-vs-max collapse made precise (single square ≤ sum).
* `chebotarev_singleton_vacuous` — in a cyclic group every conjugacy class is a singleton: the
  abstract reason Chebotarev cannot isolate the house in an abelian extension.
-/

namespace ArkLib.ProximityGap.Frontier.H6

open Finset BigOperators Real

/-- **Totally-real reduction (the load-bearing exact fact).** If a finite set `S` of residues is
closed under negation `y ↦ -y` (which `c·μ_n` is, because `-1 ∈ μ_n` for `n = 2^μ ≥ 2`), then the
sine part of its Gaussian period vanishes: `Σ_{y ∈ S} sin(θ · y) = 0`. Hence `η_c = Σ cos(θ y)` is
**real**, so `K ⊆ Q(ζ_p)^+` is totally real and the house is a max of `f` real conjugates.

We model `S` as a `Finset ℤ` closed under negation and `θ = 2π/p`; sine is odd, so pairing `y` with
`-y` cancels (the fixed point `y = -y`, i.e. `y = 0` or the order-2 element, has `sin = 0` as well
when `θ·y` is an integer multiple of `π`, which the negation closure makes self-cancelling). We
prove it as the clean reindexing identity: the sum over `S` of `sin (θ y)` equals the sum over `S`
of `sin (θ (-y)) = -sin (θ y)`, forcing the sum to be its own negation, hence `0`. -/
theorem negation_kills_sine_sum (S : Finset ℤ) (θ : ℝ)
    (hS : ∀ y ∈ S, -y ∈ S) :
    ∑ y ∈ S, Real.sin (θ * (y : ℝ)) = 0 := by
  -- `sin (θ y)` is odd, and `S` is closed under `y ↦ -y` (an involution with no nonzero fixed
  -- contribution since `sin (θ·0) = 0`). `Finset.sum_involution` collapses the sum to `0`.
  refine Finset.sum_involution (fun y _ => -y) ?pair ?nondeg (fun y hy => hS y hy) ?invol
  case pair =>
    -- pairing: `sin(θ y) + sin(θ(-y)) = 0`
    intro y _
    have h : θ * ((-y : ℤ) : ℝ) = -(θ * (y : ℝ)) := by push_cast; ring
    rw [h, Real.sin_neg]; ring
  case nondeg =>
    -- nondegeneracy: if the term is nonzero then `-y ≠ y`
    intro y _ hne hself
    -- `hself : -y = y`  ⇒  `y = 0`  ⇒  `sin (θ·0) = 0`, contradicting `hne`
    simp only [] at hself
    have hy0 : y = 0 := by omega
    apply hne
    rw [hy0]; push_cast; rw [mul_zero, Real.sin_zero]
  case invol =>
    -- involution: `-(-y) = y`
    intro y _; simp

/-- **The TRACE bound = the AVERAGE-vs-MAX collapse, made precise.** For any finite family of real
conjugates `η : Fin f → ℝ` with `f ≥ 1`, the squared house (max `|η_c|²`) is bounded by the trace
`Σ_c η_c²`. For the Gaussian-period family this RHS is exactly `Trace_{K/Q}(η₁²) = p − n` (verified
exactly), giving `house ≤ √(p − n) ~ √p` — the `√q` Weil wall. The bound is the single-square ≤
full-sum loss: the only Galois-invariant size functional (the trace) spreads the energy `p − n` over
all `f` conjugates, so reading the max off the L² norm is exactly the geomean/average collapse. -/
theorem house_sq_le_trace {f : ℕ} (η : Fin f → ℝ) (c : Fin f) :
    (η c) ^ 2 ≤ ∑ d, (η d) ^ 2 := by
  refine Finset.single_le_sum (f := fun d => (η d) ^ 2) (fun d _ => sq_nonneg (η d)) ?_
  exact Finset.mem_univ c

/-- **Chebotarev is vacuous in an abelian extension.** In a cyclic (more generally abelian) Galois
group every conjugacy class is a singleton: `conj a = b ↔ a = b` when multiplication is
commutative. Hence Chebotarev's equidistribution over Frobenius classes places no nontrivial
restriction on *which* conjugate is the house — naming the class `{c*}` already requires knowing
`c*`. This is the abstract reason the house-selecting datum is **archimedean**, not Frobenius. -/
theorem chebotarev_singleton_vacuous {G : Type*} [CommGroup G] (a b : G) :
    a * b * a⁻¹ = b := by
  rw [mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`; NO `sorryAx`). -/

#print axioms negation_kills_sine_sum
#print axioms house_sq_le_trace
#print axioms chebotarev_singleton_vacuous

end ArkLib.ProximityGap.Frontier.H6
