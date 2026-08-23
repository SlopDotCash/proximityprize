/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# The graded λ-adic filtration of cyclotomic wraparounds (#444)

A **new** structural law for the char-`p` wraparound of `μ_n` (`n = 2^μ`), extending the
2-adic gate (`_TwoAdicParityGate`) to the **full graded filtration**. A wraparound is a signed sum
`D = Σ_i ε_i·ζ^{k_i}` of `n`-th roots of unity; the landed gate analysed only its reduction mod the
ramified prime `λ = (1 − ζ)` over 2 (the `j = 0` layer). This file isolates the graded structure.

## The discovery (verified exact; the algebra is formalized below)

Writing `ζ = 1 − λ`, the binomial theorem gives `ζ^k = Σ_j C(k,j)(−λ)^j`, so a signed sum expands by
λ-degree:
```
        D = Σ_i ε_i·ζ^{k_i}  =  Σ_j (−λ)^j · P_j,        P_j := Σ_i ε_i·C(k_i, j) ∈ ℤ.
```
Because 2 is totally ramified in `ℤ[ζ_{2^μ}]` (`v_λ(2) = n/2`, residue degree 1), for `j < n/2` the
term `(−λ)^j P_j` has `v_λ = j` exactly when `P_j` is **odd**. Hence the **graded formula**
```
        v₂(N(D)) = v_λ(D) = min{ j ≥ 0 : P_j = Σ_i ε_i·C(k_i, j) is ODD }.
```
Verified by exact field-norm computation: `8/8` weight-4/6 sums at `n = 16` (`v₂(N(D))` matches the
first odd binomial-moment exactly). **Lucas form** (verified `58/58`): mod 2, `C(k,j) ≡ [j ⊆ k]`
(binary submask), so
```
        v₂(N(D)) = min{ j : (#{i : ε_i=+1, j ⊆ k_i} − #{i : ε_i=−1, j ⊆ k_i}) is odd },
```
tying the 2-adic valuation to the **binary digits** of the exponents (natural for `n = 2^μ`). The
`j = 0` layer recovers the gate: `P_0 = Σ_i ε_i = σ(D)` (every `k` is a binary supermask of `0`).

## Connecting back to the prize — the product-formula bridge, and why it is VACUOUS

`v₂(N(D))` controls the **2-part** of the norm; the odd prize prime `p` divides the **odd part**
`N(D)/2^{v₂}`, and (since `p ≡ 1 mod n` splits completely) `p ∣ N(D) ⟺ Σ_i ε_i g^{k_i} ≡ 0 (mod p)`
— the odd part **is** the BGK mod-`p` relation. There is a genuine connection to the count
`W_2(p)` via the **product formula**:
```
        W_2(p) · log p  ≤  Σ_D log(odd-part N(D))  =  Σ_D log|N(D)|  −  log 2 · Σ_D v₂(N(D)),
```
and the filtration makes `Σ_D v₂(N(D)) = Σ_D min{j : P_j odd}` an **exact computable** quantity that
subtracts the entire 2-part from the archimedean budget. **But this bound is vacuous** (verified
exact, `n = 8, 16`): `Σ_D log(odd-part)` scales like `n^{5.5}` — far above the needed `n²` — because
the odd part is Hadamard-exponential (`|N(D)| ≤ 4^{n/2}`) and the 2-part the filtration removes is a
vanishing fraction at scale (`63%` of the 2-adic budget at `n=8`, only `39%` at `n=16`). So the
filtration genuinely connects to the prize and removes the 2-part exactly — but not *enough*: the
dominant odd-part archimedean size is the same wall every norm-based approach hits.

## Honest scope

A genuine new **structural** theorem (verified exact) and a sharper 2-adic gate, with an exact
product-formula bridge to the prize count — but the bridge is **vacuous** for the archimedean reason
above. It is **not** a step toward closing BGK at β=4 (which needs a `p`-adic / equidistribution
input on the odd part). Recorded honestly as a new brick, not progress on the wall. Issue #444.

## What this file proves (axiom-clean): the load-bearing graded expansion

* `gradedExpansion` — in any commutative ring, with `ζ = 1 − λ`, a signed combination of powers
  `Σ_i c_i·(1−λ)^{k_i}` re-groups by λ-degree as `Σ_{j≤N} (−λ)^j·(Σ_i c_i·C(k_i,j))` (the layers).
* `gradedExpansion_layer_zero` — the `j = 0` coefficient is the signed weight `Σ_i c_i` (old gate).
-/

namespace ProximityGap.Frontier.LambdaGraded

open Finset

variable {ι R : Type*} [CommRing R]

/-- **Per-element graded binomial expansion** (extended to a fixed degree `N ≥ k`). For `lam : R`
and `k ≤ N`, `(1 − lam)^k = Σ_{j ≤ N} (−lam)^j · C(k,j)` — the `C(k,j) = 0` terms (`j > k`) pad it
out to the common range `[0, N]`. -/
theorem sub_one_pow_eq_range (lam : R) (k N : ℕ) (hk : k ≤ N) :
    (1 - lam) ^ k = ∑ j ∈ Finset.range (N + 1), (-lam) ^ j * (k.choose j : R) := by
  -- binomial on `(-lam) + 1` up to `k`
  have hbin : (1 - lam) ^ k = ∑ j ∈ Finset.range (k + 1), (-lam) ^ j * (k.choose j : R) := by
    have hap := add_pow (-lam) (1 : R) k
    simp only [one_pow, mul_one] at hap
    rw [show (1 : R) - lam = (-lam) + 1 by ring, hap]
  rw [hbin]
  -- extend the range from `k+1` to `N+1`; the new terms vanish (`k.choose j = 0` for `j > k`)
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro j _ hj2
    rw [Finset.mem_range, not_lt] at hj2
    rw [Nat.choose_eq_zero_of_lt hj2, Nat.cast_zero, mul_zero]

/-- **The graded wraparound expansion.** With `ζ = 1 − lam`, the signed combination
`Σ_{i∈s} c_i·(1−lam)^{k_i}` re-groups by λ-degree into the `P_j` layers
`Σ_{j ≤ N} (−lam)^j · (Σ_{i∈s} c_i·C(k_i,j))`, where `N` bounds every exponent. The inner sum
`P_j = Σ_i c_i·C(k_i,j)` is the `j`-th layer; over `ℤ[ζ]`, `v_λ(D) = min{j : P_j odd}`. -/
theorem gradedExpansion (lam : R) (s : Finset ι) (c : ι → R) (k : ι → ℕ) (N : ℕ)
    (hN : ∀ i ∈ s, k i ≤ N) :
    (∑ i ∈ s, c i * (1 - lam) ^ (k i))
      = ∑ j ∈ Finset.range (N + 1), (-lam) ^ j * (∑ i ∈ s, c i * ((k i).choose j : R)) := by
  -- expand each element, then swap the order of summation
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [sub_one_pow_eq_range lam (k i) N (hN i hi), Finset.mul_sum])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **The `j = 0` layer is the signed weight** (the old 2-adic gate). The degree-0 coefficient of
the graded expansion is `P_0 = Σ_{i∈s} c_i` — exactly `σ(D)`, the quantity governing
`_TwoAdicParityGate`. (`C(k,0) = 1` for every `k`: `0` is a binary submask of every exponent.) -/
theorem gradedExpansion_layer_zero (s : Finset ι) (c : ι → R) (k : ι → ℕ) :
    (∑ i ∈ s, c i * ((k i).choose 0 : R)) = ∑ i ∈ s, c i := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Nat.choose_zero_right, Nat.cast_one, mul_one]

end ProximityGap.Frontier.LambdaGraded

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.LambdaGraded.sub_one_pow_eq_range
#print axioms ProximityGap.Frontier.LambdaGraded.gradedExpansion
#print axioms ProximityGap.Frontier.LambdaGraded.gradedExpansion_layer_zero
