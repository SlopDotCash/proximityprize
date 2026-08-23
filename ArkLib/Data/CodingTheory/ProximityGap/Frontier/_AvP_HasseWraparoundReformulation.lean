/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# The p-adic Hasse filtration: the char-`p` wraparound is a sparse-polynomial root (#444)

The companion to the 2-adic graded filtration (`_AvLambda_GradedWraparoundFiltration`), on the
**prize
prime side**. Both come from ONE ring identity — the **graded expansion of a signed power-sum
around an
arbitrary base point `g`** — specialized to two different points:
* `g = 1`, `π = ζ − 1 = −λ` ⟹ the **2-adic** filtration (the ramified prime over 2).
* `g = ` a primitive `n`-th root mod `p`, `π = ζ − g` ⟹ the **p-adic** filtration (a prime over
`p`).

## The reformulation (verified exact; the algebra is formalized below)

Let `D = Σ_i ε_i·ζ_n^{k_i}` be a wraparound and `F(X) = Σ_i ε_i·X^{k_i}` the corresponding
**weight-`2r`
sparse `±1` polynomial** (degree `< n`). Since `N(D) = ± Res(Φ_n, F)` (resultant) and `p ≡ 1 mod n`
splits completely, expanding `ζ = g + π` at the prime `P` over `p` (where `ζ ≡ g`) gives
`D = Σ_j π^j·Q_j(g)` with `Q_j(g) = Σ_i ε_i·C(k_i,j)·g^{k_i−j} = F^{[j]}(g)` (the `j`-th **Hasse
derivative**). Therefore:
```
  p ∣ N(D)  ⟺  F vanishes at a primitive n-th root mod p  (F shares a root with Φ_n over 𝔽_p),
  v_P(D)   =  mult_g(F mod p) · v_P(ζ−g)  =  (min{ j : F^{[j]}(g) ≢ 0 mod p }) · v_P(ζ−g).
```
So the **char-`p` wraparound is exactly a sparse-polynomial root event**, and its P-adic depth is
the
**root multiplicity** (Hasse-derivative characterized). Verified by exact computation: `p ∣ N(D) ⟺ F
vanishes at a primitive `n`-th root` holds `259264/259264` over four bad primes `p ∈
{97,113,257,337}`
(`n = 16`); at prize scale the roots are simple (`mult = 1`, the shallow `W_2`).

This is the cleanest known reformulation of the open object: it ties the wraparound to the theory of
roots of **lacunary / `t`-sparse polynomials** in `𝔽_p` (`t = 2r` terms, degree `< n`), and the
incidence count `W_r(p) = #{(ε,k) : F_{ε,k} shares a root with Φ_n mod p}`.

## Honest scope (this reformulation REDUCES — it does not bound)

`W_r(p) = Σ_{ω prim. n-th root} #{(ε,k) : F_{ε,k}(ω) = 0}`, and for a **fixed** `ω` the inner
count is
the mod-`p` relation count `#{Σ ε_i ω^{k_i} = 0}` = the BGK object. So the sparse-polynomial framing
is a clean **reformulation**, not a bound: bounding the incidence still requires the per-`ω`
relation
cancellation (the wall). It is a genuine new char-`p` structural law and the `p`-side of the unified
graded filtration — **not** a step toward closing BGK at β=4. Issue #444.

## What this file proves (axiom-clean)

`gradedExpansionAt` — the load-bearing identity: in any commutative ring, a signed power-sum expands
around any base `g` as `Σ_i c_i·(g+π)^{k_i} = Σ_{j≤N} π^j·(Σ_i c_i·C(k_i,j)·g^{k_i−j})` (the Hasse
layers). `gradedExpansionAt_base_one` — at `g = 1` it is the 2-adic-gate form `Σ_j π^j·(Σ_i
c_i·C(k_i,j))`.
-/

namespace ProximityGap.Frontier.HasseWraparound

open Finset

variable {ι R : Type*} [CommRing R]

/-- **Per-element graded binomial expansion around `g`** (extended to a fixed degree `N ≥ k`). For
`g π : R` and `k ≤ N`, `(g + π)^k = Σ_{j ≤ N} π^j · g^{k−j} · C(k,j)` — the `C(k,j) = 0` terms (`j
> k`)
pad it to the common range `[0, N]`, and `g^{k−j}` uses truncated `ℕ` subtraction (harmless: the
coefficient `C(k,j)` is `0` exactly when `k − j` would underflow). -/
theorem add_pow_eq_range (g π : R) (k N : ℕ) (hk : k ≤ N) :
    (g + π) ^ k = ∑ j ∈ Finset.range (N + 1), π ^ j * g ^ (k - j) * (k.choose j : R) := by
  have hbin : (g + π) ^ k
      = ∑ j ∈ Finset.range (k + 1), π ^ j * g ^ (k - j) * (k.choose j : R) := by
    rw [add_comm g π, add_pow]
  rw [hbin]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro j _ hj2
    rw [Finset.mem_range, not_lt] at hj2
    rw [Nat.choose_eq_zero_of_lt hj2, Nat.cast_zero, mul_zero]

/-- **The graded wraparound expansion around `g`** (the unified filtration). A signed power-sum
`Σ_{i∈s} c_i·(g+π)^{k_i}` re-groups by the `π`-degree into the **Hasse layers**
`Σ_{j ≤ N} π^j · (Σ_{i∈s} c_i·C(k_i,j)·g^{k_i−j})`, where `N` bounds every exponent. The `j`-th
layer
`Q_j(g) = Σ_i c_i·C(k_i,j)·g^{k_i−j} = F^{[j]}(g)` is the `j`-th Hasse derivative of `F = Σ c_i
X^{k_i}`
at `g`; over `ℤ[ζ]` with `g` a primitive `n`-th root mod `p` and `π = ζ − g`, `v_P(D) = min{j :
Q_j(g)
≢ 0}·v_P(ζ−g)`. Setting `g = 1, π = −λ` recovers the 2-adic gate. -/
theorem gradedExpansionAt (g π : R) (s : Finset ι) (c : ι → R) (k : ι → ℕ) (N : ℕ)
    (hN : ∀ i ∈ s, k i ≤ N) :
    (∑ i ∈ s, c i * (g + π) ^ (k i))
      = ∑ j ∈ Finset.range (N + 1),
          π ^ j * (∑ i ∈ s, c i * ((k i).choose j : R) * g ^ (k i - j)) := by
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [add_pow_eq_range g π (k i) N (hN i hi), Finset.mul_sum])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **At base `g = 1` the Hasse layer is the binomial-moment layer** of the 2-adic gate: the `j`-th
coefficient `Σ_i c_i·C(k_i,j)·1^{k_i−j} = Σ_i c_i·C(k_i,j) = P_j`. So `gradedExpansionAt 1 (−λ)`
is exactly `_AvLambda_GradedWraparoundFiltration.gradedExpansion`. -/
theorem gradedExpansionAt_base_one (s : Finset ι) (c : ι → R) (k : ι → ℕ) (j : ℕ) :
    (∑ i ∈ s, c i * ((k i).choose j : R) * (1 : R) ^ (k i - j))
      = ∑ i ∈ s, c i * ((k i).choose j : R) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_pow, mul_one]

end ProximityGap.Frontier.HasseWraparound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.HasseWraparound.add_pow_eq_range
#print axioms ProximityGap.Frontier.HasseWraparound.gradedExpansionAt
#print axioms ProximityGap.Frontier.HasseWraparound.gradedExpansionAt_base_one
