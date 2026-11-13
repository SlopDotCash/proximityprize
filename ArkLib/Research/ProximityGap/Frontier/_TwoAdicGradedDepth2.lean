/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

/-!
# The depth-2 graded 2-adic gate on cyclotomic wraparound norms (#444)

This file is the **second rung** of the 2-adic parity gate of `_TwoAdicParityGate.lean`. That file proved the
*depth-1* gate `v_λ(D) ≥ 1 ⟺ σ₀(D) even`, where for a signed wraparound `D = Σ_i ε_i·ζ^{a_i}` (`ε_i = ±1`,
`n = 2^μ`) the **signed weight** is `σ₀(D) = Σ_i ε_i`, `λ = (1 − ζ)` is the unique (totally ramified, residue
degree `f = 1`) prime over 2 in `ℤ[ζ_{2^μ}]`, and `v_λ` is its valuation (`= v₂∘N` since `f = 1`).

**The new content (depth 2).** Write `t := ζ − 1`, so `I = (λ) = (t)` and `ζ = 1 + t`. The binomial expansion
gives the **graded** reduction one order deeper:
```
        ζ^a = (1 + t)^a ≡ 1 + a·t        (mod t²),
```
because `(1+t)^a − (1 + a·t) = Σ_{j≥2} C(a,j) t^j ∈ (t²) = I²`. Summing signed:
```
        D = Σ_i ε_i·ζ^{a_i}  ≡  σ₀(D)·1 + σ₁(D)·t   (mod I²),
        where  σ₀(D) = Σ_i ε_i  (signed weight),  σ₁(D) = Σ_i ε_i·a_i  (signed first moment of exponents).
```
So `D ∈ I² ⟺ σ₀·1 + σ₁·t ∈ I²`: the depth-2 gate is governed by **two** integer parities, the weight `σ₀`
*and* the first exponent-moment `σ₁`.

**Exact-verified (probe `probe_twoadic_graded_depth2.py`, `probe_twoadic_graded_tight.py`).** Over all signed
relations of support `2..4` at `n = 8, 16` (35 600 enumerated, `D ≠ 0` over `ℂ`), partitioned by `(σ₀ mod 2,
σ₁ mod 2)`:
* `(even, even)`: `v_λ(D) ≥ 2` always (min 2, up to 12) — `0` violations.
* `(even, odd)`: `v_λ(D) = 1` **exactly** (never `≥ 2`) — the `σ₁·t` term is the precise obstruction to depth 2.
* `(odd, ·)`: `v_λ(D) = 0` (the depth-1 gate, recovered).
The depth-2 prediction `v_λ(D) ≥ 2 ⟺ σ₀, σ₁ both even` holds with `0` violations and is **tight** (the
`(even, odd)` class pins `v = 1`, so `σ₁` parity is load-bearing, not vacuous).

**Honest scope.** This is **not** a proof of BGK / the prize, and it is not even the full `v_λ ≥ 2` *integer*
criterion (turning `σ₀·1 + σ₁·t ∈ I²` into `σ₀ ≡ σ₁ ≡ 0 mod 2` uses the specific arithmetic of `ℤ[ζ_{2^μ}]`,
namely `I² ∩ (ℤ + ℤ·t)` — a finite local computation, here only probe-verified). What is proved axiom-clean is the
**ring-theoretic graded congruence** `D − (σ₀·1 + σ₁·t) ∈ I²` in any commutative ring, the load-bearing algebra
of the depth-2 gate: it confines the second-order obstruction to the two integer moments `σ₀, σ₁`, climbing the
2-adic tower one rung past the committed depth-1 gate. The odd prize prime still lives in the odd part of the norm
and reaches prize scale at `r ≈ 3` (BGK wall) — this rung sharpens the low-`r` vanishing, it does not cross the wall.

**What this file proves (axiom-clean).**
* `pow_succ_sub_linear_mem_sq` — `(1 + t)^a − (1 + a·t) ∈ I²` for `t ∈ I` (binomial tail, by induction on `a`).
* `signedSum_sub_graded_mem_sq` — `Σ ε_i·g_i − (σ₀·1 + σ₁·t) ∈ I²` when each `g_i = 1 + a_i·t` mod-`I²`-linear.
* `signedSum_graded_congr` — the same in the `g_i := (1 + t)^{a_i}` form (the literal `ζ^{a_i}` instance).
* `signedSum_mem_sq_iff_graded` — the depth-2 gate biconditional `D ∈ I² ⟺ σ₀·1 + σ₁·t ∈ I²`. Issue #444.
-/

namespace ProximityGap.Frontier.TwoAdicGradedDepth2

open Finset

variable {ι R : Type*} [CommRing R]

/-- **Binomial tail at depth 2.** For `t` in an ideal `I`, `(1 + t)^a` agrees with its linear part `1 + a·t`
modulo `I²`: `(1 + t)^a − (1 + (a : R)·t) ∈ I²`. (The omitted terms are `Σ_{j≥2} C(a,j) t^j`, each a multiple of
`t² ∈ I²`.) Proven by induction on `a`. This is the depth-2 analogue of `ζ^a ≡ 1 (mod λ)`: now `ζ^a ≡ 1 + a·t
(mod λ²)` with `t = ζ − 1`. -/
theorem pow_succ_sub_linear_mem_sq (I : Ideal R) (t : R) (ht : t ∈ I) (a : ℕ) :
    (1 + t) ^ a - (1 + (a : R) * t) ∈ I ^ 2 := by
  induction a with
  | zero => simp
  | succ k ih =>
    push_cast
    -- (1+t)^(k+1) - (1 + (k+1)t)
    --   = (1+t)·[(1+t)^k - (1 + k·t)]  +  [(1+t)(1 + k·t) - (1 + (k+1)·t)]
    --   = (1+t)·[depth-2 remainder ∈ I²]  +  k·t²
    have key : (1 + t) ^ (k + 1) - (1 + ((k : R) + 1) * t)
        = (1 + t) * ((1 + t) ^ k - (1 + (k : R) * t)) + (k : R) * (t * t) := by
      ring
    rw [key]
    refine Ideal.add_mem _ ?_ ?_
    · -- (1+t)·(remainder ∈ I²) ∈ I²
      have : (1 + t) ^ k - (1 + (k : R) * t) ∈ I ^ 2 := ih
      exact Ideal.mul_mem_left _ _ this
    · -- k·(t·t) ∈ I² since t·t ∈ I·I = I²
      have htt : t * t ∈ I * I := Ideal.mul_mem_mul ht ht
      rw [← sq] at htt
      exact Ideal.mul_mem_left _ _ htt

/-- **The depth-2 graded congruence (abstract linear form).** If every `g_i` agrees with `1 + a_i·t` modulo `I²`
(`g_i − (1 + a_i·t) ∈ I²`), then the signed sum agrees with its graded weight `σ₀·1 + σ₁·t` modulo `I²`:
```
    Σ_{i∈s} ε_i·g_i  −  ((Σ_i ε_i)·1 + (Σ_i ε_i·a_i)·t)  ∈  I².
```
Here `σ₀ = Σ ε_i` is the signed weight and `σ₁ = Σ ε_i·a_i` the signed first moment. (`ε_i = c i`, `a_i = a i`.) -/
theorem signedSum_sub_graded_mem_sq (I : Ideal R) (t : R) (s : Finset ι)
    (c : ι → R) (a : ι → R) (g : ι → R)
    (hg : ∀ i ∈ s, g i - (1 + a i * t) ∈ I ^ 2) :
    (∑ i ∈ s, c i * g i)
      - ((∑ i ∈ s, c i) * 1 + (∑ i ∈ s, c i * a i) * t) ∈ I ^ 2 := by
  -- Σ c_i g_i − (σ₀·1 + σ₁·t) = Σ c_i·(g_i − (1 + a_i t))
  have hrw : (∑ i ∈ s, c i * g i)
      - ((∑ i ∈ s, c i) * 1 + (∑ i ∈ s, c i * a i) * t)
      = ∑ i ∈ s, c i * (g i - (1 + a i * t)) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hrw]
  exact Ideal.sum_mem _ (fun i hi => Ideal.mul_mem_left _ _ (hg i hi))

/-- **The depth-2 graded congruence (cyclotomic instance).** Specializing `g_i := (1 + t)^{a_i}` (the literal
`ζ^{a_i}` with `t = ζ − 1`), for `t ∈ I` the signed sum `D = Σ ε_i·(1+t)^{a_i}` satisfies
```
    D − ((Σ ε_i)·1 + (Σ ε_i·a_i)·t) ∈ I².
```
This is `D ≡ σ₀·1 + σ₁·t (mod λ²)`, the depth-2 gate congruence, obtained by feeding `pow_succ_sub_linear_mem_sq`
into the abstract form. -/
theorem signedSum_graded_congr (I : Ideal R) (t : R) (ht : t ∈ I) (s : Finset ι)
    (c : ι → R) (a : ι → ℕ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i))
      - ((∑ i ∈ s, c i) * 1 + (∑ i ∈ s, c i * (a i : R)) * t) ∈ I ^ 2 := by
  exact signedSum_sub_graded_mem_sq I t s c (fun i => (a i : R)) (fun i => (1 + t) ^ (a i))
    (fun i _ => pow_succ_sub_linear_mem_sq I t ht (a i))

/-- **The depth-2 gate biconditional.** With `t ∈ I` and `D = Σ ε_i·(1+t)^{a_i}`, membership in `I²` is governed
by the graded weight: `D ∈ I² ⟺ (σ₀·1 + σ₁·t) ∈ I²`, where `σ₀ = Σ ε_i`, `σ₁ = Σ ε_i·a_i`. For `I = (λ)` this is
`λ² ∣ D ⟺ λ² ∣ (σ₀ + σ₁·(ζ−1))` — the second rung of the 2-adic tower. (Probe-verified `v_λ(D) ≥ 2 ⟺ σ₀, σ₁
both even`, tight; the integer-parity reading of the RHS is the local computation `I² ∩ (ℤ + ℤt)`, probe-only.) -/
theorem signedSum_mem_sq_iff_graded (I : Ideal R) (t : R) (ht : t ∈ I) (s : Finset ι)
    (c : ι → R) (a : ι → ℕ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∈ I ^ 2
      ↔ ((∑ i ∈ s, c i) * 1 + (∑ i ∈ s, c i * (a i : R)) * t) ∈ I ^ 2 := by
  have h := signedSum_graded_congr I t ht s c a
  set D := ∑ i ∈ s, c i * (1 + t) ^ (a i) with hD
  set G := (∑ i ∈ s, c i) * 1 + (∑ i ∈ s, c i * (a i : R)) * t with hG
  constructor
  · intro hDmem
    have : G = D - (D - G) := by ring
    rw [this]; exact (I ^ 2).sub_mem hDmem h
  · intro hGmem
    have : D = G + (D - G) := by ring
    rw [this]; exact (I ^ 2).add_mem hGmem h

end ProximityGap.Frontier.TwoAdicGradedDepth2

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.TwoAdicGradedDepth2.pow_succ_sub_linear_mem_sq
#print axioms ProximityGap.Frontier.TwoAdicGradedDepth2.signedSum_sub_graded_mem_sq
#print axioms ProximityGap.Frontier.TwoAdicGradedDepth2.signedSum_graded_congr
#print axioms ProximityGap.Frontier.TwoAdicGradedDepth2.signedSum_mem_sq_iff_graded
