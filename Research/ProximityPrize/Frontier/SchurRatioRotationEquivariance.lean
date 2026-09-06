/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge

/-!
# Scaling homogeneity of the Schur/Lagrange divided difference, and the rotation law on the
  Schur-ratio level sets (#444 decay-rate frontier, off the BGK wall)

`lalalune`'s 2026-06-15 22:13 "decay-rate attack" comment on #444 reduced the prize's open
decay-rate core to a count over the **rotation orbits** of the Schur-ratio level sets:

  `L_γ := { (k+1)-subset R' of μ_n : γ_{R'} = γ }`,   `γ_{R'} = −h_{a−k}(R')/h_{b−k}(R')`,

with the verified-but-unformalised rotation law

  > `R' ↦ ζ·R'`  sends  `γ ↦ ζ^{a−b}·γ`   (so `D*(m) = (orbit size ≤ n)·#clique-orbits(m)`).

That rotation law is exactly the **scaling homogeneity** of the divided difference
`[s] x^b = dividedDifferencePow s v b` (`SchurLagrangeBridge`): it is homogeneous of degree
`b − (#s − 1)` in the node values. This file lands that homogeneity (multiply-through and ratio
forms), transports it to the `schurH` surrogate, and derives the **rotation law on the Schur
ratio** `γ_{R'}` over a cyclic node-scaling — the equivariance underpinning the orbit-count
reduction of the decay rate.

## Honest scope
This is the **equivariance substrate** of the orbit-counting reformulation, not a bound on
`#clique-orbits(m)` (the irreducible open cyclotomic-collision content `lalalune` pinned). It is
character-sum-free, char-agnostic, NOT thinness-essential, and does **not** close CORE
`M(μ_n) ≤ C·√(n·log(p/n))`. It supplies the missing Lean proof of the group action on the level
sets so that downstream orbit-counting bricks can quotient by it.

Probe: `scripts/probes/probe_dd_scaling_rotation.py` (homogeneity over ℂ + the rotation law
`γ(ζR') = ζ^{a−b}γ(R')` on μ_n, n ∈ {8,16,32}; NEVER validated at n=q−1 — pure char-0 identity).
-/

open Finset Polynomial

namespace ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F}

/-- **Per-node scaling of one divided-difference summand.** For a scalar `c` and a node `i ∈ s`,
the `i`-th summand of `dividedDifferencePow s (c • v) b` equals `c^{b - (#s - 1)}` times the
`i`-th summand of `dividedDifferencePow s v b`, **after clearing denominators by `c^{#s-1}`**:

  `c^{#s-1} · (c·v i)^b · (∏_{j∈s.erase i}(c·v i − c·v j))⁻¹`
    `= c^b · (v i)^b · (∏_{j∈s.erase i}(v i − v j))⁻¹`.

The product over the `#s − 1` factors of `s.erase i` pulls out `c^{#s-1}`, which cancels the
prefactor; the numerator contributes `c^b`. (`c ≠ 0` so the rotation is invertible.) -/
theorem dividedDifferencePow_smul_term (c : F) (hc : c ≠ 0) (b : ℕ) (i : ι) (hi : i ∈ s) :
    c ^ (#s - 1) * ((c * v i) ^ b * (∏ j ∈ s.erase i, (c * v i - c * v j))⁻¹)
      = c ^ b * ((v i) ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
  have hcard : (s.erase i).card = #s - 1 := by
    rw [Finset.card_erase_of_mem hi]
  -- Factor `c` out of each difference in the product.
  have hprod : (∏ j ∈ s.erase i, (c * v i - c * v j))
      = c ^ (#s - 1) * ∏ j ∈ s.erase i, (v i - v j) := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    ring
  rw [hprod, mul_pow, mul_inv]
  have hci : c ^ (#s - 1) * (c ^ (#s - 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hc)
  rw [show c ^ (#s - 1) * (c ^ b * v i ^ b * ((c ^ (#s - 1))⁻¹
        * (∏ j ∈ s.erase i, (v i - v j))⁻¹))
        = (c ^ (#s - 1) * (c ^ (#s - 1))⁻¹)
          * (c ^ b * (v i ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹)) from by ring,
    hci, one_mul]

/-- **Scaling homogeneity of the divided difference (multiply-through form).**
`dividedDifferencePow` is homogeneous of degree `b − (#s − 1)` in the node values; multiply-through
form clearing the `c^{#s-1}` denominator (`c ≠ 0`, the rotation is a unit):

  `c^{#s-1} · [s] (c·v)^b  =  c^b · [s] v^b`.

Proof: distribute over the defining sum and apply `dividedDifferencePow_smul_term` termwise. -/
theorem dividedDifferencePow_smul (c : F) (hc : c ≠ 0) (b : ℕ) :
    c ^ (#s - 1) * dividedDifferencePow s (fun i => c * v i) b
      = c ^ b * dividedDifferencePow s v b := by
  unfold dividedDifferencePow
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => dividedDifferencePow_smul_term c hc b i hi)

/-- **Scaling homogeneity, ratio (genuine `c^{b-(#s-1)}`) form.** For `c ≠ 0`,

  `[s] (c·v)^b  =  c^{(b : ℤ) − (#s − 1)} · [s] v^b`   (`zpow`, since `b − (#s−1)` may be negative).

This is the clean statement of "homogeneous of degree `b − (#s − 1)`". Derived from the
multiply-through form by dividing the nonzero `c^{#s-1}`. -/
theorem dividedDifferencePow_smul_zpow (c : F) (hc : c ≠ 0) (b : ℕ) :
    dividedDifferencePow s (fun i => c * v i) b
      = c ^ ((b : ℤ) - (#s - 1 : ℕ)) * dividedDifferencePow s v b := by
  have hkey := dividedDifferencePow_smul (s := s) (v := v) c hc b
  have hcpow : (c ^ (#s - 1) : F) ≠ 0 := pow_ne_zero _ hc
  -- From `c^{#s-1} · X = c^b · Y`, get `X = (c^{#s-1})⁻¹ · c^b · Y`.
  have hX : dividedDifferencePow s (fun i => c * v i) b
      = (c ^ (#s - 1))⁻¹ * (c ^ b * dividedDifferencePow s v b) := by
    rw [← hkey, ← mul_assoc, inv_mul_cancel₀ hcpow, one_mul]
  rw [hX, zpow_sub₀ hc, zpow_natCast, zpow_natCast]
  ring

/-- **Scaling homogeneity transported to the `schurH` surrogate (multiply-through form).**
The complete-homogeneous surrogate inherits the same homogeneity:

  `c^{#s-1} · schurH s (c·v) b  =  c^b · schurH s v b`,

for `c ≠ 0` and `s` nonempty (the bridge `dividedDifferencePow_eq_schurH` needs injectivity of the
scaled node map, which holds when `c ≠ 0` and `v` is injective on `s`). -/
theorem schurH_smul (hvs : Set.InjOn v s) (hs : s.Nonempty) (c : F) (hc : c ≠ 0) (b : ℕ) :
    c ^ (#s - 1) * schurH s (fun i => c * v i) b = c ^ b * schurH s v b := by
  have hvsc : Set.InjOn (fun i => c * v i) s := by
    intro x hx y hy hxy
    exact hvs hx hy (by
      have := mul_left_cancel₀ hc hxy
      simpa using this)
  rw [← dividedDifferencePow_eq_schurH hvsc hs b, ← dividedDifferencePow_eq_schurH hvs hs b]
  exact dividedDifferencePow_smul c hc b

/-- **The rotation law on the Schur ratio `γ_{R'} = −h_{a−k}(R')/h_{b−k}(R')` (`lalalune`'s
`R'↦ζR' ⟹ γ↦ζ^{a−b}γ`).**

Working directly with the divided differences `A := [s] x^a`, `B := [s] x^b` over a node set `s`
of size `#s = k+1` (so `h_{a−k}(R') = [s]x^a` etc. via the Schur bridge), the ratio
`γ := −A/B` transforms under node scaling `v ↦ c·v` by the multiplicative factor `c^{a−b}`:

  `−([s](c·v)^a)/([s](c·v)^b)  =  c^{(a:ℤ)−b} · (−([s]v^a)/([s]v^b))`.

The `c^{#s-1}` denominators from both divided differences cancel in the ratio, leaving exactly
`c^{a−b}`. Only hypothesis: `c ≠ 0` (the scaling is invertible — the rotation `ζ` on `μ_n` is a
unit). Notably the law needs **no** `B = [s] v^b ≠ 0` hypothesis: it holds even on the level-set
boundary `h_{b−k} = 0` (both ratios degenerate to `·/0 = 0` consistently in a field), so the
equivariance is total on `(k+1)`-subsets. This is the equivariance making the level sets `L_γ` a
union of `⟨ζ⟩`-orbits — the substrate of `D*(m) = (orbit size)·#clique-orbits(m)`. -/
theorem schurRatio_smul (c : F) (hc : c ≠ 0) (a b : ℕ) :
    (-(dividedDifferencePow s (fun i => c * v i) a)) / dividedDifferencePow s (fun i => c * v i) b
      = c ^ ((a : ℤ) - b) * ((-(dividedDifferencePow s v a)) / dividedDifferencePow s v b) := by
  rw [dividedDifferencePow_smul_zpow c hc a, dividedDifferencePow_smul_zpow c hc b]
  -- `−(c^{a-(#s-1)} A) / (c^{b-(#s-1)} B) = c^{a-b} · (−A/B)`.
  generalize hN : ((#s - 1 : ℕ) : ℤ) = N
  have hcb : (c ^ ((b : ℤ) - N) : F) ≠ 0 := zpow_ne_zero _ hc
  have hcab : c ^ ((a : ℤ) - N) = c ^ ((a : ℤ) - b) * c ^ ((b : ℤ) - N) := by
    rw [← zpow_add₀ hc]; congr 1; ring
  rw [hcab]
  -- Goal: `-(c^{a-b} * c^{b-N} * A) / (c^{b-N} * B) = c^{a-b} * (-A/B)`.
  rw [show -(c ^ ((a : ℤ) - b) * c ^ ((b : ℤ) - N) * dividedDifferencePow s v a)
        = c ^ ((b : ℤ) - N) * (c ^ ((a : ℤ) - b) * -dividedDifferencePow s v a) from by ring,
    mul_div_mul_left _ _ hcb, mul_div_assoc, neg_div]

/-- **The Schur-vanishing locus is rotation-invariant.** The bad-α / unified-open-core carrier is
the Schur-vanishing set `{ R' : [R'] x^b = 0 }` (`= h_{b−k}(R') = 0`, the elementary/complete-
symmetric vanishing the core `K` counts — see `SchurLagrangeBridge`). Scaling the node set by a
unit `c ≠ 0` **preserves vanishing**: `[s] (c·v)^b = 0 ⟺ [s] v^b = 0`. Immediate from the
multiply-through homogeneity (`c^{#s-1} · [s](c·v)^b = c^b · [s]v^b` with both `c^{#s-1}, c^b` units).

On `μ_n` (with `c = ζ` a root of unity) this makes the bad-α set a union of `⟨ζ⟩`-orbits — the
orbit structure on the core-`K` carrier itself, supporting `K = (orbit size)·#K-orbits`. Probe:
`scripts/probes/probe_schur_vanishing_rotation_invariant.py` (12000 cases on `μ_n`, n∈{8,16,32},
1797 actual vanishings, invariance never broken; NEVER `n=q−1`). -/
theorem dividedDifferencePow_eq_zero_iff_smul (c : F) (hc : c ≠ 0) (b : ℕ) :
    dividedDifferencePow s (fun i => c * v i) b = 0 ↔ dividedDifferencePow s v b = 0 := by
  have hkey := dividedDifferencePow_smul (s := s) (v := v) c hc b
  have hcs : (c ^ (#s - 1) : F) ≠ 0 := pow_ne_zero _ hc
  have hcb : (c ^ b : F) ≠ 0 := pow_ne_zero _ hc
  constructor
  · intro h
    rw [h, mul_zero] at hkey
    exact (mul_eq_zero.mp hkey.symm).resolve_left hcb
  · intro h
    rw [h, mul_zero] at hkey
    exact (mul_eq_zero.mp hkey).resolve_left hcs

/-- **The `schurH` (complete-homogeneous surrogate) vanishing locus is rotation-invariant.**
The same statement on the surrogate: `schurH s (c·v) b = 0 ⟺ schurH s v b = 0` for `c ≠ 0`,
`v` injective on `s`, `s` nonempty. Via `dividedDifferencePow_eq_schurH` on both node sets. -/
theorem schurH_eq_zero_iff_smul (hvs : Set.InjOn v s) (hs : s.Nonempty)
    (c : F) (hc : c ≠ 0) (b : ℕ) :
    schurH s (fun i => c * v i) b = 0 ↔ schurH s v b = 0 := by
  have hvsc : Set.InjOn (fun i => c * v i) s := by
    intro x hx y hy hxy
    exact hvs hx hy (by
      have := mul_left_cancel₀ hc hxy
      simpa using this)
  rw [← dividedDifferencePow_eq_schurH hvsc hs b, ← dividedDifferencePow_eq_schurH hvs hs b]
  exact dividedDifferencePow_eq_zero_iff_smul c hc b

end ProximityGap.SchurLagrange

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_smul_term
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_smul
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_smul_zpow
#print axioms ProximityGap.SchurLagrange.schurH_smul
#print axioms ProximityGap.SchurLagrange.schurRatio_smul
#print axioms ProximityGap.SchurLagrange.dividedDifferencePow_eq_zero_iff_smul
#print axioms ProximityGap.SchurLagrange.schurH_eq_zero_iff_smul
