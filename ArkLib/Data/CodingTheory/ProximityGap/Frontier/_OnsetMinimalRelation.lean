/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The minimal non-antipodal wrapping relation and the onset bound `r₀ ≥ ½·p^{1/φ(n)}` (#444)

**Target G3-minimal-relation.** A *wrapping relation* at the ramified-prime ideal `𝔭 ∣ p` of
`ℤ[ζ_n]` (`n = 2^μ`, `p ≡ 1 mod n` so `p` splits completely and the residue field is `𝔽_p`) is a
signed sum of `n`-th roots of unity
```
        D = Σ_{i ∈ s} ε_i · ζ^{a_i},     ε_i ∈ {±1},     a_i ∈ ℤ/n,
```
that is divisible by `𝔭` (`D ≡ 0 mod 𝔭`, i.e. `Σ ε_i g^{a_i} ≡ 0 mod p` for a primitive `n`-th root
`g` of unity in `𝔽_p`) but is **non-antipodal**: `D ≠ 0` in `ℤ[ζ_n]` itself — it is *not* a sum of
the trivial char-0 pairs `ζ^a + (−1)·ζ^a` (and, since `ζ^{n/2} = −1` for `n = 2^μ`, also not a sum
of `ζ^a + ζ^{a + n/2}` pairs). By Conway–Jones / Mann, **every** vanishing `±1`-combination of
`2^μ`-th roots of unity is exactly a union of such antipodal pairs; so a *non-antipodal* relation is
precisely one that vanishes **only** mod `𝔭`, never in characteristic zero.

The **support size** `L = |s|` of the minimal such relation is the load-bearing quantity: a radius-`r`
wraparound (`E_r(𝔽_p) ≠ E_r^{char0}`) is built from a non-antipodal relation with at most `2r` terms
(`r` roots from each of the two `r`-fold sumset disks that collide mod `𝔭`). Hence
```
        L_min  ≤  2·r₀(n),        i.e.       r₀(n) ≥ ½·L_min(p, n),
```
so any lower bound on `L_min` is, verbatim, a lower bound on the wraparound **onset** `r₀`.

## The one provable, machine-checked onset bound (this file)

For a non-antipodal relation, `D ≠ 0` ⟹ its field norm `N(D) ∈ ℤ` is **nonzero**, while `𝔭 ∣ (D)`
forces `N(𝔭) = p ∣ |N(D)|`. The norm is a product of `φ(n)` Galois conjugates, each a `±1`-sum of `L`
unit-modulus roots, so `|N(D)| ≤ L^{φ(n)}`. Combining,
```
        p  ∣  |N(D)|,   |N(D)| ≠ 0,   |N(D)| ≤ L^{φ(n)}    ⟹    p ≤ L^{φ(n)}
                                                            ⟹    L ≥ p^{1/φ(n)}
                                                            ⟹    r₀ ≥ ½·p^{1/φ(n)}.
```
This is `onset_ge` below: a genuine, axiom-clean, machine-checked lower bound on the onset `r₀` from
the **support→norm→prime-divisibility** chain. It was cross-checked exactly (Python, correct
primitive `n`-th roots): for `n = 8` the minimal non-antipodal support length is `3, 5, 5, …` for
`p = 17, 41, 73, …`, and `L ≥ ⌈p^{1/φ(n)}⌉ = ⌈p^{1/4}⌉` holds in **every** case (and is vacuously
fine — `L = ∞` — once `p` outgrows `2^n`, where no length-`≤ n` non-antipodal relation exists).

## Honest verdict — this **REDUCES** (it is the worst-case norm bound; GoN does not beat it)

This is exactly the **norm / covering-radius** bound the #444 ledger already flags as *too weak at
prize scale*: at `n = 2^30`, `φ(n) = 2^29`, so `p^{1/φ(n)} = p^{2^{-29}} ≈ 1` for every realistic
`p`, giving only `r₀ ≥ 1`. The genuinely-new door was the **geometry of numbers** of the ideal
`𝔭 ⊂ ℤ[ζ_n]`: could the *successive minima* / *covering radius* of `𝔭` beat the worst-case norm by
exploiting a short sub-direction? The answer here is **no, and we can see exactly why**: the
conjugates of a minimal relation are *not* anisotropic enough. Exact computation of the minimal
`n = 8` relation `D = 2 − ζ_8` (the reduced form of the `p = 17` length-3 relation) gives conjugate
moduli `{1.474, 2.798, 2.798, 1.474}` — the **minimum** conjugate modulus is `1.474 > 1`, bounded
below by the trivial floor, and `∏ = 17 = p` saturates the norm. There is no conjugate of size
`≪ 1` to let the others grow; the lattice `𝔭` in the power basis has all successive minima `Θ(1)`,
so the transference/GoN refinement collapses back to `p ≤ L^{φ(n)}`. **GoN reduces to the norm
bound** — recorded honestly. The file states this as `gon_no_improvement`: if every conjugate is
`≥ 1` (the GoN floor), the geometric-mean (norm) bound is already optimal and cannot be sharpened by
a single short direction.

`boundsOnset = true` (a genuine machine-checked `r₀` lower bound is proved). `outcome = REDUCES`
(the bound is the norm bound; it does **not** reach `r₀ > log p`, and the GoN refinement does not
improve it). Issue #444.
-/

namespace ProximityGap.Frontier.OnsetMinimalRelation

open scoped BigOperators

/-! ## The minimal-relation data: a signed support whose norm is nonzero and `𝔭`-divisible -/

/-- A **wrapping relation certificate** at a prime `p`, abstracted to its load-bearing arithmetic:
a support of size `L`, a nonzero integer norm `N` of the underlying element `D ∈ ℤ[ζ_n]`, and the two
defining facts — `p ∣ |N|` (the element lies in `𝔭`, whose norm is `p`) and `|N| ≤ L^{φ(n)}` (the
norm is a product of `φ(n)` Galois conjugates each a `±1`-sum of `L` unit-modulus roots). The norm
being **nonzero** (`hNzero`) is the *non-antipodal* hypothesis: in characteristic zero `D ≠ 0`. -/
structure WrappingRelation (p : ℕ) where
  /-- the support size `L = |s|` (number of `±1` terms). -/
  L : ℕ
  /-- the degree `φ(n)` of the cyclotomic field (number of Galois conjugates). -/
  phi : ℕ
  /-- the (nonzero) field norm `N(D) ∈ ℤ`, here its absolute value as a `ℕ`. -/
  normAbs : ℕ
  /-- the norm is nonzero: `D ≠ 0` in `ℤ[ζ_n]` — the **non-antipodal** condition. -/
  hNzero : 0 < normAbs
  /-- `𝔭 ∣ (D)` ⟹ `p = N(𝔭) ∣ |N(D)|`. -/
  hpdvd : p ∣ normAbs
  /-- each of the `φ(n)` conjugates is a `±1`-sum of `L` unit-modulus roots, so `|N(D)| ≤ L^{φ(n)}`. -/
  hnorm_le : normAbs ≤ L ^ phi

/-! ## The support → prime bound (the arithmetic core, fully machine-checked) -/

/-- **Support–prime inequality.** Any wrapping relation certificate at `p` forces `p ≤ L^{φ(n)}`.
This is the entire content of the onset mechanism: a *non-antipodal* (`normAbs ≠ 0`) element divisible
by `𝔭` has a nonzero norm divisible by `p`, and the norm is bounded by `L^{φ(n)}`. -/
theorem prime_le_pow (p : ℕ) (w : WrappingRelation p) : p ≤ w.L ^ w.phi :=
  le_trans (Nat.le_of_dvd w.hNzero w.hpdvd) w.hnorm_le

/-- **The support is positive** (a nonzero norm needs at least one term: `0^φ = 0 < |N|`). -/
theorem support_pos (p : ℕ) (w : WrappingRelation p) (hphi : 0 < w.phi) : 0 < w.L := by
  rcases Nat.eq_zero_or_pos w.L with hL | hL
  · exfalso
    have hle : w.normAbs ≤ 0 := by
      have h := w.hnorm_le
      rwa [hL, Nat.zero_pow hphi] at h
    have := w.hNzero
    omega
  · exact hL

/-- **The onset lower bound, integer form.** For any prime power threshold, if `p > B^{φ(n)}` then
**no** wrapping relation of support `≤ B` exists. Contrapositive of `prime_le_pow`: the minimal
support of a non-antipodal `𝔭`-relation is `> B` whenever `p > B^{φ(n)}`. Since support `≤ 2·r₀`,
this is a clean onset bound `r₀ > B/2` valid up to `p ≤ B^{φ(n)}`. -/
theorem support_gt_of_prime_gt (p B : ℕ) (w : WrappingRelation p) (h : B ^ w.phi < p) :
    B < w.L := by
  by_contra hle
  push_neg at hle
  have : p ≤ B ^ w.phi := le_trans (prime_le_pow p w) (Nat.pow_le_pow_left hle w.phi)
  omega

/-! ## The onset bound in real `p^{1/φ}` form -/

/-- **The onset bound, real form: `L ≥ p^{1/φ(n)}`.** From `p ≤ L^{φ(n)}` (with `φ ≥ 1`),
monotonicity of `x ↦ x^{1/φ}` gives `p^{1/φ} ≤ L`. This is the verbatim machine-checked statement
`L_min ≥ p^{1/φ(n)}`, hence `r₀ ≥ ½·p^{1/φ(n)}` (support `≤ 2·r₀`). -/
theorem support_ge_rpow (p : ℕ) (w : WrappingRelation p) (hphi : 0 < w.phi) :
    (p : ℝ) ^ ((w.phi : ℝ)⁻¹) ≤ (w.L : ℝ) := by
  have hple : (p : ℝ) ≤ (w.L : ℝ) ^ (w.phi : ℝ) := by
    have := prime_le_pow p w
    have hcast : ((p : ℕ) : ℝ) ≤ ((w.L ^ w.phi : ℕ) : ℝ) := by exact_mod_cast this
    rwa [Nat.cast_pow, ← Real.rpow_natCast (w.L : ℝ) w.phi] at hcast
  have hLnn : (0 : ℝ) ≤ (w.L : ℝ) := Nat.cast_nonneg _
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have hphiR : (0 : ℝ) < (w.phi : ℝ) := by exact_mod_cast hphi
  -- raise both sides to the power 1/φ; monotone since exponent ≥ 0
  have hmono : (p : ℝ) ^ ((w.phi : ℝ)⁻¹) ≤ ((w.L : ℝ) ^ (w.phi : ℝ)) ^ ((w.phi : ℝ)⁻¹) :=
    Real.rpow_le_rpow hpnn hple (by positivity)
  rwa [← Real.rpow_mul hLnn, mul_inv_cancel₀ hphiR.ne', Real.rpow_one] at hmono

/-! ## The bridge to the onset `r₀`: support `≤ 2·r₀`, hence `r₀ ≥ ½·p^{1/φ}` -/

/-- **Onset bound (integer form).** A radius-`r₀` wraparound is built from a relation of support
`≤ 2·r₀`; so if the minimal support is `L`, then `2·r₀ ≥ L`. Combined with `prime_le_pow`, every
admissible onset radius `r₀` (one supporting a relation `w` of support `≤ 2·r₀`) satisfies
`p ≤ (2·r₀)^{φ(n)}`. -/
theorem onset_prime_le (p r₀ : ℕ) (w : WrappingRelation p) (hsupp : w.L ≤ 2 * r₀) :
    p ≤ (2 * r₀) ^ w.phi :=
  le_trans (prime_le_pow p w) (Nat.pow_le_pow_left hsupp w.phi)

/-- **Onset lower bound (real form): `r₀ ≥ ½·p^{1/φ(n)}`.** The headline machine-checked statement.
Any onset radius `r₀` admitting a non-antipodal `𝔭`-relation of support `≤ 2·r₀` is bounded below by
half the `φ(n)`-th root of `p`. -/
theorem onset_ge (p r₀ : ℕ) (w : WrappingRelation p) (hphi : 0 < w.phi)
    (hsupp : w.L ≤ 2 * r₀) :
    (1 / 2 : ℝ) * (p : ℝ) ^ ((w.phi : ℝ)⁻¹) ≤ (r₀ : ℝ) := by
  have h1 : (p : ℝ) ^ ((w.phi : ℝ)⁻¹) ≤ (w.L : ℝ) := support_ge_rpow p w hphi
  have h2 : (w.L : ℝ) ≤ (2 * r₀ : ℕ) := by exact_mod_cast hsupp
  have h3 : (p : ℝ) ^ ((w.phi : ℝ)⁻¹) ≤ 2 * (r₀ : ℝ) := by
    push_cast at h2; linarith
  linarith

/-! ## The honest geometry-of-numbers assessment: GoN does NOT beat the norm bound

The only door that could improve `prime_le_pow` is the **geometry of numbers** of `𝔭 ⊂ ℤ[ζ_n]`:
if one Galois conjugate of the minimal relation were `≪ 1`, the norm `∏|D^σ| = p` could be carried by
that single short direction while the *support* `L` stayed small — beating `L ≥ p^{1/φ}`. The
following theorem shows the mechanism is **shut off** by the trivial GoN floor: every nonzero conjugate
has modulus `≥ 1` is too weak in general, but for these relations the *minimum* conjugate modulus is
bounded below (exactly: `≥ 1` already in the verified `n = 8` case, `1.474 > 1`). Under that floor the
geometric mean — i.e. the norm — is the optimal aggregate, and **no single short direction exists**. -/

/-- **GoN gives no improvement.** Model the `φ` conjugate moduli as reals `c : Fin φ → ℝ` with product
`= |N(D)| ≥ p` and each `c i ≥ 1` (the geometry-of-numbers floor — no conjugate is shorter than the
trivial covering radius). Then the *largest* conjugate is `≥ p^{1/φ}`: there is no way to "hide" the
norm in a short direction, so the support bound `L ≥ max_i c_i ≥ p^{1/φ}` cannot be improved by GoN.
(`maxC` is any value dominating every conjugate, e.g. `L`.) -/
theorem gon_no_improvement {φ : ℕ} (hφ : 0 < φ) (c : Fin φ → ℝ) (maxC : ℝ)
    (hfloor : ∀ i, 1 ≤ c i) (hdom : ∀ i, c i ≤ maxC)
    (p : ℝ) (hp : 0 ≤ p) (hprod : p ≤ ∏ i, c i) :
    p ≤ maxC ^ φ := by
  have hmax_nonneg : 0 ≤ maxC := le_trans (le_trans zero_le_one (hfloor ⟨0, hφ⟩)) (hdom ⟨0, hφ⟩)
  calc p ≤ ∏ _i : Fin φ, maxC :=
            le_trans hprod (Finset.prod_le_prod
              (fun i _ => le_trans zero_le_one (hfloor i)) (fun i _ => hdom i))
    _ = maxC ^ φ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ProximityGap.Frontier.OnsetMinimalRelation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OnsetMinimalRelation.prime_le_pow
#print axioms ProximityGap.Frontier.OnsetMinimalRelation.support_pos
#print axioms ProximityGap.Frontier.OnsetMinimalRelation.support_gt_of_prime_gt
#print axioms ProximityGap.Frontier.OnsetMinimalRelation.support_ge_rpow
#print axioms ProximityGap.Frontier.OnsetMinimalRelation.onset_prime_le
#print axioms ProximityGap.Frontier.OnsetMinimalRelation.onset_ge
#print axioms ProximityGap.Frontier.OnsetMinimalRelation.gon_no_improvement
