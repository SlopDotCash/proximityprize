/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24DBlockIndependence
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot

/-!
# LANE D8 (#466 round 25): `DBlockIndependence` at `d = 8` — PROVEN (recursive tower descent)

Round 24 proved the first `d > 2` instance of the r22 Stepanov block-independence target:
`DBlockIndependence F 4 q D g` at budget `4D + 3·deg g < q`, via ONE fold (alternating
conjugate) into the in-tree `d = 2` core plus an extension-free `quartic_descent`.  This file
tests the conjectured `2^k` recursion at the next rung and **proves `d = 8`**, exhibiting the
general pattern.

## The recursion (probe `probe_r25_d8_descent.py`; identities verified over ℚ and F₁₇/F₄₁/F₇₃)

**Step 1 (fold 8 → 4, consumes `dBlockIndependence_four` ONCE).**  With `w = g^e`,
`e = (q−1)/8`, `s_j = subq (A_j)`, multiply `R = Σ_{j<8} w^j s_j = 0` by the alternating
conjugate `Σ (−1)^j w^j s_j`: the product is `P(v)² − v·Q(v)²` with `v = w² = g^((q−1)/4)`,
`P = s₀ + s₂v + s₄v² + s₆v³`, `Q = s₁ + s₃v + s₅v² + s₇v³`.  Multiplying by `g` and folding
`g^q = g(X^q)` gives a **4-block relation in `v`** whose blocks are the four octic norm blocks
  `E₀ = γA₀² + γ̂(2A₂A₆ + A₄² − 2A₁A₇ − 2A₃A₅)`
  `E₁ = γ(2A₀A₂ − A₁²) + γ̂(2A₄A₆ − 2A₃A₇ − A₅²)`
  `E₂ = γ(2A₀A₄ + A₂² − 2A₁A₃) + γ̂(A₆² − 2A₅A₇)`
  `E₃ = γ(2A₀A₆ + 2A₂A₄ − 2A₁A₅ − A₃²) − γ̂A₇²`
(`γ = g(X)`, `γ̂ = g(Y)`; blocks `≤ deg g + 2D`), so `dBlockIndependence_four` applies at
`4(deg g + 2D) + 3 deg g = 8D + 7·deg g < q` and yields `E₀ = ⋯ = E₃ = 0`.

**Step 2 (octic descent = quartic descent OVER `K(√c)`).**  The key structural discovery:
regrouping the four equations `e_i = 0` (`E_i` divided by `γ`, `c = g(Y)/g(X)`) along the
quadratic subfield `K ⊂ K(s)`, `s² = c`, with `P₀ = a₀ + a₄s`, `Q₀ = a₁ + a₅s`,
`P₁ = a₂ + a₆s`, `Q₁ = a₃ + a₇s`, one gets EXACTLY the two r24 quartic hypotheses with `c ↦ s`:
  `e₀ + s·e₂ = P₀² + s(P₁² − 2Q₀Q₁)`   and   `e₁ + s·e₃ = 2P₀P₁ − Q₀² − sQ₁²`.
So `quartic_descent` fires over `K(√c)` (a single quadratic `AdjoinRoot`, NOT the octic
extension), gives `P₀ = Q₀ = P₁ = Q₁ = 0`, and `{1, s}`-independence splits each into the two
`K`-components.  The side conditions `¬IsSquare(±s)` in `K(√c)` reduce (by direct component
computation) to the Kummer condition `c ∉ −4K⁴` — and `c = −4b⁴ ⟹ −c = (2b²)²`, so the SAME
two hypotheses as `d = 4` suffice: `¬IsSquare c ∧ ¬IsSquare (−c)`.  No new obstruction class
appears at `d = 8`.

## What this file proves (all axiom-clean, real locked build)

* `octic_descent` — the `d = 8` descent over any field, from `¬IsSquare c ∧ ¬IsSquare (−c)`,
  via `quartic_descent` over the single quadratic adjunction `K(√c)`.
* `octic_norm_forces_trivial` — the `d = 8` genus statement in `F[X][Y]`.
* `dBlockIndependence_eight` — **`DBlockIndependence F 8 q D g` for every squarefree `g` of
  positive degree, `8 ∣ q − 1`, at budget `8D + 7·deg g < q`** (`q` odd is automatic).

## The general `2^k` pattern (conjecture, now with the recursion explicit)

The `d = 2^(k+1)` descent is the `d = 2^k` descent over `K(√c)` with `c ↦ √c`: the `2^(k+1)`
norm-block equations regroup pairwise into the `2^k` equations over `K(√c)`, side conditions
telescope through `¬IsSquare(±√c) ⟸ c ∉ −4K⁴ ⟸ ¬IsSquare(−c)`, and `{1, √c}`-independence
splits components.  Budget prediction: `2^k·D + (2^k − 1)·deg g < q`, hypotheses stable at
`¬IsSquare c ∧ ¬IsSquare (−c)` for ALL `k` — the `d = 2^k` tower needs no new conditions.
-/

namespace ArkLib.ProximityGap.Frontier.R25D8Descent

open Polynomial ArkLib.ProximityGap.StepanovNonVanishing
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence

set_option linter.unusedFintypeInType false

variable {F : Type*} [Field F]

/-! ## 1. The octic descent — quartic descent over the quadratic adjunction `K(√c)` -/

set_option maxHeartbeats 1600000 in
-- The AdjoinRoot representation and the two regrouped quartic linear_combinations are large.
/-- **Octic descent.**  Over any field `K`, if `c` and `−c` are both non-squares, the four
component equations of the octic norm form force `a₀ = ⋯ = a₇ = 0`.  Proof: adjoin ONE square
root `s = √c` (quadratic `AdjoinRoot`, irreducible since `¬IsSquare c`); the four equations
regroup into the two r24 quartic equations over `K(s)` with parameter `s`; `¬IsSquare (±s)`
in `K(s)` reduces to the Kummer condition `c ∉ −4K⁴`, which follows from `¬IsSquare (−c)`;
`quartic_descent` fires; `{1, s}`-independence splits the components. -/
theorem octic_descent {K : Type*} [Field K] (c a0 a1 a2 a3 a4 a5 a6 a7 : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    (h0 : a0 ^ 2 + c * (2 * a2 * a6 + a4 ^ 2 - 2 * a1 * a7 - 2 * a3 * a5) = 0)
    (h1 : 2 * a0 * a2 - a1 ^ 2 + c * (2 * a4 * a6 - 2 * a3 * a7 - a5 ^ 2) = 0)
    (h2 : 2 * a0 * a4 + a2 ^ 2 - 2 * a1 * a3 + c * (a6 ^ 2 - 2 * a5 * a7) = 0)
    (h3 : 2 * a0 * a6 + 2 * a2 * a4 - 2 * a1 * a5 - a3 ^ 2 - c * a7 ^ 2 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a7 = 0 := by
  -- the quadratic adjunction K(√c)
  have hpow : ∀ b : K, b ^ 2 ≠ c := fun b hb => hc ⟨b, by rw [← hb]; ring⟩
  set f : K[X] := X ^ 2 - C c with hfdef
  haveI hIrr : Fact (Irreducible f) :=
    ⟨hfdef ▸ X_pow_sub_C_irreducible_of_prime Nat.prime_two hpow⟩
  set ι : K →+* AdjoinRoot f := AdjoinRoot.of f with hιdef
  set s : AdjoinRoot f := AdjoinRoot.root f with hsdef
  have hmkC : ∀ x : K, AdjoinRoot.mk f (C x) = ι x := fun _ => rfl
  have hM : f.Monic := by rw [hfdef]; exact monic_X_pow_sub_C c (by norm_num : (2 : ℕ) ≠ 0)
  have hfd : f.natDegree = 2 := by rw [hfdef]; exact natDegree_X_pow_sub_C
  have hf1 : f ≠ 1 := by intro h; rw [h, natDegree_one] at hfd; omega
  have hs2 : s ^ 2 = ι c := by
    have h : AdjoinRoot.mk f (X ^ 2 - C c) = 0 := by rw [← hfdef]; exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, hmkC, ← hsdef] at h
    linear_combination h
  have hinj : Function.Injective ι := ι.injective
  -- every element of K(s) is ι α + ι β · s
  have rep : ∀ z : AdjoinRoot f, ∃ α β : K, z = ι α + ι β * s := by
    intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    have hmk : AdjoinRoot.mk f p = AdjoinRoot.mk f (p %ₘ f) := by
      conv_lhs => rw [← modByMonic_add_div p f]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    have hlt := natDegree_modByMonic_lt p hM hf1
    rw [hfd] at hlt
    obtain ⟨c1, c0, hrepr⟩ : ∃ u v : K, p %ₘ f = C u * X + C v :=
      ⟨_, _, eq_X_add_C_of_natDegree_le_one (by omega)⟩
    refine ⟨c0, c1, ?_⟩
    rw [hmk, hrepr, map_add, map_mul, AdjoinRoot.mk_X, hmkC, hmkC, ← hsdef]
    ring
  -- {1, s}-independence over K
  have hindep : ∀ α β : K, ι α + ι β * s = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    by_cases hβ : β = 0
    · subst hβ
      rw [map_zero, zero_mul, add_zero] at h
      exact ⟨hinj (by rw [map_zero]; exact h), rfl⟩
    · exfalso
      have hsq : (ι β) ^ 2 * ι c = (ι α) ^ 2 := by
        linear_combination (ι β * s - ι α) * h - (ι β) ^ 2 * hs2
      have hKey : β ^ 2 * c = α ^ 2 := by
        apply hinj
        rw [map_mul, map_pow, map_pow]
        exact hsq
      exact hc ⟨α / β, by field_simp; linear_combination hKey⟩
  -- ±s are non-squares in K(s): the Kummer condition c ∉ −4K⁴, from ¬IsSquare (−c)
  have hs_nsq : ¬ IsSquare s := by
    rintro ⟨x, hx⟩
    obtain ⟨α, β, rfl⟩ := rep x
    have hz : ι (α ^ 2 + c * β ^ 2) + ι (2 * α * β - 1) * s = 0 := by
      simp only [map_add, map_mul, map_sub, map_pow, map_one, map_ofNat]
      linear_combination -hx - (ι β) ^ 2 * hs2
    obtain ⟨hA, hB⟩ := hindep _ _ hz
    have hβ : β ≠ 0 := by intro h; rw [h] at hB; norm_num at hB
    exact hnc ⟨α / β, by field_simp; linear_combination -hA⟩
  have hns_nsq : ¬ IsSquare (-s) := by
    rintro ⟨x, hx⟩
    obtain ⟨α, β, rfl⟩ := rep x
    have hz : ι (α ^ 2 + c * β ^ 2) + ι (2 * α * β + 1) * s = 0 := by
      simp only [map_add, map_mul, map_pow, map_one, map_ofNat]
      linear_combination -hx - (ι β) ^ 2 * hs2
    obtain ⟨hA, hB⟩ := hindep _ _ hz
    have hβ : β ≠ 0 := by intro h; rw [h] at hB; norm_num at hB
    exact hnc ⟨α / β, by field_simp; linear_combination -hA⟩
  -- map the four hypotheses into K(s)
  have hι0 : (ι a0) ^ 2
      + ι c * (2 * ι a2 * ι a6 + (ι a4) ^ 2 - 2 * ι a1 * ι a7 - 2 * ι a3 * ι a5) = 0 := by
    have h := congrArg ι h0
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι1 : 2 * ι a0 * ι a2 - (ι a1) ^ 2
      + ι c * (2 * ι a4 * ι a6 - 2 * ι a3 * ι a7 - (ι a5) ^ 2) = 0 := by
    have h := congrArg ι h1
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι2 : 2 * ι a0 * ι a4 + (ι a2) ^ 2 - 2 * ι a1 * ι a3
      + ι c * ((ι a6) ^ 2 - 2 * ι a5 * ι a7) = 0 := by
    have h := congrArg ι h2
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι3 : 2 * ι a0 * ι a6 + 2 * ι a2 * ι a4 - 2 * ι a1 * ι a5 - (ι a3) ^ 2
      - ι c * (ι a7) ^ 2 = 0 := by
    have h := congrArg ι h3
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  -- regroup: the two quartic hypotheses over K(s) with parameter s
  have H0 : (ι a0 + ι a4 * s) ^ 2
      + s * ((ι a2 + ι a6 * s) ^ 2 - 2 * (ι a1 + ι a5 * s) * (ι a3 + ι a7 * s)) = 0 := by
    linear_combination hι0 + s * hι2
      + ((ι a4) ^ 2 + 2 * ι a2 * ι a6 - 2 * ι a1 * ι a7 - 2 * ι a3 * ι a5
        + s * ((ι a6) ^ 2 - 2 * ι a5 * ι a7)) * hs2
  have H1 : 2 * (ι a0 + ι a4 * s) * (ι a2 + ι a6 * s) - (ι a1 + ι a5 * s) ^ 2
      - s * (ι a3 + ι a7 * s) ^ 2 = 0 := by
    linear_combination hι1 + s * hι3
      + (2 * ι a4 * ι a6 - (ι a5) ^ 2 - 2 * ι a3 * ι a7 - (ι a7) ^ 2 * s) * hs2
  -- the r24 quartic descent fires over K(s)
  obtain ⟨u0, u1, u2, u3⟩ := quartic_descent s (ι a0 + ι a4 * s) (ι a1 + ι a5 * s)
    (ι a2 + ι a6 * s) (ι a3 + ι a7 * s) hs_nsq hns_nsq H0 H1
  obtain ⟨e0, e4⟩ := hindep _ _ u0
  obtain ⟨e1, e5⟩ := hindep _ _ u1
  obtain ⟨e2, e6⟩ := hindep _ _ u2
  obtain ⟨e3, e7⟩ := hindep _ _ u3
  exact ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩

/-! ## 2. The octic genus statement in `F[X][Y]` -/

set_option maxHeartbeats 1600000 in
-- The fraction-field descent performs several large polynomial-map normalizations.
/-- **The `d = 8` genus statement, PROVEN** (octic analogue of the in-tree
`genus_squarefree_forces_trivial` / r24 `quartic_norm_forces_trivial`).  Route: map into
`K = Frac(F(X)[Y])`, set `c = g(Y)/g(X)`; both `±c` non-squares (unit multiples of the
squarefree positive-degree `g(Y)`), then `octic_descent`. -/
theorem octic_norm_forces_trivial [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (A0 A1 A2 A3 A4 A5 A6 A7 : Polynomial (Polynomial F))
    (h0 : C g * A0 ^ 2
      + (g.map C) * (2 * A2 * A6 + A4 ^ 2 - 2 * A1 * A7 - 2 * A3 * A5) = 0)
    (h1 : C g * (2 * A0 * A2 - A1 ^ 2)
      + (g.map C) * (2 * A4 * A6 - 2 * A3 * A7 - A5 ^ 2) = 0)
    (h2 : C g * (2 * A0 * A4 + A2 ^ 2 - 2 * A1 * A3)
      + (g.map C) * (A6 ^ 2 - 2 * A5 * A7) = 0)
    (h3 : C g * (2 * A0 * A6 + 2 * A2 * A4 - 2 * A1 * A5 - A3 ^ 2)
      - (g.map C) * A7 ^ 2 = 0) :
    A0 = 0 ∧ A1 = 0 ∧ A2 = 0 ∧ A3 = 0 ∧ A4 = 0 ∧ A5 = 0 ∧ A6 = 0 ∧ A7 = 0 := by
  set ι : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F) with hιdef
  have hιinj : Function.Injective ι := IsFractionRing.injective F[X] (RatFunc F)
  set φ : Polynomial (Polynomial F) →+* Polynomial (RatFunc F) := Polynomial.mapRingHom ι with hφ
  have hφinj : Function.Injective φ := Polynomial.map_injective ι hιinj
  set G : Polynomial (RatFunc F) := g.map (algebraMap F (RatFunc F)) with hGdef
  have hφC : φ (C g) = C (ι g) := by rw [hφ, coe_mapRingHom, Polynomial.map_C]
  have hφmap : φ (g.map (C : F →+* F[X])) = G := by
    rw [hφ, coe_mapRingHom, Polynomial.map_map, hGdef]; congr 1
  have hg0 : g ≠ 0 := fun h => by simp [h] at hdeg
  have hιg0 : ι g ≠ 0 := fun h => hg0 (hιinj (h.trans (map_zero ι).symm))
  have hGsf : Squarefree G := by
    rw [hGdef]
    exact (PerfectField.separable_iff_squarefree.mpr hg).map.squarefree
  have hGdeg : 0 < G.natDegree := by
    rw [hGdef, natDegree_map_eq_of_injective (algebraMap F (RatFunc F)).injective]; exact hdeg
  set ψ : Polynomial (RatFunc F) →+* FractionRing (Polynomial (RatFunc F)) :=
    (algebraMap (Polynomial (RatFunc F)) (FractionRing (Polynomial (RatFunc F)))) with hψdef
  have hψinj : Function.Injective ψ :=
    IsFractionRing.injective (Polynomial (RatFunc F)) (FractionRing (Polynomial (RatFunc F)))
  set a0 := ψ (φ A0) with ha0def
  set a1 := ψ (φ A1) with ha1def
  set a2 := ψ (φ A2) with ha2def
  set a3 := ψ (φ A3) with ha3def
  set a4 := ψ (φ A4) with ha4def
  set a5 := ψ (φ A5) with ha5def
  set a6 := ψ (φ A6) with ha6def
  set a7 := ψ (φ A7) with ha7def
  set γK := ψ (C (ι g)) with hγKdef
  set GK := ψ G with hGKdef
  have hγK0 : γK ≠ 0 := fun h => by
    have h2 : (C (ι g) : Polynomial (RatFunc F)) = 0 := hψinj (h.trans (map_zero ψ).symm)
    rw [C_eq_zero] at h2
    exact hιg0 h2
  set c := GK / γK with hcdef
  have hGKc : GK = c * γK := by rw [hcdef, div_mul_cancel₀ _ hγK0]
  -- map the four hypotheses through ψ ∘ φ
  have h0K : γK * a0 ^ 2 + GK * (2 * a2 * a6 + a4 ^ 2 - 2 * a1 * a7 - 2 * a3 * a5) = 0 := by
    have h := congrArg ψ (congrArg φ h0)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h1K : γK * (2 * a0 * a2 - a1 ^ 2)
      + GK * (2 * a4 * a6 - 2 * a3 * a7 - a5 ^ 2) = 0 := by
    have h := congrArg ψ (congrArg φ h1)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h2K : γK * (2 * a0 * a4 + a2 ^ 2 - 2 * a1 * a3)
      + GK * (a6 ^ 2 - 2 * a5 * a7) = 0 := by
    have h := congrArg ψ (congrArg φ h2)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h3K : γK * (2 * a0 * a6 + 2 * a2 * a4 - 2 * a1 * a5 - a3 ^ 2)
      - GK * a7 ^ 2 = 0 := by
    have h := congrArg ψ (congrArg φ h3)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  -- normalize to the descent shape
  have h0' : a0 ^ 2 + c * (2 * a2 * a6 + a4 ^ 2 - 2 * a1 * a7 - 2 * a3 * a5) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h0K - (2 * a2 * a6 + a4 ^ 2 - 2 * a1 * a7 - 2 * a3 * a5) * hGKc
  have h1' : 2 * a0 * a2 - a1 ^ 2 + c * (2 * a4 * a6 - 2 * a3 * a7 - a5 ^ 2) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h1K - (2 * a4 * a6 - 2 * a3 * a7 - a5 ^ 2) * hGKc
  have h2' : 2 * a0 * a4 + a2 ^ 2 - 2 * a1 * a3 + c * (a6 ^ 2 - 2 * a5 * a7) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h2K - (a6 ^ 2 - 2 * a5 * a7) * hGKc
  have h3' : 2 * a0 * a6 + 2 * a2 * a4 - 2 * a1 * a5 - a3 ^ 2 - c * a7 ^ 2 = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h3K + a7 ^ 2 * hGKc
  -- non-square conditions (verbatim r24)
  have hnotsq : ∀ δ : RatFunc F, δ ≠ 0 → ¬ IsSquare (ψ (C δ * G)) := by
    intro δ hδ
    have hsf2 : Squarefree (C δ * G) := by
      have hassoc : Associated (C δ * G) G :=
        ⟨(isUnit_C.mpr (Ne.isUnit (inv_ne_zero hδ))).unit, by
          rw [IsUnit.unit_spec]
          rw [mul_comm (C δ) G, mul_assoc, ← C_mul, mul_inv_cancel₀ hδ, C_1, mul_one]⟩
      exact hassoc.squarefree_iff.mpr hGsf
    have hdeg2 : 0 < (C δ * G).natDegree := by
      rw [natDegree_C_mul hδ]; exact hGdeg
    exact squarefree_pos_not_isSquare_frac (C δ * G) hsf2 hdeg2
  have hc : ¬ IsSquare c := by
    rintro ⟨r, hr⟩
    apply hnotsq (ι g) hιg0
    refine ⟨γK * r, ?_⟩
    rw [map_mul]
    linear_combination γK * hGKc + γK * γK * hr
  have hnc : ¬ IsSquare (-c) := by
    rintro ⟨r, hr⟩
    apply hnotsq (-(ι g)) (neg_ne_zero.mpr hιg0)
    refine ⟨γK * r, ?_⟩
    rw [show (C (-(ι g)) : Polynomial (RatFunc F)) = -(C (ι g)) from by rw [map_neg], neg_mul,
      map_neg, map_mul]
    linear_combination -γK * hGKc + γK * γK * hr
  obtain ⟨hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7⟩ :=
    octic_descent c a0 a1 a2 a3 a4 a5 a6 a7 hc hnc h0' h1' h2' h3'
  refine ⟨hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_),
    hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_)⟩ <;>
    simp only [map_zero]
  · exact hz0
  · exact hz1
  · exact hz2
  · exact hz3
  · exact hz4
  · exact hz5
  · exact hz6
  · exact hz7

/-! ## 3. Block-degree bookkeeping -/

/-- Blocks of a sum (common bound); companion to r24 `blocks_sub_le`. -/
theorem blocks_add_le {A B : Polynomial (Polynomial F)} {a : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ a) (hB : ∀ j, (B.coeff j).natDegree ≤ a) :
    ∀ j, ((A + B).coeff j).natDegree ≤ a := by
  intro j
  rw [coeff_add]
  exact (natDegree_add_le _ _).trans (max_le (hA j) (hB j))

/-! ## 4. The main theorem: `DBlockIndependence` at `d = 8` -/

set_option maxHeartbeats 1600000 in
-- The 8-to-4 conjugate-fold linear_combination and degree bookkeeping are large.
/-- **`DBlockIndependence F 8 q D g`, PROVEN** — the second `2`-power rung of the r22 target,
at the predicted budget `8D + 7·deg g < q`, for `8 ∣ q − 1` (oddness is automatic).

Step 1 folds the 8-block relation via the alternating conjugate and `g^q = g(X^q)` into a
4-block relation whose blocks are the octic norm blocks `E₀…E₃`; `dBlockIndependence_four`
(the r24 result) fires once and gives `E_i = 0`.  Step 2 is `octic_norm_forces_trivial`. -/
theorem dBlockIndependence_eight [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (h8 : 8 ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 8 * D + 7 * g.natDegree < Fintype.card F) :
    DBlockIndependence F 8 (Fintype.card F) D g := by
  intro A hblk hsum j
  set q := Fintype.card F with hqdef
  obtain ⟨e, he⟩ := h8
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hqe : q = 8 * e + 1 := by omega
  have hq_odd : Odd q := ⟨4 * e, by omega⟩
  have h4dvd : 4 ∣ (q - 1) := ⟨2 * e, by omega⟩
  have h8e : (q - 1) / 8 = e := by omega
  have h4e : (q - 1) / 4 = 2 * e := by omega
  -- the folded 8-block relation
  have hsum8 : subq q (A 0) + g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
      + g ^ (3 * e) * subq q (A 3) + g ^ (4 * e) * subq q (A 4)
      + g ^ (5 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 6)
      + g ^ (7 * e) * subq q (A 7) = 0 := by
    have h := hsum
    rw [Fin.sum_univ_eight] at h
    have h0v : ((0 : Fin 8) : ℕ) = 0 := rfl
    have h1v : ((1 : Fin 8) : ℕ) = 1 := rfl
    have h2v : ((2 : Fin 8) : ℕ) = 2 := rfl
    have h3v : ((3 : Fin 8) : ℕ) = 3 := rfl
    have h4v : ((4 : Fin 8) : ℕ) = 4 := rfl
    have h5v : ((5 : Fin 8) : ℕ) = 5 := rfl
    have h6v : ((6 : Fin 8) : ℕ) = 6 := rfl
    have h7v : ((7 : Fin 8) : ℕ) = 7 := rfl
    rw [h0v, h1v, h2v, h3v, h4v, h5v, h6v, h7v, h8e] at h
    linear_combination h
  -- the octic norm blocks
  set E0 : Polynomial (Polynomial F) := C g * (A 0) ^ 2
    + (g.map C) * (2 * (A 2) * (A 6) + (A 4) ^ 2 - 2 * (A 1) * (A 7) - 2 * (A 3) * (A 5))
    with hE0def
  set E1 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 2) - (A 1) ^ 2)
    + (g.map C) * (2 * (A 4) * (A 6) - 2 * (A 3) * (A 7) - (A 5) ^ 2) with hE1def
  set E2 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 4) + (A 2) ^ 2
    - 2 * (A 1) * (A 3)) + (g.map C) * ((A 6) ^ 2 - 2 * (A 5) * (A 7)) with hE2def
  set E3 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 6) + 2 * (A 2) * (A 4)
    - 2 * (A 1) * (A 5) - (A 3) ^ 2) - (g.map C) * (A 7) ^ 2 with hE3def
  -- fold subq through the blocks
  have hgq : subq q (g.map (C : F →+* F[X])) = g ^ q := (pow_card_eq_subq_map_C g).symm
  have hSE0 : subq q E0 = g * (subq q (A 0)) ^ 2
      + g ^ q * (2 * subq q (A 2) * subq q (A 6) + (subq q (A 4)) ^ 2
        - 2 * subq q (A 1) * subq q (A 7) - 2 * subq q (A 3) * subq q (A 5)) := by
    rw [hE0def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE1 : subq q E1 = g * (2 * subq q (A 0) * subq q (A 2) - (subq q (A 1)) ^ 2)
      + g ^ q * (2 * subq q (A 4) * subq q (A 6) - 2 * subq q (A 3) * subq q (A 7)
        - (subq q (A 5)) ^ 2) := by
    rw [hE1def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE2 : subq q E2 = g * (2 * subq q (A 0) * subq q (A 4) + (subq q (A 2)) ^ 2
        - 2 * subq q (A 1) * subq q (A 3))
      + g ^ q * ((subq q (A 6)) ^ 2 - 2 * subq q (A 5) * subq q (A 7)) := by
    rw [hE2def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE3 : subq q E3 = g * (2 * subq q (A 0) * subq q (A 6)
        + 2 * subq q (A 2) * subq q (A 4) - 2 * subq q (A 1) * subq q (A 5)
        - (subq q (A 3)) ^ 2)
      - g ^ q * (subq q (A 7)) ^ 2 := by
    rw [hE3def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  -- the conjugate-fold identity 8 → 4
  have hkey : (subq q (A 0) + g ^ (2 * e) * subq q (A 2) + g ^ (4 * e) * subq q (A 4)
        + g ^ (6 * e) * subq q (A 6)) ^ 2
      - g ^ (2 * e) * (subq q (A 1) + g ^ (2 * e) * subq q (A 3)
        + g ^ (4 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 7)) ^ 2 = 0 := by
    linear_combination (subq q (A 0) - g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
      - g ^ (3 * e) * subq q (A 3) + g ^ (4 * e) * subq q (A 4)
      - g ^ (5 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 6)
      - g ^ (7 * e) * subq q (A 7)) * hsum8
  -- the 4-block relation for the octic norm blocks
  have hR : g ^ (0 * ((q - 1) / 4)) * subq q E0 + g ^ (1 * ((q - 1) / 4)) * subq q E1
      + g ^ (2 * ((q - 1) / 4)) * subq q E2 + g ^ (3 * ((q - 1) / 4)) * subq q E3 = 0 := by
    have hgq8 : g ^ q = g ^ (8 * e + 1) := by rw [← hqe]
    rw [h4e, hSE0, hSE1, hSE2, hSE3, hgq8]
    linear_combination g * hkey
  -- block-degree bookkeeping: E_i blocks ≤ deg g + 2D
  have hsq : ∀ i : Fin 8, ∀ k, (((A i) ^ 2).coeff k).natDegree ≤ 2 * D := fun i =>
    blocks_pow_le (hblk i) 2
  have hp : ∀ i i' : Fin 8, ∀ k, ((2 * (A i) * (A i')).coeff k).natDegree ≤ 2 * D := by
    intro i i' k
    have := blocks_two_mul_mul_le (hblk i) (hblk i') k
    omega
  have hb0 : ∀ k, (E0.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE0def, coeff_add]
    have ht1 := blocks_C_mul_le g (hsq 0) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_add_le (hp 2 6) (hsq 4)) (hp 1 7)) (hp 3 5)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb1 : ∀ k, (E1.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE1def, coeff_add]
    have ht1 := blocks_C_mul_le g (blocks_sub_le (hp 0 2) (hsq 1)) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (hp 4 6) (hp 3 7)) (hsq 5)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb2 : ∀ k, (E2.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE2def, coeff_add]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_add_le (hp 0 4) (hsq 2)) (hp 1 3)) k
    have ht2 := blocks_mapC_mul_le g (blocks_sub_le (hsq 6) (hp 5 7)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb3 : ∀ k, (E3.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE3def, coeff_sub]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_add_le (hp 0 6) (hp 2 4)) (hp 1 5)) (hsq 3)) k
    have ht2 := blocks_mapC_mul_le g (hsq 7) k
    exact (natDegree_sub_le _ _).trans (max_le ht1 (by omega))
  -- the d = 4 result fires once
  have hD4 : 4 * (g.natDegree + 2 * D) + 3 * g.natDegree < q := by omega
  have hEz := dBlockIndependence_four g hg hdeg hq_odd h4dvd hD4 ![E0, E1, E2, E3]
    (by
      intro i
      fin_cases i
      · exact hb0
      · exact hb1
      · exact hb2
      · exact hb3)
    (by rw [Fin.sum_univ_four]; exact hR)
  have hE0z : E0 = 0 := hEz 0
  have hE1z : E1 = 0 := hEz 1
  have hE2z : E2 = 0 := hEz 2
  have hE3z : E3 = 0 := hEz 3
  -- the octic descent finishes
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7⟩ := octic_norm_forces_trivial g hg hdeg
    (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) (A 6) (A 7)
    (hE0def.symm.trans hE0z) (hE1def.symm.trans hE1z)
    (hE2def.symm.trans hE2z) (hE3def.symm.trans hE3z)
  fin_cases j
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact z4
  · exact z5
  · exact z6
  · exact z7

end ArkLib.ProximityGap.Frontier.R25D8Descent

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R25D8Descent in
#print axioms octic_descent
open ArkLib.ProximityGap.Frontier.R25D8Descent in
#print axioms octic_norm_forces_trivial
open ArkLib.ProximityGap.Frontier.R25D8Descent in
#print axioms dBlockIndependence_eight
