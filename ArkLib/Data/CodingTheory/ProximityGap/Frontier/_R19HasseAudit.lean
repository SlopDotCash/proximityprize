/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# LANE HASSE (#466 round 19): Mathlib Hasse audit + exact quartic→cubic reduction (d = 2 face)

`QuarticWeilInput` (`_R18FourthMomentTwist.lean`) at `d = 2` needs, for the quadratic
character `χ` and nondegenerate `(x₁,x₂,y₁,y₂)`:
`|∑_t χ((t−x₁)(t−x₂)(t−y₁)(t−y₂))| ≤ 3√p` — Hasse–Weil for the genus-1 curve
`y² = quartic`.

## (a) Mathlib audit (verified by grep, 2026-07-07, mathlib rev in `.lake`)

* **NO Hasse point-count bound**: `grep -rln "Hasse" Mathlib/` hits only
  `Algebra/Polynomial/HasseDeriv.lean`, `Combinatorics/SimpleGraph/Hasse.lean`,
  `RingTheory/LaurentSeries.lean` (Hasse derivatives) and friends. Nothing under
  `AlgebraicGeometry/EllipticCurve/*` mentions Hasse, `card`-of-points bounds, or a
  Frobenius trace bound.  `#E(F_p)` counting does not exist.
* **NO norm bound on Gauss/Jacobi sums**: no `norm_gaussSum`/`abs_gaussSum`/
  `norm_jacobiSum` anywhere.  What EXISTS is the algebraic square:
  `gaussSum_mul_gaussSum_eq_card` (`g(χ)·g(χ⁻¹ ∘ conj ψ) = card F`),
  `gaussSum_sq` (`g(χ)² = χ(−1)·card F` for quadratic `χ`), and
  `jacobiSum_mul_jacobiSum_inv` (`J(χ,φ)·J(χ⁻¹,φ⁻¹) = card F`) — over ℂ these DO yield
  `|g| = √p`, `|J| = √p`, but the archimedean statements are not in Mathlib.
* Jacobi-sum route for the GENERAL quartic is a dead end: a Möbius change of variable
  reduces the 4-distinct-root quartic to the Legendre family `y² = x(x−1)(x−λ)` with
  `λ` = cross-ratio of the roots; a closed Jacobi-sum evaluation of its trace exists
  only at CM values of `λ` (e.g. `λ = −1`, `j = 1728`, Jacobsthal / `p = a² + b²`).
  Our tuples from `μ_n` have generic cross-ratio, so the general case IS Hasse.

## (b) What this file proves (axiom-clean, integer-valued `quadraticChar` model)

For `F` a finite field of odd characteristic, `χ = quadraticChar F : MulChar F ℤ`:

1. `sum_comp_sq` — exact square-fiber interchange
   `∑_t f(t²) = ∑_s (1 + χ s)·f s` (fiber count `= χ s + 1`).
2. `sum_quadraticChar_mul_shift`, `sum_quadraticChar_quadratic` — the classical complete
   quadratic evaluation `∑_x χ((x−u)(x−v)) = −1` for `u ≠ v` (ABSENT from Mathlib;
   proved via `s ↦ 1 + c·s⁻¹` reindexing onto `univ.erase 1`).
3. `quartic_even_split` — EXACT identity: for `u ≠ v`
   `∑_t χ((t²−u)(t²−v)) = −1 + ∑_s χ(s(s−u)(s−v))`.
   This reduces the ±-paired subfamily of `QuarticWeilInput` tuples (available in the
   campaign setting since `−1 ∈ μ_n`, `n = 2^μ`: take `x₂ = −x₁`, `y₂ = −y₁`,
   `u = x₁²`, `v = y₁²`) to the Legendre-CUBIC family `y² = s(s−u)(s−v)`, genus 1.
4. `LegendreCubicHasse` — the NAMED residual: `(∑_s χ(s(s−u)(s−v)))² ≤ 4·card F` for
   `0 ≠ u ≠ v ≠ 0` (Hasse `|a_p| ≤ 2√p` for the full-2-torsion curve).
5. `quartic_even_bound_of_cubicHasse` — integer-clean budget transfer:
   `LegendreCubicHasse F → (∑_t χ((t²−u)(t²−v)))² ≤ 9·card F` (the `3√p` shape of
   `QuarticWeilInput`, no `Real.sqrt` needed: `(C−1)² ≤ 2C²+2 ≤ 8p+2 ≤ 9p`).

Probe: identities (2),(3) verified exactly at `p ∈ {13,17,29,37,53,97}`, all
`(u,v)` cells (probe in round-19 scratchpad; no failures, cubic max `< 2√p`).

## (c) Minimal missing Mathlib statement (verbatim, for the ledger)

`theorem hasse_cubic (F) [Field F] [Fintype F] (hF : ringChar F ≠ 2) {u v : F}
  (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
  (∑ s : F, quadraticChar F (s * ((s - u) * (s - v))))^2 ≤ 4 * Fintype.card F`
— Hasse for genus 1 (elementary Stepanov/Manin proof exists on paper; nothing in
Mathlib to build it from).  Given this ONE statement, the ±-paired `d = 2` face of
`QuarticWeilInput` closes by `quartic_even_bound_of_cubicHasse`; the general face
additionally needs the Möbius/cross-ratio reduction (routine but unformalized).

No closure claimed: `LegendreCubicHasse` is left as a named Prop.
-/

namespace ArkLib.ProximityGap.Frontier.R19HasseAudit

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Square-fiber interchange**: summing `f` over squares counts each value `s` with
multiplicity `1 + χ(s)`.  Exact, no error term. -/
theorem sum_comp_sq (hF : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ t : F, f (t ^ 2) = ∑ s : F, (1 + quadraticChar F s) * f s := by
  classical
  calc ∑ t : F, f (t ^ 2)
      = ∑ s : F, ∑ t ∈ univ.filter (fun t : F => t ^ 2 = s), f (t ^ 2) :=
        (sum_fiberwise_of_maps_to (fun t _ => mem_univ _) _).symm
    _ = ∑ s : F, ((univ.filter (fun t : F => t ^ 2 = s)).card : ℤ) * f s := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_congr rfl fun t ht => by rw [(mem_filter.mp ht).2], sum_const,
          nsmul_eq_mul]
    _ = ∑ s : F, (1 + quadraticChar F s) * f s := by
        refine sum_congr rfl fun s _ => ?_
        have h := quadraticChar_card_sqrts hF s
        have hset : {x : F | x ^ 2 = s}.toFinset = univ.filter (fun t : F => t ^ 2 = s) := by
          ext x; simp
        rw [hset] at h
        rw [h]; ring

/-- Complete sum of the quadratic character over `s(s+c)`, `c ≠ 0`: equals `−1`.
Proof: drop `s = 0`, write `s(s+c) = s²(1 + c s⁻¹)`, reindex `s ↦ 1 + c s⁻¹`
bijectively onto `univ.erase 1`, and use `∑ χ = 0`, `χ(1) = 1`. -/
theorem sum_quadraticChar_mul_shift (hF : ringChar F ≠ 2) {c : F} (hc : c ≠ 0) :
    ∑ s : F, quadraticChar F (s * (s + c)) = -1 := by
  classical
  have h0 : quadraticChar F ((0 : F) * (0 + c)) = 0 := by simp
  have hsplit : ∑ s : F, quadraticChar F (s * (s + c))
      = ∑ s ∈ univ.erase (0 : F), quadraticChar F (s * (s + c)) := by
    rw [← sum_erase_add univ _ (mem_univ (0 : F)), h0, add_zero]
  have hstep : ∀ s ∈ univ.erase (0 : F),
      quadraticChar F (s * (s + c)) = quadraticChar F (1 + c * s⁻¹) := by
    intro s hs
    have hs0 : s ≠ 0 := (mem_erase.mp hs).1
    have hval : s * (s + c) = s ^ 2 * (1 + c * s⁻¹) := by
      field_simp
    rw [hval, map_mul, quadraticChar_sq_one' hs0, one_mul]
  have hbij : ∑ s ∈ univ.erase (0 : F), quadraticChar F (1 + c * s⁻¹)
      = ∑ w ∈ univ.erase (1 : F), quadraticChar F w := by
    refine sum_nbij' (fun s => 1 + c * s⁻¹) (fun w => c * (w - 1)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      have hs0 : s ≠ 0 := (mem_erase.mp hs).1
      refine mem_erase.mpr ⟨?_, mem_univ _⟩
      intro h
      have : c * s⁻¹ = 0 := by linear_combination h
      exact hc (by
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · exact absurd (inv_eq_zero.mp h') hs0)
    · intro w hw
      have hw1 : w ≠ 1 := (mem_erase.mp hw).1
      refine mem_erase.mpr ⟨?_, mem_univ _⟩
      intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact hc h'
      · exact hw1 (by
          have := inv_eq_zero.mp h'
          have : w = 1 := by linear_combination this
          exact this)
    · intro s hs
      have hs0 : s ≠ 0 := (mem_erase.mp hs).1
      show c * ((1 + c * s⁻¹) - 1)⁻¹ = s
      have h1 : (1 + c * s⁻¹) - 1 = c * s⁻¹ := by ring
      rw [h1, mul_inv_rev, inv_inv, mul_comm s c⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hc, one_mul]
    · intro w hw
      have hw1 : w ≠ 1 := (mem_erase.mp hw).1
      have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
      show 1 + c * (c * (w - 1)⁻¹)⁻¹ = w
      rw [mul_inv_rev, inv_inv, mul_comm (w - 1) c⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hc, one_mul]
      ring
    · intro s _; rfl
  have hsum : ∑ w ∈ univ.erase (1 : F), quadraticChar F w = -1 := by
    have h := sum_erase_add univ (fun w => quadraticChar F w) (mem_univ (1 : F))
    simp only [map_one, quadraticChar_sum_zero hF] at h
    linarith
  rw [hsplit, sum_congr rfl hstep, hbij, hsum]

/-- **Complete quadratic evaluation** (absent from Mathlib): for `u ≠ v`,
`∑_x χ((x−u)(x−v)) = −1`. -/
theorem sum_quadraticChar_quadratic (hF : ringChar F ≠ 2) {u v : F} (huv : u ≠ v) :
    ∑ x : F, quadraticChar F ((x - u) * (x - v)) = -1 := by
  classical
  have hre : ∑ x : F, quadraticChar F ((x - u) * (x - v))
      = ∑ s : F, quadraticChar F (s * (s + (u - v))) := by
    refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun x => ?_
    simp only [Equiv.subRight_apply]
    ring_nf
  rw [hre]
  exact sum_quadraticChar_mul_shift hF (sub_ne_zero.mpr huv)

/-- **EXACT quartic→cubic reduction**: for `u ≠ v`,
`∑_t χ((t²−u)(t²−v)) = −1 + ∑_s χ(s(s−u)(s−v))`.
The even-quartic char sum IS the Legendre-cubic char sum, up to the exact constant `−1`. -/
theorem quartic_even_split (hF : ringChar F ≠ 2) {u v : F} (huv : u ≠ v) :
    ∑ t : F, quadraticChar F ((t ^ 2 - u) * (t ^ 2 - v))
      = -1 + ∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) := by
  classical
  have h1 := sum_comp_sq hF (fun s => quadraticChar F ((s - u) * (s - v)))
  have h2 : ∀ s : F, (1 + quadraticChar F s) * quadraticChar F ((s - u) * (s - v))
      = quadraticChar F ((s - u) * (s - v))
        + quadraticChar F (s * ((s - u) * (s - v))) := by
    intro s
    rw [map_mul (quadraticChar F) s]
    ring
  rw [h1, sum_congr rfl fun s _ => h2 s, sum_add_distrib,
    sum_quadraticChar_quadratic hF huv]

/-- **THE NAMED RESIDUAL (Hasse for genus 1, absent from Mathlib, docstring (a))**:
for distinct nonzero `u, v` the Legendre-cubic char sum is at most `2√p` in absolute
value, stated integer-cleanly as `S² ≤ 4p`.  This is `|a_p(E)| ≤ 2√p` for the
full-2-torsion elliptic curve `y² = s(s−u)(s−v)`. -/
def LegendreCubicHasse (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ u v : F, u ≠ 0 → v ≠ 0 → u ≠ v →
    (∑ s : F, quadraticChar F (s * ((s - u) * (s - v)))) ^ 2 ≤ 4 * Fintype.card F

/-- **Budget transfer, integer-clean**: Hasse for the cubic gives the `3√p`-shaped bound
`Q² ≤ 9p` for the ±-paired quartic family — no `Real.sqrt`, valid for every odd-char
finite field (uses only `card F ≥ 2` and `(C+1)² ≥ 0`). -/
theorem quartic_even_bound_of_cubicHasse (hF : ringChar F ≠ 2)
    (hH : LegendreCubicHasse F) {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (∑ t : F, quadraticChar F ((t ^ 2 - u) * (t ^ 2 - v))) ^ 2
      ≤ 9 * Fintype.card F := by
  have hsplit := quartic_even_split hF huv
  set C : ℤ := ∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) with hC
  have hHC : C ^ 2 ≤ 4 * Fintype.card F := hH u v hu hv huv
  have hcard : (2 : ℤ) ≤ Fintype.card F := by
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    exact_mod_cast h1
  rw [hsplit]
  nlinarith [sq_nonneg (C + 1), sq_nonneg (C - 1)]

#print axioms sum_comp_sq
#print axioms sum_quadraticChar_mul_shift
#print axioms sum_quadraticChar_quadratic
#print axioms quartic_even_split
#print axioms quartic_even_bound_of_cubicHasse

end ArkLib.ProximityGap.Frontier.R19HasseAudit
