/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25D8Descent
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot

/-!
# LANE D16 (#466 round 26): `DBlockIndependence` at `d = 16` — PROVEN (third tower rung)

Round 24 proved `d = 4`, round 25 proved `d = 8` and conjectured the `2^k` recursion with
budget `2^k·D + (2^k − 1)·deg g < q` and hypotheses stable at `¬IsSquare c ∧ ¬IsSquare (−c)`.
This file validates the recursion end-to-end at the next rung and **proves `d = 16`** at the
predicted budget `16D + 15·deg g < q`, by the exact mechanical route the r25 docstring
predicted (probe `probe_r26_d16.py`: fold, convolution blocks, regroup all verified
symbolically over ℚ and numerically over F₉₇, 200 trials).

## The recursion, instantiated once more

**Step 1 (fold 16 → 8, consumes `dBlockIndependence_eight` ONCE).**  With `w = g^e`,
`e = (q−1)/16`, `s_j = subq (A_j)`, multiply `R = Σ_{j<16} w^j s_j = 0` by the alternating
conjugate: the product is `P(v)² − v·Q(v)²`, `v = w²`, `P = Σ_{i<8} s_{2i} v^i`,
`Q = Σ_{i<8} s_{2i+1} v^i`.  Multiplying by `g` and folding `g^q = g(X^q)` gives an 8-block
relation in `v` whose blocks are `E_j = γ·c_j + γ̂·c_{j+8}` (`γ = g(X)`, `γ̂ = g(Y)`), where
`c_m` is the convolution coefficient
  `c_m = Σ_{i+i'=m} A_{2i}A_{2i'} − Σ_{i+i'=m−1} A_{2i+1}A_{2i'+1}`  (indices `< 8`),
blocks `≤ deg g + 2D`, so `dBlockIndependence_eight` applies at
`8(deg g + 2D) + 7·deg g = 16D + 15·deg g < q` and yields `E₀ = ⋯ = E₇ = 0`.

**Step 2 (sedecic descent = octic descent OVER `K(√c)`).**  Exactly as at `d = 8`: adjoin
ONE square root `s = √c`; the eight equations `e_j = c_j + c·c_{j+8} = 0` regroup pairwise as
  `e_j + s·e_{j+4} = h_j^{octic}(s; b₀,…,b₇) − (c_{j+8} + s·c_{j+12})·(s² − c)`,
`b_i = a_i + a_{i+8}·s` — i.e. the four r25 octic hypotheses over `K(s)` with parameter `s`
(correction quotients `K_j = c_{j+8} + s·c_{j+12}`, computed and verified in the probe).
`¬IsSquare (±s)` in `K(s)` again reduces to `¬IsSquare c ∧ ¬IsSquare (−c)` (the same Kummer
component computation as r25, verbatim); `octic_descent` fires; `{1, s}`-independence splits
the sixteen components.  **No new obstruction class appears at `d = 16`.**

## What this file proves (all axiom-clean)

* `sedecic_descent` — the `d = 16` descent over any field, from
  `¬IsSquare c ∧ ¬IsSquare (−c)`, via `octic_descent` over the single quadratic adjunction.
* `sedecic_norm_forces_trivial` — the `d = 16` genus statement in `F[X][Y]`.
* `dBlockIndependence_sixteen` — **`DBlockIndependence F 16 q D g` for every squarefree `g`
  of positive degree, `16 ∣ q − 1`, at budget `16D + 15·deg g < q`** — the r25-predicted
  shape, confirmed.

## Honest assessment of the generic `2^k` induction (task (b))

The recursion is now VALIDATED at three consecutive rungs (4, 8, 16) with zero new
obstructions, and every step of this file was produced mechanically from the r25 file by the
documented rules.  The generic `dBlockIndependence_two_pow` is NOT a one-session job,
because the generic statement forces a change of proof technology, not just of statement:
(i) the norm-block equations must become `Fin (2^k)`-indexed `Finset` convolutions, so the
`linear_combination` closing of the fold/regroup identities (a single `ring` certificate at
each fixed `d`) must be replaced by genuine `Finset.sum` reindexing arguments
(Cauchy-product/antidiagonal manipulation under `subq` and under the `K(s)`-regrouping); and
(ii) the block-degree bookkeeping must become a lemma about convolution coefficients rather
than a per-monomial chain.  Both are standard but each is its own multi-brick lane.  The
right generic skeleton is now, however, completely pinned by rounds 24–26: a single
`descent_step` lemma (`2^(k+1)`-descent over `K` ⟸ `2^k`-descent over `K(√c)`) whose three
inputs — the convolution regrouping identity, the telescoping side condition
`¬IsSquare(±√c) ⟸ ¬IsSquare c ∧ ¬IsSquare (−c)` (proved here verbatim for the third time —
THIS part is already generic), and `{1,√c}`-splitting (also already generic) — are exactly
the three blocks of `sedecic_descent` below.
-/

namespace ArkLib.ProximityGap.Frontier.R26D16

open Polynomial ArkLib.ProximityGap.StepanovNonVanishing
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence
open ArkLib.ProximityGap.Frontier.R25D8Descent

set_option linter.unusedFintypeInType false

variable {F : Type*} [Field F]

/-! ## 0. `Fin` sum expansion helpers (Mathlib stops at `sum_univ_eight`) -/

section SumUniv

variable {M : Type*} [AddCommMonoid M]

theorem sum_univ_nine (f : Fin 9 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

theorem sum_univ_ten (f : Fin 10 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, sum_univ_nine]
  rfl

theorem sum_univ_eleven (f : Fin 11 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  rw [Fin.sum_univ_castSucc, sum_univ_ten]
  rfl

theorem sum_univ_twelve (f : Fin 12 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  rw [Fin.sum_univ_castSucc, sum_univ_eleven]
  rfl

theorem sum_univ_thirteen (f : Fin 13 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11
      + f 12 := by
  rw [Fin.sum_univ_castSucc, sum_univ_twelve]
  rfl

theorem sum_univ_fourteen (f : Fin 14 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11
      + f 12 + f 13 := by
  rw [Fin.sum_univ_castSucc, sum_univ_thirteen]
  rfl

theorem sum_univ_fifteen (f : Fin 15 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11
      + f 12 + f 13 + f 14 := by
  rw [Fin.sum_univ_castSucc, sum_univ_fourteen]
  rfl

theorem sum_univ_sixteen (f : Fin 16 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11
      + f 12 + f 13 + f 14 + f 15 := by
  rw [Fin.sum_univ_castSucc, sum_univ_fifteen]
  rfl

end SumUniv

/-! ## 1. The sedecic descent — octic descent over the quadratic adjunction `K(√c)` -/

set_option maxHeartbeats 3200000 in
-- The AdjoinRoot representation and the four regrouped octic linear_combinations are large.
/-- **Sedecic descent.**  Over any field `K`, if `c` and `−c` are both non-squares, the eight
component equations of the sedecic norm form force `a₀ = ⋯ = a₁₅ = 0`.  Proof: adjoin ONE
square root `s = √c`; the eight equations regroup into the four r25 octic equations over
`K(s)` with parameter `s` (correction quotients `c_{j+8} + s·c_{j+12}` on `s² = c`);
`¬IsSquare (±s)` in `K(s)` reduces to `¬IsSquare (−c)` exactly as at `d = 8`;
`octic_descent` fires; `{1, s}`-independence splits the components. -/
theorem sedecic_descent {K : Type*} [Field K]
    (c a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    (h0 : a0 ^ 2 + c * (2 * a2 * a14 + 2 * a4 * a12 + 2 * a6 * a10 + a8 ^ 2
      - 2 * a1 * a15 - 2 * a3 * a13 - 2 * a5 * a11 - 2 * a7 * a9) = 0)
    (h1 : 2 * a0 * a2 - a1 ^ 2 + c * (2 * a4 * a14 + 2 * a6 * a12 + 2 * a8 * a10
      - 2 * a3 * a15 - 2 * a5 * a13 - 2 * a7 * a11 - a9 ^ 2) = 0)
    (h2 : 2 * a0 * a4 + a2 ^ 2 - 2 * a1 * a3 + c * (2 * a6 * a14 + 2 * a8 * a12 + a10 ^ 2
      - 2 * a5 * a15 - 2 * a7 * a13 - 2 * a9 * a11) = 0)
    (h3 : 2 * a0 * a6 + 2 * a2 * a4 - 2 * a1 * a5 - a3 ^ 2 + c * (2 * a8 * a14
      + 2 * a10 * a12 - 2 * a7 * a15 - 2 * a9 * a13 - a11 ^ 2) = 0)
    (h4 : 2 * a0 * a8 + 2 * a2 * a6 + a4 ^ 2 - 2 * a1 * a7 - 2 * a3 * a5
      + c * (2 * a10 * a14 + a12 ^ 2 - 2 * a9 * a15 - 2 * a11 * a13) = 0)
    (h5 : 2 * a0 * a10 + 2 * a2 * a8 + 2 * a4 * a6 - 2 * a1 * a9 - 2 * a3 * a7 - a5 ^ 2
      + c * (2 * a12 * a14 - 2 * a11 * a15 - a13 ^ 2) = 0)
    (h6 : 2 * a0 * a12 + 2 * a2 * a10 + 2 * a4 * a8 + a6 ^ 2 - 2 * a1 * a11 - 2 * a3 * a9
      - 2 * a5 * a7 + c * (a14 ^ 2 - 2 * a13 * a15) = 0)
    (h7 : 2 * a0 * a14 + 2 * a2 * a12 + 2 * a4 * a10 + 2 * a6 * a8 - 2 * a1 * a13
      - 2 * a3 * a11 - 2 * a5 * a9 - a7 ^ 2 - c * a15 ^ 2 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a7 = 0
      ∧ a8 = 0 ∧ a9 = 0 ∧ a10 = 0 ∧ a11 = 0 ∧ a12 = 0 ∧ a13 = 0 ∧ a14 = 0 ∧ a15 = 0 := by
  -- the quadratic adjunction K(√c)  (verbatim r25)
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
  -- ±s are non-squares in K(s): the Kummer condition, from ¬IsSquare (−c)  (verbatim r25)
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
  -- map the eight hypotheses into K(s)
  have hι0 : (ι a0) ^ 2 + ι c * (2 * ι a2 * ι a14 + 2 * ι a4 * ι a12 + 2 * ι a6 * ι a10
      + (ι a8) ^ 2 - 2 * ι a1 * ι a15 - 2 * ι a3 * ι a13 - 2 * ι a5 * ι a11
      - 2 * ι a7 * ι a9) = 0 := by
    have h := congrArg ι h0
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι1 : 2 * ι a0 * ι a2 - (ι a1) ^ 2 + ι c * (2 * ι a4 * ι a14 + 2 * ι a6 * ι a12
      + 2 * ι a8 * ι a10 - 2 * ι a3 * ι a15 - 2 * ι a5 * ι a13 - 2 * ι a7 * ι a11
      - (ι a9) ^ 2) = 0 := by
    have h := congrArg ι h1
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι2 : 2 * ι a0 * ι a4 + (ι a2) ^ 2 - 2 * ι a1 * ι a3 + ι c * (2 * ι a6 * ι a14
      + 2 * ι a8 * ι a12 + (ι a10) ^ 2 - 2 * ι a5 * ι a15 - 2 * ι a7 * ι a13
      - 2 * ι a9 * ι a11) = 0 := by
    have h := congrArg ι h2
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι3 : 2 * ι a0 * ι a6 + 2 * ι a2 * ι a4 - 2 * ι a1 * ι a5 - (ι a3) ^ 2
      + ι c * (2 * ι a8 * ι a14 + 2 * ι a10 * ι a12 - 2 * ι a7 * ι a15 - 2 * ι a9 * ι a13
      - (ι a11) ^ 2) = 0 := by
    have h := congrArg ι h3
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι4 : 2 * ι a0 * ι a8 + 2 * ι a2 * ι a6 + (ι a4) ^ 2 - 2 * ι a1 * ι a7
      - 2 * ι a3 * ι a5 + ι c * (2 * ι a10 * ι a14 + (ι a12) ^ 2 - 2 * ι a9 * ι a15
      - 2 * ι a11 * ι a13) = 0 := by
    have h := congrArg ι h4
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι5 : 2 * ι a0 * ι a10 + 2 * ι a2 * ι a8 + 2 * ι a4 * ι a6 - 2 * ι a1 * ι a9
      - 2 * ι a3 * ι a7 - (ι a5) ^ 2 + ι c * (2 * ι a12 * ι a14 - 2 * ι a11 * ι a15
      - (ι a13) ^ 2) = 0 := by
    have h := congrArg ι h5
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι6 : 2 * ι a0 * ι a12 + 2 * ι a2 * ι a10 + 2 * ι a4 * ι a8 + (ι a6) ^ 2
      - 2 * ι a1 * ι a11 - 2 * ι a3 * ι a9 - 2 * ι a5 * ι a7 + ι c * ((ι a14) ^ 2
      - 2 * ι a13 * ι a15) = 0 := by
    have h := congrArg ι h6
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  have hι7 : 2 * ι a0 * ι a14 + 2 * ι a2 * ι a12 + 2 * ι a4 * ι a10 + 2 * ι a6 * ι a8
      - 2 * ι a1 * ι a13 - 2 * ι a3 * ι a11 - 2 * ι a5 * ι a9 - (ι a7) ^ 2
      - ι c * (ι a15) ^ 2 = 0 := by
    have h := congrArg ι h7
    simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_zero] using h
  -- regroup: the four octic hypotheses over K(s) with parameter s
  -- (correction quotients K_j = c_{j+8} + s·c_{j+12}, verified in probe_r26_d16.py §D)
  have H0 : (ι a0 + ι a8 * s) ^ 2
      + s * (2 * (ι a2 + ι a10 * s) * (ι a6 + ι a14 * s) + (ι a4 + ι a12 * s) ^ 2
        - 2 * (ι a1 + ι a9 * s) * (ι a7 + ι a15 * s)
        - 2 * (ι a3 + ι a11 * s) * (ι a5 + ι a13 * s)) = 0 := by
    linear_combination hι0 + s * hι4
      + (2 * ι a2 * ι a14 + 2 * ι a4 * ι a12 + 2 * ι a6 * ι a10 + (ι a8) ^ 2
        - 2 * ι a1 * ι a15 - 2 * ι a3 * ι a13 - 2 * ι a5 * ι a11 - 2 * ι a7 * ι a9
        + s * (2 * ι a10 * ι a14 + (ι a12) ^ 2 - 2 * ι a9 * ι a15
          - 2 * ι a11 * ι a13)) * hs2
  have H1 : 2 * (ι a0 + ι a8 * s) * (ι a2 + ι a10 * s) - (ι a1 + ι a9 * s) ^ 2
      + s * (2 * (ι a4 + ι a12 * s) * (ι a6 + ι a14 * s)
        - 2 * (ι a3 + ι a11 * s) * (ι a7 + ι a15 * s) - (ι a5 + ι a13 * s) ^ 2) = 0 := by
    linear_combination hι1 + s * hι5
      + (2 * ι a4 * ι a14 + 2 * ι a6 * ι a12 + 2 * ι a8 * ι a10 - 2 * ι a3 * ι a15
        - 2 * ι a5 * ι a13 - 2 * ι a7 * ι a11 - (ι a9) ^ 2
        + s * (2 * ι a12 * ι a14 - 2 * ι a11 * ι a15 - (ι a13) ^ 2)) * hs2
  have H2 : 2 * (ι a0 + ι a8 * s) * (ι a4 + ι a12 * s) + (ι a2 + ι a10 * s) ^ 2
      - 2 * (ι a1 + ι a9 * s) * (ι a3 + ι a11 * s)
      + s * ((ι a6 + ι a14 * s) ^ 2
        - 2 * (ι a5 + ι a13 * s) * (ι a7 + ι a15 * s)) = 0 := by
    linear_combination hι2 + s * hι6
      + (2 * ι a6 * ι a14 + 2 * ι a8 * ι a12 + (ι a10) ^ 2 - 2 * ι a5 * ι a15
        - 2 * ι a7 * ι a13 - 2 * ι a9 * ι a11
        + s * ((ι a14) ^ 2 - 2 * ι a13 * ι a15)) * hs2
  have H3 : 2 * (ι a0 + ι a8 * s) * (ι a6 + ι a14 * s)
      + 2 * (ι a2 + ι a10 * s) * (ι a4 + ι a12 * s)
      - 2 * (ι a1 + ι a9 * s) * (ι a5 + ι a13 * s) - (ι a3 + ι a11 * s) ^ 2
      - s * (ι a7 + ι a15 * s) ^ 2 = 0 := by
    linear_combination hι3 + s * hι7
      + (2 * ι a8 * ι a14 + 2 * ι a10 * ι a12 - 2 * ι a7 * ι a15 - 2 * ι a9 * ι a13
        - (ι a11) ^ 2 - s * (ι a15) ^ 2) * hs2
  -- the r25 octic descent fires over K(s)
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7⟩ := octic_descent s
    (ι a0 + ι a8 * s) (ι a1 + ι a9 * s) (ι a2 + ι a10 * s) (ι a3 + ι a11 * s)
    (ι a4 + ι a12 * s) (ι a5 + ι a13 * s) (ι a6 + ι a14 * s) (ι a7 + ι a15 * s)
    hs_nsq hns_nsq H0 H1 H2 H3
  obtain ⟨e0, e8⟩ := hindep _ _ u0
  obtain ⟨e1, e9⟩ := hindep _ _ u1
  obtain ⟨e2, e10⟩ := hindep _ _ u2
  obtain ⟨e3, e11⟩ := hindep _ _ u3
  obtain ⟨e4, e12⟩ := hindep _ _ u4
  obtain ⟨e5, e13⟩ := hindep _ _ u5
  obtain ⟨e6, e14⟩ := hindep _ _ u6
  obtain ⟨e7, e15⟩ := hindep _ _ u7
  exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩

/-! ## 2. The sedecic genus statement in `F[X][Y]` -/

set_option maxHeartbeats 3200000 in
-- The fraction-field descent performs several large polynomial-map normalizations.
/-- **The `d = 16` genus statement, PROVEN** (sedecic analogue of the r25
`octic_norm_forces_trivial`).  Route: map into `K = Frac(F(X)[Y])`, set `c = g(Y)/g(X)`;
both `±c` non-squares (unit multiples of the squarefree positive-degree `g(Y)`), then
`sedecic_descent`. -/
theorem sedecic_norm_forces_trivial [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Polynomial (Polynomial F))
    (h0 : C g * A0 ^ 2 + (g.map C) * (2 * A2 * A14 + 2 * A4 * A12 + 2 * A6 * A10 + A8 ^ 2
      - 2 * A1 * A15 - 2 * A3 * A13 - 2 * A5 * A11 - 2 * A7 * A9) = 0)
    (h1 : C g * (2 * A0 * A2 - A1 ^ 2) + (g.map C) * (2 * A4 * A14 + 2 * A6 * A12
      + 2 * A8 * A10 - 2 * A3 * A15 - 2 * A5 * A13 - 2 * A7 * A11 - A9 ^ 2) = 0)
    (h2 : C g * (2 * A0 * A4 + A2 ^ 2 - 2 * A1 * A3) + (g.map C) * (2 * A6 * A14
      + 2 * A8 * A12 + A10 ^ 2 - 2 * A5 * A15 - 2 * A7 * A13 - 2 * A9 * A11) = 0)
    (h3 : C g * (2 * A0 * A6 + 2 * A2 * A4 - 2 * A1 * A5 - A3 ^ 2) + (g.map C)
      * (2 * A8 * A14 + 2 * A10 * A12 - 2 * A7 * A15 - 2 * A9 * A13 - A11 ^ 2) = 0)
    (h4 : C g * (2 * A0 * A8 + 2 * A2 * A6 + A4 ^ 2 - 2 * A1 * A7 - 2 * A3 * A5)
      + (g.map C) * (2 * A10 * A14 + A12 ^ 2 - 2 * A9 * A15 - 2 * A11 * A13) = 0)
    (h5 : C g * (2 * A0 * A10 + 2 * A2 * A8 + 2 * A4 * A6 - 2 * A1 * A9 - 2 * A3 * A7
      - A5 ^ 2) + (g.map C) * (2 * A12 * A14 - 2 * A11 * A15 - A13 ^ 2) = 0)
    (h6 : C g * (2 * A0 * A12 + 2 * A2 * A10 + 2 * A4 * A8 + A6 ^ 2 - 2 * A1 * A11
      - 2 * A3 * A9 - 2 * A5 * A7) + (g.map C) * (A14 ^ 2 - 2 * A13 * A15) = 0)
    (h7 : C g * (2 * A0 * A14 + 2 * A2 * A12 + 2 * A4 * A10 + 2 * A6 * A8 - 2 * A1 * A13
      - 2 * A3 * A11 - 2 * A5 * A9 - A7 ^ 2) - (g.map C) * A15 ^ 2 = 0) :
    A0 = 0 ∧ A1 = 0 ∧ A2 = 0 ∧ A3 = 0 ∧ A4 = 0 ∧ A5 = 0 ∧ A6 = 0 ∧ A7 = 0
      ∧ A8 = 0 ∧ A9 = 0 ∧ A10 = 0 ∧ A11 = 0 ∧ A12 = 0 ∧ A13 = 0 ∧ A14 = 0 ∧ A15 = 0 := by
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
  set a8 := ψ (φ A8) with ha8def
  set a9 := ψ (φ A9) with ha9def
  set a10 := ψ (φ A10) with ha10def
  set a11 := ψ (φ A11) with ha11def
  set a12 := ψ (φ A12) with ha12def
  set a13 := ψ (φ A13) with ha13def
  set a14 := ψ (φ A14) with ha14def
  set a15 := ψ (φ A15) with ha15def
  set γK := ψ (C (ι g)) with hγKdef
  set GK := ψ G with hGKdef
  have hγK0 : γK ≠ 0 := fun h => by
    have h2 : (C (ι g) : Polynomial (RatFunc F)) = 0 := hψinj (h.trans (map_zero ψ).symm)
    rw [C_eq_zero] at h2
    exact hιg0 h2
  set c := GK / γK with hcdef
  have hGKc : GK = c * γK := by rw [hcdef, div_mul_cancel₀ _ hγK0]
  -- map the eight hypotheses through ψ ∘ φ
  have h0K : γK * a0 ^ 2 + GK * (2 * a2 * a14 + 2 * a4 * a12 + 2 * a6 * a10 + a8 ^ 2
      - 2 * a1 * a15 - 2 * a3 * a13 - 2 * a5 * a11 - 2 * a7 * a9) = 0 := by
    have h := congrArg ψ (congrArg φ h0)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h1K : γK * (2 * a0 * a2 - a1 ^ 2) + GK * (2 * a4 * a14 + 2 * a6 * a12 + 2 * a8 * a10
      - 2 * a3 * a15 - 2 * a5 * a13 - 2 * a7 * a11 - a9 ^ 2) = 0 := by
    have h := congrArg ψ (congrArg φ h1)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h2K : γK * (2 * a0 * a4 + a2 ^ 2 - 2 * a1 * a3) + GK * (2 * a6 * a14 + 2 * a8 * a12
      + a10 ^ 2 - 2 * a5 * a15 - 2 * a7 * a13 - 2 * a9 * a11) = 0 := by
    have h := congrArg ψ (congrArg φ h2)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h3K : γK * (2 * a0 * a6 + 2 * a2 * a4 - 2 * a1 * a5 - a3 ^ 2) + GK * (2 * a8 * a14
      + 2 * a10 * a12 - 2 * a7 * a15 - 2 * a9 * a13 - a11 ^ 2) = 0 := by
    have h := congrArg ψ (congrArg φ h3)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h4K : γK * (2 * a0 * a8 + 2 * a2 * a6 + a4 ^ 2 - 2 * a1 * a7 - 2 * a3 * a5)
      + GK * (2 * a10 * a14 + a12 ^ 2 - 2 * a9 * a15 - 2 * a11 * a13) = 0 := by
    have h := congrArg ψ (congrArg φ h4)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h5K : γK * (2 * a0 * a10 + 2 * a2 * a8 + 2 * a4 * a6 - 2 * a1 * a9 - 2 * a3 * a7
      - a5 ^ 2) + GK * (2 * a12 * a14 - 2 * a11 * a15 - a13 ^ 2) = 0 := by
    have h := congrArg ψ (congrArg φ h5)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h6K : γK * (2 * a0 * a12 + 2 * a2 * a10 + 2 * a4 * a8 + a6 ^ 2 - 2 * a1 * a11
      - 2 * a3 * a9 - 2 * a5 * a7) + GK * (a14 ^ 2 - 2 * a13 * a15) = 0 := by
    have h := congrArg ψ (congrArg φ h6)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  have h7K : γK * (2 * a0 * a14 + 2 * a2 * a12 + 2 * a4 * a10 + 2 * a6 * a8 - 2 * a1 * a13
      - 2 * a3 * a11 - 2 * a5 * a9 - a7 ^ 2) - GK * a15 ^ 2 = 0 := by
    have h := congrArg ψ (congrArg φ h7)
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hφC, hφmap] using h
  -- normalize to the descent shape
  have h0' : a0 ^ 2 + c * (2 * a2 * a14 + 2 * a4 * a12 + 2 * a6 * a10 + a8 ^ 2
      - 2 * a1 * a15 - 2 * a3 * a13 - 2 * a5 * a11 - 2 * a7 * a9) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h0K - (2 * a2 * a14 + 2 * a4 * a12 + 2 * a6 * a10 + a8 ^ 2
      - 2 * a1 * a15 - 2 * a3 * a13 - 2 * a5 * a11 - 2 * a7 * a9) * hGKc
  have h1' : 2 * a0 * a2 - a1 ^ 2 + c * (2 * a4 * a14 + 2 * a6 * a12 + 2 * a8 * a10
      - 2 * a3 * a15 - 2 * a5 * a13 - 2 * a7 * a11 - a9 ^ 2) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h1K - (2 * a4 * a14 + 2 * a6 * a12 + 2 * a8 * a10 - 2 * a3 * a15
      - 2 * a5 * a13 - 2 * a7 * a11 - a9 ^ 2) * hGKc
  have h2' : 2 * a0 * a4 + a2 ^ 2 - 2 * a1 * a3 + c * (2 * a6 * a14 + 2 * a8 * a12
      + a10 ^ 2 - 2 * a5 * a15 - 2 * a7 * a13 - 2 * a9 * a11) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h2K - (2 * a6 * a14 + 2 * a8 * a12 + a10 ^ 2 - 2 * a5 * a15
      - 2 * a7 * a13 - 2 * a9 * a11) * hGKc
  have h3' : 2 * a0 * a6 + 2 * a2 * a4 - 2 * a1 * a5 - a3 ^ 2 + c * (2 * a8 * a14
      + 2 * a10 * a12 - 2 * a7 * a15 - 2 * a9 * a13 - a11 ^ 2) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h3K - (2 * a8 * a14 + 2 * a10 * a12 - 2 * a7 * a15 - 2 * a9 * a13
      - a11 ^ 2) * hGKc
  have h4' : 2 * a0 * a8 + 2 * a2 * a6 + a4 ^ 2 - 2 * a1 * a7 - 2 * a3 * a5
      + c * (2 * a10 * a14 + a12 ^ 2 - 2 * a9 * a15 - 2 * a11 * a13) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h4K - (2 * a10 * a14 + a12 ^ 2 - 2 * a9 * a15
      - 2 * a11 * a13) * hGKc
  have h5' : 2 * a0 * a10 + 2 * a2 * a8 + 2 * a4 * a6 - 2 * a1 * a9 - 2 * a3 * a7 - a5 ^ 2
      + c * (2 * a12 * a14 - 2 * a11 * a15 - a13 ^ 2) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h5K - (2 * a12 * a14 - 2 * a11 * a15 - a13 ^ 2) * hGKc
  have h6' : 2 * a0 * a12 + 2 * a2 * a10 + 2 * a4 * a8 + a6 ^ 2 - 2 * a1 * a11
      - 2 * a3 * a9 - 2 * a5 * a7 + c * (a14 ^ 2 - 2 * a13 * a15) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h6K - (a14 ^ 2 - 2 * a13 * a15) * hGKc
  have h7' : 2 * a0 * a14 + 2 * a2 * a12 + 2 * a4 * a10 + 2 * a6 * a8 - 2 * a1 * a13
      - 2 * a3 * a11 - 2 * a5 * a9 - a7 ^ 2 - c * a15 ^ 2 = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h7K + a15 ^ 2 * hGKc
  -- non-square conditions (verbatim r24/r25)
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
  obtain ⟨hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13,
    hz14, hz15⟩ := sedecic_descent c a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    hc hnc h0' h1' h2' h3' h4' h5' h6' h7'
  refine ⟨hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_),
    hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_),
    hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_),
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
  · exact hz8
  · exact hz9
  · exact hz10
  · exact hz11
  · exact hz12
  · exact hz13
  · exact hz14
  · exact hz15

/-! ## 3. The main theorem: `DBlockIndependence` at `d = 16` -/

set_option maxHeartbeats 6400000 in
-- The 16-to-8 conjugate-fold linear_combination and degree bookkeeping are large.
/-- **`DBlockIndependence F 16 q D g`, PROVEN** — the third `2`-power rung of the r22 target,
at the r25-predicted budget `16D + 15·deg g < q`, for `16 ∣ q − 1` (oddness is automatic).

Step 1 folds the 16-block relation via the alternating conjugate and `g^q = g(X^q)` into an
8-block relation whose blocks are the sedecic norm blocks `E₀…E₇`; `dBlockIndependence_eight`
(the r25 result) fires once and gives `E_j = 0`.  Step 2 is `sedecic_norm_forces_trivial`. -/
theorem dBlockIndependence_sixteen [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (h16 : 16 ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 16 * D + 15 * g.natDegree < Fintype.card F) :
    DBlockIndependence F 16 (Fintype.card F) D g := by
  intro A hblk hsum j
  set q := Fintype.card F with hqdef
  obtain ⟨e, he⟩ := h16
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hqe : q = 16 * e + 1 := by omega
  have h8dvd : 8 ∣ (q - 1) := ⟨2 * e, by omega⟩
  have h16e : (q - 1) / 16 = e := by omega
  have h8e : (q - 1) / 8 = 2 * e := by omega
  -- the folded 16-block relation
  have hsum16 : subq q (A 0) + g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
      + g ^ (3 * e) * subq q (A 3) + g ^ (4 * e) * subq q (A 4)
      + g ^ (5 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 6)
      + g ^ (7 * e) * subq q (A 7) + g ^ (8 * e) * subq q (A 8)
      + g ^ (9 * e) * subq q (A 9) + g ^ (10 * e) * subq q (A 10)
      + g ^ (11 * e) * subq q (A 11) + g ^ (12 * e) * subq q (A 12)
      + g ^ (13 * e) * subq q (A 13) + g ^ (14 * e) * subq q (A 14)
      + g ^ (15 * e) * subq q (A 15) = 0 := by
    have h := hsum
    rw [sum_univ_sixteen] at h
    have h0v : ((0 : Fin 16) : ℕ) = 0 := rfl
    have h1v : ((1 : Fin 16) : ℕ) = 1 := rfl
    have h2v : ((2 : Fin 16) : ℕ) = 2 := rfl
    have h3v : ((3 : Fin 16) : ℕ) = 3 := rfl
    have h4v : ((4 : Fin 16) : ℕ) = 4 := rfl
    have h5v : ((5 : Fin 16) : ℕ) = 5 := rfl
    have h6v : ((6 : Fin 16) : ℕ) = 6 := rfl
    have h7v : ((7 : Fin 16) : ℕ) = 7 := rfl
    have h8v : ((8 : Fin 16) : ℕ) = 8 := rfl
    have h9v : ((9 : Fin 16) : ℕ) = 9 := rfl
    have h10v : ((10 : Fin 16) : ℕ) = 10 := rfl
    have h11v : ((11 : Fin 16) : ℕ) = 11 := rfl
    have h12v : ((12 : Fin 16) : ℕ) = 12 := rfl
    have h13v : ((13 : Fin 16) : ℕ) = 13 := rfl
    have h14v : ((14 : Fin 16) : ℕ) = 14 := rfl
    have h15v : ((15 : Fin 16) : ℕ) = 15 := rfl
    rw [h0v, h1v, h2v, h3v, h4v, h5v, h6v, h7v, h8v, h9v, h10v, h11v, h12v, h13v, h14v,
      h15v, h16e] at h
    linear_combination h
  -- the sedecic norm blocks E_j = C g · c_j + ĝ · c_{j+8}
  set E0 : Polynomial (Polynomial F) := C g * (A 0) ^ 2
    + (g.map C) * (2 * (A 2) * (A 14) + 2 * (A 4) * (A 12) + 2 * (A 6) * (A 10) + (A 8) ^ 2
      - 2 * (A 1) * (A 15) - 2 * (A 3) * (A 13) - 2 * (A 5) * (A 11) - 2 * (A 7) * (A 9))
    with hE0def
  set E1 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 2) - (A 1) ^ 2)
    + (g.map C) * (2 * (A 4) * (A 14) + 2 * (A 6) * (A 12) + 2 * (A 8) * (A 10)
      - 2 * (A 3) * (A 15) - 2 * (A 5) * (A 13) - 2 * (A 7) * (A 11) - (A 9) ^ 2)
    with hE1def
  set E2 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 4) + (A 2) ^ 2
      - 2 * (A 1) * (A 3))
    + (g.map C) * (2 * (A 6) * (A 14) + 2 * (A 8) * (A 12) + (A 10) ^ 2
      - 2 * (A 5) * (A 15) - 2 * (A 7) * (A 13) - 2 * (A 9) * (A 11)) with hE2def
  set E3 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 6) + 2 * (A 2) * (A 4)
      - 2 * (A 1) * (A 5) - (A 3) ^ 2)
    + (g.map C) * (2 * (A 8) * (A 14) + 2 * (A 10) * (A 12) - 2 * (A 7) * (A 15)
      - 2 * (A 9) * (A 13) - (A 11) ^ 2) with hE3def
  set E4 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 8) + 2 * (A 2) * (A 6)
      + (A 4) ^ 2 - 2 * (A 1) * (A 7) - 2 * (A 3) * (A 5))
    + (g.map C) * (2 * (A 10) * (A 14) + (A 12) ^ 2 - 2 * (A 9) * (A 15)
      - 2 * (A 11) * (A 13)) with hE4def
  set E5 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 10) + 2 * (A 2) * (A 8)
      + 2 * (A 4) * (A 6) - 2 * (A 1) * (A 9) - 2 * (A 3) * (A 7) - (A 5) ^ 2)
    + (g.map C) * (2 * (A 12) * (A 14) - 2 * (A 11) * (A 15) - (A 13) ^ 2) with hE5def
  set E6 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 12) + 2 * (A 2) * (A 10)
      + 2 * (A 4) * (A 8) + (A 6) ^ 2 - 2 * (A 1) * (A 11) - 2 * (A 3) * (A 9)
      - 2 * (A 5) * (A 7))
    + (g.map C) * ((A 14) ^ 2 - 2 * (A 13) * (A 15)) with hE6def
  set E7 : Polynomial (Polynomial F) := C g * (2 * (A 0) * (A 14) + 2 * (A 2) * (A 12)
      + 2 * (A 4) * (A 10) + 2 * (A 6) * (A 8) - 2 * (A 1) * (A 13) - 2 * (A 3) * (A 11)
      - 2 * (A 5) * (A 9) - (A 7) ^ 2)
    - (g.map C) * (A 15) ^ 2 with hE7def
  -- fold subq through the blocks
  have hgq : subq q (g.map (C : F →+* F[X])) = g ^ q := (pow_card_eq_subq_map_C g).symm
  have hSE0 : subq q E0 = g * (subq q (A 0)) ^ 2
      + g ^ q * (2 * subq q (A 2) * subq q (A 14) + 2 * subq q (A 4) * subq q (A 12)
        + 2 * subq q (A 6) * subq q (A 10) + (subq q (A 8)) ^ 2
        - 2 * subq q (A 1) * subq q (A 15) - 2 * subq q (A 3) * subq q (A 13)
        - 2 * subq q (A 5) * subq q (A 11) - 2 * subq q (A 7) * subq q (A 9)) := by
    rw [hE0def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE1 : subq q E1 = g * (2 * subq q (A 0) * subq q (A 2) - (subq q (A 1)) ^ 2)
      + g ^ q * (2 * subq q (A 4) * subq q (A 14) + 2 * subq q (A 6) * subq q (A 12)
        + 2 * subq q (A 8) * subq q (A 10) - 2 * subq q (A 3) * subq q (A 15)
        - 2 * subq q (A 5) * subq q (A 13) - 2 * subq q (A 7) * subq q (A 11)
        - (subq q (A 9)) ^ 2) := by
    rw [hE1def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE2 : subq q E2 = g * (2 * subq q (A 0) * subq q (A 4) + (subq q (A 2)) ^ 2
        - 2 * subq q (A 1) * subq q (A 3))
      + g ^ q * (2 * subq q (A 6) * subq q (A 14) + 2 * subq q (A 8) * subq q (A 12)
        + (subq q (A 10)) ^ 2 - 2 * subq q (A 5) * subq q (A 15)
        - 2 * subq q (A 7) * subq q (A 13) - 2 * subq q (A 9) * subq q (A 11)) := by
    rw [hE2def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE3 : subq q E3 = g * (2 * subq q (A 0) * subq q (A 6)
        + 2 * subq q (A 2) * subq q (A 4) - 2 * subq q (A 1) * subq q (A 5)
        - (subq q (A 3)) ^ 2)
      + g ^ q * (2 * subq q (A 8) * subq q (A 14) + 2 * subq q (A 10) * subq q (A 12)
        - 2 * subq q (A 7) * subq q (A 15) - 2 * subq q (A 9) * subq q (A 13)
        - (subq q (A 11)) ^ 2) := by
    rw [hE3def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE4 : subq q E4 = g * (2 * subq q (A 0) * subq q (A 8)
        + 2 * subq q (A 2) * subq q (A 6) + (subq q (A 4)) ^ 2
        - 2 * subq q (A 1) * subq q (A 7) - 2 * subq q (A 3) * subq q (A 5))
      + g ^ q * (2 * subq q (A 10) * subq q (A 14) + (subq q (A 12)) ^ 2
        - 2 * subq q (A 9) * subq q (A 15) - 2 * subq q (A 11) * subq q (A 13)) := by
    rw [hE4def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE5 : subq q E5 = g * (2 * subq q (A 0) * subq q (A 10)
        + 2 * subq q (A 2) * subq q (A 8) + 2 * subq q (A 4) * subq q (A 6)
        - 2 * subq q (A 1) * subq q (A 9) - 2 * subq q (A 3) * subq q (A 7)
        - (subq q (A 5)) ^ 2)
      + g ^ q * (2 * subq q (A 12) * subq q (A 14) - 2 * subq q (A 11) * subq q (A 15)
        - (subq q (A 13)) ^ 2) := by
    rw [hE5def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE6 : subq q E6 = g * (2 * subq q (A 0) * subq q (A 12)
        + 2 * subq q (A 2) * subq q (A 10) + 2 * subq q (A 4) * subq q (A 8)
        + (subq q (A 6)) ^ 2 - 2 * subq q (A 1) * subq q (A 11)
        - 2 * subq q (A 3) * subq q (A 9) - 2 * subq q (A 5) * subq q (A 7))
      + g ^ q * ((subq q (A 14)) ^ 2 - 2 * subq q (A 13) * subq q (A 15)) := by
    rw [hE6def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  have hSE7 : subq q E7 = g * (2 * subq q (A 0) * subq q (A 14)
        + 2 * subq q (A 2) * subq q (A 12) + 2 * subq q (A 4) * subq q (A 10)
        + 2 * subq q (A 6) * subq q (A 8) - 2 * subq q (A 1) * subq q (A 13)
        - 2 * subq q (A 3) * subq q (A 11) - 2 * subq q (A 5) * subq q (A 9)
        - (subq q (A 7)) ^ 2)
      - g ^ q * (subq q (A 15)) ^ 2 := by
    rw [hE7def]
    change subqHom q _ = _
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    simp only [subqHom_apply, subq_C]
    rw [hgq]
  -- the conjugate-fold identity 16 → 8
  have hkey : (subq q (A 0) + g ^ (2 * e) * subq q (A 2) + g ^ (4 * e) * subq q (A 4)
        + g ^ (6 * e) * subq q (A 6) + g ^ (8 * e) * subq q (A 8)
        + g ^ (10 * e) * subq q (A 10) + g ^ (12 * e) * subq q (A 12)
        + g ^ (14 * e) * subq q (A 14)) ^ 2
      - g ^ (2 * e) * (subq q (A 1) + g ^ (2 * e) * subq q (A 3)
        + g ^ (4 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 7)
        + g ^ (8 * e) * subq q (A 9) + g ^ (10 * e) * subq q (A 11)
        + g ^ (12 * e) * subq q (A 13) + g ^ (14 * e) * subq q (A 15)) ^ 2 = 0 := by
    linear_combination (subq q (A 0) - g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
      - g ^ (3 * e) * subq q (A 3) + g ^ (4 * e) * subq q (A 4)
      - g ^ (5 * e) * subq q (A 5) + g ^ (6 * e) * subq q (A 6)
      - g ^ (7 * e) * subq q (A 7) + g ^ (8 * e) * subq q (A 8)
      - g ^ (9 * e) * subq q (A 9) + g ^ (10 * e) * subq q (A 10)
      - g ^ (11 * e) * subq q (A 11) + g ^ (12 * e) * subq q (A 12)
      - g ^ (13 * e) * subq q (A 13) + g ^ (14 * e) * subq q (A 14)
      - g ^ (15 * e) * subq q (A 15)) * hsum16
  -- the 8-block relation for the sedecic norm blocks
  have hR : g ^ (0 * ((q - 1) / 8)) * subq q E0 + g ^ (1 * ((q - 1) / 8)) * subq q E1
      + g ^ (2 * ((q - 1) / 8)) * subq q E2 + g ^ (3 * ((q - 1) / 8)) * subq q E3
      + g ^ (4 * ((q - 1) / 8)) * subq q E4 + g ^ (5 * ((q - 1) / 8)) * subq q E5
      + g ^ (6 * ((q - 1) / 8)) * subq q E6 + g ^ (7 * ((q - 1) / 8)) * subq q E7 = 0 := by
    have hgq16 : g ^ q = g ^ (16 * e + 1) := by rw [← hqe]
    rw [h8e, hSE0, hSE1, hSE2, hSE3, hSE4, hSE5, hSE6, hSE7, hgq16]
    linear_combination g * hkey
  -- block-degree bookkeeping: E_j blocks ≤ deg g + 2D
  have hsq : ∀ i : Fin 16, ∀ k, (((A i) ^ 2).coeff k).natDegree ≤ 2 * D := fun i =>
    blocks_pow_le (hblk i) 2
  have hp : ∀ i i' : Fin 16, ∀ k, ((2 * (A i) * (A i')).coeff k).natDegree ≤ 2 * D := by
    intro i i' k
    have := blocks_two_mul_mul_le (hblk i) (hblk i') k
    omega
  have hb0 : ∀ k, (E0.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE0def, coeff_add]
    have ht1 := blocks_C_mul_le g (hsq 0) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_sub_le (blocks_sub_le
        (blocks_add_le (blocks_add_le (blocks_add_le (hp 2 14) (hp 4 12)) (hp 6 10))
          (hsq 8)) (hp 1 15)) (hp 3 13)) (hp 5 11)) (hp 7 9)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb1 : ∀ k, (E1.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE1def, coeff_add]
    have ht1 := blocks_C_mul_le g (blocks_sub_le (hp 0 2) (hsq 1)) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_sub_le (blocks_sub_le
        (blocks_add_le (blocks_add_le (hp 4 14) (hp 6 12)) (hp 8 10)) (hp 3 15))
        (hp 5 13)) (hp 7 11)) (hsq 9)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb2 : ∀ k, (E2.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE2def, coeff_add]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_add_le (hp 0 4) (hsq 2)) (hp 1 3)) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_sub_le
        (blocks_add_le (blocks_add_le (hp 6 14) (hp 8 12)) (hsq 10)) (hp 5 15))
        (hp 7 13)) (hp 9 11)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb3 : ∀ k, (E3.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE3def, coeff_add]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_add_le (hp 0 6) (hp 2 4)) (hp 1 5)) (hsq 3)) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_sub_le
        (blocks_add_le (hp 8 14) (hp 10 12)) (hp 7 15)) (hp 9 13)) (hsq 11)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb4 : ∀ k, (E4.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE4def, coeff_add]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_add_le (blocks_add_le (hp 0 8) (hp 2 6))
        (hsq 4)) (hp 1 7)) (hp 3 5)) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_add_le (hp 10 14) (hsq 12)) (hp 9 15))
        (hp 11 13)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb5 : ∀ k, (E5.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE5def, coeff_add]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_sub_le (blocks_add_le (blocks_add_le
        (hp 0 10) (hp 2 8)) (hp 4 6)) (hp 1 9)) (hp 3 7)) (hsq 5)) k
    have ht2 := blocks_mapC_mul_le g
      (blocks_sub_le (blocks_sub_le (hp 12 14) (hp 11 15)) (hsq 13)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb6 : ∀ k, (E6.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE6def, coeff_add]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_sub_le (blocks_add_le (blocks_add_le
        (blocks_add_le (hp 0 12) (hp 2 10)) (hp 4 8)) (hsq 6)) (hp 1 11)) (hp 3 9))
        (hp 5 7)) k
    have ht2 := blocks_mapC_mul_le g (blocks_sub_le (hsq 14) (hp 13 15)) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb7 : ∀ k, (E7.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hE7def, coeff_sub]
    have ht1 := blocks_C_mul_le g
      (blocks_sub_le (blocks_sub_le (blocks_sub_le (blocks_sub_le (blocks_add_le
        (blocks_add_le (blocks_add_le (hp 0 14) (hp 2 12)) (hp 4 10)) (hp 6 8))
        (hp 1 13)) (hp 3 11)) (hp 5 9)) (hsq 7)) k
    have ht2 := blocks_mapC_mul_le g (hsq 15) k
    exact (natDegree_sub_le _ _).trans (max_le ht1 (by omega))
  -- the d = 8 result fires once
  have hD8 : 8 * (g.natDegree + 2 * D) + 7 * g.natDegree < q := by omega
  have hEz := dBlockIndependence_eight g hg hdeg h8dvd hD8 ![E0, E1, E2, E3, E4, E5, E6, E7]
    (by
      intro i
      fin_cases i
      · exact hb0
      · exact hb1
      · exact hb2
      · exact hb3
      · exact hb4
      · exact hb5
      · exact hb6
      · exact hb7)
    (by rw [Fin.sum_univ_eight]; exact hR)
  have hE0z : E0 = 0 := hEz 0
  have hE1z : E1 = 0 := hEz 1
  have hE2z : E2 = 0 := hEz 2
  have hE3z : E3 = 0 := hEz 3
  have hE4z : E4 = 0 := hEz 4
  have hE5z : E5 = 0 := hEz 5
  have hE6z : E6 = 0 := hEz 6
  have hE7z : E7 = 0 := hEz 7
  -- the sedecic descent finishes
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15⟩ :=
    sedecic_norm_forces_trivial g hg hdeg
    (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) (A 6) (A 7)
    (A 8) (A 9) (A 10) (A 11) (A 12) (A 13) (A 14) (A 15)
    (hE0def.symm.trans hE0z) (hE1def.symm.trans hE1z)
    (hE2def.symm.trans hE2z) (hE3def.symm.trans hE3z)
    (hE4def.symm.trans hE4z) (hE5def.symm.trans hE5z)
    (hE6def.symm.trans hE6z) (hE7def.symm.trans hE7z)
  fin_cases j
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact z4
  · exact z5
  · exact z6
  · exact z7
  · exact z8
  · exact z9
  · exact z10
  · exact z11
  · exact z12
  · exact z13
  · exact z14
  · exact z15

/-! ## 4. The uniform `2^k` statement over the landed rungs

The generic-`k` induction is not attempted here (see the header's honest assessment: the
fold/regroup ring certificates and the block-degree bookkeeping must be re-stated as
`Finset` convolution lemmas before an induction can be written).  What CAN be stated today,
uniformly, is the r25-predicted family shape over every landed rung — a single theorem with
the budget `2^k·D + (2^k − 1)·deg g < q` and hypothesis `2^k ∣ q − 1`, dispatching to the
four proven instances.  Any future rung extends this by one `interval_cases` branch. -/

/-- **The `2^k` tower, uniform statement over the proven rungs `k = 1, 2, 3, 4`** (i.e.
`d = 2, 4, 8, 16`): for squarefree `g` of positive degree with `2^k ∣ q − 1`, block
independence holds at the r25-predicted budget `2^k·D + (2^k − 1)·deg g < q`.  Oddness of
`q` is derived (`2 ∣ q − 1` with `q ≥ 1`). -/
theorem dBlockIndependence_two_pow [Fintype F] (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hdvd : 2 ^ k ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 2 ^ k * D + (2 ^ k - 1) * g.natDegree < Fintype.card F) :
    DBlockIndependence F (2 ^ k) (Fintype.card F) D g := by
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  interval_cases k
  · -- k = 1, d = 2
    have hq_odd : Odd (Fintype.card F) := by
      obtain ⟨e, he⟩ := hdvd
      exact ⟨e, by omega⟩
    have : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [this] at hD ⊢
    exact dBlockIndependence_two g hg hdeg hq_odd (by omega)
  · -- k = 2, d = 4
    have h4 : 4 ∣ (Fintype.card F - 1) := by
      obtain ⟨e, he⟩ := hdvd; exact ⟨e, by omega⟩
    have hq_odd : Odd (Fintype.card F) := by
      obtain ⟨e, he⟩ := hdvd
      exact ⟨2 * e, by omega⟩
    have : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [this] at hD ⊢
    exact dBlockIndependence_four g hg hdeg hq_odd h4 (by omega)
  · -- k = 3, d = 8
    have h8 : 8 ∣ (Fintype.card F - 1) := by
      obtain ⟨e, he⟩ := hdvd; exact ⟨e, by omega⟩
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [this] at hD ⊢
    exact dBlockIndependence_eight g hg hdeg h8 (by omega)
  · -- k = 4, d = 16
    have h16 : 16 ∣ (Fintype.card F - 1) := by
      obtain ⟨e, he⟩ := hdvd; exact ⟨e, by omega⟩
    have : (2 : ℕ) ^ 4 = 16 := by norm_num
    rw [this] at hD ⊢
    exact dBlockIndependence_sixteen g hg hdeg h16 (by omega)

end ArkLib.ProximityGap.Frontier.R26D16

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R26D16 in
#print axioms sedecic_descent
open ArkLib.ProximityGap.Frontier.R26D16 in
#print axioms sedecic_norm_forces_trivial
open ArkLib.ProximityGap.Frontier.R26D16 in
#print axioms dBlockIndependence_sixteen
open ArkLib.ProximityGap.Frontier.R26D16 in
#print axioms dBlockIndependence_two_pow
