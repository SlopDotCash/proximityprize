/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# wf-OT1 (#444): Action-Orbit (Chai–Fan, eprint 2026/861) Q1 at fixed `d = 2^μ`, char-0

This file settles the **char-0** content of the Chai–Fan "Action–Orbit" Q1 question at the
last clean dyadic level `d = 16` (and uniformly at every `d`), as an axiom-clean Lean
statement.

## The object (campaign reconstruction of Chai–Fan Q1)

Let `d = 2^μ`, `ω` a primitive `d`-th root of unity in `ℂ`. Then `ω^(d/2) = -1`, so every
element of `μ_d` is `± ω^j` with `0 ≤ j < d/2` (the *half-basis*). An **antipodal-free**
configuration `Y ⊆ μ_d` chooses, for each antipodal pair `{ω^j, -ω^j}`, a coefficient
`c j ∈ {-1, 0, 1}` (`0` = pick neither). Its first power sum is
`p₁(Y) = ∑_{j < d/2} c j • ω^j`.

Chai–Fan Q1 / the self-similarity `(*)_d` asks that the only antipodal-free `Y` with
`p₁(Y) = 0` is the empty one — equivalently, `Norm_{K_d/ℚ}(F_d(α)) ≠ 0`. The resultant/norm
route reduces this to a single clean algebraic fact:

> **the only `{-1,0,1}`-coefficient combination of the cyclotomic power basis
> `{1, ω, …, ω^(φ d - 1)}` that vanishes in `ℂ` is the trivial one.**

For `d = 2^μ`, `φ(d) = d/2`, so the half-basis has exactly `φ(d)` elements and is the power
basis of `ℚ(ω)/ℚ`; its `ℤ`-linear independence is the cyclotomic field-degree fact.

## What is proven here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)

* `chaiFan_Q1_charZero` : for any primitive `n`-th root of unity `μ : ℂ` and any *integer*
  coefficient vector `c : Fin (φ n) → ℤ` that is **not identically zero**,
  `∑ j, (c j : ℂ) • μ^(j:ℕ) ≠ 0`. This is the resultant/norm-nonvanishing fact for the power
  basis, valid for **every** `n` (the `{-1,0,1}` antipodal-free coefficients are a special
  case). Proof: such a vanishing combination is an integer polynomial of `natDegree < φ n`
  annihilating `μ`, contradicting `φ n ≤ natDegree (minpoly ℤ μ)`
  (`IsPrimitiveRoot.totient_le_degree_minpoly`) via `IsIntegrallyClosed.degree_le_of_ne_zero`.
* `chaiFan_Q1_d16` : the `d = 16` instantiation (`φ 16 = 8`): no nontrivial `{-1,0,1}`
  combination of `{ω^0,…,ω^7}` for a primitive 16-th root vanishes.

## Honest scope

This is a **per-fixed-`d` increment** (CHAR0 settlement of Q1), NOT the BGK wall. The char-`p`
prize-regime witnesses are pigeonhole / mod-`p` noise (`~ 3^(d/2)/p`) that do not survive
cross-prime; see `scripts/probes/probe_wf9OT1_q1_d16_charp.py` (d=16: 0 per-prime hits at
prize scale already, `3^8/p < 1`) and `_q1_d32_crossprime.py` (d=32: ~32–64 per-prime hits
matching the pigeonhole prediction, but `0` cross-prime survivors over 6 prize primes). So Q1
holds at prize scale for `d = 16, 32`, but this does not bound the worst Gauss period `M(n)`.
-/

namespace ArkLib.ProximityGap.ChaiFanQ1

open Polynomial

/-- **Action–Orbit Q1, char-0 (general `n`).**
For a primitive `n`-th root of unity `μ : ℂ`, the power basis `{1, μ, …, μ^(φ n - 1)}` is
`ℤ`-linearly independent: any integer coefficient vector `c : Fin (φ n) → ℤ` with
`∑ j, (c j : ℂ) • μ^(j:ℕ) = 0` must be identically zero.

This is the resultant/norm-nonvanishing fact underlying Chai–Fan Q1: an antipodal-free
configuration `Y ⊆ μ_d` with first power sum zero corresponds to such a `c` with entries in
`{-1, 0, 1}`, so `Y` must be empty. -/
theorem chaiFan_Q1_charZero {n : ℕ} {μ : ℂ}
    (hμ : IsPrimitiveRoot μ n) (hn : n ≠ 0)
    (c : Fin (Nat.totient n) → ℤ)
    (hc : ∑ j : Fin (Nat.totient n), (c j : ℂ) • μ ^ (j : ℕ) = 0) :
    ∀ j, c j = 0 := by
  classical
  by_contra hcontra
  push_neg at hcontra
  -- The annihilating integer polynomial `P = ∑ j, C (c j) * X^j`.
  set P : ℤ[X] := ∑ j : Fin (Nat.totient n), C (c j) * X ^ (j : ℕ) with hP
  -- `P` is nonzero, since some coefficient `c j ≠ 0`.
  obtain ⟨j₀, hj₀⟩ := hcontra
  have hPcoeff : ∀ k : Fin (Nat.totient n), P.coeff (k : ℕ) = c k := by
    intro k
    rw [hP, finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · simp [coeff_C_mul, coeff_X_pow]
    · intro b _ hbk
      have hbk' : (k : ℕ) ≠ (b : ℕ) := fun h => hbk (Fin.ext h.symm)
      simp [coeff_C_mul, coeff_X_pow, hbk']
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hPne : P ≠ 0 := by
    intro h0
    have := hPcoeff j₀
    rw [h0, coeff_zero] at this
    exact hj₀ this.symm
  -- `μ` is a root of `P`: `aeval μ P = ∑ (c j : ℂ) μ^j = 0`.
  have haeval : (aeval μ) P = 0 := by
    rw [hP, map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp
  -- Degree bound: every term has degree `< φ n`, so `natDegree P < φ n`.
  have hPdeg : P.natDegree < Nat.totient n := by
    refine lt_of_le_of_lt (natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_lt]
    refine ⟨Nat.pos_of_ne_zero ?_, ?_⟩
    · -- `φ n ≠ 0` since `n ≠ 0`
      exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    · intro j _
      calc (C (c j) * X ^ (j : ℕ)).natDegree
            ≤ (C (c j)).natDegree + (X ^ (j : ℕ)).natDegree := natDegree_mul_le
        _ ≤ 0 + (j : ℕ) := by
              gcongr
              · exact (natDegree_C _).le
              · exact (natDegree_X_pow_le _)
        _ < Nat.totient n := by simpa using j.isLt
  -- Contradiction with `φ n ≤ natDegree (minpoly ℤ μ) ≤ natDegree P`.
  have hmin : Nat.totient n ≤ (minpoly ℤ μ).natDegree := hμ.totient_le_degree_minpoly
  have hdeg : (minpoly ℤ μ).degree ≤ P.degree :=
    minpoly.IsIntegrallyClosed.degree_le_of_ne_zero hPne haeval
  have hnatdeg : (minpoly ℤ μ).natDegree ≤ P.natDegree :=
    natDegree_le_natDegree hdeg
  omega

/-- **Action–Orbit Q1, char-0, at the clean dyadic level `d = 16`.**
`φ 16 = 8`. No nontrivial `{-1,0,1}`-combination of the half-basis `{ω^0, …, ω^7}` of a
primitive 16-th root of unity vanishes, i.e. the only antipodal-free `Y ⊆ μ₁₆` with first
power sum zero is empty. -/
theorem chaiFan_Q1_d16 {μ : ℂ} (hμ : IsPrimitiveRoot μ 16)
    (c : Fin (Nat.totient 16) → ℤ)
    (hc : ∑ j : Fin (Nat.totient 16), (c j : ℂ) • μ ^ (j : ℕ) = 0) :
    ∀ j, c j = 0 :=
  chaiFan_Q1_charZero hμ (by norm_num) c hc

/-- `φ 16 = 8` (the half-basis size at the prize-relevant dyadic level). -/
example : Nat.totient 16 = 8 := by decide

-- Axiom audit: must be exactly [propext, Classical.choice, Quot.sound].
#print axioms chaiFan_Q1_charZero
#print axioms chaiFan_Q1_d16

end ArkLib.ProximityGap.ChaiFanQ1
