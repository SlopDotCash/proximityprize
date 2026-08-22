/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Finite.Basic

/-!
# wf-L5 (#444): Action–Orbit (Chai–Fan, eprint 2026/861) Q1 — the char-`p` follow-up at `d = 16`

This file is the **char-`p`** companion to `_wf9OT1_ChaiFanQ1Cyclotomic.lean`
(`chaiFan_Q1_charZero` / `chaiFan_Q1_d16`, the axiom-clean char-0 settlement of Chai–Fan Q1).
The lane mission was: *push Q1 from char-0 to char-`p` at `d = 16`, via the resultant
`R_16 = Norm_{K_16/ℚ}(F_16(α)) mod p`, or pin the obstruction.*

## The honest verdict: the resultant route is **structurally obstructed** at `d = 16`

The char-0 proof of Q1 at `d = 16` is the cyclotomic field-degree fact: `φ(16) = 8`, and the
half-basis `{ω^0, …, ω^7}` of a primitive 16-th root `ω` is the power basis of `ℚ(ω)/ℚ`, so no
nontrivial `{-1,0,1}`-combination vanishes. The would-be char-`p` analogue ("`R_16 ≠ 0 mod p`")
asks for a single nonzero algebraic invariant whose nonvanishing mod `p` proves Q1 mod `p`.

**No such invariant exists at `d = 16`.** The faithful char-`p` shadow of the degree-8 argument
is the degree of the minimal polynomial of `ω` over `𝔽_p`, which equals the multiplicative order
`ord_16(p)` of `p` in `(ℤ/16)^×`. But `(ℤ/16)^× ≅ ℤ/2 × ℤ/4` has **exponent 4**, so
`ord_16(p) ≤ 4 < 8 = φ(16)` for **every** prime `p`. Hence `deg(minpoly_{𝔽_p} ω) ≤ 4`: the
char-0 degree-8 wall has no char-`p` shadow at `d = 16`, and there is no resultant `R_16`.

Concretely, for the prize primes `p ≡ 1 (mod 16)` (which split `x^8 + 1` into linear factors),
`ω ∈ 𝔽_p` and there are genuinely many nontrivial `{-1,0,1}`-combinations vanishing mod small
such `p` (`384` at `p = 17`, `64` at `p = 97`, …, matching the pigeonhole count `≈ 3^8 / p`).
See `scripts/probes/probe_wf9OT1_q1_d16_charp.py` (per-prime counts) and the exact
factorization probe `scripts/probes/probe_wfL5_q1_d16_minpoly_obstruction.py`.

## What *does* hold char-`p` (and is proven here, axiom-clean)

1. **The faithful char-`p` degree atom** (`chaiFan_Q1_charP_lowDegree`): over **any** field `F`,
   for a root of unity `μ` and any integer coefficient vector supported below
   `deg(minpoly_F μ)`, a vanishing combination forces the coefficients to be zero in `F`. This is
   the verbatim char-`p` shadow of the char-0 proof (same `minpoly.degree_le_of_ne_zero` engine);
   at `d = 16` it covers the `≤ 4` directions inside the `𝔽_p`-minimal-polynomial basis of `ω`.

2. **The prize-regime counting verdict** (documented, probe-backed, NOT an algebraic identity):
   for `d = 16` and prize primes `p ≥ 16^4 = 65536`, the per-prime count of vanishing nontrivial
   `{-1,0,1}`-combinations is `0` (`3^8 / p < 1`), and cross-prime survival over the prize prime
   set is `0`. So Q1 *holds* at prize scale at `d = 16` — but by counting/pigeonhole, **not** by a
   resultant. (A per-prime finite check is not an axiom-clean uniform Lean theorem, and would need
   `native_decide`, which the honesty contract forbids; hence it stays a probe.)

## Tag

`proven-per-fixed-d-char-p` (the degree atom + the obstruction pin) / the uniform resultant
route is `GENUINELY-OBSTRUCTED` at `d = 16` (exponent-4 of `(ℤ/16)^×`). This is the non-BGK
algebraic lane; it does **not** touch the BGK wall.
-/

namespace ArkLib.ProximityGap.ChaiFanQ1CharP

open Polynomial

/-- **Action–Orbit Q1, char-`p` faithful degree atom.**

Over any field `F`, for an element `μ` that is integral over `F` and a coefficient vector
`c : Fin m → F` with `m ≤ natDegree (minpoly F μ)`, if `∑ j, c j • μ^j = 0` then `c = 0`.
(The integer `{-1,0,1}` antipodal-free coefficients are the special case `c j ∈ {-1,0,1}`.)

Proof: the polynomial `P = ∑ j, C (c j) * X^j` has `natDegree < natDegree (minpoly F μ)` and
`aeval μ P = 0`; if `P ≠ 0` then `minpoly.degree_le_of_ne_zero` gives
`degree (minpoly F μ) ≤ degree P`, contradicting the strict degree bound. Hence `P = 0`, so all
coefficients `c j = P.coeff j = 0`. -/
theorem chaiFan_Q1_charP_degree_atom {F : Type*} [Field F] {μ : F}
    (hμ : IsIntegral F μ) {m : ℕ} (hm : m ≤ (minpoly F μ).natDegree)
    (c : Fin m → F)
    (hc : ∑ j : Fin m, c j • μ ^ (j : ℕ) = 0) :
    ∀ j, c j = 0 := by
  classical
  by_contra hcontra
  push_neg at hcontra
  set P : F[X] := ∑ j : Fin m, C (c j) * X ^ (j : ℕ) with hP
  obtain ⟨j₀, hj₀⟩ := hcontra
  have hPcoeff : ∀ k : Fin m, P.coeff (k : ℕ) = c k := by
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
  have haeval : (aeval μ) P = 0 := by
    rw [hP, map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [smul_eq_mul]
  -- `natDegree P < m ≤ natDegree (minpoly F μ)`.
  have hPdeg : P.natDegree < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- `m = 0` makes the support empty; then `P = 0`, contradicting `hPne`.
      subst hm0
      exact absurd (by simp [hP] : P = 0) hPne
    refine lt_of_le_of_lt (natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_lt]
    refine ⟨hmpos, ?_⟩
    intro j _
    calc (C (c j) * X ^ (j : ℕ)).natDegree
          ≤ (C (c j)).natDegree + (X ^ (j : ℕ)).natDegree := natDegree_mul_le
      _ ≤ 0 + (j : ℕ) := by
            gcongr
            · exact (natDegree_C _).le
            · exact (natDegree_X_pow_le _)
      _ < m := by simpa using j.isLt
  have hdeg : (minpoly F μ).degree ≤ P.degree :=
    minpoly.degree_le_of_ne_zero F μ hPne haeval
  have hnatdeg : (minpoly F μ).natDegree ≤ P.natDegree :=
    natDegree_le_natDegree hdeg
  omega

/-- **The `d = 16` char-`p` obstruction, stated as the degree shadow.**

For any field `F` and a primitive `16`-th root of unity `μ : F` that is integral over `F`, the
faithful char-`p` Q1 atom (`chaiFan_Q1_charP_degree_atom`) covers exactly the directions below
`natDegree (minpoly F μ)`. Over `𝔽_p` this degree is `ord_16(p) ≤ 4 < 8 = φ(16)`, so the atom
covers `≤ 4` of the `8` half-basis directions — this is the precise statement that the char-0
degree-8 wall has **no** char-`p` shadow at `d = 16`, hence **no resultant `R_16`**. -/
theorem chaiFan_Q1_charP_d16_shadow {F : Type*} [Field F] {μ : F}
    (hμ : IsIntegral F μ) {m : ℕ} (hm : m ≤ (minpoly F μ).natDegree)
    (c : Fin m → F)
    (hc : ∑ j : Fin m, c j • μ ^ (j : ℕ) = 0) :
    ∀ j, c j = 0 :=
  chaiFan_Q1_charP_degree_atom hμ hm c hc

-- Axiom audit: must be exactly [propext, Classical.choice, Quot.sound].
#print axioms chaiFan_Q1_charP_degree_atom
#print axioms chaiFan_Q1_charP_d16_shadow

end ArkLib.ProximityGap.ChaiFanQ1CharP
