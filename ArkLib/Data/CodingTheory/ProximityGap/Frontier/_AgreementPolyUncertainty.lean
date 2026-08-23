/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SparseCoeffZeros
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RThinSparseRealizability

/-!
# Far-line agreement polynomial → DFT-uncertainty list-decoding radius (#407 — capstone)

This file closes the #407 c.349 chain **end-to-end over `ℂ`**: it connects the far-line
**agreement polynomial** `P = X^a + γ·X^b − c` (sparse coefficients) to the Donoho–Stark
DFT-uncertainty list-decoding-radius bound, via the substrate `sparse_coeff_zeros_le`.

## The bridge identity (char-0, clean)

The discrete Fourier transform on `ZMod N` (Mathlib's `ZMod.dft`, convention
`𝓕 c k = ∑_j stdAddChar(-(j·k)) · c j`) **is** polynomial evaluation at roots of unity. For a
coefficient vector `c : ZMod N → ℂ`, set `coeffPoly c = ∑_{j} C (c j) · X^(j.val)` (a polynomial
of degree `< N` whose `j`-th coefficient is `c j`). Then for each frequency `k`,

> `eval (stdAddChar (-k)) (coeffPoly c) = 𝓕 c k`,

because `stdAddChar(-(j·k)) = stdAddChar(-k) ^ (j.val)` (the additive character on `ZMod N` is
`ζ^•`). So the points `k` where `𝓕 c k = 0` are **exactly** the `N`-th roots of unity
`ζ_k = stdAddChar(-k)` at which `coeffPoly c` vanishes — the far-line *agreement set*. Its support
`supp c` equals the polynomial's exponent set, with card `≤ t` for a `t`-sparse signal.

## The capstone

`sparse_coeff_zeros (c) (hc : c ≠ 0) (ht : |supp c| ≤ t)`:

> a `t`-sparse `ℂ`-coefficient signal's polynomial `coeffPoly c` vanishes on at most
> `N·(1 − 1/t)` of the `N`-th roots of unity `{stdAddChar (-k) : k}`.

For `t = k+2` on `Z_n` this is the char-0 far-line agreement / list-decoding-radius bound
`≤ n·(1 − 1/(k+2))` for the smooth (`2`-power) domain. The specialization
`agreementPoly_rootsOfUnity_zeros_le` wires the explicit agreement polynomial
`X^a + C γ * X^b − c` (`deg c < k`, exponents `a, b < N`) into this bound: its `(k+2)`-sparsity
(`agreementPoly_support_card_le`) feeds `t = k+2`. Axiom-clean. Issue #407.
-/

open Finset ZMod Polynomial
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.SparseCoeffZeros
open ProximityGap.Frontier.RThinSparseRealizability

namespace ProximityGap.Frontier.AgreementPolyUncertainty

variable {N : ℕ} [NeZero N]

/-- **The coefficient polynomial of a signal.** `coeffPoly c = ∑_{j : ZMod N} C (c j) · X^(j.val)`:
the (degree-`< N`) polynomial whose exponent `j.val`'s coefficient is the signal value `c j`. Its
`N`-th-root-of-unity evaluations are the DFT `𝓕 c`. -/
noncomputable def coeffPoly (c : ZMod N → ℂ) : ℂ[X] :=
  ∑ j : ZMod N, C (c j) * X ^ (j.val)

/-- **The bridge identity:** `𝓕 c k = eval (stdAddChar (-k)) (coeffPoly c)`. The DFT value at
frequency `k` is the coefficient polynomial evaluated at the `N`-th root of unity
`ζ_k = stdAddChar (-k)`, since `stdAddChar(-(j·k)) = (stdAddChar (-k)) ^ (j.val)`. -/
theorem dft_eq_eval_coeffPoly (c : ZMod N → ℂ) (k : ZMod N) :
    (𝓕 c) k = (coeffPoly c).eval (stdAddChar (-k)) := by
  rw [dft_apply, coeffPoly, eval_finset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X]
  -- `stdAddChar (-(j * k)) = stdAddChar (-k) ^ j.val`
  have hchar : (stdAddChar (-(j * k)) : ℂ) = (stdAddChar (-k)) ^ (j.val) := by
    have hjk : -(j * k) = (j.val) • (-k) := by
      rw [nsmul_eq_mul, natCast_zmod_val]; ring
    rw [hjk, AddChar.map_nsmul_eq_pow]
  rw [hchar, smul_eq_mul, mul_comm]

/-- **The zero-set of `𝓕 c` is the root-of-unity zero set of `coeffPoly c`.** A frequency `k` has
`𝓕 c k = 0` iff `coeffPoly c` vanishes at the `N`-th root of unity `stdAddChar (-k)`. -/
theorem dft_zero_iff_eval_zero (c : ZMod N → ℂ) (k : ZMod N) :
    (𝓕 c) k = 0 ↔ (coeffPoly c).eval (stdAddChar (-k)) = 0 := by
  rw [dft_eq_eval_coeffPoly]

/-- **Capstone (clean `ℂ`-coefficient form).** A `t`-sparse nonzero `ℂ`-coefficient signal's
polynomial `coeffPoly c` vanishes on at most `N·(1 − 1/t)` of the `N`-th roots of unity (counted by
frequency `k`, i.e. on the *agreement set*). This is the Donoho–Stark far-line agreement /
list-decoding-radius bound; for `t = k+2` on `Z_n` it is `≤ n·(1 − 1/(k+2))`. -/
theorem sparse_coeffPoly_rootsOfUnity_zeros_le (c : ZMod N → ℂ) (hc : c ≠ 0) {t : ℕ}
    (ht1 : 1 ≤ t) (ht : (supp c).card ≤ t) :
    ((univ.filter (fun k => (coeffPoly c).eval ((stdAddChar (N := N)) (-k)) = 0)).card : ℝ)
      ≤ (N : ℝ) * (1 - 1 / t) := by
  have hset : (univ.filter (fun k => (coeffPoly c).eval ((stdAddChar (N := N)) (-k)) = 0))
      = (univ.filter (fun k => (𝓕 c) k = 0)) := by
    apply Finset.filter_congr
    intro k _
    rw [dft_zero_iff_eval_zero]
  rw [hset]
  exact sparse_coeff_zeros_le c hc ht1 ht

/-! ### The agreement-polynomial specialization

We wire the explicit far-line agreement polynomial `P = X^a + C γ * X^b − c` into the capstone. Its
coefficient vector is `coeffVec P = fun j : ZMod N ↦ P.coeff j.val`. Two facts:
* `coeffPoly (coeffVec P) = P` when `P.natDegree < N` (the `val`-bijection reindexes the
  degree-`< N` sum), so the root-of-unity evaluations of `coeffPoly (coeffVec P)` are `P`'s;
* `(supp (coeffVec P)).card ≤ P.support.card` (the `val`-injection), so the `(k+2)`-sparsity of the
  agreement polynomial (`agreementPoly_support_card_le`) bounds the signal sparsity by `k+2`. -/

/-- The coefficient vector of a polynomial: `coeffVec P j = P.coeff j.val`. -/
noncomputable def coeffVec (P : ℂ[X]) : ZMod N → ℂ := fun j => P.coeff j.val

/-- **Reconstruction:** for a degree-`< N` polynomial, `coeffPoly (coeffVec P) = P`. The sum over
`ZMod N` reindexes (via the bijection `val`) to the sum over `range N`, which is `P`. -/
theorem coeffPoly_coeffVec (P : ℂ[X]) (hP : P.natDegree < N) :
    coeffPoly (coeffVec (N := N) P) = P := by
  have hstep : coeffPoly (coeffVec (N := N) P) = ∑ i ∈ Finset.range N, C (P.coeff i) * X ^ i := by
    rw [coeffPoly]
    refine Finset.sum_nbij' (i := fun j : ZMod N => j.val) (j := fun m : ℕ => (m : ZMod N))
      (s := (Finset.univ : Finset (ZMod N))) (t := Finset.range N)
      ?_ ?_ ?_ ?_ ?_
    · intro j _; simp only [Finset.mem_range]; exact ZMod.val_lt j
    · intro m hm; exact Finset.mem_univ _
    · intro j _; exact ZMod.natCast_zmod_val j
    · intro m hm; rw [Finset.mem_range] at hm; exact ZMod.val_natCast_of_lt hm
    · intro j _; rfl
  rw [hstep, ← P.as_sum_range_C_mul_X_pow' hP]

/-- **Sparsity transfer:** the coefficient-vector support injects (via `val`) into the polynomial's
exponent support, so `(supp (coeffVec P)).card ≤ P.support.card`. -/
theorem supp_coeffVec_card_le (P : ℂ[X]) :
    (supp (coeffVec (N := N) P)).card ≤ P.support.card := by
  refine Finset.card_le_card_of_injOn (fun j => j.val) (fun j hj => ?_)
    (fun a _ b _ h => ZMod.val_injective N h)
  rw [Finset.mem_coe, supp, Finset.mem_filter] at hj
  exact Polynomial.mem_support_iff.mpr hj.2

/-- **Capstone (agreement-polynomial form).** The far-line agreement polynomial
`P = X^a + C γ * X^b − c` (degree-`< k` codeword `c`, exponents `a, b < N`, `k ≤ N`), if nonzero,
vanishes on at most `N·(1 − 1/(k+2))` of the `N`-th roots of unity — the char-0 far-line agreement /
list-decoding-radius bound. Its `(k+2)`-sparsity (`agreementPoly_support_card_le`) feeds `t = k+2`
into the Donoho–Stark `sparse_coeff_zeros_le`. -/
theorem agreementPoly_rootsOfUnity_zeros_le (a b k : ℕ) (γ : ℂ) (c : ℂ[X])
    (ha : a < N) (hb : b < N) (hk : k ≤ N) (hc : c.natDegree < k)
    (hP : agreementPoly a b γ c ≠ 0) :
    ((univ.filter
        (fun j => (agreementPoly a b γ c).eval ((stdAddChar (N := N)) (-j)) = 0)).card : ℝ)
      ≤ (N : ℝ) * (1 - 1 / (k + 2 : ℕ)) := by
  set P : ℂ[X] := agreementPoly a b γ c with hPdef
  -- `P` has degree `< N`: it is `X^a + C γ * X^b - c` with `a, b < N` and `deg c < k ≤ N`.
  have hdeg : P.natDegree < N := by
    rw [hPdef, agreementPoly]
    have hsub : (X ^ a + C γ * X ^ b - c : ℂ[X]).support
        ⊆ insert a (insert b (Finset.range k)) := agreementPoly_support_subset a b k γ hc
    have hbound : ∀ m ∈ (X ^ a + C γ * X ^ b - c : ℂ[X]).support, m < N := by
      intro m hm
      have := hsub hm
      simp only [Finset.mem_insert, Finset.mem_range] at this
      rcases this with h | h | h
      · omega
      · omega
      · omega
    -- natDegree < N from all support exponents < N
    by_cases hzero : (X ^ a + C γ * X ^ b - c : ℂ[X]) = 0
    · rw [hzero]; simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    · have hmem : (X ^ a + C γ * X ^ b - c : ℂ[X]).natDegree
          ∈ (X ^ a + C γ * X ^ b - c : ℂ[X]).support :=
        Polynomial.natDegree_mem_support_of_nonzero hzero
      exact hbound _ hmem
  -- nonzero coefficient vector
  have hcv : coeffVec (N := N) P ≠ 0 := by
    intro h
    apply hP
    rw [← coeffPoly_coeffVec P hdeg, h, coeffPoly]
    simp
  -- sparsity ≤ k+2
  have hsparse : (supp (coeffVec (N := N) P)).card ≤ k + 2 := by
    calc (supp (coeffVec (N := N) P)).card ≤ P.support.card := supp_coeffVec_card_le P
      _ ≤ k + 2 := by rw [hPdef]; exact agreementPoly_support_card_le a b k γ hc
  -- apply the clean capstone with t = k+2, then rewrite coeffPoly = P
  have hmain := sparse_coeffPoly_rootsOfUnity_zeros_le (coeffVec (N := N) P) hcv
    (t := k + 2) (by omega) hsparse
  rwa [coeffPoly_coeffVec P hdeg] at hmain

end ProximityGap.Frontier.AgreementPolyUncertainty

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AgreementPolyUncertainty.dft_eq_eval_coeffPoly
#print axioms ProximityGap.Frontier.AgreementPolyUncertainty.dft_zero_iff_eval_zero
#print axioms ProximityGap.Frontier.AgreementPolyUncertainty.sparse_coeffPoly_rootsOfUnity_zeros_le
#print axioms ProximityGap.Frontier.AgreementPolyUncertainty.coeffPoly_coeffVec
#print axioms ProximityGap.Frontier.AgreementPolyUncertainty.supp_coeffVec_card_le
#print axioms ProximityGap.Frontier.AgreementPolyUncertainty.agreementPoly_rootsOfUnity_zeros_le
