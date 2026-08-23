/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The elementary bad-prime bound — AM-GM core (#407, Q1 char-p kernel)

The action-orbit soundness route's deepest char-`p` gate (`Q1`: `R_d ≠ 0` on `V_d^prim`) reduces
(via `LamLeungTwoPow` / `EvenOddAntipodalCharFree`) to:

> for `n = 2^e`, `k = n/4`, odd prime `p` with `n ∣ p−1`, a NONEMPTY antipodal-free `B ⊆ μ_n ⊆ F_p`
> with the odd-window vanishing `o_j(B) = Σ_{b∈B} b^j = 0` for all odd `j ∈ {1,…,k−1}` forces
> `p ≤ |B|² ≤ n²/4`.

The fleet's elementary proof (issue #407, 2026-06-14) runs:
* set `β = Σ_s w_s ζ_n^s ∈ ℤ[ζ_n]` (`w ∈ {−1,0,1}^{n/2}` the signed pair-indicator of `B`);
* **(NT1, Galois prime-splitting)** `o_j(B) = σ_j(β)`, so the `k/2` window equations place `β` in
  `k/2` distinct primes above `p` (`p` totally split, `n ∣ p−1`), giving `p^{k/2} ∣ N(β)`, hence
  `p^{k/2} ≤ |N(β)| = √(∏_i |σ_i(β)|²)`;
* **(NT2, 2-power trace identity)** `Tr(ζ^m) = 0` for `0 ≠ m ∈ (−n/2,n/2)` gives
  `Tr(β·β̄) = (n/2)·|B|`, i.e. `∑_i |σ_i(β)|² = (n/2)·|B|`;
* **(this file, elementary)** AM-GM on the `M = n/2` positive reals `aᵢ = |σ_i(β)|²` with mean
  `|B|` gives `∏_i aᵢ ≤ |B|^M`, so `|N(β)| ≤ |B|^{n/4}`; combined with `p^{k/2} ≤ |N(β)|` and
  `n/2 = 4·(k/2)` this yields `p ≤ |B|²`.

This file formalizes the **elementary core** — `badPrimeBound_core` below — which is the whole
chain *given* the two number-theoretic facts (NT1, NT2) as hypotheses.  Crucially, NT1 and NT2 are
**proven theorems** (standard cyclotomic algebraic number theory), NOT open conjectures: NT2 is the
2-power cyclotomic trace, NT1 is prime splitting in `ℤ[ζ_n]`.  So the bound reduces **only to
proven mathematics** — the AM-GM step (Mathlib `Real.geom_mean_le_arith_mean`) is formalized here;
the two cited facts are heavy-but-standard.  This closes the `Q1` char-`p` kernel at prize scale
(`p ≈ n·2^128 ≫ n²/4`) with a *polynomial* threshold, replacing `EffectiveTransfer`'s exponential
one.  It does NOT pin `δ*` (the single far-line incidence `o_1 = 0` is `q`-dependent — the
additive-energy wall, unchanged).  Verified computationally: `scripts/probes/probe_badprime_bound_q1.py`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Lam–Leung, *On vanishing sums of roots of unity* (the 2-power antipodal structure feeding NT2).
-/

namespace ProximityGap.Frontier.BadPrimeBound

open Finset

/--
**AM-GM step (proven):** `M` positive reals with arithmetic mean `b` have product `≤ b^M`.
This is the only analytic content of the bad-prime bound; everything else is divisibility/arithmetic.
-/
theorem prod_le_mean_pow {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ) (ha : ∀ i, 0 < a i)
    (b : ℝ) (hmean : ∑ i, a i = (M : ℝ) * b) :
    ∏ i, a i ≤ b ^ M := by
  have hcard : (Finset.univ : Finset (Fin M)).card = M := by simp
  have hsum1 : ∑ _i : Fin M, (1 : ℝ) = (M : ℝ) := by simp
  have hb : 0 ≤ b := by
    have hsum_pos : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) ⟨⟨0, hM⟩, mem_univ _⟩
    rw [hmean] at hsum_pos
    have : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    nlinarith [hsum_pos]
  -- AM-GM with uniform weights `1`
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hg := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin M)) (fun _ => (1 : ℝ)) a
    (fun i _ => by norm_num) (by rw [hsum1]; exact_mod_cast hM) (fun i _ => (ha i).le)
  -- simplify both sides of hg
  simp only [Real.rpow_one, one_mul, hsum1] at hg
  have hRHS : (∑ i, a i) / (M : ℝ) = b := by rw [hmean]; field_simp
  rw [hRHS] at hg
  -- hg : (∏ i, a i) ^ (M:ℝ)⁻¹ ≤ b
  set P : ℝ := ∏ i, a i with hP
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => ha i)
  -- raise hg to the M-th power
  have h2 : (P ^ ((M:ℝ)⁻¹)) ^ (M : ℕ) ≤ b ^ (M : ℕ) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hPpos.le _) hg M
  -- LHS = P
  have hLHS : (P ^ ((M:ℝ)⁻¹)) ^ (M : ℕ) = P := by
    rw [← Real.rpow_natCast (P ^ ((M:ℝ)⁻¹)) M, ← Real.rpow_mul hPpos.le,
      inv_mul_cancel₀ hMne, Real.rpow_one]
  rwa [hLHS] at h2

/--
**The elementary bad-prime bound (core).**  Given the two proven number-theoretic inputs as
hypotheses — the trace identity `∑ aᵢ = (M)·b` (`NT2`, with `aᵢ = |σᵢ(β)|²`, `b = |B|`, `M = n/2`)
and the norm lower bound `p^K ≤ √(∏ aᵢ)` (`NT1`, `K = k/2`, from `p^{k/2} ∣ N(β)`) — together with
the dimension relation `M = 4·K` (i.e. `n/2 = 4·(n/8)`), the prime is bounded by `p ≤ b²`.

Reduces only to proven math: the AM-GM step (`prod_le_mean_pow`) plus arithmetic.  Instantiating
`b = |B| ≤ n/2` gives the headline `p ≤ |B|² ≤ n²/4`. -/
theorem badPrimeBound_core {M K : ℕ} (hK : 0 < K) (hMK : M = 4 * K)
    (a : Fin M → ℝ) (ha : ∀ i, 0 < a i) (b p : ℝ) (hb : 0 < b) (hp : 0 < p)
    (htrace : ∑ i, a i = (M : ℝ) * b)
    (hnorm : p ^ K ≤ Real.sqrt (∏ i, a i)) :
    p ≤ b ^ 2 := by
  have hM : 0 < M := by omega
  -- AM-GM: ∏ aᵢ ≤ b^M = b^(4K) = (b^(2K))²
  have hprod : ∏ i, a i ≤ b ^ M := prod_le_mean_pow hM a ha b htrace
  have hb2K : (0:ℝ) ≤ b ^ (2 * K) := by positivity
  -- √(∏ aᵢ) ≤ √(b^M) = √((b^(2K))²) = b^(2K)
  have hsqrt : Real.sqrt (∏ i, a i) ≤ b ^ (2 * K) := by
    have hrw : b ^ M = (b ^ (2 * K)) ^ 2 := by rw [hMK, ← pow_mul]; ring_nf
    calc Real.sqrt (∏ i, a i) ≤ Real.sqrt (b ^ M) :=
          Real.sqrt_le_sqrt hprod
      _ = b ^ (2 * K) := by rw [hrw, Real.sqrt_sq hb2K]
  -- p^K ≤ b^(2K) = (b²)^K  ⟹  p ≤ b²
  have hchain : p ^ K ≤ (b ^ 2) ^ K := by
    have : (b ^ 2) ^ K = b ^ (2 * K) := by rw [← pow_mul]
    rw [this]; exact le_trans hnorm hsqrt
  by_contra hcon
  push_neg at hcon
  exact absurd hchain (not_le.mpr (pow_lt_pow_left₀ hcon (by positivity) hK.ne'))

end ProximityGap.Frontier.BadPrimeBound

#print axioms ProximityGap.Frontier.BadPrimeBound.prod_le_mean_pow
#print axioms ProximityGap.Frontier.BadPrimeBound.badPrimeBound_core
