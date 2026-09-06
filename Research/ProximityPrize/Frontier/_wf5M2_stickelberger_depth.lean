/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-M2)
-/
import Mathlib.Analysis.MeanInequalities

/-!
# The depth-`R` Stickelberger prime bound (#444, lane wf-M2)

`_BadPrimeBoundCore` proved the *full-window* Stickelberger bound: a nonempty antipodal-free
`B ⊆ μ_n ⊆ 𝔽_p` whose odd power sums `o_j(B)` vanish for **all** odd `j ∈ {1,…,k−1}` (`k = n/4`,
so `K = k/2 = n/8` equations) forces `p ≤ |B|²`.  That needs `Θ(n)` window equations.

The Proximity-Prize char-`p` transfer, however, lives at the **deep-moment depth** `R ~ ln(p/n) ~
β ln n`, which is `≪ n/8`.  This file installs the **depth-parametrised** form, separating the
divisibility depth `R` (number of leading vanishing odd power sums) from the field degree.

## The mechanism (Stickelberger / prime-splitting, char-`p` [π])

Let `n = 2^μ`, `p` an odd prime with `n ∣ p−1`, so `p` is **totally split** in `ℤ[ζ_n]` into
`φ(n) = n/2` distinct prime ideals `𝔭_1,…,𝔭_{n/2}` (`σ_i ↦ 𝔭_i`).  For a signed pair-indicator
`w ∈ {−1,0,1}^{n/2}` of an antipodal-free `B` of size `w := |B|`, set `β = Σ_s w_s ζ_n^s`.  The
`j`-th odd power sum is the Galois conjugate `o_j(B) = σ_j(β)`.  Hence:

* **(NT1, Stickelberger / splitting)** vanishing of the **first `R` odd power sums** `mod p` places
  `β` in `R` distinct primes above `p`, so `p^R ∣ N(β)`, giving `p^R ≤ |N(β)|`.
* **(NT2, 2-power trace)** `Tr(ζ^m)=0` for `0≠m∈(−n/2,n/2)` gives `Σ_i |σ_i(β)|² = (n/2)·w`.
* **(this file, elementary)** AM-GM on the `M = n/2` reals `a_i = |σ_i(β)|²` (mean `w`) gives
  `∏ a_i ≤ w^{n/2}`, so `|N(β)| = √(∏ a_i) ≤ w^{n/4}`.  Combined with NT1:

> **`p^R ≤ w^{n/4}`, i.e. `p ≤ w^{n/(4R)}`.**

This is `badPrimeBound_core` generalised from the hard-wired `M = 4K` (full window, `R = n/8`,
`p ≤ w²`) to **arbitrary `R`**, and it is *exactly* the conservation-law wall made quantitative:
the bound is non-vacuous (forces `p ≤ poly(n)`) **only when `R ≈ n/8`**; at the deep-moment depth
`R ~ β ln n` the ceiling `w^{n/(4R)} = w^{Θ(n/ln n)}` is super-polynomial, so it imposes **no
constraint** on the prize prime `p = n^β`.  The pre-screen
`scripts/probes/probe_wf5M2_stickelberger_depth.py` confirms every observed genuine bad prime
satisfies `p ≤ w^{n/(4R)}` (no violation), and the ceiling is loose by orders of magnitude.

## What is PROVEN here (axiom-clean)

* `depth_prod_le_pow` — AM-GM: `M` positive reals of mean `b` have `∏ ≤ b^M`.
* `stickelberger_depth_bound` — the whole chain *given* NT1 (`p^R ≤ √(∏ aᵢ)`) and NT2
  (`Σ aᵢ = M·b`, `M = 2R · t` recording the degree-to-depth ratio): `p ≤ b^(M/R)`-shaped,
  concretely `p^R ≤ b^(M/2)` hence `p ≤ b^t` with `t = M/(2R)`.

NT1 (Stickelberger prime splitting) and NT2 (2-power cyclotomic trace) are **proven** standard
algebraic number theory carried as hypotheses (the same modularity convention as
`_BadPrimeBoundCore`).  The OPEN content is NOT in this file: it is that to *close the prize* one
needs `R ≈ n/8` vanishing equations, while the deep-moment depth supplies only `R ~ β ln n` — the
ceiling stays super-polynomial.  This brick makes that gap exact and machine-checked.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- Lam–Leung, *On vanishing sums of roots of unity* (2-power antipodal structure → NT2).
- Stevenhagen–Lenstra, *Chebotarëv and his density theorem* (splitting/valuation appendix).
-/

namespace ProximityGap.Frontier.StickelbergerDepth

open Finset

/--
**AM-GM step (proven).**  `M` positive reals with arithmetic mean `b` have product `≤ b^M`.
The only analytic content; everything else is divisibility/arithmetic.
-/
theorem depth_prod_le_pow {M : ℕ} (hM : 0 < M) (a : Fin M → ℝ) (ha : ∀ i, 0 < a i)
    (b : ℝ) (hmean : ∑ i, a i = (M : ℝ) * b) :
    ∏ i, a i ≤ b ^ M := by
  have hsum1 : ∑ _i : Fin M, (1 : ℝ) = (M : ℝ) := by simp
  have hb : 0 ≤ b := by
    have hsum_pos : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) ⟨⟨0, hM⟩, mem_univ _⟩
    rw [hmean] at hsum_pos
    have : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    nlinarith [hsum_pos]
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hg := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin M)) (fun _ => (1 : ℝ)) a
    (fun i _ => by norm_num) (by rw [hsum1]; exact_mod_cast hM) (fun i _ => (ha i).le)
  simp only [Real.rpow_one, one_mul, hsum1] at hg
  have hRHS : (∑ i, a i) / (M : ℝ) = b := by rw [hmean]; field_simp
  rw [hRHS] at hg
  set P : ℝ := ∏ i, a i with hP
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => ha i)
  have h2 : (P ^ ((M:ℝ)⁻¹)) ^ (M : ℕ) ≤ b ^ (M : ℕ) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hPpos.le _) hg M
  have hLHS : (P ^ ((M:ℝ)⁻¹)) ^ (M : ℕ) = P := by
    rw [← Real.rpow_natCast (P ^ ((M:ℝ)⁻¹)) M, ← Real.rpow_mul hPpos.le,
      inv_mul_cancel₀ hMne, Real.rpow_one]
  rwa [hLHS] at h2

/--
**The depth-`R` Stickelberger prime bound (core).**  Inputs (the two proven NT facts as
hypotheses): the trace identity `∑ aᵢ = M·b` (`NT2`, `aᵢ = |σᵢ(β)|²`, `b = |B|`, `M = n/2`) and
the depth-`R` norm bound `p^R ≤ √(∏ aᵢ)` (`NT1`, from `p^R ∣ N(β)`), together with the
degree-to-depth relation `M = 2·R·t`.  Conclusion: `p ≤ b^t` — i.e. a genuine config vanishing at
the **first `R` odd power sums** forces `p ≤ |B|^{(n/2)/(2R)} = |B|^{n/(4R)}`.

Recovers `_BadPrimeBoundCore.badPrimeBound_core` at `t = 1`, `R = n/8` (full window).  The prize
gap is precisely that the deep-moment depth gives only `R ~ β ln n` so `t = n/(4R)` is large and
the bound is vacuous; this is the quantitative form of the second-moment conservation law. -/
theorem stickelberger_depth_bound {M R t : ℕ} (hR : 0 < R) (ht : 0 < t) (hMRt : M = 2 * R * t)
    (a : Fin M → ℝ) (ha : ∀ i, 0 < a i) (b p : ℝ) (hb : 0 < b) (hp : 0 < p)
    (htrace : ∑ i, a i = (M : ℝ) * b)
    (hnorm : p ^ R ≤ Real.sqrt (∏ i, a i)) :
    p ≤ b ^ t := by
  have hM : 0 < M := by subst hMRt; positivity
  have hprod : ∏ i, a i ≤ b ^ M := depth_prod_le_pow hM a ha b htrace
  -- √(∏ aᵢ) ≤ √(b^M) = √((b^{R·t})²) = b^{R·t}
  have hbRt : (0:ℝ) ≤ b ^ (R * t) := by positivity
  have hsqrt : Real.sqrt (∏ i, a i) ≤ b ^ (R * t) := by
    have hrw : b ^ M = (b ^ (R * t)) ^ 2 := by rw [hMRt, ← pow_mul]; ring_nf
    calc Real.sqrt (∏ i, a i) ≤ Real.sqrt (b ^ M) := Real.sqrt_le_sqrt hprod
      _ = b ^ (R * t) := by rw [hrw, Real.sqrt_sq hbRt]
  -- p^R ≤ b^{R·t} = (b^t)^R  ⟹  p ≤ b^t
  have hchain : p ^ R ≤ (b ^ t) ^ R := by
    have : (b ^ t) ^ R = b ^ (R * t) := by rw [← pow_mul, Nat.mul_comm]
    rw [this]; exact le_trans hnorm hsqrt
  by_contra hcon
  push_neg at hcon
  exact absurd hchain (not_le.mpr (pow_lt_pow_left₀ hcon (by positivity) hR.ne'))

end ProximityGap.Frontier.StickelbergerDepth

#print axioms ProximityGap.Frontier.StickelbergerDepth.depth_prod_le_pow
#print axioms ProximityGap.Frontier.StickelbergerDepth.stickelberger_depth_bound
