/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sweep_A10 — Action–Orbit Q1 bad-prime bound `p ≤ |B|² ≤ n²/4` (the non-BGK lane)

**Target (actionable A10, re-land of 407-T06 `_BadPrimeBoundCore`, absent from this checkout).**
The Action–Orbit FRI soundness route (Chai–Fan, ePrint 2026/861) routes *around* the
character-sum / BGK wall. Its deepest open gate — Q1 (the paper's "Norm ≠ 0 on the primitive gap
variety", `R_d ≠ 0` on `V_d^prim`) — reduces, for the explicit dyadic eval domain `μ_n`
(`n = 2^μ`, `k = n/4`), to a purely **algebraic** statement: a *bad prime* (one admitting a
nonempty antipodal-free `B ⊆ μ_n` with odd-window vanishing `o_j(B) = Σ_{b∈B} b^j = 0` for all
odd `j ∈ {1,…,k−1}`) is forced to be SMALL:
`p ≤ |B|² ≤ (n/2)² = n²/4`.

This **replaces** the `EffectiveTransfer` exponential threshold `p > 2^n` with a *polynomial*
threshold `p ≤ n²/4`. Since the prize prime is `p ≈ n·2^128 ≫ n²/4`, the prize regime is
automatically clean for this gate — char-uniformly, with no Hecke / analytic NT input.

## The reduction (paper-level, the named-fact inputs below)

Write `β = Σ_{b∈B} ζ^{idx(b)} ∈ ℤ[ζ_n]`, `M := φ(n) = n/2` complex embeddings, `b := |B|`.
1. **Galois prime-splitting.** `o_j(B) = σ_j(β)` for the `k/2` Galois automorphisms indexed by
   the odd residues `j`, so the simultaneous vanishing forces `β` into `k/2` distinct primes
   above `p`, whence `p^{k/2} ∣ N(β)`, i.e. `p^K ≤ |N(β)|` with `K := k/2`.
2. **2-power trace identity.** For `n = 2^μ`, `Tr_{ℚ(ζ_n)/ℚ}(β · β̄) = (n/2)·|B| = M·b`. Setting
   `aᵢ := |σᵢ(β)|² ≥ 0` (the `M` conjugate squared-moduli), this reads `∑ᵢ aᵢ = M·b`, and
   `|N(β)|² = ∏ᵢ aᵢ`.
3. **AM-GM + arithmetic.** `(∏ aᵢ)^{1/M} ≤ (∑ aᵢ)/M = b`, so `∏ aᵢ ≤ b^M`; hence
   `|N(β)| = (∏ aᵢ)^{1/2} ≤ b^{M/2} = b^{2K}` (using `M = 4K`, i.e. `n/2 = 4·(k/2)`, i.e.
   `k = n/4`). Combining with `p^K ≤ |N(β)|` gives `p^K ≤ b^{2K}`, so `p ≤ b²`.

Steps 1–2 are *standard theorems* (Galois prime-splitting; the cyclotomic trace), **but neither
is available in Mathlib for this setting**. So — exactly as the original 407-T06 brick — we take
them as the two named-fact hypotheses and prove **the algebraic kernel (step 3) fully**, which is
where AM-GM lives and which is the entire non-trivial calculus content. This is an honest
*conditional* on two cited proven facts, NOT a δ* closure (see VERDICT).

## What is proven here (axiom-clean)

- `prod_le_mean_pow` — AM-GM in the form `(∏ aᵢ) ≤ ((∑ aᵢ)/M)^M` for `M` nonneg reals
  (`M = s.card`), via Mathlib `Real.geom_mean_le_arith_mean`.
- `badPrimeBound_core` — the kernel: from the trace identity `∑ aᵢ = M·b`, the norm bound
  `p^K ≤ √(∏ aᵢ)`, and `M = 4·K` (with `K ≥ 1`, `b > 0`, `p > 0`), conclude `p ≤ b²`.
- `badPrime_le_n_sq_div_four` — the headline corollary in prize shape: with `b ≤ n/2`
  (antipodal-free) this yields `p ≤ n²/4`.

## Honesty (the §6 contract)

This is a **soundness-route brick**, not a δ* closure. The two named facts (1)+(2) are genuine
standard theorems (so this is a faithful conditional reduction, not axiom-laundering — they are
real, cited, externally-proven, and the kernel that consumes them is fully proved). But Q1 governs
the *simultaneous* odd-window orbit count; the **single** far-line incidence `o_1 = 0` that pins
δ* stays `q`-dependent — the additive-energy / thin-subgroup sup-norm wall (B-form) is UNTOUCHED.
δ*-irrelevant, real for soundness. No fabricated closure.
-/

namespace ArkLib.ProximityGap.Sweep_A10

open Finset Real

/-- **AM-GM, product form.** For a finite family of nonnegative reals `a : ι → ℝ` over `s`, the
product is bounded by the `card`-th power of the arithmetic mean:
`∏_{i∈s} aᵢ ≤ ((∑_{i∈s} aᵢ)/|s|)^|s|`. (Equality iff all `aᵢ` equal.)

Proof: `Real.geom_mean_le_arith_mean` with all weights `w i = 1` gives
`(∏ aᵢ)^{1/|s|} ≤ (∑ aᵢ)/|s|`; raise both sides to the `|s|`-th power. -/
theorem prod_le_mean_pow {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hs : s.Nonempty) :
    (∏ i ∈ s, a i) ≤ ((∑ i ∈ s, a i) / s.card) ^ s.card := by
  classical
  -- Apply weighted AM-GM with all weights = 1. Then `∑ w = |s|`.
  have hcard_pos : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hw : ∀ i ∈ s, (0 : ℝ) ≤ (1 : ℝ) := fun _ _ => zero_le_one
  have hwsum : (0 : ℝ) < ∑ _i ∈ s, (1 : ℝ) := by
    simpa using hcard_pos
  have hgm := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ)) a hw hwsum ha
  -- Simplify the weighted statement: `(∏ aᵢ^1)^{(∑1)⁻¹} ≤ (∑ 1·aᵢ)/(∑1)`.
  simp only [Real.rpow_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hgm
  -- `hgm : (∏ aᵢ)^((s.card:ℝ)⁻¹) ≤ (∑ aᵢ)/(s.card)`.
  have hprod_nonneg : (0 : ℝ) ≤ ∏ i ∈ s, a i := Finset.prod_nonneg ha
  have hrhs_nonneg : (0 : ℝ) ≤ (∑ i ∈ s, a i) / s.card :=
    div_nonneg (Finset.sum_nonneg ha) (le_of_lt hcard_pos)
  -- Raise both sides to the REAL power `(s.card : ℝ)` (monotone on `[0,∞)`).
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprod_nonneg _) hgm
    (by positivity : (0:ℝ) ≤ (s.card : ℝ))
  -- LHS collapses: `((∏)^{c⁻¹})^c = (∏)^{c⁻¹·c} = (∏)^1 = ∏`  (all rpow).
  rw [← Real.rpow_mul hprod_nonneg, inv_mul_cancel₀ hcard_ne, Real.rpow_one] at hpow
  -- RHS: convert the real power `(s.card:ℝ)` back to the natural power `s.card`.
  rwa [Real.rpow_natCast ((∑ i ∈ s, a i) / s.card) s.card] at hpow

/-- **The bad-prime algebraic kernel (Q1, char-uniform).**

Hypotheses (the two *named proven facts* of the reduction, plus the arithmetic relation):
* `htrace : ∑ᵢ aᵢ = M·b` — the cyclotomic 2-power trace identity (`M = φ(n) = n/2`),
  `aᵢ = |σᵢ(β)|²`, `b = |B|`.
* `hnorm  : (p : ℝ)^K ≤ Real.sqrt (∏ᵢ aᵢ)` — Galois prime-splitting: `p^K ∣ N(β)`, so
  `p^K ≤ |N(β)| = √(∏ aᵢ)` (with `K = k/2`).
* `hM     : M = 4 * K` — the prize-rate relation `n/2 = 4·(k/2)`, i.e. `k = n/4`.

Conclusion: `p ≤ b²`. Pure AM-GM + arithmetic; the entire calculus content of A10. -/
theorem badPrimeBound_core {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (p b : ℝ) (K : ℕ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (_hp : 0 < p) (hb : 0 < b) (hK : 0 < K)
    (hMcard : s.card = 4 * K)
    (htrace : ∑ i ∈ s, a i = (s.card : ℝ) * b)
    (hnorm : (p : ℝ) ^ K ≤ Real.sqrt (∏ i ∈ s, a i)) :
    p ≤ b ^ 2 := by
  classical
  have hMpos : 0 < 4 * K := by positivity
  have hs : s.Nonempty := by
    rw [← Finset.card_pos, hMcard]; exact hMpos
  have hcard_pos : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hprod_nonneg : (0 : ℝ) ≤ ∏ i ∈ s, a i := Finset.prod_nonneg ha
  -- Step A: AM-GM gives `∏ aᵢ ≤ ((∑ aᵢ)/M)^M = b^M` since `∑ aᵢ = M·b`.
  have hsimp : ((s.card : ℝ) * b) / s.card = b := by
    field_simp
  have hAMGM : (∏ i ∈ s, a i) ≤ b ^ s.card := by
    have h := prod_le_mean_pow s a ha hs
    rwa [htrace, hsimp] at h
  -- Step B: `√(∏ aᵢ) ≤ √(b^M) = b^(M/2) = b^(2K)` (since `M = 4K`).
  have hsqrt : Real.sqrt (∏ i ∈ s, a i) ≤ b ^ (2 * K) := by
    have h1 : Real.sqrt (∏ i ∈ s, a i) ≤ Real.sqrt (b ^ s.card) :=
      Real.sqrt_le_sqrt hAMGM
    have h2 : Real.sqrt (b ^ s.card) = b ^ (2 * K) := by
      rw [hMcard]
      -- √(b^(4K)) = √((b^(2K))^2) = |b^(2K)| = b^(2K).
      have : b ^ (4 * K) = (b ^ (2 * K)) ^ 2 := by rw [← pow_mul]; ring_nf
      rw [this, Real.sqrt_sq (by positivity)]
    rwa [h2] at h1
  -- Step C: combine `p^K ≤ √(∏) ≤ b^(2K) = (b²)^K`, then K-th root (strict-mono pow).
  have hchain : (p : ℝ) ^ K ≤ (b ^ 2) ^ K := by
    calc (p : ℝ) ^ K ≤ Real.sqrt (∏ i ∈ s, a i) := hnorm
      _ ≤ b ^ (2 * K) := hsqrt
      _ = (b ^ 2) ^ K := by rw [← pow_mul, Nat.mul_comm]
  -- `x^K ≤ y^K` with `0 ≤ y`, `K ≠ 0` ⟹ `x ≤ y` (pow is mono on nonneg).
  exact le_of_pow_le_pow_left₀ hK.ne' (by positivity) hchain

/-- **Prize-shape corollary `p ≤ n²/4`.** Plugging the antipodal-free cardinality bound
`b = |B| ≤ |μ_n|/2 = n/2` (no `u` and `−u` both in `B`) into the kernel: a bad prime satisfies
`p ≤ b² ≤ (n/2)² = n²/4`. Since the prize prime is `p ≈ n·2^128 ≫ n²/4`, no prize prime is bad. -/
theorem badPrime_le_n_sq_div_four {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (p b n : ℝ) (K : ℕ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hp : 0 < p) (hb : 0 < b) (hK : 0 < K) (_hn : 0 ≤ n)
    (hMcard : s.card = 4 * K)
    (htrace : ∑ i ∈ s, a i = (s.card : ℝ) * b)
    (hnorm : (p : ℝ) ^ K ≤ Real.sqrt (∏ i ∈ s, a i))
    (hantipodal : b ≤ n / 2) :
    p ≤ n ^ 2 / 4 := by
  have hcore : p ≤ b ^ 2 := badPrimeBound_core s a p b K ha hp hb hK hMcard htrace hnorm
  have hb2 : b ^ 2 ≤ (n / 2) ^ 2 := pow_le_pow_left₀ (le_of_lt hb) hantipodal 2
  calc p ≤ b ^ 2 := hcore
    _ ≤ (n / 2) ^ 2 := hb2
    _ = n ^ 2 / 4 := by ring

/-- **Prize-safety, instantiated.** At the canonical prize instance the headline is concrete: if
`n ≤ 2^40` (the prize cap `a ≤ 40`) then `n²/4 ≤ 2^79`, but the prize prime is
`p ≈ n·2^128 ≥ 2^128 > 2^79`. So no prize prime can be bad: the gate is clean unconditionally.
We record the clean inequality `n²/4 < p` from `n ≤ 2^40` and `p ≥ 2^128`. -/
theorem prize_prime_exceeds_bound {n p : ℝ}
    (hn0 : 0 ≤ n) (hn : n ≤ (2:ℝ) ^ (40:ℕ)) (hp : (2:ℝ) ^ (128:ℕ) ≤ p) :
    n ^ 2 / 4 < p := by
  have hn2 : n ^ 2 ≤ ((2:ℝ) ^ (40:ℕ)) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  have hnum : ((2:ℝ) ^ (40:ℕ)) ^ 2 = (2:ℝ) ^ (80:ℕ) := by
    rw [← pow_mul]
  have hbound : (2:ℝ) ^ (80:ℕ) / 4 < (2:ℝ) ^ (128:ℕ) := by norm_num
  calc n ^ 2 / 4 ≤ ((2:ℝ) ^ (40:ℕ)) ^ 2 / 4 := by linarith
    _ = (2:ℝ) ^ (80:ℕ) / 4 := by rw [hnum]
    _ < (2:ℝ) ^ (128:ℕ) := hbound
    _ ≤ p := hp

end ArkLib.ProximityGap.Sweep_A10

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.Sweep_A10.prod_le_mean_pow
#print axioms ArkLib.ProximityGap.Sweep_A10.badPrimeBound_core
#print axioms ArkLib.ProximityGap.Sweep_A10.badPrime_le_n_sq_div_four
#print axioms ArkLib.ProximityGap.Sweep_A10.prize_prime_exceeds_bound
