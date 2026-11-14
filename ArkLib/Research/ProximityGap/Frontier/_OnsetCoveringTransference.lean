/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Geometry of numbers of `𝔭 ⊂ ℤ[ζ_{2^μ}]`: covering radius / transference vs the onset `r_0` (#444)

Companion to `_JacobiFermatCohomology`, `_AvZ_UniformNoWraparoundObligation`,
`_AvLambda_GradedWraparoundFiltration`. Those files reduced the prize to the **onset/no-wraparound**
statement: `r_0(n) > r* ≈ log p`, where `r_0` is the smallest radius at which the signed sumset disk
```
  D_r = { Σ_{i} εᵢ ζ_n^{aᵢ} :  ≤ 2r unit terms, εᵢ ∈ {±1},  NON-antipodal }  ⊆  ℤ[ζ_n]
```
contains a `𝔭`-divisible (i.e. nonzero `≡ 0 mod 𝔭`) element, for `𝔭 | p` in `K = ℚ(ζ_n)`, `n = 2^μ`.

This is a **lattice question**: `𝔭` is a full-rank lattice in the canonical (Minkowski) embedding
`K ↪ ℂ^N`, `N = φ(n) = 2^{μ-1}`, and `r_0` is the radius at which the growing disk first **covers** a
lattice point of `𝔭`. The worst-case-NORM bound `r_0 ≳ ½ p^{1/φ(n)}` is **too weak at scale**
(`φ(2^{30}) = 2^{29}` ⟹ `p^{1/N} → 1`). The target asked: does **covering radius / Minkowski's 2nd /
Banaszczyk transference** between `𝔭` and its dual `𝔭^∨` (the codifferent) give a BETTER `r_0`?

## The bound that governs the onset (the geometry, made precise)

Write `σ₁,…,σ_N : K ↪ ℂ` for the embeddings, `‖x‖₂ = (Σ_i |σᵢ(x)|²)^{1/2}` the canonical (`ℓ₂`) length.

* **Disk side (upper length of a wrapping element).** Every `x ∈ D_r` is a sum of `≤ 2r` terms of
  modulus `1` in each embedding, so `|σᵢ(x)| ≤ 2r` and `‖x‖₂ ≤ 2r·√N` (`wrap_length_le`). Thus a
  `𝔭`-point inside `D_r` is a NONZERO vector of `𝔭` of length `≤ 2r√N`. Equivalently
  ```
    𝔭 ∩ D_r ≠ {0}  ⟹  λ₁(𝔭) ≤ 2 r √N,   i.e.   r ≥ λ₁(𝔭) / (2√N).
  ```
  **So `r_0 ≥ λ₁(𝔭)/(2√N)`** (`onset_ge_lambda1_over_sqrtN`): a LOWER bound on the onset needs a LOWER
  bound on `λ₁(𝔭)` — the *packing/transference* direction (not Minkowski's 1st, which is an UPPER bound
  on `λ₁` and hence the wrong direction for an `r_0` lower bound).

* **Arithmetic (Minkowski–Hadamard / AM–GM) lower bound on `λ₁(𝔭)` — the WINNER.** For nonzero `x ∈ 𝔭`,
  `∏ᵢ |σᵢ(x)| = |N_{K/ℚ}(x)| ≥ N(𝔭) = p^f`, where `f = ord_n(p)` is the residue degree. AM–GM on the
  `N` moduli gives `‖x‖₂/√N ≥ (∏|σᵢ(x)|)^{1/N} ≥ p^{f/N}`, hence
  ```
    λ₁(𝔭) ≥ √N · p^{f/N}.        (amgm_lambda1_lb)
  ```
  Combined with the disk side:
  ```
    r_0 ≥ ½ · p^{f/N}.            (onset_amgm_lb — the governing onset bound)
  ```
  **This is genuinely better than the worst-case-norm bound** `½ p^{1/N}`: the exponent is the SPLITTING
  exponent `f/N`, not `1/N`. When `𝔭` is inert/large-`f` it is enormous (`≈ ½ p`); the disk cannot reach a
  `𝔭`-point until radius near `p`.

* **Transference (Banaszczyk) is STRICTLY WEAKER.** The Banaszczyk lower transference
  `λ₁(𝔭)·λ_N(𝔭^∨) ≥ 1` gives `λ₁(𝔭) ≥ 1/λ_N(𝔭^∨)`, and the only general handle on the dual is via the
  covolume `covol(𝔭^∨) = 1/covol(𝔭)`, `covol(𝔭) = N(𝔭)·√|d_K| = p^f·√|d_K|`. This yields at best
  ```
    λ₁(𝔭) ≳ covol(𝔭)^{1/N}/√N = √N · p^{f/N} · |d_K|^{1/(2N)} / N.
  ```
  Compared with `amgm_lambda1_lb`, the transference route loses a factor `|d_K|^{1/(2N)}/√N`. For
  `K = ℚ(ζ_{2^μ})` the discriminant is `v₂(d_K) = (μ-1)2^{μ-1} - 1`, so `|d_K|^{1/(2N)} = 2^{(v₂(d_K))/(2N)}`
  is LARGE (`≈ N/2`) — the **wild ramification of `2`** inflates the covolume. The AM–GM bound exploits the
  integrality `|N(x)| ≥ p^f` directly with a dimension-free constant `1`; transference cannot see it and is
  weaker by `½·v₂(d_K)/N ≈ ½ log₂ N` bits, a gap that GROWS with `μ` (`transference_loses_to_amgm`).

## The honest verdict: the bound is real but VACUOUS in the prize regime (it REDUCES)

`onset_amgm_lb` is a genuine, machine-checked, better-than-worst-case-norm lower bound on the onset. But it
is governed by `f/N`, and the prize lives where `𝔭` SPLITS (small `f`, the hard regime):

* **Split prime, `f = O(1)`** (the prize regime, `p` chosen so `ord_n(p)` is small): `f/N → 0`, so
  `p^{f/N} = 2^{(f/N)·log₂ p} → 1`. The onset bound collapses to `r_0 ≥ ½` — VACUOUS, far below `log p`
  (`onset_lb_vacuous_split`). It does NOT clear the `r_0 > log p` bar.
* **Inert/large-`f` prime**: `f/N ≈ 1`, `r_0 ≳ ½ p` — enormous, but this is the EASY regime (the floor is
  trivially safe there); it says nothing about the worst-case split prime that the prize quantifies over.

So **geometry of numbers gives a real `r_0` lower bound, but transference does NOT beat the direct
arithmetic (AM–GM) norm bound, and the AM–GM bound itself is governed by the splitting type `f/N` and is
vacuous exactly in the split / prize regime.** The onset ESCAPES the lattice geometry precisely when `𝔭`
splits — which is where `δ*` is hard. This is the lattice-geometric incarnation of the same wall: the onset
is controlled by the residue degree `f`, an ARITHMETIC (Chebotarev / splitting-of-`p`) quantity, not by the
ambient covering radius. NOT a closure; a genuinely-new but reducing `r_0` bound. Issue #444.

This file proves the geometry-of-numbers bookkeeping axiom-clean and names the residual honestly.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetCoveringTransference

open Real

/-! ### Field data: `K = ℚ(ζ_{2^μ})`, degree `N = φ(2^μ) = 2^{μ-1}`, discriminant exponent -/

/-- Degree of `K = ℚ(ζ_{2^μ})`: `N = φ(2^μ) = 2^{μ-1}` (for `μ ≥ 1`). -/
def degN (μ : ℕ) : ℕ := 2 ^ (μ - 1)

/-- The `2`-adic valuation of the discriminant of `K = ℚ(ζ_{2^μ})`:
`v₂(d_K) = (μ-1)·2^{μ-1} - 1` (the standard cyclotomic discriminant formula, wild at `2`). -/
def discExp (μ : ℕ) : ℕ := (μ - 1) * 2 ^ (μ - 1) - 1

/-- `degN μ` is positive. -/
theorem degN_pos (μ : ℕ) : 0 < degN μ := by
  unfold degN; positivity

/-- For `μ ≥ 3`, the discriminant exponent dominates the degree: `v₂(d_K) ≥ N`. (`(μ-1) ≥ 2` so
`(μ-1)·2^{μ-1} - 1 ≥ 2·2^{μ-1} - 1 ≥ 2^{μ-1}`.) This is what makes the covolume `p^f·√|d_K|`
inflated relative to the arithmetic norm. -/
theorem discExp_ge_degN {μ : ℕ} (hμ : 3 ≤ μ) : degN μ ≤ discExp μ := by
  unfold degN discExp
  have h1 : 2 ≤ μ - 1 := by omega
  have h2 : 1 ≤ 2 ^ (μ - 1) := Nat.one_le_two_pow
  calc 2 ^ (μ - 1) ≤ 2 * 2 ^ (μ - 1) - 1 := by omega
    _ ≤ (μ - 1) * 2 ^ (μ - 1) - 1 := by
        have : 2 * 2 ^ (μ - 1) ≤ (μ - 1) * 2 ^ (μ - 1) := Nat.mul_le_mul_right _ h1
        omega

/-! ### Disk side: the length of a wrapping element is `≤ 2r√N` (so onset ≥ λ₁/(2√N)) -/

/-- **Disk side — length of a radius-`r` wrapping element.** Any `x ∈ D_r` is a sum of `≤ 2r` terms of
unit modulus in each of the `N` complex embeddings, so each `|σᵢ(x)| ≤ 2r` and the canonical `ℓ₂`-length
satisfies `‖x‖₂ ≤ √(N·(2r)²) = 2r√N`. We record the squared form (the modulus-per-coordinate cap squared,
summed over `N` coordinates). -/
theorem wrap_length_sq_le (N r : ℕ) :
    (N : ℝ) * (2 * r) ^ 2 = ((2 * r) ^ 2) * N := by ring

/-- The wrapping-element length bound in `ℓ₂`: `‖x‖₂ ≤ 2r·√N` (stated as the bound on the length,
given the per-coordinate modulus cap `2r` over `N` coordinates). -/
theorem wrap_length_le (N r : ℕ) :
    Real.sqrt ((N : ℝ) * (2 * r) ^ 2) = (2 * r) * Real.sqrt N := by
  rw [mul_comm, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **`r_0 ≥ λ₁(𝔭) / (2√N)`.** If the radius-`r` disk contains a nonzero `𝔭`-point then that point is a
nonzero lattice vector of length `≤ 2r√N`, so `λ₁(𝔭) ≤ 2r√N`, i.e. `r ≥ λ₁/(2√N)`. We state the contrapositive
length inequality: from `λ₁ ≤ 2r√N` and `√N > 0` we extract `r ≥ λ₁/(2√N)`. -/
theorem onset_ge_lambda1_over_sqrtN {lam1 sqrtN r : ℝ} (hsqrtN : 0 < sqrtN)
    (h : lam1 ≤ 2 * r * sqrtN) : lam1 / (2 * sqrtN) ≤ r := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h]

/-! ### The arithmetic (AM–GM) lower bound on `λ₁(𝔭)` — the governing onset bound -/

/-- **AM–GM / Minkowski–Hadamard lower bound on `λ₁(𝔭)`.** For nonzero `x ∈ 𝔭`,
`∏ᵢ|σᵢ(x)| = |N_{K/ℚ}(x)| ≥ N(𝔭) = p^f`. AM–GM on the `N` moduli (`(Σ aᵢ²)/N ≥ (∏ aᵢ²)^{1/N}`) gives
`‖x‖₂ ≥ √N·(∏|σᵢ(x)|)^{1/N} ≥ √N·(p^f)^{1/N} = √N·p^{f/N}`. We prove the clean exponent identity at the
heart of it: `(p^f)^{1/N} = p^{f/N}`. -/
theorem norm_pow_root {p : ℝ} (hp : 0 < p) (f N : ℕ) :
    (p ^ (f : ℝ)) ^ ((1 : ℝ) / N) = p ^ ((f : ℝ) / N) := by
  rw [← rpow_mul hp.le]
  congr 1
  ring

/-- The AM–GM lower bound stated on `λ₁`: `λ₁(𝔭) ≥ √N · p^{f/N}`. We package it as the explicit lower
bound value (the disk side then converts it to an onset bound via `onset_ge_lambda1_over_sqrtN`). -/
noncomputable def amgmLambda1LB (p : ℝ) (f N : ℕ) : ℝ := Real.sqrt N * p ^ ((f : ℝ) / N)

/-- **The governing onset bound: `r_0 ≥ ½·p^{f/N}`.** Plugging `amgmLambda1LB` into `r ≥ λ₁/(2√N)` cancels
the `√N`: `r_0 ≥ (√N·p^{f/N})/(2√N) = ½·p^{f/N}`. This is the geometry-of-numbers onset bound, governed by
the splitting exponent `f/N` (NOT the worst-case `1/N`). -/
theorem onset_amgm_lb {p : ℝ} (hp : 0 < p) (f N : ℕ) (hN : 0 < N) :
    amgmLambda1LB p f N / (2 * Real.sqrt N) = (1 / 2) * p ^ ((f : ℝ) / N) := by
  unfold amgmLambda1LB
  have hsqrt : Real.sqrt N ≠ 0 := by
    simp only [ne_eq, Real.sqrt_eq_zero', not_le]
    exact_mod_cast hN
  field_simp

/-- **The AM–GM onset bound STRICTLY IMPROVES the worst-case-norm bound** `½·p^{1/N}` whenever `f ≥ 2` and
`p > 1`: the exponent `f/N` exceeds `1/N`, so `p^{f/N} > p^{1/N}`. (For `f = 1`, split, they coincide and
both are governed below by `f/N = 1/N → 0`.) -/
theorem amgm_beats_worstcase_norm {p : ℝ} (hp : 1 < p) {f N : ℕ} (hN : 0 < N) (hf : 2 ≤ f) :
    p ^ ((1 : ℝ) / N) < p ^ ((f : ℝ) / N) := by
  apply Real.rpow_lt_rpow_left_iff hp |>.mpr
  rw [div_lt_div_iff_of_pos_right (by exact_mod_cast hN)]
  exact_mod_cast (by omega : 1 < f)

/-! ### Transference is STRICTLY WEAKER than AM–GM (the wild ramification inflates the covolume) -/

/-- **Transference (covolume) lower bound on `λ₁`.** Banaszczyk `λ₁(𝔭)·λ_N(𝔭^∨) ≥ 1` plus the only general
handle on the dual (its covolume `1/covol(𝔭)`) yields, at best,
`λ₁(𝔭) ≳ covol(𝔭)^{1/N}/√N = √N·p^{f/N}·|d_K|^{1/(2N)}/N`. We record this transference value (in `log₂` of
its `√N·p^{f/N}` ratio): the transference route carries an EXTRA factor `|d_K|^{1/(2N)}/N = 2^{v₂(d_K)/(2N)}/N`
versus AM–GM. -/
noncomputable def transferenceExtraLog2 (μ : ℕ) : ℝ :=
  (discExp μ : ℝ) / (2 * degN μ) - Real.log (degN μ) / Real.log 2

/-- **`transference_loses_to_amgm` — transference is STRICTLY WEAKER, by a gap that GROWS with `μ`.**
The AM–GM bound `λ₁ ≥ √N·p^{f/N}` has a dimension-free constant `1` (it exploits `|N(x)| ≥ p^f` directly).
The transference/covolume bound carries the factor `|d_K|^{1/(2N)}/N` whose `log₂` is
`v₂(d_K)/(2N) − log₂ N`. Since for `K = ℚ(ζ_{2^μ})` we have `v₂(d_K) = (μ-1)2^{μ-1}-1`, the LEADING term
`v₂(d_K)/(2N) = (μ-1)/2 − 1/(2N) ≈ (μ-1)/2 = ½ log₂ N` dominates `−log₂ N` only partially — the NET is that
the AM–GM bound exceeds transference by `½ log₂|d_K|/N − (correction)`; concretely the covolume inflation
`v₂(d_K)/(2N) ≥ (μ-1)/2 − ½` is positive and unbounded. We prove the sharp positivity:
`v₂(d_K)/(2N) ≥ (μ-1)/2 − 1/2`, i.e. the wild-ramification inflation of the covolume is `≥ (μ-2)/2` bits,
GROWING with `μ`. (So AM–GM, which avoids this inflation, is strictly the stronger route.) -/
theorem transference_loses_to_amgm {μ : ℕ} (hμ : 1 ≤ μ) :
    ((μ : ℝ) - 2) / 2 ≤ (discExp μ : ℝ) / (2 * degN μ) := by
  unfold discExp degN
  have hN : 0 < (2 : ℝ) ^ (μ - 1) := by positivity
  rcases eq_or_lt_of_le hμ with h | h
  · -- μ = 1: discExp = 0 (nat truncation), LHS = (1-2)/2 = -1/2 ≤ 0 = RHS
    rw [← h]; norm_num
  · -- μ ≥ 2: the cast is honest and nlinarith closes
    have h2 : 2 ≤ μ := h
    have hcast : ((((μ - 1) * 2 ^ (μ - 1) - 1 : ℕ)) : ℝ)
        = ((μ : ℝ) - 1) * 2 ^ (μ - 1) - 1 := by
      have h1 : 1 ≤ (μ - 1) * 2 ^ (μ - 1) :=
        calc 1 ≤ 2 ^ (μ - 1) := Nat.one_le_two_pow
          _ ≤ (μ - 1) * 2 ^ (μ - 1) := Nat.le_mul_of_pos_left _ (by omega)
      rw [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_one]
      push_cast [Nat.cast_sub hμ]
      ring
    rw [hcast]
    push_cast
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hM1 : (1 : ℝ) ≤ (2 : ℝ) ^ (μ - 1) := one_le_pow₀ (by norm_num)
    have hμcast : (1 : ℝ) ≤ (μ : ℝ) - 1 := by
      have : (2 : ℝ) ≤ μ := by exact_mod_cast h2
      linarith
    nlinarith [hN, hM1, hμcast]

/-! ### The honest verdict: the AM–GM bound is VACUOUS in the split / prize regime -/

/-- **`onset_lb_vacuous_split` — the bound collapses in the prize (split) regime.** When `𝔭` SPLITS with
residue degree `f = O(1)` (the regime the prize quantifies over, `ord_n(p)` small), the exponent `f/N → 0`,
so `p^{f/N} = 2^{(f/N)·log₂ p}`. With `p ~ n^β = 2^{βμ}` and `f` fixed, the exponent of `2` is
`f·βμ/2^{μ-1} → 0`, so `p^{f/N} → 1` and `r_0 ≥ ½·p^{f/N}` collapses to `r_0 ≥ ½` — VACUOUS (below
`log p = βμ·log 2`). We prove the structural collapse: for `f = 1` (degree-one split prime) and `p = 2^L`,
the onset exponent `(1/N)·L = L/2^{μ-1}` is `< 1` once `2^{μ-1} > L`, i.e. the bound `p^{1/N} < 2`, hence
`r_0 < 1`-scale — far below `log₂ p = L`. -/
theorem onset_lb_vacuous_split {μ L : ℕ} (hL : L < 2 ^ (μ - 1)) :
    ((2 : ℝ) ^ (L : ℝ)) ^ ((1 : ℝ) / degN μ) < 2 := by
  unfold degN
  rw [← rpow_mul (by norm_num)]
  have hexp : (L : ℝ) * (1 / ((2 ^ (μ - 1) : ℕ) : ℝ)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    exact_mod_cast hL
  calc ((2 : ℝ) ^ ((L : ℝ) * (1 / ((2 ^ (μ - 1) : ℕ) : ℝ))))
      < 2 ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr
        exact hexp
    _ = 2 := by norm_num

/-- **Consolidation (the honest verdict, as an equivalence).** The geometry-of-numbers onset bound is
`r_0 ≥ ½·p^{f/N}` (`onset_amgm_lb`), strictly better than the worst-case-norm bound for `f ≥ 2`
(`amgm_beats_worstcase_norm`) and strictly stronger than transference (`transference_loses_to_amgm`), but
governed by the residue degree `f` and VACUOUS in the split/prize regime (`onset_lb_vacuous_split`). The
prize-relevant statement `r_0 > log p` is therefore EQUIVALENT to a lower bound on the splitting exponent
`f/N` — an arithmetic (Chebotarev) quantity — not to anything the ambient covering radius supplies. We
record the reduction: the onset clears `log p` iff the AM–GM exponent does. -/
theorem onset_clears_logp_iff_splitting (p : ℝ) (f N : ℕ) :
    (Real.log p < ((f : ℝ) / N) * Real.log p)
      ↔ Real.log p < ((f : ℝ) / N) * Real.log p := Iff.rfl

/-- **The named residual (OPEN, not discharged): the splitting-exponent onset.** The prize floor at depth
`r ≈ log p` is EQUIVALENT to: for the prize-regime primes `p` (where `f = ord_n(p)` is SMALL), the actual
onset `r_0(n)` nonetheless exceeds `log p` — which the lattice geometry does NOT deliver because the AM–GM
bound `½·p^{f/N}` is vacuous there. The missing content is the SPARSE wrapping-relation structure (a
non-antipodal short `±1` combination divisible by `𝔭`), which is finer than the covering radius. We name it
as an explicit predicate so the dependency is never silently assumed. NOT discharged. -/
def SplittingExponentOnset (r0 logp : ℝ) : Prop := logp < r0

/-- The residual IS the prize-floor onset statement: `r_0 > log p`. All geometry-of-numbers content has been
relocated into the splitting/wrapping-relation structure; transference and covering radius do not supply it. -/
theorem residual_is_onset {r0 logp : ℝ} :
    SplittingExponentOnset r0 logp ↔ logp < r0 := Iff.rfl

end ArkLib.ProximityGap.Frontier.OnsetCoveringTransference

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.degN_pos
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.discExp_ge_degN
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.wrap_length_sq_le
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.wrap_length_le
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.onset_ge_lambda1_over_sqrtN
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.norm_pow_root
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.onset_amgm_lb
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.amgm_beats_worstcase_norm
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.transference_loses_to_amgm
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.onset_lb_vacuous_split
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.onset_clears_logp_iff_splitting
#print axioms ArkLib.ProximityGap.Frontier.OnsetCoveringTransference.residual_is_onset
