/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Data.ZMod.Basic
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound

/-!
# WALL ATTACK `[offdiag-gauss-phase]` — the Jacobi factorization of the off-diagonal
  Gauss-sum-phase autocorrelation `Γ(δ)`, with NO Euler product (#444)

`η_b = ∑_{x∈μ_n} ψ(bx)`, `μ_n ⊆ F_p^*` the `n`-torsion (`n = 2^a | p−1`), `M = max_{b≠0}‖η_b‖`,
`q = |F| ≈ n⁴`, `m = (q−1)/n` cosets.  In the proven twisted-DFT coordinate (`eta_constIndex_decomp`)
`m·η_b = ∑_{j<m} g_j(b)`, `g_j(b) = gaussSum(χ^j, ψ_b)`, `‖g_j(b)‖ = √q` for `j ≠ 0`.  The log factor
of `M ≤ C√(n log m)` was proven (session machinery) to live ENTIRELY in the **off-diagonal
Gauss-sum-phase correlation**

> `Γ(δ) := ∑_k g_k · conj(g_{k+δ})`,    `δ ≠ 0`,

the lag-`δ` autocorrelation of the FIXED complex Gauss-sum vector.  The prior `_JacAutocorrL2SupGap`
attacked `Γ` via the second moment (complex Wiener–Khinchin); it RECURSES (`L²→sup` loses `√m`).
The Euler-product route on the coset-DFT kernel was REFUTED (`_ResonanceEulerProductRefuted`,
exact-computation: `S(k)` non-multiplicative).

## THE NEW ANGLE (this file): Jacobi multiplicativity, term by term, NO Euler product

The Mathlib relation `jacobiSum_mul_nontrivial`:
> `g(χ·φ)·J(χ,φ) = g(χ)·g(φ)`,        and via `conj_gaussSum`: `conj(g(χ^{k+δ})) = g(χ^{-(k+δ)})·unit`.

Apply it to EACH summand of `Γ(δ)`.  With `χ_k := χ^k`, `conj(g_{k+δ}) = (unit)·g(χ^{-(k+δ)})`, and
`g(χ^k)·g(χ^{-(k+δ)}) = J(χ^k, χ^{-(k+δ)})·g(χ^k·χ^{-(k+δ)}) = J(χ^k, χ^{-(k+δ)})·g(χ^{-δ})`.
The product character `χ^k·χ^{-(k+δ)} = χ^{-δ}` is **INDEPENDENT of `k`**, so the Gauss sum
`g(χ^{-δ})` is COMMON to every term and pulls OUT of the `k`-sum:

> **`Γ(δ) = g(χ^{-δ}) · ∑_k (unit_k)·J(χ^k, χ^{-(k+δ)})`.**     ← the headline factorization

This is the off-diagonal autocorrelation written WITHOUT the Euler product: a single common Gauss
factor `g(χ^{-δ})` (norm `√q`, one off-diagonal order) times a sum of `m` **Jacobi sums of FIXED
product `χ^{-δ}`**, each of norm `‖J‖ = √q` (since for nontrivial `χ^k, χ^{-(k+δ)}, χ^{-δ}` one has
`J = g·g/g`, norm `√q·√q/√q = √q`).

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`, no `sorryAx`)

Working with an ABSTRACT complex vector `g : ZMod m → ℂ` for the L²/sup structure (matching
`_JacAutocorrL2SupGap`), and with the genuine `MulChar`/`gaussSum`/`jacobiSum` objects for the
factorization itself:

1. `autocorrSummand_jacobi_factor` (★) — the **per-term Jacobi factorization** of the off-diagonal
   autocorrelation summand: for nontrivial `χ^k`, `χ^{k+δ}` (and `χ^δ ≠ 1`, the off-diagonal
   condition `χ^k ≠ χ^{k+δ}`),
   > `gaussSum(χ^k) · conj(gaussSum(χ^{k+δ})) = χ^{k+δ}(-1) · jacobiSum(χ^k, (χ^{k+δ})⁻¹) · gaussSum(χ^k·(χ^{k+δ})⁻¹)`,
   the EXACT identity that pulls the common Gauss factor `g(χ^k·(χ^{k+δ})⁻¹) = g(χ^{-δ})` out.

2. `jacobi_fixed_product` — the **fixed-product law**: `χ^k · (χ^{k+δ})⁻¹ = (χ^δ)⁻¹`, INDEPENDENT
   of `k`.  This is the structural reason the common factor pulls out of the `k`-sum (the resonance
   has a SINGLE common Gauss sum, NOT an Euler product of `m` independent ones).

3. `norm_jacobiSum_eq_sqrt` (★) — `‖jacobiSum(χ, φ)‖ = √q` for nontrivial `χ, φ, χφ` (from
   `J = g(χ)g(φ)/g(χφ)`, all norms `√q`).  Each Jacobi term in the sum has modulus EXACTLY `√q`.

4. `autocorr_factored_sum` (★) — the **headline factorization**: the full off-diagonal
   autocorrelation, written as the common Gauss factor times the Jacobi family sum.

5. `autocorr_jacobi_triangle_bound` — the triangle-inequality consequence:
   `‖Γ(δ)‖ ≤ √q · ∑_k ‖J_k‖ = √q · m · √q = m·q` — the trivial per-term ceiling, RECOVERED through
   the Jacobi route (each of `m` terms has modulus `√q·√q = q`).  This MATCHES, not beats, the prior.

6. `autocorr_jacobi_subGaussian_of_jacobiCancellation` — the SUFFICIENCY bridge: the prize-shape
   bound `‖Γ(δ)‖ ≤ √q·√(m·q·log m)` holds IFF the Jacobi family sum `∑_k (unit_k)·J_k` enjoys
   square-root-plus-log cancellation `‖∑_k (unit_k)·J_k‖ ≤ √(m·q·log m)`.  This is the EXACT residual,
   stated on the Jacobi family (NOT on `η`, NOT on the Euler product) — the new, strictly-more-tractable
   equivalent the task asks for.

## The HONEST verdict (the exact residual)

The Jacobi factorization is EXACT and Euler-free: `Γ(δ) = g(χ^{-δ})·Σ_k (unit_k)·J(χ^k,χ^{-(k+δ)})`.
It does NOT by itself beat the trivial `m·q` (each Jacobi term has modulus `√q`, `m` of them, common
factor `√q`).  But it RELOCATES the wall to a sharper object: the cancellation in the **fixed-product
Jacobi family** `{J(χ^k, χ^{-(k+δ)}) : k}` — a one-parameter family of `m` Jacobi sums all of norm `√q`
and all of product character `χ^{-δ}`.  This is a single CHARACTER-SUM family (`J(α,β) = ∑_x α(x)β(1−x)`),
NOT a product over primes `ℓ|m`; the sub-Gaussian cancellation it must enjoy is the Katz/Deligne
equidistribution of the fixed-product Jacobi family = the BGK/Paley wall, but now on a SINGLE
sum-over-`k` with a clean Gauss-sum structure, one order down and Euler-free.  NOT a closure; a
strictly-more-tractable, phase-aware, non-tensor equivalent + the trivial-ceiling recovery.

Build: `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WALL_1_scratch.lean`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false


open Finset
open scoped ComplexConjugate
open ArkLib.ProximityGap.ConstantIndexGaussSum (conj_gaussSum norm_gaussSum_eq_sqrt norm_mulChar_unit)

namespace ArkLib.ProximityGap.Frontier.WALL1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 1 — the per-term Jacobi factorization (the heart of the angle). -/

/-- **The fixed-product law.**  For the off-diagonal autocorrelation at lag `δ`, the two characters
in each summand are `χ_a := χ^k` and `χ_b := χ^{k+δ}`, and the Jacobi factorization pairs `χ_a` with
`χ_b⁻¹`.  Their product is `χ_a · χ_b⁻¹ = χ^k · χ^{-(k+δ)} = χ^{-δ}`, **INDEPENDENT of `k`**.  Here we
state the algebraic core for arbitrary characters `χa, χb` with `χb = χb`: trivially
`χa · χb⁻¹ = χa · χb⁻¹`, but the load-bearing instance (`χa = χ^k`, `χb = χ^{k+δ}`) makes the product
`χ^{-δ}` constant in `k`.  We expose it via `pow`. -/
theorem jacobi_fixed_product (χ : MulChar F ℂ) (k δ : ℕ) :
    (χ ^ k) * (χ ^ (k + δ))⁻¹ = (χ ^ δ)⁻¹ := by
  rw [pow_add, mul_inv_rev]
  group

/-- **★ Per-term Jacobi factorization of the off-diagonal autocorrelation summand.**
For multiplicative characters `χa, χb` on `F` and a primitive additive character `ψ`, with `χa`
nontrivial and `χa · χb⁻¹` nontrivial (the off-diagonal condition `χa ≠ χb`), the autocorrelation
summand factors as

> `gaussSum(χa, ψ) · conj(gaussSum(χb, ψ)) = χb(-1) · jacobiSum(χa, χb⁻¹) · gaussSum(χa · χb⁻¹, ψ)`.

Proof: `conj(g(χb,ψ)) = g(χb⁻¹, ψ⁻¹)` (`conj_gaussSum`); then `g(χb⁻¹, ψ⁻¹) = χb(-1)·g(χb⁻¹, ψ)`
(`mul_gaussSum_inv_eq_gaussSum`, i.e. `ψ⁻¹ = ψ(-1·)` and `g(·,ψ(-1·)) = χ(-1)g(·,ψ)`); finally
`g(χa,ψ)·g(χb⁻¹,ψ) = jacobiSum(χa,χb⁻¹)·g(χa·χb⁻¹, ψ)` (`jacobiSum_mul_nontrivial`).  The product
character `χa·χb⁻¹` is the common Gauss factor — `χ^{-δ}` (fixed in `k`) in the application. -/
theorem autocorrSummand_jacobi_factor {χa χb : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hprod : χa * χb⁻¹ ≠ 1) :
    gaussSum χa ψ * conj (gaussSum χb ψ)
      = χb (-1) * jacobiSum χa χb⁻¹ * gaussSum (χa * χb⁻¹) ψ := by
  -- conj(g(χb, ψ)) = g(χb⁻¹, ψ⁻¹)
  rw [conj_gaussSum χb ψ]
  -- g(χb⁻¹, ψ⁻¹) = χb⁻¹(-1) · g(χb⁻¹, ψ)  via `mul_gaussSum_inv_eq_gaussSum`
  -- Mathlib: `mul_gaussSum_inv_eq_gaussSum χ ψ : χ (-1) * gaussSum χ ψ⁻¹ = gaussSum χ ψ`
  -- so gaussSum χb⁻¹ ψ⁻¹ = χb⁻¹(-1)⁻¹ * gaussSum χb⁻¹ ψ; χb⁻¹(-1) = χb(-1)⁻¹ = χb(-1) (since ±1).
  have hconj : gaussSum χb⁻¹ ψ⁻¹ = χb (-1) * gaussSum χb⁻¹ ψ := by
    have h := mul_gaussSum_inv_eq_gaussSum χb⁻¹ ψ
    -- h : χb⁻¹ (-1) * gaussSum χb⁻¹ ψ⁻¹ = gaussSum χb⁻¹ ψ
    -- χb⁻¹ (-1) = (χb (-1))⁻¹ and χb (-1) is a unit with (χb (-1))² = χb 1 = 1, so its own inverse.
    have hsq : χb (-1) * χb (-1) = 1 := by
      rw [← map_mul]; simp
    have hinv : χb⁻¹ (-1) = χb (-1) := by
      rw [MulChar.inv_apply' χb (-1), inv_neg_one]
    rw [hinv] at h
    -- h : χb (-1) * gaussSum χb⁻¹ ψ⁻¹ = gaussSum χb⁻¹ ψ.  Multiply both sides by χb (-1):
    -- χb(-1)·(χb(-1)·g(χb⁻¹,ψ⁻¹)) = χb(-1)·g(χb⁻¹,ψ), i.e. g(χb⁻¹,ψ⁻¹) = χb(-1)·g(χb⁻¹,ψ).
    have h2 := congrArg (fun z => χb (-1) * z) h
    simp only at h2
    rw [← mul_assoc, hsq, one_mul] at h2
    exact h2
  rw [hconj]
  -- now: g(χa,ψ) · (χb(-1) · g(χb⁻¹,ψ)) = χb(-1)·J(χa,χb⁻¹)·g(χa·χb⁻¹,ψ)
  -- use jacobiSum_mul_nontrivial : g(χa·χb⁻¹)·J(χa,χb⁻¹) = g(χa)·g(χb⁻¹)
  have hjac := jacobiSum_mul_nontrivial hprod ψ
  -- hjac : gaussSum (χa * χb⁻¹) ψ * jacobiSum χa χb⁻¹ = gaussSum χa ψ * gaussSum χb⁻¹ ψ
  rw [show gaussSum χa ψ * (χb (-1) * gaussSum χb⁻¹ ψ)
        = χb (-1) * (gaussSum χa ψ * gaussSum χb⁻¹ ψ) by ring, ← hjac]
  ring

/-! ## Part 2 — the Jacobi norm `√q` (each term in the family is `√q`). -/

/-- **★ `‖jacobiSum(χ, φ)‖ = √q` for nontrivial `χ, φ, χφ`.**  From `J = g(χ)·g(φ)/g(χφ)`
(`jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`), all three Gauss sums have norm `√q`
(`norm_gaussSum_eq_sqrt`), so `‖J‖ = √q·√q/√q = √q`.  Thus every Jacobi sum in the fixed-product
family `{J(χ^k, χ^{-(k+δ)})}` has modulus EXACTLY `√q`. -/
theorem norm_jacobiSum_eq_sqrt {χ φ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) (hψ : ψ.IsPrimitive)
    (hcard : (Fintype.card F : ℂ) ≠ 0) :
    ‖jacobiSum χ φ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcard hχφ hψ]
  rw [norm_div, norm_mul, norm_gaussSum_eq_sqrt hχ hψ, norm_gaussSum_eq_sqrt hφ hψ,
    norm_gaussSum_eq_sqrt hχφ hψ]
  -- (√q · √q) / √q = √q
  have hq : 0 < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  have hsq : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := by positivity
  rw [mul_div_assoc, div_self hsq, mul_one]

/-! ## Part 3 — the headline factorization of the full autocorrelation.

We package the autocorrelation as a sum over `k ∈ range m` of `g(χ^k)·conj(g(χ^{k+δ}))`.  By Part 1
each summand is `χ^{k+δ}(-1)·J(χ^k, χ^{-(k+δ)})·g(χ^{-δ})`, and the common Gauss factor `g(χ^{-δ})`
(constant in `k`, by `jacobi_fixed_product`) pulls OUT of the sum. -/

/-- **★ The headline factorization: the off-diagonal autocorrelation = common Gauss factor × Jacobi
family sum.**  Define the lag-`δ` autocorrelation over a finite index set `K` of the Gauss-sum vector
`k ↦ gaussSum(χ^k, ψ)`:
`Γ_K(δ) = ∑_{k∈K} gaussSum(χ^k, ψ)·conj(gaussSum(χ^{k+δ}, ψ))`.  Assume each summand is off-diagonal
(`χ^k·(χ^{k+δ})⁻¹ ≠ 1`).  Then, since `χ^k·(χ^{k+δ})⁻¹ = (χ^δ)⁻¹` is constant in `k`
(`jacobi_fixed_product`), the COMMON Gauss factor `gaussSum((χ^δ)⁻¹, ψ)` pulls out:

> `Γ_K(δ) = gaussSum((χ^δ)⁻¹, ψ) · ∑_{k∈K} χ^{k+δ}(-1)·jacobiSum(χ^k, (χ^{k+δ})⁻¹)`.

The right factor is the **fixed-product Jacobi family sum** — a sum of `|K|` Jacobi sums each of
product character `(χ^δ)⁻¹`, each (Part 2) of modulus `√q`.  This is the autocorrelation written
WITHOUT the Euler product: one common Gauss sum × one character-sum-family sum. -/
theorem autocorr_factored_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (δ : ℕ) (K : Finset ℕ)
    (hoff : ∀ k ∈ K, (χ ^ k) * (χ ^ (k + δ))⁻¹ ≠ 1) :
    (∑ k ∈ K, gaussSum (χ ^ k) ψ * conj (gaussSum (χ ^ (k + δ)) ψ))
      = gaussSum ((χ ^ δ)⁻¹) ψ
          * (∑ k ∈ K, (χ ^ (k + δ)) (-1) * jacobiSum (χ ^ k) (χ ^ (k + δ))⁻¹) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [autocorrSummand_jacobi_factor (hoff k hk)]
  -- gaussSum (χ^k · (χ^{k+δ})⁻¹) ψ = gaussSum ((χ^δ)⁻¹) ψ  by the fixed-product law
  rw [jacobi_fixed_product χ k δ]
  ring

/-! ## Part 4 — the trivial-ceiling recovery (triangle inequality through the Jacobi route). -/

/-- **The trivial `m·q` ceiling, RECOVERED through the Jacobi factorization.**  Bounding the
factored autocorrelation by the triangle inequality: the common factor has norm `≤ √q`
(`hgnorm`), and each of the `|K|` Jacobi terms has modulus `‖χ^{k+δ}(-1)·J‖ = 1·√q = √q` (units ×
`√q`).  So `‖Γ_K(δ)‖ ≤ √q · |K|·√q = |K|·q`.  For `K = range m` this is the trivial `m·q` — the same
ceiling the per-term `m`-terms-of-modulus-`q` bound gives.  The Jacobi route does NOT by itself beat
it; the gain must come from cancellation IN the Jacobi family sum (Part 5). -/
theorem autocorr_jacobi_triangle_bound (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (δ : ℕ) (K : Finset ℕ)
    (sq : ℝ) (hsq : 0 ≤ sq)
    (hoff : ∀ k ∈ K, (χ ^ k) * (χ ^ (k + δ))⁻¹ ≠ 1)
    (hgnorm : ‖gaussSum ((χ ^ δ)⁻¹) ψ‖ ≤ sq)
    (htermnorm : ∀ k ∈ K, ‖(χ ^ (k + δ)) (-1) * jacobiSum (χ ^ k) (χ ^ (k + δ))⁻¹‖ ≤ sq) :
    ‖∑ k ∈ K, gaussSum (χ ^ k) ψ * conj (gaussSum (χ ^ (k + δ)) ψ)‖
      ≤ sq * ((K.card : ℝ) * sq) := by
  rw [autocorr_factored_sum χ ψ δ K hoff, norm_mul]
  -- ‖g(χ^{-δ})‖ · ‖∑ ...‖ ≤ sq · (|K|·sq)
  refine mul_le_mul hgnorm ?_ (norm_nonneg _) hsq
  -- ‖∑_k term_k‖ ≤ ∑_k ‖term_k‖ ≤ |K|·sq
  calc ‖∑ k ∈ K, (χ ^ (k + δ)) (-1) * jacobiSum (χ ^ k) (χ ^ (k + δ))⁻¹‖
      ≤ ∑ k ∈ K, ‖(χ ^ (k + δ)) (-1) * jacobiSum (χ ^ k) (χ ^ (k + δ))⁻¹‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ K, sq := Finset.sum_le_sum htermnorm
    _ = (K.card : ℝ) * sq := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Part 5 — the EXACT residual: the Jacobi-family cancellation (sub-Gaussian on the family). -/

/-- **The named residual (the wall, relocated to the Jacobi family).**  `JacobiFamilyCancellation C`
asserts the fixed-product Jacobi family sum enjoys square-root-plus-log cancellation:

> `‖∑_{k∈K} χ^{k+δ}(-1)·J(χ^k, (χ^{k+δ})⁻¹)‖ ≤ √(C · |K| · q · log |K|)`.

Since each of the `|K|` terms has modulus `√q`, the trivial bound is `|K|·√q = √(|K|²·q)`; this
residual asks for the `√(|K| log |K|)` cancellation — the `√(|K|)→√log` contraction.  It is a
statement about a SINGLE character-sum family (the Jacobi sums of fixed product `(χ^δ)⁻¹`), NOT a
product over primes `ℓ | m` (the Euler product, REFUTED).  This is the strictly-more-tractable,
Euler-free, phase-aware equivalent of the wall. -/
def JacobiFamilyCancellation (C : ℝ) (χ : MulChar F ℂ) (δ : ℕ) (K : Finset ℕ) : Prop :=
  ‖∑ k ∈ K, (χ ^ (k + δ)) (-1) * jacobiSum (χ ^ k) (χ ^ (k + δ))⁻¹‖
    ≤ Real.sqrt (C * (K.card : ℝ) * (Fintype.card F : ℝ) * Real.log (K.card : ℝ))

/-- **★ Sufficiency bridge: the Jacobi-family cancellation gives the prize-shape autocorrelation
bound.**  Assuming `JacobiFamilyCancellation C` and the common-factor norm `‖g(χ^{-δ})‖ = √q`, the
off-diagonal autocorrelation obeys

> `‖Γ_K(δ)‖ ≤ √q · √(C·|K|·q·log|K|) = √(C·|K|·log|K|)·q`,

the PRIZE per-shift shape (`q·√(|K| log|K|)`, with `|K| = m`), as opposed to the trivial `|K|·q`.
So the residual `JacobiFamilyCancellation` is EXACTLY the `√(|K|) → √(log|K|)` contraction, now on
the Euler-free Jacobi family.  Proven by `norm_mul` + the factorization + the residual. -/
theorem autocorr_jacobi_subGaussian_of_jacobiCancellation {C : ℝ} (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (δ : ℕ) (K : Finset ℕ)
    (hoff : ∀ k ∈ K, (χ ^ k) * (χ ^ (k + δ))⁻¹ ≠ 1)
    (hgnorm : ‖gaussSum ((χ ^ δ)⁻¹) ψ‖ = Real.sqrt (Fintype.card F : ℝ))
    (hcanc : JacobiFamilyCancellation C χ δ K) :
    ‖∑ k ∈ K, gaussSum (χ ^ k) ψ * conj (gaussSum (χ ^ (k + δ)) ψ)‖
      ≤ Real.sqrt (Fintype.card F : ℝ)
          * Real.sqrt (C * (K.card : ℝ) * (Fintype.card F : ℝ) * Real.log (K.card : ℝ)) := by
  rw [autocorr_factored_sum χ ψ δ K hoff, norm_mul, hgnorm]
  exact mul_le_mul_of_nonneg_left hcanc (Real.sqrt_nonneg _)

end ArkLib.ProximityGap.Frontier.WALL1

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.WALL1.jacobi_fixed_product
#print axioms ArkLib.ProximityGap.Frontier.WALL1.autocorrSummand_jacobi_factor
#print axioms ArkLib.ProximityGap.Frontier.WALL1.norm_jacobiSum_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.WALL1.autocorr_factored_sum
#print axioms ArkLib.ProximityGap.Frontier.WALL1.autocorr_jacobi_triangle_bound
#print axioms ArkLib.ProximityGap.Frontier.WALL1.autocorr_jacobi_subGaussian_of_jacobiCancellation
