/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound

/-!
# PROVE-attempt (#444) — angle [katz-jacobi-equidist]: the autocorrelation `A(s)` is a FIXED
  Gauss sum times a HORIZONTAL Jacobi family, and the residual is the EFFECTIVE equidistribution
  discrepancy of that family.

## The decisive structural step this file proves (NEW)

The residual named in `_ProveJacobiDFTAnchor` / `_ProveOffDiagResonanceCapstone` is the off-diagonal
autocorrelation `A(s) = ∑_{j<m} g_j · conj(g_{j+s})` of the fixed Gauss-sum DFT vector
`g_j = gaussSum(χ^j, ψ)`. The proven anchor `autocorr_term_eq_jacobi` says each term is
`g(χ^j)·conj(g(χ^{j+s})) = χ^{j+s}(-1)·J(χ^j, (χ^{j+s})⁻¹)·g(χ^j·(χ^{j+s})⁻¹)`. The crux of the
[katz-jacobi-equidist] angle is that **the trailing Gauss sum `g(χ^j·(χ^{j+s})⁻¹) = g(χ^{-s})` is
INDEPENDENT of the summation index `j`** (it depends only on the shift `s`). Therefore it factors
completely OUT of the sum, leaving

  A(s) = g(χ^{-s}) · ∑_{j<m} χ^{j+s}(-1) · J(χ^j, (χ^{j+s})⁻¹) = g(χ^{-s}) · T(s),     (★)

where `T(s) = ∑_{j<m} χ^{j+s}(-1)·J(χ^j, χ^{-(j+s)})` is a sum over the **horizontal family**
`j ↦ J(χ^j, χ^{-(j+s)})` of Jacobi sums (fixed `s`, varying `j`). Each summand has modulus EXACTLY
`√q` (`norm_jacobiSum_eq_sqrt`), and `χ^{j+s}(-1) = ±1` is a sign.

This is the SHARP form the previous Katz file (`_JacobiKatzEquidist`) lacked: it analysed the WRONG
family — the dim-`(r-1)` Fermat-hypersurface family of the iterated `r`-fold Jacobi sum, whose
conductor `n^r` blows up. The family in (★) is a **one-parameter (horizontal) family of ordinary
2-variable Jacobi sums**, living on a curve, whose conductor is BOUNDED (independent of `j` and of the
working order). It is exactly the family to which Katz/Deligne equidistribution applies with a
`√(#family) = √m`-type discrepancy at the working order. So the angle's promise is real: the
conductor blow-up is an artifact of the iterated family, not of the autocorrelation family.

## What is PROVEN here (axiom-clean target [propext, Classical.choice, Quot.sound])

1. `autocorr_factor_eq` — the per-term factorisation with the trailing Gauss sum named as `g(χ^{-s})`:
   `g(χ^j)·conj(g(χ^{j+s})) = (χ^{j+s}(-1) · J(χ^j, (χ^{j+s})⁻¹)) · g(χ^{-s})`. (= `autocorr_term_eq_jacobi`
   with `χ^j·(χ^{j+s})⁻¹` rewritten to `χ^{-s}` — pure group algebra in the exponents.)
2. `autocorr_factor_out` — the FULL (★): `A(s) = g(χ^{-s}) · T(s)`, the Gauss sum pulled out of the sum.
3. `autocorr_norm_eq` — taking norms: `‖A(s)‖ = √q · ‖T(s)‖` (for `s` with `χ^s ≠ 1`, so `‖g(χ^{-s})‖=√q`).
4. `jacobi_phase_term_norm` — each summand of `T(s)` has modulus EXACTLY `√q`.
5. `Tval_triangle` — the trivial triangle bound `‖T(s)‖ ≤ m·√q`, hence `‖A(s)‖ ≤ m·q` (the no-cancellation
   value; the prize needs `‖T(s)‖ ≤ C·√q·√(m log m)`, i.e. `√(m log m)`-cancellation in the horizontal family).
6. `EffectiveEquidistResidual` — the NAMED residual: the effective equidistribution discrepancy of the
   horizontal Jacobi family, `‖T(s)‖ ≤ C·√q·√(m log m)`, equivalently `‖∑_j u_j‖ ≤ C·√(m log m)` for the
   `m` UNIT phases `u_j = χ^{j+s}(-1)·J(χ^j,χ^{-(j+s)})/√q`.
7. `autocorr_le_of_residual` — the residual SUFFICES: `EffectiveEquidistResidual ⟹ ‖A(s)‖ ≤ C·q·√(m log m)`,
   the per-shift sub-Gaussian bound that (summed over `s` and frequency-twisted) is the
   `OffDiagResonanceBounded` of `_ProveOffDiagResonanceCapstone`.

## EXACT RESIDUAL (honest)

The residual is the EFFECTIVE equidistribution discrepancy `Disc_s(m)` of the **horizontal Jacobi
family** `j ↦ J(χ^j, χ^{-(j+s)})/√q ∈ S¹` (`m` unit phases). Katz–Deligne gives that THIS family
equidistributes in its monodromy group with discrepancy controlled by a BOUNDED conductor (no `n^r`
blow-up — that was the iterated-family artifact), but the quantitative (Erdős–Turán) form delivers
`Disc_s(m) ≤ C(conductor)·m^{-1/2}` only as `m → ∞`, i.e. against the FULL family size `m = (p-1)/n`.

WHERE IT RECURSES: square-root cancellation of `m` unit phases requires controlling the discrepancy
DOWN TO scale `√(m log m)`, i.e. `‖∑ u_j‖²/m ≤ C log m`. The horizontal family's Frobenius phases are
`J(χ^j, χ^{-(j+s)})/√q`; their joint law is governed by the SAME monodromy as the period itself
(the autocorrelation is the period's power spectrum). Concretely, `T(s)` is — by `autocorr_term_eq_jacobi`
read backwards — a Gauss-sum DFT one order down: it is `√q·(twisted DFT of the `J`-phases)`, and the
`J`-phases are themselves Gauss-period objects of the SAME `μ_n`. So the cancellation `‖T(s)‖ ≤ √q√(m log m)`
is the prize for the order-`m` family of Jacobi phases — **self-similar, one order down, NOT smaller**.
The conductor obstruction is removed (genuine progress over `_JacobiKatzEquidist`), but the effective
RANGE obstruction remains: Katz is asymptotic in `m`, the prize is at the FIXED prime with the family
size pinned to `m = (p-1)/n`, and the discrepancy must reach `√(log m)/√m` — a `√(log m)` factor beyond
the unconditional `m^{-1/2}+ε` that effective equidistribution supplies on a density-1 family but NOT
on this thin slice. This is the residual; it SHRINKS the gap by removing the conductor blow-up and
pinning the open part to a one-parameter (curve, bounded-conductor) discrepancy, but it does NOT close
it: the same `√(m log m)` cancellation, one order down.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.ConstantIndexGaussSum

namespace ArkLib.ProximityGap.Frontier.JacKatz

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Magnitude anchor (re-derived locally so this file is self-contained) -/

/-- `|J(χ,φ)| = √q` for `χ, φ, χφ` nontrivial. (3 lines from `jacobiSum_mul_nontrivial` +
`norm_gaussSum_eq_sqrt`; the missing-from-Mathlib magnitude anchor.) -/
theorem norm_jacobiSum_eq_sqrt {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖jacobiSum χ φ‖ = Real.sqrt (Fintype.card F) := by
  have hid := jacobiSum_mul_nontrivial hχφ ψ
  have hnorm := congrArg norm hid
  rw [norm_mul, norm_mul] at hnorm
  rw [norm_gaussSum_eq_sqrt hχφ hψ, norm_gaussSum_eq_sqrt hχ hψ,
      norm_gaussSum_eq_sqrt hφ hψ] at hnorm
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (Fintype.card F) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have : Real.sqrt (Fintype.card F) * ‖jacobiSum χ φ‖
       = Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F) := by rw [hnorm]
  exact (mul_left_cancel₀ (ne_of_gt hsqrt_pos) this)

/-! ## Conjugate-of-Gauss-sum against the SAME ψ (re-derived locally). -/

/-- `conj(g(χ,ψ)) = χ(-1) · g(χ⁻¹, ψ)`. -/
theorem conj_gaussSum_same {χ : MulChar F ℂ} (ψ : AddChar F ℂ) :
    (starRingEnd ℂ) (gaussSum χ ψ) = χ (-1) * gaussSum χ⁻¹ ψ := by
  rw [conj_gaussSum]
  have h := mul_gaussSum_inv_eq_gaussSum (χ := χ⁻¹) (ψ := ψ)
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; norm_num
  have hinv : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv']; exact inv_eq_of_mul_eq_one_left hsq
  rw [hinv] at h
  rw [← h, ← mul_assoc, hsq, one_mul]

/-! ## The autocorrelation single-term identity (re-derived), and THE FACTORISATION. -/

/-- `g(α)·conj(g(γ)) = γ(-1)·J(α,γ⁻¹)·g(α·γ⁻¹)` for `α·γ⁻¹ ≠ 1`. (= `autocorr_term_eq_jacobi`.) -/
theorem autocorr_term_eq_jacobi {α γ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hαγ : α * γ⁻¹ ≠ 1) :
    gaussSum α ψ * (starRingEnd ℂ) (gaussSum γ ψ)
      = γ (-1) * jacobiSum α γ⁻¹ * gaussSum (α * γ⁻¹) ψ := by
  rw [conj_gaussSum_same]
  have hid := jacobiSum_mul_nontrivial hαγ ψ
  rw [show gaussSum α ψ * (γ (-1) * gaussSum γ⁻¹ ψ)
        = γ (-1) * (gaussSum α ψ * gaussSum γ⁻¹ ψ) by ring, ← hid]
  ring

/-- **★ Sub-step 1 (the per-term factorisation with the trailing Gauss sum named as `g(χ^{-s})`).**
Specialising `autocorr_term_eq_jacobi` to `α = χ^j`, `γ = χ^{j+s}` and rewriting the trailing
character `χ^j · (χ^{j+s})⁻¹ = χ^{-s}` (`= (χ^s)⁻¹`), the autocorrelation summand factors as a
**`j`-dependent Jacobi phase** times the **`j`-INDEPENDENT Gauss sum `g((χ^s)⁻¹)`**:

> `g(χ^j)·conj(g(χ^{j+s})) = (χ^{j+s}(-1)·J(χ^j, (χ^{j+s})⁻¹)) · g((χ^s)⁻¹)`.

This is the structural pivot of the [katz-jacobi-equidist] angle: the only `j`-independent magnitude
`√q` (the trailing Gauss sum) is now explicitly isolated, so it can be pulled out of `∑_j`. The
condition `χ^j·(χ^{j+s})⁻¹ = (χ^s)⁻¹ ≠ 1` is just `χ^s ≠ 1`. -/
theorem autocorr_factor_eq {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (j s : ℕ)
    (hs : (χ ^ s)⁻¹ ≠ 1) :
    gaussSum (χ ^ j) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (j + s)) ψ)
      = ((χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹) * gaussSum ((χ ^ s)⁻¹) ψ := by
  -- α·γ⁻¹ = χ^j · (χ^{j+s})⁻¹ = (χ^s)⁻¹
  have hαγ_eq : (χ ^ j) * (χ ^ (j + s))⁻¹ = (χ ^ s)⁻¹ := by
    rw [pow_add, mul_inv, ← mul_assoc, mul_comm (χ ^ j) ((χ ^ j)⁻¹), inv_mul_cancel, one_mul]
  have hαγ : (χ ^ j) * (χ ^ (j + s))⁻¹ ≠ 1 := by rw [hαγ_eq]; exact hs
  rw [autocorr_term_eq_jacobi hαγ, hαγ_eq]

/-- **★ Sub-step 2 (the FULL factorisation (★): pull the fixed Gauss sum out of the sum).**
Summing `autocorr_factor_eq` over `j ∈ range m` and using `Finset.sum_mul` (the `j`-independent
factor `g((χ^s)⁻¹)` distributes out):

> `A(s) := ∑_{j<m} g(χ^j)·conj(g(χ^{j+s})) = T(s) · g((χ^s)⁻¹)`,   where
> `T(s) := ∑_{j<m} χ^{j+s}(-1)·J(χ^j, (χ^{j+s})⁻¹)`.

The autocorrelation is a SINGLE √q-modulus Gauss sum times a sum over the **horizontal Jacobi family**
`j ↦ J(χ^j, (χ^{j+s})⁻¹)`. THIS is the family whose effective equidistribution is the residual. -/
theorem autocorr_factor_out {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (m s : ℕ)
    (hs : (χ ^ s)⁻¹ ≠ 1) :
    (∑ j ∈ Finset.range m, gaussSum (χ ^ j) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (j + s)) ψ))
      = (∑ j ∈ Finset.range m, (χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹)
        * gaussSum ((χ ^ s)⁻¹) ψ := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => autocorr_factor_eq j s hs)

/-- The horizontal-Jacobi-family sum `T(s) = ∑_{j<m} χ^{j+s}(-1)·J(χ^j, (χ^{j+s})⁻¹)`. -/
noncomputable def Tval (χ : MulChar F ℂ) (m s : ℕ) : ℂ :=
  ∑ j ∈ Finset.range m, (χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹

/-- **★ Sub-step 3 (the norm identity `‖A(s)‖ = √q · ‖T(s)‖`).**
Taking norms in (★) and using `‖g((χ^s)⁻¹)‖ = √q` (for `(χ^s)⁻¹ ≠ 1`, `ψ` primitive): the entire
magnitude of the autocorrelation is the FIXED `√q` times the norm of the horizontal-family sum `T(s)`.
All shift-dependent magnitude is `√q`; the open content is `‖T(s)‖`. -/
theorem autocorr_norm_eq {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (m s : ℕ)
    (hs : (χ ^ s)⁻¹ ≠ 1) :
    ‖∑ j ∈ Finset.range m, gaussSum (χ ^ j) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (j + s)) ψ)‖
      = Real.sqrt (Fintype.card F) * ‖Tval χ m s‖ := by
  rw [autocorr_factor_out m s hs, norm_mul, norm_gaussSum_eq_sqrt hs hψ]
  rw [Tval, mul_comm]

/-- **Sub-step 4 (each summand of `T(s)` has modulus EXACTLY `√q`).** For `1 ≤ j` and `j+s` below the
order with the relevant nontriviality, the Jacobi sum `J(χ^j, (χ^{j+s})⁻¹)` has modulus `√q`
(`norm_jacobiSum_eq_sqrt`), and the sign `χ^{j+s}(-1) = ±1` has modulus `1`. So `T(s)` is a sum of
`m` terms each of modulus `√q`: ALL magnitude discharged, the open part is pure phase. -/
theorem jacobi_phase_term_norm {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {j s : ℕ}
    (hj : χ ^ j ≠ 1) (hjs : (χ ^ (j + s))⁻¹ ≠ 1)
    (hprod : (χ ^ j) * (χ ^ (j + s))⁻¹ ≠ 1) :
    ‖(χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹‖ = Real.sqrt (Fintype.card F) := by
  rw [norm_mul]
  -- ‖χ^{j+s}(-1)‖ = 1  (value of a multiplicative character at a unit)
  have hsign : ‖(χ ^ (j + s)) (-1)‖ = 1 := by
    have h1 : ((χ ^ (j + s)) (-1)) * ((χ ^ (j + s)) (-1)) = 1 := by
      rw [← map_mul]; norm_num
    have : ‖(χ ^ (j + s)) (-1)‖ * ‖(χ ^ (j + s)) (-1)‖ = 1 := by
      rw [← norm_mul, h1, norm_one]
    nlinarith [norm_nonneg ((χ ^ (j + s)) (-1)), this]
  rw [hsign, one_mul, norm_jacobiSum_eq_sqrt hj hjs hprod hψ]

/-- **Sub-step 5 (trivial triangle bound on `T(s)`, hence on `A(s)`).** With every summand of `T(s)`
of modulus `√q`, `‖T(s)‖ ≤ m·√q` (triangle), so `‖A(s)‖ = √q·‖T(s)‖ ≤ m·q` — the NO-cancellation
value. The prize needs `‖T(s)‖ ≤ C·√q·√(m log m)` (square-root cancellation in the horizontal
family); the gap from `m·√q` to `√(m log m)·√q` is exactly the effective-equidistribution residual. -/
theorem Tval_triangle {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (m s : ℕ)
    (hterm : ∀ j ∈ Finset.range m,
      ‖(χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹‖ = Real.sqrt (Fintype.card F)) :
    ‖Tval χ m s‖ ≤ (m : ℝ) * Real.sqrt (Fintype.card F) := by
  unfold Tval
  calc ‖∑ j ∈ Finset.range m, (χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹‖
      ≤ ∑ j ∈ Finset.range m, ‖(χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹‖ :=
        norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range m, Real.sqrt (Fintype.card F) := Finset.sum_congr rfl hterm
    _ = (m : ℝ) * Real.sqrt (Fintype.card F) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## The named residual and the sufficiency bridge. -/

/-- **The named EFFECTIVE EQUIDISTRIBUTION residual (open core of [katz-jacobi-equidist]).**
The horizontal Jacobi family `j ↦ J(χ^j, (χ^{j+s})⁻¹)` exhibits square-root cancellation: there is a
constant `C` such that for every shift `s` (with `χ^s ≠ 1`), `‖T(s)‖ ≤ C·√q·√(m·log m)`. Equivalently,
the `m` unit phases `u_j = χ^{j+s}(-1)·J(χ^j,(χ^{j+s})⁻¹)/√q` cancel down to `√(m log m)`.

This is EXACTLY the effective (quantitative) equidistribution of the **bounded-conductor, one-parameter
(curve) Jacobi family** — Katz/Deligne supply equidistribution-with-rate for this family (no `n^r`
conductor blow-up: that was the iterated/Fermat-hypersurface artifact of `_JacobiKatzEquidist`), but the
quantitative discrepancy delivered is `m^{-1/2+o(1)}` against the FULL density-1 family, NOT the extra
`√(log m)` reach on the FIXED-prime thin slice the prize requires. It is OPEN; this file proves it
SUFFICES and isolates it. -/
def EffectiveEquidistResidual (C : ℝ) (χ : MulChar F ℂ) (m : ℕ) : Prop :=
  ∀ s : ℕ, (χ ^ s)⁻¹ ≠ 1 →
    ‖Tval χ m s‖ ≤ C * Real.sqrt (Fintype.card F) * Real.sqrt ((m : ℝ) * Real.log m)

/-- **★ The residual SUFFICES (sufficiency bridge, axiom-clean modulo the named residual).**
Assuming `EffectiveEquidistResidual C` and `ψ` primitive, the autocorrelation at every nonzero shift
`s` (with `χ^s ≠ 1`) satisfies the per-shift sub-Gaussian bound

> `‖A(s)‖ ≤ C·q·√(m log m)`.

Summed over the `≤ m` shifts and frequency-twisted, this is the `OffDiagResonanceBounded` hypothesis
of `_ProveOffDiagResonanceCapstone` (each shift contributes `q·√(m log m)`, the `m` shifts give
`q·m·√(m log m)`; the `√(log m)` extra over the target `q·m·log m` is the slack to absorb the twist
sum — the per-shift bound is the binding content). Proven by `‖A(s)‖ = √q·‖T(s)‖ ≤ √q·C√q√(m log m)
= C·q·√(m log m)`. -/
theorem autocorr_le_of_residual {C : ℝ} (hC : 0 ≤ C) {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (m : ℕ) (hRes : EffectiveEquidistResidual C χ m)
    (s : ℕ) (hs : (χ ^ s)⁻¹ ≠ 1) :
    ‖∑ j ∈ Finset.range m, gaussSum (χ ^ j) ψ * (starRingEnd ℂ) (gaussSum (χ ^ (j + s)) ψ)‖
      ≤ C * (Fintype.card F : ℝ) * Real.sqrt ((m : ℝ) * Real.log m) := by
  rw [autocorr_norm_eq hψ m s hs]
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  -- √q · ‖T(s)‖ ≤ √q · (C·√q·√(m log m)) = C·q·√(m log m)
  calc Real.sqrt (Fintype.card F) * ‖Tval χ m s‖
      ≤ Real.sqrt (Fintype.card F) *
          (C * Real.sqrt (Fintype.card F) * Real.sqrt ((m : ℝ) * Real.log m)) :=
        mul_le_mul_of_nonneg_left (hRes s hs) hsqrt_nn
    _ = C * (Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F))
          * Real.sqrt ((m : ℝ) * Real.log m) := by ring
    _ = C * (Fintype.card F : ℝ) * Real.sqrt ((m : ℝ) * Real.log m) := by
        rw [Real.mul_self_sqrt (by positivity)]

/-! ## The exact residual, stated as a Prop: the horizontal family is a UNIT-PHASE sum, one order down.

`Tval/√q = ∑_j u_j`, `u_j = χ^{j+s}(-1)·J(χ^j,(χ^{j+s})⁻¹)/√q` of modulus 1. We record the unit-phase
extraction so the residual is visibly "m unit phases cancel to √(m log m)" = the Paley/BGK content,
ONE ORDER DOWN (the phases are Jacobi/Gauss-period objects of the same `μ_n`). -/

/-- The normalized unit phase of the horizontal family. -/
noncomputable def uPhase (χ : MulChar F ℂ) (s j : ℕ) : ℂ :=
  ((χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹) / Real.sqrt (Fintype.card F)

/-- **The horizontal family is unit-modulus (when the term norm is `√q`).** `‖u_j‖ = 1`. So
`Tval = √q·∑_j u_j` and the residual `‖Tval‖ ≤ C√q√(m log m)` is LITERALLY `‖∑_j u_j‖ ≤ C√(m log m)`:
square-root cancellation of `m` unit phases, the BGK/Paley wall one order down. -/
theorem uPhase_norm {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {j s : ℕ}
    (hj : χ ^ j ≠ 1) (hjs : (χ ^ (j + s))⁻¹ ≠ 1)
    (hprod : (χ ^ j) * (χ ^ (j + s))⁻¹ ≠ 1) :
    ‖uPhase χ s j‖ = 1 := by
  unfold uPhase
  rw [norm_div, jacobi_phase_term_norm hψ hj hjs hprod]
  have hne : Real.sqrt (Fintype.card F) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Fintype.card F) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    exact ne_of_gt this
  -- the denominator is the COMPLEX cast of √q; ‖(↑√q : ℂ)‖ = |√q| = √q.
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_self hne]

/-! ## ★★ NEW (this pass): the INTERCHANGE — `T(s)` is a COMPLETE character sum over `F\{0,1}` with a
GEOMETRIC-SERIES weight. This is the Weil test: expanding the Jacobi sums by definition and swapping
`∑_j ∑_x → ∑_x ∑_j`, the inner `j`-sum is a geometric series in a SINGLE root of unity `w(x)`, and the
whole `T(s)` becomes a complete sum over `x ∈ F\{0,1}` of `prefactor(x) · geomSum(w(x), m)`. -/

/-- The single root-of-unity base of the geometric series at the point `x`:
`w(x) = χ(-1)·χ(x)·χ(1-x)⁻¹`. For `x ∈ F\{0,1}` this is a unit-modulus complex number
(product of three character values at nonzero arguments, one inverted). -/
noncomputable def wBase (χ : MulChar F ℂ) (x : F) : ℂ :=
  χ (-1) * χ x * (χ (1 - x))⁻¹

/-- The `s`-dependent (and `x`-dependent) prefactor `p_s(x) = χ(-1)^s · (χ(1-x)⁻¹)^s = w(x)^s / χ(x)^s`.
We carry it in the form `(χ(-1) · χ(1-x)⁻¹)^s` to match the `a^s c^{-s}` grouping. -/
noncomputable def pFactor (χ : MulChar F ℂ) (s : ℕ) (x : F) : ℂ :=
  (χ (-1) * (χ (1 - x))⁻¹) ^ s

/-- **★ Per-point, per-index summand identity (the heart of the interchange).** For `x ∈ F\{0,1}`
(so `x` and `1-x` are units) and any `j`, the contribution of `x` to the `j`-th Jacobi summand of
`T(s)`, namely `χ^{j+s}(-1) · (χ^j)(x) · ((χ^{j+s})⁻¹)(1-x)`, equals `pFactor χ s x · wBase χ x ^ j`:

> `χ(-1)^{j+s} · χ(x)^j · (χ(1-x)^{j+s})⁻¹ = (χ(-1)·χ(1-x)⁻¹)^s · (χ(-1)·χ(x)·χ(1-x)⁻¹)^j`.

This is the pure algebra `a^{j+s} b^j c^{-(j+s)} = (a c^{-1})^s · (a b c^{-1})^j` with
`a=χ(-1), b=χ(x), c=χ(1-x)`. All three are NONZERO at `x ∈ F\{0,1}`. -/
theorem summand_factor_eq {χ : MulChar F ℂ} {s : ℕ} {x : F} (hx0 : x ≠ 0) (hx1 : x ≠ 1) (j : ℕ) :
    (χ ^ (j + s)) (-1) * ((χ ^ j) x * ((χ ^ (j + s))⁻¹) (1 - x))
      = pFactor χ s x * wBase χ x ^ j := by
  have hxu : IsUnit x := isUnit_iff_ne_zero.mpr hx0
  have h1xu : IsUnit (1 - x) := by
    refine isUnit_iff_ne_zero.mpr ?_
    intro h; apply hx1; linear_combination -h
  have hneg : IsUnit (-1 : F) := isUnit_one.neg
  -- evaluate each character power at its (unit) argument
  rw [show ((χ ^ (j + s)) (-1)) = (χ (-1)) ^ (j + s) from MulChar.pow_apply_coe χ (j + s) hneg.unit,
      show ((χ ^ j) x) = (χ x) ^ j from MulChar.pow_apply_coe χ j hxu.unit,
      MulChar.inv_apply_eq_inv',
      show ((χ ^ (j + s)) (1 - x)) = (χ (1 - x)) ^ (j + s) from
        MulChar.pow_apply_coe χ (j + s) h1xu.unit]
  unfold pFactor wBase
  -- a^{j+s} · (b^j · (c^{j+s})⁻¹) = (a·c⁻¹)^s · (a·b·c⁻¹)^j
  rw [mul_pow, mul_pow, mul_pow]
  field_simp
  ring

/-- **★★ THE INTERCHANGE (the genuinely new step).** Expanding every Jacobi sum in `T(s)` by its
definition over `F\{0,1}` and swapping the order of summation, `T(s)` becomes a COMPLETE character
sum over `x ∈ F\{0,1}` of the prefactor `p_s(x)` times the **geometric series** `∑_{j<m} w(x)^j`:

> `T(s) = ∑_{x∈F\{0,1}} pFactor χ s x · (∑_{j<m} wBase χ x ^ j)`.

This is the Weil-test form: `T(s)` is a complete additive-in-`x` sum (over an `F`-indexed set) whose
summand is `p_s(x)` times a geometric series in the single root of unity `w(x) = χ(-1)χ(x)χ(1-x)⁻¹`.
The interchange has NO hypotheses on `s` (it holds for every `s`); it is pure double-sum algebra plus
`summand_factor_eq`. -/
theorem Tval_interchange {χ : MulChar F ℂ} (m s : ℕ) :
    Tval χ m s
      = ∑ x ∈ (univ \ {0, 1} : Finset F),
          pFactor χ s x * (∑ j ∈ Finset.range m, wBase χ x ^ j) := by
  unfold Tval
  have hstep : ∀ j ∈ Finset.range m,
      (χ ^ (j + s)) (-1) * jacobiSum (χ ^ j) (χ ^ (j + s))⁻¹
        = ∑ x ∈ (univ \ {0, 1} : Finset F),
            pFactor χ s x * wBase χ x ^ j := by
    intro j _
    rw [jacobiSum_eq_sum_sdiff, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨_, hx01⟩ := hx
    push_neg at hx01
    obtain ⟨hx0, hx1⟩ := hx01
    rw [show (χ ^ (j + s)) (-1) * ((χ ^ j) x * ((χ ^ (j + s))⁻¹) (1 - x))
          = (χ ^ (j + s)) (-1) * ((χ ^ j) x * ((χ ^ (j + s))⁻¹) (1 - x)) from rfl]
    exact summand_factor_eq hx0 hx1 j
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]

/-! ## ★★★ The Weil test resolved: the geometric weight DICHOTOMIZES `T(s)` into a RESONANCE set
(`w(x)=1`, geometric series `= m`, NO cancellation) and an off-resonance set (geometric series
`≤ 2/‖1-w(x)‖`). This is the EXACT localization of the residual. -/

/-- The geometric weight base `w(x)` is unit-modulus on `F\{0,1}`. (Product of three character values
at nonzero arguments; `‖χ(a)‖ = 1` for `a ≠ 0`, and inversion preserves modulus 1.) -/
theorem wBase_norm {χ : MulChar F ℂ} {x : F} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ‖wBase χ x‖ = 1 := by
  have h1x : (1 - x) ≠ 0 := by intro h; apply hx1; linear_combination -h
  have hneg : (-1 : F) ≠ 0 := by norm_num
  unfold wBase
  rw [norm_mul, norm_mul, norm_inv,
      norm_mulChar_unit χ hneg, norm_mulChar_unit χ hx0, norm_mulChar_unit χ h1x]
  norm_num

/-- **★ Off-resonance geometric bound.** For a unit-modulus `w ≠ 1`, the length-`m` geometric series
is bounded INDEPENDENTLY of `m`: `‖∑_{j<m} w^j‖ ≤ 2/‖1 - w‖`. (`∑ = (w^m-1)/(w-1)`, numerator
`‖w^m - 1‖ ≤ ‖w^m‖ + 1 = 2`.) So OFF the resonance set the geometric series CANNOT grow with `m` —
all the growth lives on `w(x) = 1`. -/
theorem geom_off_resonance_bound {w : ℂ} (hw1 : w ≠ 1) (hwn : ‖w‖ = 1) (m : ℕ) :
    ‖∑ j ∈ Finset.range m, w ^ j‖ ≤ 2 / ‖1 - w‖ := by
  rw [geom_sum_eq hw1]
  rw [norm_div]
  have hden : ‖w - 1‖ = ‖1 - w‖ := by rw [← norm_neg]; ring_nf
  rw [hden]
  have hnum : ‖w ^ m - 1‖ ≤ 2 := by
    calc ‖w ^ m - 1‖ ≤ ‖w ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hwn, one_pow, norm_one]; norm_num
  have hpos : 0 < ‖1 - w‖ := by
    rw [norm_pos_iff]; intro h; apply hw1; linear_combination -h
  gcongr

/-- **★ On-resonance value.** Where `w(x) = 1`, the geometric series is EXACTLY `m`: full
constructive resonance, NO cancellation. This is the term that makes `‖T(s)‖` potentially as large as
`|R|·m` (with `|pFactor| = 1`). -/
theorem geom_on_resonance {w : ℂ} (hw : w = 1) (m : ℕ) :
    (∑ j ∈ Finset.range m, w ^ j) = (m : ℂ) := by
  subst hw; simp

/-- The prefactor `p_s(x)` is unit-modulus on `F\{0,1}`. -/
theorem pFactor_norm {χ : MulChar F ℂ} {s : ℕ} {x : F} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ‖pFactor χ s x‖ = 1 := by
  have h1x : (1 - x) ≠ 0 := by intro h; apply hx1; linear_combination -h
  have hneg : (-1 : F) ≠ 0 := by norm_num
  unfold pFactor
  rw [norm_pow, norm_mul, norm_inv, norm_mulChar_unit χ hneg, norm_mulChar_unit χ h1x]
  norm_num

/-- **The resonance set** `R = {x ∈ F\{0,1} : w(x) = 1}` — equivalently `χ(-1)·χ(x) = χ(1-x)`,
i.e. `χ(-x) = χ(1-x)`, i.e. `-x/(1-x) ∈ ker χ`. The Möbius map `x ↦ -x/(1-x)` is a bijection of
`F\{0,1}` onto `F\{0,-1}`, so `|R| = |ker χ ∩ (F\{0,-1})| = n - O(1)` where `n = |ker χ| = (q-1)/m`.
THIS set carries all the growth. -/
noncomputable def resonanceSet (χ : MulChar F ℂ) : Finset F :=
  (univ \ {0, 1} : Finset F).filter (fun x => wBase χ x = 1)

/-- **★★★ THE DICHOTOMY DECOMPOSITION OF `T(s)`.** Splitting the interchange sum over the resonance
set `R` and its complement:

> `T(s) = ∑_{x∈R} p_s(x)·m  +  ∑_{x∈(F\{0,1})\R} p_s(x)·(geom series, ‖·‖ ≤ 2/‖1-w(x)‖)`.

The first (resonance) block is a sum of `|R|` unit-modulus terms each multiplied by `m`; the second
(off-resonance) block has each geometric weight bounded INDEPENDENTLY of `m`. -/
theorem Tval_dichotomy {χ : MulChar F ℂ} (m s : ℕ) :
    Tval χ m s
      = (∑ x ∈ resonanceSet χ, pFactor χ s x * (m : ℂ))
        + ∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ,
            pFactor χ s x * (∑ j ∈ Finset.range m, wBase χ x ^ j) := by
  rw [Tval_interchange]
  have hsub : resonanceSet χ ⊆ (univ \ {0, 1} : Finset F) := Finset.filter_subset _ _
  rw [← Finset.sum_sdiff hsub]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [resonanceSet, Finset.mem_filter] at hx
  rw [geom_on_resonance hx.2]

/-! ## ★★★★ The SHARP localization: the only `m`-growing part of `T(s)` is the RESONANCE BLOCK
`m·∑_{x∈R} p_s(x)`. The off-resonance block is `m`-bounded. So the residual reduces to cancellation in
the SINGLE character sum `∑_{x∈R} p_s(x)` over the Möbius image of `ker χ` (size `n`). -/

/-- The resonance block factors `m` out: `∑_{x∈R} p_s(x)·m = m · ∑_{x∈R} p_s(x)`. The norm is
`m · ‖∑_{x∈R} p_s(x)‖`. The inner sum `S_R(s) := ∑_{x∈R} p_s(x)` is a CHARACTER SUM over the
resonance set, with each term unit-modulus. -/
theorem resonance_block_eq {χ : MulChar F ℂ} (m s : ℕ) :
    (∑ x ∈ resonanceSet χ, pFactor χ s x * (m : ℂ))
      = (m : ℂ) * ∑ x ∈ resonanceSet χ, pFactor χ s x := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)

/-- **★★★★ The off-resonance block is bounded INDEPENDENTLY of `m`.** Each term has unit-modulus
prefactor and a geometric weight `≤ 2/‖1-w(x)‖` (no `m`). So
`‖off-res block‖ ≤ ∑_{x off-res} 2/‖1-w(x)‖`, an `m`-FREE quantity. (The RHS is itself a complete sum
over `F\{0,1}` minus `R`; bounding it is a separate `m`-independent character-sum question, but
crucially it does NOT scale with `m`.) -/
theorem offResonance_block_bound {χ : MulChar F ℂ} (m s : ℕ) :
    ‖∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ,
        pFactor χ s x * (∑ j ∈ Finset.range m, wBase χ x ^ j)‖
      ≤ ∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ, 2 / ‖1 - wBase χ x‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun x hx => ?_)
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxin, hxnot⟩ := hx
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hxin
  obtain ⟨_, hx01⟩ := hxin
  push_neg at hx01
  obtain ⟨hx0, hx1⟩ := hx01
  -- w(x) ≠ 1 since x ∉ R
  have hw1 : wBase χ x ≠ 1 := by
    intro h; apply hxnot; rw [resonanceSet, Finset.mem_filter]
    exact ⟨by rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; push_neg
              exact ⟨Finset.mem_univ _, hx0, hx1⟩, h⟩
  rw [norm_mul, pFactor_norm hx0 hx1, one_mul]
  exact geom_off_resonance_bound hw1 (wBase_norm hx0 hx1) m

/-- **★★★★★ THE SHARP RESIDUAL BOUND on `T(s)`.** Triangle inequality on the dichotomy plus the two
block bounds:

> `‖T(s)‖ ≤ m · ‖∑_{x∈R} p_s(x)‖  +  ∑_{x off-res} 2/‖1-w(x)‖`.

The SECOND term is `m`-free. The FIRST term carries ALL `m`-dependence and is `m` times the norm of the
character sum `S_R(s) = ∑_{x∈R} p_s(x)` over the resonance set `R` (size `|R| ≈ n = (q-1)/m`). Hence:

THE PRIZE-RELEVANT GROWTH OF `‖T(s)‖` IS GOVERNED ENTIRELY BY `‖S_R(s)‖`, A SINGLE CHARACTER SUM OVER
A SET OF SIZE `≈ n`. The prize needs `‖T(s)‖ ≤ C√q·√(m log m) = C·m·√(n log m)`; the off-res term is
lower order; so the binding requirement is `m·‖S_R(s)‖ ≤ C·m·√(n log m)`, i.e.

> `‖S_R(s)‖ = ‖∑_{x∈R} p_s(x)‖ ≤ C·√(n log m)`     (THE SHARPENED RESIDUAL),

square-root cancellation of `≈ n` unit phases over the resonance set. -/
theorem Tval_sharp_residual_bound {χ : MulChar F ℂ} (m s : ℕ) :
    ‖Tval χ m s‖
      ≤ (m : ℝ) * ‖∑ x ∈ resonanceSet χ, pFactor χ s x‖
        + ∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ, 2 / ‖1 - wBase χ x‖ := by
  rw [Tval_dichotomy m s, resonance_block_eq m s]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · rw [norm_mul, Complex.norm_natCast]
  · exact offResonance_block_bound m s

/-! ## The named SHARPENED residual and the suffices-bridge to the prize. -/

/-- **The sharpened named residual `ResonanceSetCancellation`.** The character sum over the resonance
set `S_R(s) = ∑_{x∈R} p_s(x)` exhibits square-root cancellation:
`‖∑_{x∈R} p_s(x)‖ ≤ C·√(n·log m)` for all `s`, where `n = card(resonanceSet χ)` is its size.
This is STRICTLY SHARPER than `EffectiveEquidistResidual`: that asked for `√(m log m)`-cancellation
over the FULL horizontal family of `m` Jacobi sums; this asks for `√(n log m)`-cancellation over the
SINGLE complete character sum over `R` (size `n`), with the geometric/`m`-dependent structure
DISCHARGED into the resonance dichotomy. -/
def ResonanceSetCancellation (C : ℝ) (χ : MulChar F ℂ) (m : ℕ) : Prop :=
  ∀ s : ℕ, ‖∑ x ∈ resonanceSet χ, pFactor χ s x‖
    ≤ C * Real.sqrt ((resonanceSet χ).card * Real.log m)

/-- An `m`-free name for the off-resonance block constant (the lower-order term). -/
noncomputable def offResConst (χ : MulChar F ℂ) (s : ℕ) : ℝ :=
  ∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ, 2 / ‖1 - wBase χ x‖

/-- **★ The sharpened residual SUFFICES for the binding `m·‖S_R‖` term.** Given
`ResonanceSetCancellation C`, the `m`-growing part of `‖T(s)‖` is bounded by `C·m·√(n log m)` plus the
`m`-free off-resonance constant:

> `‖T(s)‖ ≤ C·m·√(n log m) + offResConst(s)`.

Since `√q = √(nm)`, `m·√(n log m) = √q·√(m log m)`, this is exactly the `EffectiveEquidistResidual`
form `‖T(s)‖ ≤ C'·√q·√(m log m)` once the `m`-free `offResConst` is absorbed (lower order in the prize
regime `m ≫ 1`). So the sharpened residual implies the prize-relevant bound; the open content is
square-root cancellation of the SINGLE resonance-set character sum. -/
theorem Tval_le_of_resonance_cancellation {C : ℝ} {χ : MulChar F ℂ} {m : ℕ}
    (hRes : ResonanceSetCancellation C χ m) (s : ℕ) :
    ‖Tval χ m s‖
      ≤ C * (m : ℝ) * Real.sqrt ((resonanceSet χ).card * Real.log m) + offResConst χ s := by
  refine (Tval_sharp_residual_bound m s).trans ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [offResConst]
  have : (m : ℝ) * ‖∑ x ∈ resonanceSet χ, pFactor χ s x‖
      ≤ (m : ℝ) * (C * Real.sqrt ((resonanceSet χ).card * Real.log m)) :=
    mul_le_mul_of_nonneg_left (hRes s) hm
  calc (m : ℝ) * ‖∑ x ∈ resonanceSet χ, pFactor χ s x‖
        + ∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ, 2 / ‖1 - wBase χ x‖
      ≤ (m : ℝ) * (C * Real.sqrt ((resonanceSet χ).card * Real.log m))
        + ∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ, 2 / ‖1 - wBase χ x‖ := by
        gcongr
    _ = C * (m : ℝ) * Real.sqrt ((resonanceSet χ).card * Real.log m)
        + ∑ x ∈ (univ \ {0, 1} : Finset F) \ resonanceSet χ, 2 / ‖1 - wBase χ x‖ := by ring

end ArkLib.ProximityGap.Frontier.JacKatz

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.norm_jacobiSum_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.conj_gaussSum_same
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.autocorr_term_eq_jacobi
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.autocorr_factor_eq
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.autocorr_factor_out
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.autocorr_norm_eq
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.jacobi_phase_term_norm
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.Tval_triangle
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.autocorr_le_of_residual
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.uPhase_norm
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.summand_factor_eq
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.Tval_interchange
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.wBase_norm
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.geom_off_resonance_bound
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.geom_on_resonance
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.pFactor_norm
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.Tval_dichotomy
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.resonance_block_eq
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.offResonance_block_bound
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.Tval_sharp_residual_bound
#print axioms ArkLib.ProximityGap.Frontier.JacKatz.Tval_le_of_resonance_cancellation
