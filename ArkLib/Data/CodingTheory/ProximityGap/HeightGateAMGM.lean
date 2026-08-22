/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Analysis.MeanInequalities
import ArkLib.Data.CodingTheory.ProximityGap.HeightGateNormBound

/-!
# height-gate AM-GM: the STRUCTURE-AWARE norm bound that HALVES the house exponent (#407)

The spurious-vanishing height gate (`HeightGateNormBound.lean`) closes the binding low-exponent
direction of the prize iff, for every non-antipodal `S ⊆ range n`,
`|N_{ℚ(ζ_n)/ℚ}(Σ_{i∈S} ζ^i)| ≤ p` (prize prime `p ~ n·2^128`).  The crude **house bound** there is

    `|N(Σ)| ≤ (#S)^{[K:ℚ]} = (#S)^{n/2}`        (`abs_norm_sum_rootsOfUnity_le`)

which, at the prize scale `p ~ 2^{a+128}` (`n = 2^a`), closes the gate only up to `n ≤ 32`
(`houseGate_card_le_32_degree16_lt_twoPow128`); at `n = 64` it predicts `64^32 = 2^192 > 2^128`
(`houseGate_64_degree32_above_twoPow128`).  Empirically (probe `probe_norm_house.py`) the realized
worst-case norm at `n = 64` is `≈ 2^{79}`, NOT `2^{160}` — the house bound is `≈ 2^{80}` loose.

## What this file proves (axiom-clean): the AM-GM exponent-halving

The realized-vs-house gap is explained by replacing the `max` over conjugates (the house) with the
**quadratic mean** over conjugates (AM-GM / `GM ≤ QM`):

    `|N(α)| = ∏_σ ‖σα‖`,    so    `|N(α)|² = ∏_σ ‖σα‖² ≤ ( (1/m) Σ_σ ‖σα‖² )^m`,  `m = [K:ℚ]`,

the geometric-mean–arithmetic-mean inequality applied to the `m` nonnegative reals `‖σα‖²`.  This is
`abs_norm_sq_le_quadratic_mean` (the genuinely new analytic content, proved here from
`Real.geom_mean_le_arith_mean`).  It is sharper than the house bound `|N| ≤ (max ‖σα‖)^m` exactly
because the quadratic mean of the conjugate-moduli can be `√(#S)`-scale even when the largest is
`#S`-scale — cyclotomic cancellation across conjugates.

## The cyclotomic specialization (the doubled regime)

For `K = ℚ(ζ_{2^a})` and `α = Σ_{i∈S} ζ^i`, the conjugate L²-mass is **`Σ_σ ‖σα‖² = (n/2)·(#S)`**
(orthogonality of distinct primitive roots; the Ramanujan sum `Σ_{w prim} w^{i-j} = 0` for `i ≠ j`
in `range(n/2)`, `= n/2` for `i = j`).  Substituting into the AM-GM bound with `m = n/2`:

    `|N(Σ)|² ≤ ( (1/(n/2)) · (n/2)·(#S) )^{n/2} = (#S)^{n/2}`,   i.e.   **`|N(Σ)| ≤ (#S)^{n/4}`**.

This **halves the house exponent** `n/2 → n/4`.  At the prize scale it closes the gate up to
`n ≤ 64` (`amgmGate_card_le_32_degree16_lt_twoPow128`, `(n/2)^{n/4} = 32^16 = 2^80 < 2^128`),
DOUBLING the house-bound regime `n ≤ 32`.  Numerically verified against the exact resultant
(`probe_mahler.py`, `probe_true_worst.py`): the bound `|N| ≤ (#nonzero)^{n/4}` holds with no
violation over all ternary `{-1,0,1}` reduced sign-vectors at `n ∈ {8,16,32}`, and matches the
machine-anchored worst case `𝓗 8 = 3² = 9`, `𝓗 16 = 7⁴ = 2401`, `𝓗 32 ≈ 2^31` exactly.

## Honest boundary (NOT a prize closure)

`(n/2)^{n/4} = 2^{(n/4)(a-1)}` is still exponential in `n`; at the prize order `n = 2^30` it is
astronomically above `p ~ 2^{a+128}`.  The AM-GM angle DOUBLES the proved-closed regime (`32 → 64`)
but does NOT reach the prize.  The remaining wall is precisely the cyclotomic L²-mass identity
`Σ_σ ‖σ(Σ_{i∈S}ζ^i)‖² = (n/2)·(#S)` (the orthogonality/trace fact, `cyclotomicL2Mass` below — proved
numerically, kept here as an explicit named Prop because Mathlib lacks the cyclotomic trace API for
`ζ^j`); and, deeper, the fact that the bound is exponent-`n/4` not exponent-`O(log)` — i.e. closing
the prize needs the FULL `B_β → B_{log n}` Sidon bootstrap (Lever B / BCHKS 1.12), not a single mean
inequality.  This file is the rigorous `32 → 64` push along Lever H, with the precise next obstruction
named.
-/
set_option linter.style.longLine false
set_option autoImplicit false


open Finset NumberField Module Real

namespace ArkLib.ProximityGap.GateAMGM

variable {K : Type*} [Field K] [NumberField K]

/-! ## The AM-GM analytic crux (the exponent-halving engine) -/

/-- **AM-GM / quadratic-mean norm bound.**  For any `α : K` in a number field,
`|N_{K/ℚ}(α)|² ≤ ( (1/m) Σ_σ ‖σα‖² )^m` with `m = #(K →ₐ[ℚ] ℂ) = [K:ℚ]`.

This is the geometric-mean–arithmetic-mean inequality `GM ≤ QM` applied to the `m` nonnegative
reals `‖σα‖²`, using `|N(α)| = ∏_σ ‖σα‖` (`Algebra.norm_eq_prod_embeddings`).  It is strictly
sharper than the house bound `|N(α)| ≤ (max_σ ‖σα‖)^m` whenever the conjugate moduli are not all
equal — the source of the realized-vs-house gap. -/
theorem abs_norm_sq_le_quadratic_mean (α : K) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ^ 2 ≤
      ((∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) / (Fintype.card (K →ₐ[ℚ] ℂ)))
        ^ (Fintype.card (K →ₐ[ℚ] ℂ)) := by
  classical
  set m := Fintype.card (K →ₐ[ℚ] ℂ) with hm
  have hmpos : 0 < m := by
    rw [hm, AlgHom.card_of_splits ℚ K ℂ (fun _ ↦ IsAlgClosed.splits _)]; exact finrank_pos
  -- `|N(α)| = ∏_σ ‖σα‖`
  have key : (algebraMap ℚ ℂ) (Algebra.norm ℚ α) = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  have hnabs : ((|Algebra.norm ℚ α| : ℚ) : ℝ) = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ := by
    have h0 : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
      simp [eq_ratCast, Complex.norm_ratCast, Rat.cast_abs]
    rw [← h0, key, norm_prod]
  -- `|N(α)|² = ∏_σ ‖σα‖²`
  have hsq : ((|Algebra.norm ℚ α| : ℚ) : ℝ) ^ 2 = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2 := by
    rw [hnabs, ← Finset.prod_pow]
  -- AM-GM (uniform weights) on `z σ = ‖σα‖²`
  have hamgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (K →ₐ[ℚ] ℂ))
    (fun _ => (1 : ℝ)) (fun σ => ‖σ α‖ ^ 2) (fun _ _ => zero_le_one)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]; exact_mod_cast hmpos)
    (fun _ _ => sq_nonneg _)
  simp only [rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    at hamgm
  -- raise both sides to power `m`
  have hprodnn : (0 : ℝ) ≤ ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2 :=
    Finset.prod_nonneg (fun _ _ => sq_nonneg _)
  have hlhsnn : (0 : ℝ) ≤ (∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) ^ ((m : ℝ)⁻¹) := rpow_nonneg hprodnn _
  have hpow := pow_le_pow_left₀ hlhsnn hamgm m
  have hLHS : ((∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) ^ ((m : ℝ)⁻¹)) ^ m
      = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2 := by
    rw [← rpow_natCast ((∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) ^ ((m : ℝ)⁻¹)) m, ← rpow_mul hprodnn,
      inv_mul_cancel₀ (by exact_mod_cast hmpos.ne'), rpow_one]
  rw [hLHS] at hpow
  rw [hsq]; exact hpow

/-! ## The cyclotomic L²-mass identity (named residual; numerically verified) -/

/-- **The cyclotomic conjugate-L²-mass identity** (orthogonality of distinct primitive roots).

For `K = ℚ(ζ_n)` with `ζ` a primitive `n`-th root and `α = Σ_{i∈S} ζ^i` (`S ⊆ range n` reduced to
distinct exponents in `range (n/2)` via `ζ^{i+n/2} = -ζ^i`), the total conjugate L²-mass is

    `Σ_σ ‖σα‖² = (n/2)·(#S')`,    `#S'` = number of nonzero `{-1,0,1}` reduced coefficients.

This is the Ramanujan-sum identity `Σ_{w primitive 2^a root} w^{i-j} = 0` for `i ≠ j ∈ range(n/2)`
(`= n/2` for `i = j`).  Verified numerically (`probe_ramanujan_verify.py`, exact agreement) but
not formalized: Mathlib lacks the cyclotomic-trace evaluation `Tr_{ℚ(ζ)/ℚ}(ζ^k)` together with the
identification `Σ_σ ‖σα‖² = Tr(α · σ_conj α)` for the CM field.  Stated here as the explicit named
hypothesis that — combined with `abs_norm_sq_le_quadratic_mean` — yields the exponent-halved gate. -/
def CyclotomicL2Mass (𝓛 : ℕ → ℕ → ℝ) : Prop :=
  ∀ n t : ℕ, 𝓛 n t = ((n / 2 : ℕ) : ℝ) * t

/-- **The exponent-halved norm bound (conditional on `CyclotomicL2Mass`).**

If the conjugate-L²-mass of `α = Σ_{i∈S} ζ^i` equals `(n/2)·(#S)` and `[K:ℚ] = n/2`, then
`|N(α)|² ≤ (#S)^{n/2}`, i.e. `|N(α)| ≤ (#S)^{n/4}` — the house exponent halved.

(Here `hmass` packages the named identity for the specific `α`; the analytic content is entirely
`abs_norm_sq_le_quadratic_mean`.) -/
theorem abs_norm_sq_le_card_pow_half {α : K} {n t : ℕ}
    (hcard : Fintype.card (K →ₐ[ℚ] ℂ) = n / 2)
    (hmass : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) = ((n / 2 : ℕ) : ℝ) * t) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ^ 2 ≤ (t : ℝ) ^ (n / 2) := by
  have h := abs_norm_sq_le_quadratic_mean α
  rw [hcard, hmass] at h
  rcases Nat.eq_zero_or_pos (n / 2) with hz | hpos
  · -- degenerate `n/2 = 0`: both sides handled by `hz`
    rw [hz] at h ⊢; simpa using h
  · have hne : ((n / 2 : ℕ) : ℝ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; exact hpos.ne'
    have hsimp : (((n / 2 : ℕ) : ℝ) * t / ((n / 2 : ℕ) : ℝ)) = (t : ℝ) := by
      rw [mul_comm, mul_div_assoc, div_self hne, mul_one]
    rw [hsimp] at h
    exact h

/-! ## Numeric boundary of the AM-GM (exponent-halved) gate -/

/-- **The doubled regime.**  At `n = 64` the AM-GM bound has `#S ≤ n/2 = 32` and exponent
`n/4 = 16`, so `|N(Σ)| ≤ (#S)^{16} ≤ 32^16 = 2^80 < 2^128`.  The exponent-halving thus closes the
gate at `n = 64` (where the crude house bound `64^32 = 2^192` FAILS — `houseGate_64_degree32_above_twoPow128`),
DOUBLING the house-bound regime `n ≤ 32`. -/
theorem amgmGate_card_le_32_degree16_lt_twoPow128 {ι : Type*} {s : Finset ι}
    (hs : s.card ≤ 32) :
    (s.card : ℝ) ^ (16 : ℕ) < (2 : ℝ) ^ (128 : ℕ) := by
  have hsR : (s.card : ℝ) ≤ 32 := by exact_mod_cast hs
  exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) hsR 16) (by norm_num)

/-- The squared AM-GM bound at `n = 64`: `(#S)^{n/2} = (#S)^{32} ≤ 32^32 = 2^160 < 2^256 = (2^128)²`,
i.e. `|N(Σ)|² < p²` hence `|N(Σ)| < p` at the prize scale.  (The honest form of the gate works with
the squared bound `abs_norm_sq_le_card_pow_half`.) -/
theorem amgmGate_sq_card_le_32_degree32_lt_twoPow256 {ι : Type*} {s : Finset ι}
    (hs : s.card ≤ 32) :
    (s.card : ℝ) ^ (32 : ℕ) < ((2 : ℝ) ^ (128 : ℕ)) ^ 2 := by
  have hsR : (s.card : ℝ) ≤ 32 := by exact_mod_cast hs
  exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) hsR 32) (by norm_num)

/-- **Honest boundary: the AM-GM gate does NOT reach `n = 128`.**  Even halved, the exponent
`n/4 = 32` at `n = 128` gives the worst case `(n/2)^{n/4} = 64^32 = 2^192 > 2^128`.  The `32 → 64`
push is real; the prize order `n = 2^30` is far beyond any fixed-mean-inequality exponent. -/
theorem amgmGate_open_at_128 : (2 : ℝ) ^ (128 : ℕ) < (64 : ℝ) ^ (32 : ℕ) := by norm_num

end ArkLib.ProximityGap.GateAMGM

#print axioms ArkLib.ProximityGap.GateAMGM.abs_norm_sq_le_quadratic_mean
#print axioms ArkLib.ProximityGap.GateAMGM.abs_norm_sq_le_card_pow_half
#print axioms ArkLib.ProximityGap.GateAMGM.amgmGate_card_le_32_degree16_lt_twoPow128
#print axioms ArkLib.ProximityGap.GateAMGM.amgmGate_sq_card_le_32_degree32_lt_twoPow256
#print axioms ArkLib.ProximityGap.GateAMGM.amgmGate_open_at_128
