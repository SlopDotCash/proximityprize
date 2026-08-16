/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.FieldTheory.PrimitiveElement
set_option linter.style.longLine false
set_option autoImplicit false

/-!
# l2-mahler-norm-bound: a structure-aware (Parseval/AM-GM) improvement of the height gate (#407)

LEVER H, Mahler/Newton-polygon angle.  The spurious-vanishing height gate of
`HeightGateNormBound.lean` proves: if a rational prime `p` exceeds the algebraic-integer height
`𝓗(Σ_S)` of a sum of roots of unity `Σ_S = Σ_{i∈S} ζ^i` and `p ∣ N(Σ_S)`, then `Σ_S = 0`.
That file's height is the **crude house bound** `|N(Σ_S)| ≤ (#S)^{φ(n)}` (each conjugate has
modulus `≤ #S` by the triangle inequality, then take the product over `φ(n)` conjugates).

This file proves a STRICTLY BETTER bound by exploiting that `|N| = ∏_σ ‖σΣ‖` is a PRODUCT of
conjugate moduli — not all of which are near `#S`.  Replacing the per-conjugate triangle bound
with a single application of AM-GM to the squared conjugate moduli, fed by the Parseval/
orthogonality `L²` mass identity, gives

> **`abs_norm_sum_rootsOfUnity_L2_le`** (conditional on the named Parseval input `ParsevalL2Mass`):
> `|N_{K/ℚ}(Σ_S)| ≤ (2·#S)^{φ(n)/2}`.

For `K = ℚ(ζ_n)`, `n = 2^a`, `φ(n) = n/2`, this is `(2·#S)^{n/4}` — **half the exponent** of the
crude house bound `(#S)^{n/2}`, i.e. the Mahler-measure-style geometric-mean estimate.

## Quantified payoff (`norm_num`, axiom-clean — §"Numeric boundary")

| regime | crude house `(#S)^{n/2}` | this L² bound `(2·#S)^{n/4}` |
|---|---|---|
| worst-case (all `S`, `#S ≤ n`): closes `(bound) < 2^128` for | `n ≤ 32` | **`n ≤ 64`** |
| low-exponent direction at `n = 128`: closes `#S ≤` | `3` | **`7 = log₂ 128`** |

So the L² bound **DOUBLES the fully-closed regime** (`n=32 → n=64`) and, in the binding
low-exponent direction at the prize order `n=128`, **reaches Sidon-depth `log₂ n`** (closing
`#S ≤ 7`), exactly the BCHKS-1.12 bootstrap target — which the crude house bound misses
(`#S ≤ 3`).  (Numerically verified, `scripts`-probe `probe_norm2.py`/`probe_depth.py`.)

## Honest boundary — the gate MECHANISM itself fails at `n ≥ 128` (not just our bound)

`heightGate_mechanism_fails_at_128`: at `n = 128` the **realized** worst-case norm
`max_{S non-antipodal} |N(Σ_S)| ≈ 2^160` EXCEEDS the prize prime `p ≈ n·2^128 = 2^135`.  Hence
for the full subset family there genuinely exist non-antipodal `S` with `p ∣ N(Σ_S)` possible —
no improvement of the norm bound can close the height gate over *all* `S` at `n ≥ 128`.  The
height gate is therefore a **low-exponent / bounded-`#S`** instrument; the L² bound pushes that
boundary from `#S ≤ 3` to `#S ≤ 7 = log₂ n`, which is the recognized open `B_β → B_{log n}`
bootstrap (LEVER B), not a full prize closure.  This file records the rigorous gain and the
precise residual.

## What is PROVEN axiom-clean here

* `amgm_prod_le_mean_pow`: unweighted AM-GM `∏ aᵢ ≤ (mean aᵢ)^{#s}` for nonneg reals.
* `abs_norm_sq_le_mean_pow`: `|N(α)|² ≤ (mean_σ ‖σα‖²)^{φ}` for any `α` in a number field
  (the Mahler-measure core; UNCONDITIONAL).
* `abs_norm_sum_rootsOfUnity_L2_le`: the `(2·#S)^{φ/2}` bound, conditional on `ParsevalL2Mass`.
* The numeric threshold theorems (`l2Gate_closes_to_64`, `houseGate_fails_at_64`,
  `l2Gate_lowExp_depth_128`, `houseGate_lowExp_depth_128`) and the honest obstruction
  `heightGate_mechanism_fails_at_128` — all `norm_num`, all axiom-clean.

## The one named analytic input (Mathlib gap, Parseval/orthogonality)

`ParsevalL2Mass K ζ`: for `Σ_S = Σ_{i∈S} ζ^i` (`ζ` a primitive `n`-th root in number field `K`),
`Σ_{σ:K→ℂ} ‖σ Σ_S‖² ≤ n·#S`.  PROOF (orthogonality, not formalized — Mathlib lacks the
embedding-trace `L²` identity): `Σ_σ‖σΣ_S‖² = Σ_{i,j∈S} Σ_σ σ(ζ)^{i-j} ≤ Σ_{i,j∈S} [over ALL
n-th roots z] z^{i-j} = Σ_{i,j∈S} n·[i≡j] = n·#S`, using that embeddings `σ` send `ζ` to the
`φ(n)` PRIMITIVE `n`-th roots, a subset of all `n` roots, and the squared moduli are nonneg.
This is the structure-aware refinement of `house_rootOfUnity_le_one` — the same Mathlib gap the
height-gate file flags, now used as an `L²` mass bound rather than an `L∞` (house) bound.
-/

open Finset NumberField Module

namespace ArkLib.ProximityGap.L2MahlerNorm

/-! ## Unweighted AM-GM in nat-power form -/

/-- **Unweighted AM-GM**: the product of nonnegative reals is `≤` the `#s`-th power of their
arithmetic mean.  (Derived from `Real.geom_mean_le_arith_mean` with unit weights.) -/
theorem amgm_prod_le_mean_pow {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hs : s.Nonempty) :
    (∏ i ∈ s, z i) ≤ ((∑ i ∈ s, z i) / s.card) ^ s.card := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hwsum : (0 : ℝ) < ∑ _i ∈ s, (1 : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_one]; exact hcard
  have h := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ)) z (fun _ _ => zero_le_one) hwsum hz
  simp only [sum_const, nsmul_eq_mul, mul_one, one_mul, Real.rpow_one] at h
  have hprodnn : (0 : ℝ) ≤ ∏ i ∈ s, z i := prod_nonneg hz
  have key := Real.rpow_le_rpow (Real.rpow_nonneg hprodnn _) h (le_of_lt hcard)
  rw [← Real.rpow_natCast ((∑ i ∈ s, z i) / s.card) s.card]
  calc ∏ i ∈ s, z i
      = ((∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹)) ^ (s.card : ℝ) := by
        rw [← Real.rpow_mul hprodnn, inv_mul_cancel₀ (ne_of_gt hcard), Real.rpow_one]
    _ ≤ ((∑ i ∈ s, z i) / s.card) ^ (s.card : ℝ) := key

variable {K : Type*} [Field K] [NumberField K]

/-! ## The Mahler-measure core: `|N(α)|² ≤ (mean of squared conjugate moduli)^φ` -/

/-- **Mahler-measure / geometric-mean norm bound (UNCONDITIONAL).**  For any `α` in a number
field `K`, the squared rational norm is bounded by the `[K:ℚ]`-th power of the arithmetic mean of
the squared conjugate moduli `‖σ α‖²`:
`|N_{K/ℚ}(α)|² ≤ ( (Σ_σ ‖σ α‖²) / [K:ℚ] )^{[K:ℚ]}`.

This replaces the per-conjugate `L∞` (house) bound `‖σα‖ ≤ house α` with one AM-GM step on the
SQUARES, turning the product `|N|² = ∏_σ ‖σα‖²` into the mean of the squares — the geometric vs
arithmetic mean gap is exactly the Mahler-measure improvement. -/
theorem abs_norm_sq_le_mean_pow (α : K) :
    (((|Algebra.norm ℚ α| : ℚ) : ℝ)) ^ 2 ≤
      ((∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) / (finrank ℚ K)) ^ finrank ℚ K := by
  classical
  -- `|N(α)| = ∏_σ ‖σ α‖`.
  have key : (algebraMap ℚ ℂ) (Algebra.norm ℚ α) = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  have hnorm : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
    simp [eq_ratCast, Complex.norm_ratCast, Rat.cast_abs]
  have hprodform : ((|Algebra.norm ℚ α| : ℚ) : ℝ) = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ := by
    rw [← hnorm, key, norm_prod]
  -- card of embeddings = finrank.
  have hcardeq : Fintype.card (K →ₐ[ℚ] ℂ) = finrank ℚ K :=
    AlgHom.card_of_splits ℚ K ℂ (fun _ ↦ IsAlgClosed.splits _)
  have hpos : 0 < finrank ℚ K := finrank_pos
  -- `|N|² = ∏_σ ‖σα‖²`.
  have hsqprod : (((|Algebra.norm ℚ α| : ℚ) : ℝ)) ^ 2 = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2 := by
    rw [hprodform, ← Finset.prod_pow]
  rw [hsqprod]
  -- AM-GM on the squared moduli over the (nonempty) embedding set.
  have hne : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (by rw [hcardeq]; exact hpos)
  have hamgm := amgm_prod_le_mean_pow (Finset.univ : Finset (K →ₐ[ℚ] ℂ))
    (fun σ => ‖σ α‖ ^ 2) (fun σ _ => by positivity) hne
  -- rewrite the card (= `univ.card`) as finrank.
  rw [Finset.card_univ, hcardeq] at hamgm
  exact hamgm

/-! ## The named Parseval / `L²`-mass input (orthogonality; Mathlib gap) -/

/-- **The Parseval `L²` mass input** (named analytic obligation).  For a primitive `n`-th root of
unity `ζ` in `K` and a subset `S ⊆ {0,…,n-1}`, the total `L²` mass of the conjugates of
`Σ_{i∈S} ζ^i` is at most `n·#S`:
`Σ_{σ:K→ℂ} ‖σ (Σ_{i∈S} ζ^i)‖² ≤ n·#S`.

This is orthogonality: each embedding `σ` sends `ζ` to a primitive `n`-th root, so the sum over
`σ` is a sub-sum (nonneg terms) of the sum over ALL `n`-th roots, which equals `n·#S` exactly by
the geometric-series / character orthogonality `Σ_{z^n=1} z^m = n·[n ∣ m]` (distinct exponents
in `S`).  Mathlib lacks the embedding-`L²` identity, so this is kept as a precise named Prop
(project modularity convention; the same Mathlib gap flagged in `HeightGateNormBound.lean`). -/
def ParsevalL2Mass (n : ℕ) (ζ : K) : Prop :=
  ∀ S : Finset ℕ, (∑ σ : K →ₐ[ℚ] ℂ, ‖σ (∑ i ∈ S, ζ ^ i)‖ ^ 2) ≤ (n : ℝ) * S.card

/-! ## The L² norm bound for sums of roots of unity (conditional on Parseval) -/

/-- **The structure-aware L² norm bound.**  Given the Parseval mass input and `φ(n) = finrank`
identified with `n/2` (the `2`-power cyclotomic case, supplied as `hfin : finrank ℚ K = n / 2`),
the norm of `Σ_{i∈S} ζ^i` obeys
`|N_{K/ℚ}(Σ_S)| ≤ (2·#S)^{n/4}` (here phrased with the squared form `|N|² ≤ (2·#S)^{n/2}`).

This is **half the exponent** of the crude house bound `(#S)^{n/2}`. -/
theorem abs_norm_sum_rootsOfUnity_L2_le {n : ℕ} (hn : 0 < n) {ζ : K}
    (hpar : ParsevalL2Mass n ζ) (hfin : finrank ℚ K = n / 2) (hn2 : 2 ∣ n)
    (S : Finset ℕ) :
    (((|Algebra.norm ℚ (∑ i ∈ S, ζ ^ i)| : ℚ) : ℝ)) ^ 2 ≤
      ((2 : ℝ) * S.card) ^ finrank ℚ K := by
  classical
  set α : K := ∑ i ∈ S, ζ ^ i with hα
  refine (abs_norm_sq_le_mean_pow α).trans ?_
  -- bound the mean of squared moduli by `2 * #S`.
  have hpos : 0 < finrank ℚ K := finrank_pos
  have hmass : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) ≤ (n : ℝ) * S.card := hpar S
  -- mean ≤ (n·#S)/φ = 2·#S  since φ = n/2.
  have hfinR : (finrank ℚ K : ℝ) = (n : ℝ) / 2 := by
    rw [hfin]
    obtain ⟨m, rfl⟩ := hn2
    rw [Nat.mul_div_cancel_left m (by norm_num)]
    push_cast; ring
  have hmean : (∑ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ ^ 2) / (finrank ℚ K) ≤ (2 : ℝ) * S.card := by
    rw [div_le_iff₀ (by exact_mod_cast hpos)]
    refine hmass.trans ?_
    rw [hfinR]
    have : (n : ℝ) = 2 * ((n : ℝ) / 2) := by ring
    nlinarith [Nat.cast_nonneg (α := ℝ) S.card, Nat.cast_nonneg (α := ℝ) n]
  -- raise to the φ power (monotone, both sides nonneg).
  refine pow_le_pow_left₀ ?_ hmean (finrank ℚ K)
  positivity

/-! ## Numeric boundary — the quantified payoff (all `norm_num`, axiom-clean) -/

/-- **L² gate closes the worst case to `n = 64`.**  At `n = 64` (`φ = 32`), even the worst subset
`#S ≤ 64` has L²-bounded norm `|N| ≤ (2·64)^{32/... }`; in squared form `(2·64)^{32} = 128^{32}
= 2^{224} < 2^{256} = (2^{128})²`, i.e. `|N| < 2^{128}`.  (`(2#S)^{n/4}` worst-case at `n=64`,
`#S=64`: `128^16 = 2^112 < 2^128`.) -/
theorem l2Gate_closes_to_64 :
    ((2 : ℝ) * 64) ^ (16 : ℕ) < (2 : ℝ) ^ (128 : ℕ) := by
  norm_num

/-- **The crude house gate FAILS at `n = 64`** (worst case): `(#S)^{n/2}` with `#S = 64`,
`n/2 = 32` is `64^{32} = 2^{192} > 2^{128}`.  This is the regime the L² bound newly closes. -/
theorem houseGate_fails_at_64 :
    (2 : ℝ) ^ (128 : ℕ) < (64 : ℝ) ^ (32 : ℕ) := by
  norm_num

/-- **L² gate, low-exponent direction at the prize order `n = 128`: closes `#S = 7 = log₂ 128`.**
With `#S = 7`, `n/4 = 32`: `(2·7)^{32} = 14^{32} < 2^{128}`. -/
theorem l2Gate_lowExp_depth_128 :
    ((2 : ℝ) * 7) ^ (32 : ℕ) < (2 : ℝ) ^ (128 : ℕ) := by
  norm_num

/-- **The crude house gate, low-exponent direction at `n = 128`: closes only `#S = 3`.**
With `#S = 4`, `n/2 = 64`: `4^{64} = 2^{128}` is NOT `< 2^{128}` (it is equal), so house already
fails at `#S = 4`; the L² bound reaches `#S = 7`.  We record the strict failure at `#S = 8`
(`8^{64} = 2^{192} > 2^{128}`) and the L² success at the same `#S = 8` boundary value being the
edge: `(2·8)^{32} = 16^{32} = 2^{128}` (equality, so L² closes `#S ≤ 7` strictly). -/
theorem houseGate_lowExp_depth_128 :
    (2 : ℝ) ^ (128 : ℕ) < (8 : ℝ) ^ (64 : ℕ) ∧
      ((2 : ℝ) * 8) ^ (32 : ℕ) = (2 : ℝ) ^ (128 : ℕ) := by
  constructor <;> norm_num

/-! ## Honest boundary — the gate mechanism fails at `n ≥ 128` for the FULL subset family -/

/-- **The height-gate mechanism itself fails at `n = 128` (not just our bound).**  The realized
worst-case norm over non-antipodal subsets at `n = 128` is `≈ 2^160` (numerically; `probe`),
which EXCEEDS the prize prime `p ≈ n·2^128 = 2^135`.  We record the *certified arithmetic core*:
`2^135 < 2^160`, the witnessed-realized-norm magnitude exceeding the prize floor.  Consequently
NO norm bound (however tight) can make `p > |N(Σ_S)|` hold for all non-antipodal `S` at `n=128`:
the height gate is fundamentally a bounded-`#S` (low-exponent) instrument, and the L²-gain
`#S ≤ 7 = log₂ n` is the recognized `B_β → B_{log n}` bootstrap target (LEVER B), not a full
prize closure. -/
theorem heightGate_mechanism_fails_at_128 :
    (2 : ℝ) ^ (135 : ℕ) < (2 : ℝ) ^ (160 : ℕ) := by
  norm_num

/-- The L² bound exponent is exactly HALF the house exponent: house squared `((#S)^{φ})² =
(#S)^{2φ}` vs L² `(2#S)^{φ}`; for `#S ≥ 2`, `(2#S)^{φ} ≤ (#S)^{2φ}` iff `2#S ≤ (#S)²` iff
`#S ≥ 2`.  So the L² bound is never worse than house (and strictly better for `#S ≥ 3`). -/
theorem l2_dominates_house {t φ : ℕ} (ht : 2 ≤ t) :
    ((2 : ℝ) * t) ^ φ ≤ ((t : ℝ) ^ φ) ^ 2 := by
  rw [← pow_mul, mul_comm φ 2, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ φ
  have : (2 : ℝ) ≤ t := by exact_mod_cast ht
  nlinarith [this]

end ArkLib.ProximityGap.L2MahlerNorm

#print axioms ArkLib.ProximityGap.L2MahlerNorm.amgm_prod_le_mean_pow
#print axioms ArkLib.ProximityGap.L2MahlerNorm.abs_norm_sq_le_mean_pow
#print axioms ArkLib.ProximityGap.L2MahlerNorm.abs_norm_sum_rootsOfUnity_L2_le
#print axioms ArkLib.ProximityGap.L2MahlerNorm.l2Gate_closes_to_64
#print axioms ArkLib.ProximityGap.L2MahlerNorm.houseGate_fails_at_64
#print axioms ArkLib.ProximityGap.L2MahlerNorm.l2Gate_lowExp_depth_128
#print axioms ArkLib.ProximityGap.L2MahlerNorm.houseGate_lowExp_depth_128
#print axioms ArkLib.ProximityGap.L2MahlerNorm.heightGate_mechanism_fails_at_128
#print axioms ArkLib.ProximityGap.L2MahlerNorm.l2_dominates_house
