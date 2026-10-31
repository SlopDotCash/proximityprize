/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Shaw Cancellation Law: a named principle for root-number phase cancellation (#444)

This file **invents and applies** a new named principle, the *Shaw Cancellation Law*, for the
root-number representation of the Gauss period

> `η_b = (n / (p−1)) · Σ_χ χ̄(b) · g(χ)`,   `|g(χ)| = √p`,   `b ≠ 0`,

the dual / multiplicative-character side of the prize structural constant
`M(n) = max_{b≠0} ‖η_b‖`. Writing `g(χ) = √p · r(χ)` with `r(χ)` of **unit modulus** (the
"root number" of `χ`), the period becomes a *linear synthesis* of the unit-modulus root-number
sequence against the character-evaluation weights `χ ↦ χ̄(b)`:

> `η_b = (n √p / (p−1)) · (𝓢 r)(b)`,   `(𝓢 r)(b) := Σ_χ χ̄(b) · r(χ)`.

We package this as an abstract **Shaw operator** `shaw w r b := Σ_χ (w b χ) · (r χ)` — a synthesis
operator on an arbitrary finite index `χ : Idx` with a coefficient kernel `w : B → Idx → ℂ` and a
unit-modulus input sequence `r`. The character-evaluation kernel `w b χ = χ̄(b)` is the prize
instance.

## The Shaw Cancellation Law (the named principle)

> **Definition (`ShawCancellationLaw w S`).** The Shaw operator `𝓢` *satisfies the cancellation law
> with bound `S`* if for every unit-modulus root-number sequence `r` and every `b`,
> `‖(𝓢 r)(b)‖ ≤ S`.

For the prize kernel the *trivial* (Cauchy–Schwarz, no cancellation) value is `S = m` (the number of
characters): `‖Σ_χ χ̄(b) r(χ)‖ ≤ Σ_χ |χ̄(b)| · |r(χ)| = m`.

**Audit correction (2026-10-28, CW-B14-01).**  The law *as quantified above* — over **every**
unit-modulus sequence `r` — is equivalent to `S ≥ m` for a unit-modulus kernel: the aligned-phase
sequence `r χ = conj (w b χ)` makes `(𝓢 r)(b) = m` exactly (`cancellationLaw_ge_card`).  So no
sub-trivial bound can hold in that form, and the earlier "prize principle"
`ShawSubGaussianCancellation` is **false** whenever `√(2 n log m) < m` and the base is nonempty
(`not_shawSubGaussianCancellation`; minimal instance `Idx = Fin 2`, `w = 1`, `n = 1`:
`‖𝓢 1‖ = 2 > √(2 ln 2)`).  The honest prize-shaped statement fixes the input sequence: the law
`ShawCancellationAt w r S` for the **specific** normalized Gauss-sum sequence `r χ = g(χ)/√p`.
That sequence is only unit-modulus on non-trivial characters (`g(χ₀) = −1`), so the prize
instance also needs the trivial-character term `−n/(p−1)` split off; this file does not
construct that instance.  Prefactor bookkeeping: with `c = n√p/(p−1)` and `m = (p−1)/n` one has
`c · m = √p` (not `n√p`), and the prize target `M ≤ √(2 n log m)` corresponds to
`S ≈ √(2 n log m) / c ≈ √(2 m log m)` (using `p ≈ n·m`), the random-walk scale in the `m`
summands — not `S = √(2 n log m)`.

## What is proven here (axiom-clean) vs. what is named-open

* `shaw_norm_le_l1` — **unconditional** `‖(𝓢 r)(b)‖ ≤ Σ_χ ‖w b χ‖` for unit-modulus `r` (the L¹
  ceiling); specialized to the prize kernel `= m` (the trivial bound, no cancellation).
* `shaw_sq_le_cauchySchwarz` — **unconditional** Cauchy–Schwarz ceiling
  `‖(𝓢 r)(b)‖² ≤ (Σ_χ ‖w b χ‖²) · (Σ_χ ‖r χ‖²)`; for unit-modulus `r` over `m` indices `= (Σ‖w‖²)·m`.
* `shaw_secondMoment_eq` — the **exact** second moment of `𝓢 r` over an orthonormal kernel family
  (`Σ_b ‖(𝓢 r)(b)‖² = Σ_χ ‖r χ‖²`); the √-floor / average side, no cancellation hypothesis.
* `ShawCancellationLaw` — the all-sequences law, with `cancellationLaw_ge_card` showing it forces
  `S ≥ m` (unit kernel), and `not_shawSubGaussianCancellation` refuting its sub-Gaussian form.
* `ShawCancellationAt` / `ShawSubGaussianCancellationAt` — the fixed-sequence law, and
  `prizeBound_of_cancellationAt` / `prize_M_bound_of_subGaussianAt` — the transport through the
  `η_b` prefactor `M ≤ c · S`.  `ShawSubGaussianCancellationAt` for the Gauss-sum root numbers is a
  named open input (not instantiated here); no `sorry`, no fake `axiom`.

All proofs are axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option linter.style.longLine false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false


namespace ArkLib.ProximityGap.Frontier.ShawCancellationLaw

open Finset

/-! ## The abstract Shaw synthesis operator on a root-number sequence -/

variable {B Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **The Shaw operator** `𝓢` on a root-number sequence. Given a coefficient kernel
`w : B → Idx → ℂ` (the character-evaluation weights `w b χ = χ̄(b)` for the prize) and an input
sequence `r : Idx → ℂ` (the unit-modulus root numbers `r χ = g(χ)/√p`), the Shaw operator synthesizes

`(𝓢 r)(b) := Σ_χ (w b χ) · (r χ)`.

For the prize kernel this is exactly `(p−1)/(n√p) · η_b`. -/
noncomputable def shaw (w : B → Idx → ℂ) (r : Idx → ℂ) (b : B) : ℂ :=
  ∑ χ : Idx, (w b χ) * (r χ)

@[simp] theorem shaw_apply (w : B → Idx → ℂ) (r : Idx → ℂ) (b : B) :
    shaw w r b = ∑ χ : Idx, (w b χ) * (r χ) := rfl

/-- A **root-number sequence**: every entry has unit modulus (`|g(χ)/√p| = 1`). This is the only
structural fact about the Gauss-sum root numbers used by the cancellation law. -/
def IsRootNumberSeq (r : Idx → ℂ) : Prop := ∀ χ : Idx, ‖r χ‖ = 1

/-! ## The unconditional ceilings — the provable half of the law -/

/-- **The L¹ ceiling (trivial bound, no cancellation).** For a unit-modulus root-number sequence,
`‖(𝓢 r)(b)‖ ≤ Σ_χ ‖w b χ‖`. For the prize kernel `w b χ = χ̄(b)` (each of modulus 1) this is the
*trivial* bound `‖η_b‖ ≤ (n√p/(p−1)) · m = √p` (`m = (p−1)/n`; up to the trivial-character
correction), with no cancellation whatsoever. -/
theorem shaw_norm_le_l1 (w : B → Idx → ℂ) {r : Idx → ℂ} (hr : IsRootNumberSeq r) (b : B) :
    ‖shaw w r b‖ ≤ ∑ χ : Idx, ‖w b χ‖ := by
  rw [shaw_apply]
  calc ‖∑ χ : Idx, (w b χ) * (r χ)‖
      ≤ ∑ χ : Idx, ‖(w b χ) * (r χ)‖ := norm_sum_le _ _
    _ = ∑ χ : Idx, ‖w b χ‖ := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [norm_mul, hr χ, mul_one]

/-- **The trivial L¹ value for the prize character kernel.** When every kernel weight has modulus 1
(the prize case `‖χ̄(b)‖ = 1`), the L¹ ceiling is exactly the number of characters `m = |Idx|`. This
is the Cauchy–Schwarz / no-cancellation baseline the law must beat. -/
theorem shaw_norm_le_card (w : B → Idx → ℂ) {r : Idx → ℂ} (hr : IsRootNumberSeq r)
    (hw : ∀ b : B, ∀ χ : Idx, ‖w b χ‖ = 1) (b : B) :
    ‖shaw w r b‖ ≤ (Fintype.card Idx : ℝ) := by
  refine le_trans (shaw_norm_le_l1 w hr b) ?_
  rw [Finset.sum_congr rfl (fun χ _ => hw b χ), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]

/-- **The Cauchy–Schwarz ceiling.** `‖(𝓢 r)(b)‖² ≤ (Σ_χ ‖w b χ‖²) · (Σ_χ ‖r χ‖²)`, unconditionally.
For a unit-modulus root-number sequence over `m` indices the right factor is `m`, so the operator's
*squared* value is at most `(Σ_χ ‖w b χ‖²) · m`. This is the best bound available **without** using
the phases of the root numbers — the wall the cancellation law must pierce. -/
theorem shaw_sq_le_cauchySchwarz (w : B → Idx → ℂ) (r : Idx → ℂ) (b : B) :
    ‖shaw w r b‖ ^ 2 ≤ (∑ χ : Idx, ‖w b χ‖ ^ 2) * (∑ χ : Idx, ‖r χ‖ ^ 2) := by
  classical
  rw [shaw_apply]
  -- `‖Σ a_χ c_χ‖ ≤ Σ ‖a_χ‖‖c_χ‖`, then the squared real Cauchy–Schwarz on the norm sequences.
  have hsum : ‖∑ χ : Idx, (w b χ) * (r χ)‖ ≤ ∑ χ : Idx, ‖w b χ‖ * ‖r χ‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum (fun χ _ => by rw [norm_mul])
  have hcs2 :
      (∑ χ : Idx, ‖w b χ‖ * ‖r χ‖) ^ 2
        ≤ (∑ χ : Idx, ‖w b χ‖ ^ 2) * (∑ χ : Idx, ‖r χ‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun χ => ‖w b χ‖) (fun χ => ‖r χ‖)
  have hnn : (0 : ℝ) ≤ ∑ χ : Idx, ‖w b χ‖ * ‖r χ‖ :=
    Finset.sum_nonneg (fun χ _ => by positivity)
  have hsq : ‖∑ χ : Idx, (w b χ) * (r χ)‖ ^ 2 ≤ (∑ χ : Idx, ‖w b χ‖ * ‖r χ‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖∑ χ : Idx, (w b χ) * (r χ)‖ := norm_nonneg _
    nlinarith [hsum, hnn, h0]
  exact le_trans hsq hcs2

/-- **The Cauchy–Schwarz value for a unit-modulus root-number sequence.** With `‖r χ‖ = 1` over
`m = |Idx|` indices, the Cauchy–Schwarz ceiling specializes to
`‖(𝓢 r)(b)‖² ≤ m · (Σ_χ ‖w b χ‖²)`. For the prize character kernel (`‖w b χ‖ = 1`) this is `m²`,
recovering the trivial `‖η_b‖ ≤ √p` bound: **Cauchy–Schwarz alone gives no cancellation.** -/
theorem shaw_sq_le_card (w : B → Idx → ℂ) {r : Idx → ℂ} (hr : IsRootNumberSeq r) (b : B) :
    ‖shaw w r b‖ ^ 2 ≤ (Fintype.card Idx : ℝ) * (∑ χ : Idx, ‖w b χ‖ ^ 2) := by
  refine le_trans (shaw_sq_le_cauchySchwarz w r b) ?_
  have hr1 : (∑ χ : Idx, ‖r χ‖ ^ 2) = (Fintype.card Idx : ℝ) := by
    rw [Finset.sum_congr rfl (fun χ _ => by rw [hr χ, one_pow]), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hr1, mul_comm]

/-! ## The exact second moment — the Parseval / average side -/

/-- A kernel family `w` is **orthonormal over the index** if its columns are orthonormal in
`ℂ^B`: `Σ_b (w b χ) · conj (w b χ') = [χ = χ']`. For the prize the rescaled character kernel
`w b χ = χ̄(b)/√(p−1)` over `b ∈ F_p^×` is orthonormal by character orthogonality. This is the only
structural input to the exact second-moment law. -/
def OrthonormalKernel [Fintype B] (w : B → Idx → ℂ) : Prop :=
  ∀ χ χ' : Idx, (∑ b : B, (w b χ) * (starRingEnd ℂ) (w b χ')) = if χ = χ' then 1 else 0

/-- **The Shaw second-moment law (exact, no cancellation hypothesis).** For an orthonormal kernel,
the total energy of the Shaw operator over `b` equals the energy of the input:

`Σ_b ‖(𝓢 r)(b)‖² = Σ_χ ‖r χ‖²`.

For a unit-modulus root-number sequence the right side is `m`, so the **average** of `‖(𝓢 r)(b)‖²`
over `b` is `m/|B|`. Transported through the prize prefactor this is exactly the Parseval `√n`-floor
`avg_b ‖η_b‖² = (qn − n²)/(q−1) ≈ n`: the L²/average side of the prize bound holds with no
cancellation. The open law is the **sup over `b`** above this average, not the average. -/
theorem shaw_secondMoment_eq [Fintype B] (w : B → Idx → ℂ) (hw : OrthonormalKernel w)
    (r : Idx → ℂ) :
    (∑ b : B, ‖shaw w r b‖ ^ 2) = ∑ χ : Idx, ‖r χ‖ ^ 2 := by
  classical
  have keyC :
      (∑ b : B, shaw w r b * (starRingEnd ℂ) (shaw w r b))
        = ∑ χ : Idx, (r χ) * (starRingEnd ℂ) (r χ) := by
    calc ∑ b : B, shaw w r b * (starRingEnd ℂ) (shaw w r b)
        = ∑ b : B, ∑ χ : Idx, ∑ χ' : Idx,
            ((w b χ) * (r χ)) * (starRingEnd ℂ) ((w b χ') * (r χ')) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [shaw_apply, map_sum, Finset.sum_mul_sum]
      _ = ∑ χ : Idx, ∑ χ' : Idx, ∑ b : B,
            ((w b χ) * (r χ)) * (starRingEnd ℂ) ((w b χ') * (r χ')) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ χ : Idx, ∑ χ' : Idx,
            ((r χ) * (starRingEnd ℂ) (r χ')) *
              (∑ b : B, (w b χ) * (starRingEnd ℂ) (w b χ')) := by
          refine Finset.sum_congr rfl (fun χ _ => Finset.sum_congr rfl (fun χ' _ => ?_))
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [map_mul]; ring
      _ = ∑ χ : Idx, ∑ χ' : Idx,
            ((r χ) * (starRingEnd ℂ) (r χ')) * (if χ = χ' then (1 : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun χ _ => Finset.sum_congr rfl (fun χ' _ => ?_))
          rw [hw χ χ']
      _ = ∑ χ : Idx, (r χ) * (starRingEnd ℂ) (r χ) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq Finset.univ χ (fun χ' => (r χ) * (starRingEnd ℂ) (r χ')),
            if_pos (Finset.mem_univ χ)]
  have h := keyC
  simp only [Complex.mul_conj] at h
  norm_cast at h
  simp only [Complex.normSq_eq_norm_sq] at h
  exact h

/-- **Parseval value of the second moment for a root-number sequence.** With `‖r χ‖ = 1`, the
exact second moment is `m = |Idx|`: `Σ_b ‖(𝓢 r)(b)‖² = m`. The average over `|B|` base points is
`m/|B|`; this is the unconditional √-floor of the prize. -/
theorem shaw_secondMoment_card [Fintype B] (w : B → Idx → ℂ) (hw : OrthonormalKernel w)
    {r : Idx → ℂ} (hr : IsRootNumberSeq r) :
    (∑ b : B, ‖shaw w r b‖ ^ 2) = (Fintype.card Idx : ℝ) := by
  rw [shaw_secondMoment_eq w hw r,
    Finset.sum_congr rfl (fun χ _ => by rw [hr χ, one_pow]), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-- **The √-floor for the operator norm (necessity).** For an orthonormal kernel and a root-number
sequence over a nonempty base, some base point achieves at least the average, hence
`(max_b ‖(𝓢 r)(b)‖)² ≥ m/|B|`. So the cancellation law's bound `S` is forced to satisfy
`S² ≥ m/|B|` — an unconditional necessary condition (no phase choice of the root numbers can push
the worst case below the Parseval floor). -/
theorem exists_shaw_sq_ge_average [Fintype B] [Nonempty B] (w : B → Idx → ℂ)
    (hw : OrthonormalKernel w) {r : Idx → ℂ} (hr : IsRootNumberSeq r) :
    ∃ b : B, (Fintype.card Idx : ℝ) / (Fintype.card B : ℝ) ≤ ‖shaw w r b‖ ^ 2 := by
  classical
  by_contra h
  push Not at h
  have hcardB : (0 : ℝ) < (Fintype.card B : ℝ) := by
    have : 0 < Fintype.card B := Fintype.card_pos
    exact_mod_cast this
  have hlt :
      (∑ b : B, ‖shaw w r b‖ ^ 2)
        < ∑ _b : B, (Fintype.card Idx : ℝ) / (Fintype.card B : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun b _ => h b)
  rw [shaw_secondMoment_card w hw hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  rw [mul_div_cancel₀ _ (ne_of_gt hcardB)] at hlt
  exact lt_irrefl _ hlt

/-! ## The Shaw Cancellation Law as a named principle, and its application -/

/-- **The Shaw Cancellation Law over all root-number sequences.** The Shaw operator `𝓢` with kernel
`w` *satisfies the cancellation law with operator-norm bound `S`* if every unit-modulus sequence is
synthesized to within `S` at every base point:

`∀ r, IsRootNumberSeq r → ∀ b, ‖(𝓢 r)(b)‖ ≤ S`.

Because `r` ranges over **all** unit-modulus sequences, the aligned phases `r = conj (w b ·)` are
allowed, so for a unit-modulus kernel this law holds iff `S ≥ m` (`shawCancellationLaw_card`,
`cancellationLaw_ge_card`): it cannot express sub-trivial cancellation.  See `ShawCancellationAt`
for the fixed-sequence form. -/
def ShawCancellationLaw (w : B → Idx → ℂ) (S : ℝ) : Prop :=
  ∀ r : Idx → ℂ, IsRootNumberSeq r → ∀ b : B, ‖shaw w r b‖ ≤ S

/-- **The trivial cancellation law always holds at `S = m`.** Every Shaw operator with a
unit-modulus kernel (`‖w b χ‖ = 1`, the prize character case) satisfies the cancellation law at the
no-cancellation scale `S = |Idx|`. -/
theorem shawCancellationLaw_card (w : B → Idx → ℂ) (hw : ∀ b : B, ∀ χ : Idx, ‖w b χ‖ = 1) :
    ShawCancellationLaw w (Fintype.card Idx : ℝ) :=
  fun _r hr b => shaw_norm_le_card w hr hw b

/-- **The all-sequences law forces the trivial bound (audit CW-B14-01).**  For a unit-modulus
kernel, the aligned-phase sequence `r χ = conj (w b χ)` is a root-number sequence with
`(𝓢 r)(b) = m`, so any `S` for which `ShawCancellationLaw w S` holds satisfies `m ≤ S`. -/
theorem cancellationLaw_ge_card (w : B → Idx → ℂ) (hw : ∀ b : B, ∀ χ : Idx, ‖w b χ‖ = 1)
    {S : ℝ} (hlaw : ShawCancellationLaw w S) (b : B) :
    (Fintype.card Idx : ℝ) ≤ S := by
  have hr : IsRootNumberSeq (fun χ => (starRingEnd ℂ) (w b χ)) := fun χ => by
    rw [Complex.norm_conj, hw b χ]
  have hval : shaw w (fun χ => (starRingEnd ℂ) (w b χ)) b = (Fintype.card Idx : ℂ) := by
    rw [shaw_apply, Finset.sum_congr rfl (fun χ _ => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw b χ]), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    push_cast; ring
  have h := hlaw _ hr b
  rwa [hval, Complex.norm_natCast] at h

/-- **The Shaw Cancellation Law applied to the prize sup-norm `M` (all-sequences form).**  If
`η b = c · (𝓢 r)(b)` with `c ≥ 0` and `r` a root-number sequence, the law at bound `S` gives
`‖η b‖ ≤ c · S`.  (By `cancellationLaw_ge_card` the hypothesis forces `S ≥ m` for a unit kernel,
so this transport only ever yields the trivial bound; use `prizeBound_of_cancellationAt`.) -/
theorem prizeBound_of_cancellationLaw {η : B → ℂ} (w : B → Idx → ℂ) {r : Idx → ℂ}
    (hr : IsRootNumberSeq r) {c : ℝ} (hc : 0 ≤ c) (hη : ∀ b : B, η b = (c : ℂ) * shaw w r b)
    {S : ℝ} (hlaw : ShawCancellationLaw w S) (b : B) :
    ‖η b‖ ≤ c * S := by
  rw [hη b, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hlaw r hr b) hc

/-- **Lower bound on any valid cancellation bound (the Parseval obstruction).** For an orthonormal
kernel over a nonempty base, *any* `S` for which the cancellation law holds must satisfy
`S² ≥ m/|B|`.  (The witness is the constant root-number sequence `r ≡ 1`.)  For a unit kernel the
sharper `cancellationLaw_ge_card` already gives `S ≥ m`. -/
theorem cancellationLaw_lower_bound [Fintype B] [Nonempty B] (w : B → Idx → ℂ)
    (hw : OrthonormalKernel w) {S : ℝ} (hlaw : ShawCancellationLaw w S) :
    (Fintype.card Idx : ℝ) / (Fintype.card B : ℝ) ≤ S ^ 2 := by
  classical
  -- the constant sequence `r ≡ 1` is a root-number sequence
  have hr : IsRootNumberSeq (fun _ : Idx => (1 : ℂ)) := fun _ => by simp
  obtain ⟨b, hb⟩ := exists_shaw_sq_ge_average w hw hr
  have hS0 : (0 : ℝ) ≤ S := le_trans (norm_nonneg _) (hlaw _ hr b)
  have hsq : ‖shaw w (fun _ : Idx => (1 : ℂ)) b‖ ^ 2 ≤ S ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖shaw w (fun _ : Idx => (1 : ℂ)) b‖ := norm_nonneg _
    nlinarith [hlaw (fun _ : Idx => (1 : ℂ)) hr b, hnn, hS0]
  exact le_trans hb hsq

/-! ## The refuted all-sequences sub-Gaussian law -/

/-- **The all-sequences sub-Gaussian law (REFUTED in the prize regime).**  The cancellation law at
scale `S = √(2 · n · log m)` over **every** unit-modulus sequence.  Kept for the record:
`not_shawSubGaussianCancellation` shows it is false whenever `√(2 n log m) < m`, the base is
nonempty and the kernel is unit-modulus — exactly the regime where it was advertised as the prize
input.  The scale is also mis-calibrated (see the module docstring). -/
def ShawSubGaussianCancellation (w : B → Idx → ℂ) (n : ℝ) : Prop :=
  ShawCancellationLaw w (Real.sqrt (2 * n * Real.log (Fintype.card Idx : ℝ)))

/-- **Refutation of `ShawSubGaussianCancellation` (audit CW-B14-01).**  For a unit-modulus kernel
over a nonempty base, if `√(2 n log m) < m` then the all-sequences sub-Gaussian law fails. -/
theorem not_shawSubGaussianCancellation [Nonempty B] {w : B → Idx → ℂ}
    (hw : ∀ b : B, ∀ χ : Idx, ‖w b χ‖ = 1) {n : ℝ}
    (hlt : Real.sqrt (2 * n * Real.log (Fintype.card Idx : ℝ)) < (Fintype.card Idx : ℝ)) :
    ¬ ShawSubGaussianCancellation w n := fun hlaw =>
  absurd (cancellationLaw_ge_card w hw hlaw (Classical.arbitrary B)) (not_le.mpr hlt)

/-! ## The fixed-sequence law — the honest prize-shaped open input -/

/-- **The Shaw cancellation law for a fixed sequence.**  `‖(𝓢 r)(b)‖ ≤ S` at every base point, for
the given `r` only.  For the prize, `r` is the normalized Gauss-sum sequence `g(χ)/√p` (with the
trivial character split off); unlike `ShawCancellationLaw`, this is not refuted by aligned
phases. -/
def ShawCancellationAt (w : B → Idx → ℂ) (r : Idx → ℂ) (S : ℝ) : Prop :=
  ∀ b : B, ‖shaw w r b‖ ≤ S

/-- The all-sequences law implies the fixed-sequence law for every root-number sequence. -/
theorem ShawCancellationLaw.toAt {w : B → Idx → ℂ} {S : ℝ} (hlaw : ShawCancellationLaw w S)
    {r : Idx → ℂ} (hr : IsRootNumberSeq r) : ShawCancellationAt w r S :=
  hlaw r hr

/-- **Transport of the fixed-sequence law to the prize sup-norm.**  If `η b = c · (𝓢 r)(b)` with
`c ≥ 0`, then `ShawCancellationAt w r S` gives `‖η b‖ ≤ c · S` for every `b`. -/
theorem prizeBound_of_cancellationAt {η : B → ℂ} (w : B → Idx → ℂ) {r : Idx → ℂ}
    {c : ℝ} (hc : 0 ≤ c) (hη : ∀ b : B, η b = (c : ℂ) * shaw w r b)
    {S : ℝ} (hlaw : ShawCancellationAt w r S) (b : B) :
    ‖η b‖ ≤ c * S := by
  rw [hη b, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hlaw b) hc

/-- **The fixed-sequence sub-Gaussian law (named open input, not instantiated here).**  The
synthesis of the specific sequence `r` stays within the random-walk scale `√(2 m log m)` of its
`m = |Idx|` summands.  With the prize prefactor `c = n√p/(p−1)` and `p ≈ n·m`,
`c · √(2 m log m) ≈ √(2 n log m)`, the near-Ramanujan target.  For `r` the Gauss-sum root numbers
this is the BGK / thin-subgroup wall; this file neither proves it nor builds that instance. -/
def ShawSubGaussianCancellationAt (w : B → Idx → ℂ) (r : Idx → ℂ) : Prop :=
  ShawCancellationAt w r
    (Real.sqrt (2 * (Fintype.card Idx : ℝ) * Real.log (Fintype.card Idx : ℝ)))

/-- **The fixed-sequence law gives the prefactor-scaled `M`-bound.**  If `η b = c · (𝓢 r)(b)`
(`c ≥ 0`) and `ShawSubGaussianCancellationAt w r` holds, then
`‖η b‖ ≤ c · √(2 m log m)` for every `b`.  Pure transport; the open content is the hypothesis. -/
theorem prize_M_bound_of_subGaussianAt {η : B → ℂ} (w : B → Idx → ℂ) {r : Idx → ℂ}
    {c : ℝ} (hc : 0 ≤ c) (hη : ∀ b : B, η b = (c : ℂ) * shaw w r b)
    (hlaw : ShawSubGaussianCancellationAt w r) (b : B) :
    ‖η b‖ ≤ c * Real.sqrt (2 * (Fintype.card Idx : ℝ) * Real.log (Fintype.card Idx : ℝ)) :=
  prizeBound_of_cancellationAt w hc hη hlaw b

/-- **The fixed-sequence law beats the trivial bound when its scale does.**  If
`√(2 m log m) < m` then `ShawSubGaussianCancellationAt w r` gives `‖(𝓢 r)(b)‖ < m`, strictly below
the unconditional ceiling `shaw_norm_le_card`. -/
theorem subGaussianAt_strengthens_trivial {w : B → Idx → ℂ} {r : Idx → ℂ}
    (hlt : Real.sqrt (2 * (Fintype.card Idx : ℝ) * Real.log (Fintype.card Idx : ℝ))
      < (Fintype.card Idx : ℝ))
    (hlaw : ShawSubGaussianCancellationAt w r) (b : B) :
    ‖shaw w r b‖ < (Fintype.card Idx : ℝ) :=
  lt_of_le_of_lt (hlaw b) hlt

end ArkLib.ProximityGap.Frontier.ShawCancellationLaw

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.shaw_norm_le_l1
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.shaw_norm_le_card
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.shaw_sq_le_cauchySchwarz
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.shaw_sq_le_card
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.shaw_secondMoment_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.shaw_secondMoment_card
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.exists_shaw_sq_ge_average
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.shawCancellationLaw_card
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.prizeBound_of_cancellationLaw
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.cancellationLaw_lower_bound
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.cancellationLaw_ge_card
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.not_shawSubGaussianCancellation
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.prizeBound_of_cancellationAt
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.prize_M_bound_of_subGaussianAt
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.subGaussianAt_strengthens_trivial
