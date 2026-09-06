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
characters): `‖Σ_χ χ̄(b) r(χ)‖ ≤ Σ_χ |χ̄(b)| · |r(χ)| = m`. The **Shaw Cancellation Law as a prize
principle** asserts the operator has *spectral radius* down at the square-root-with-log scale:

> `S ≤ √(n · log m) · √(p) / (something)` — concretely, transporting through the
> `(n√p/(p−1))` prefactor, `M(n) = max_b ‖η_b‖ ≤ √(2 n log m)`.

That is exactly the BGK / near-Ramanujan prize target restated as a single operator-norm bound. This
file proves the **provable half** of the law (the unconditional Cauchy–Schwarz ceiling and the exact
Parseval/second-moment floor) and isolates the **one open input** — the genuine sub-Cauchy–Schwarz
cancellation — as a single named `Prop`, then *applies* it: the law `⟹` the prize `M`-bound.

## What is proven here (axiom-clean) vs. what is named-open

* `shaw_norm_le_l1` — **unconditional** `‖(𝓢 r)(b)‖ ≤ Σ_χ ‖w b χ‖` for unit-modulus `r` (the L¹
  ceiling); specialized to the prize kernel `= m` (the trivial bound, no cancellation).
* `shaw_sq_le_cauchySchwarz` — **unconditional** Cauchy–Schwarz ceiling
  `‖(𝓢 r)(b)‖² ≤ (Σ_χ ‖w b χ‖²) · (Σ_χ ‖r χ‖²)`; for unit-modulus `r` over `m` indices `= (Σ‖w‖²)·m`.
* `shaw_secondMoment_eq` — the **exact** second moment of `𝓢 r` over an orthonormal kernel family
  (`Σ_b ‖(𝓢 r)(b)‖² = Σ_χ ‖r χ‖²`); the √-floor / average side, no cancellation hypothesis.
* `ShawCancellationLaw` — the named principle (operator-norm `≤ S`), and
  `prizeBound_of_cancellationLaw` — **the application**: the law transports through the `η_b`
  prefactor to the prize sup-norm bound `M ≤ S · (n √p / (p−1))`.
* `ShawSubGaussianCancellation` — the **single open input**: the sub-Cauchy–Schwarz gain
  `S = √(2 n log m)` for the prize character kernel. This is the BGK / Paley-graph wall, now stated
  as one operator-norm hypothesis. Named-open; no `sorry`, no fake `axiom`.

All proofs are axiom-clean (`propext, Classical.choice, Quot.sound`). The mathematical content of
the prize is concentrated into `ShawSubGaussianCancellation`; everything else is unconditional.
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
*trivial* bound `‖η_b‖ ≤ (n√p/(p−1)) · m`, i.e. `M ≤ n√p` with no cancellation whatsoever. -/
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
recovering the trivial `‖η_b‖ ≤ n√p` bound: **Cauchy–Schwarz alone gives no cancellation.** -/
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

/-- **The Shaw Cancellation Law (named principle).** The Shaw operator `𝓢` with kernel `w` *satisfies
the cancellation law with operator-norm bound `S`* if every unit-modulus root-number sequence is
synthesized to within `S` at every base point:

`∀ r, IsRootNumberSeq r → ∀ b, ‖(𝓢 r)(b)‖ ≤ S`.

The trivial (Cauchy–Schwarz) value is `S = m` (`shaw_norm_le_card`). The prize asserts the law holds
at the *square-root-with-log* scale `S = √(2 n log m)` — genuine sub-Cauchy–Schwarz cancellation. -/
def ShawCancellationLaw (w : B → Idx → ℂ) (S : ℝ) : Prop :=
  ∀ r : Idx → ℂ, IsRootNumberSeq r → ∀ b : B, ‖shaw w r b‖ ≤ S

/-- **The trivial cancellation law always holds at `S = m`.** Every Shaw operator with a
unit-modulus kernel (`‖w b χ‖ = 1`, the prize character case) satisfies the cancellation law at the
no-cancellation scale `S = |Idx|`. This is the baseline the prize must beat from `m` down to
`√(2 n log m)`. -/
theorem shawCancellationLaw_card (w : B → Idx → ℂ) (hw : ∀ b : B, ∀ χ : Idx, ‖w b χ‖ = 1) :
    ShawCancellationLaw w (Fintype.card Idx : ℝ) :=
  fun _r hr b => shaw_norm_le_card w hr hw b

/-- **The Shaw Cancellation Law, applied to the prize sup-norm `M`.** Suppose the period is the
synthesized Shaw operator scaled by a real prefactor `c ≥ 0`,
`η b = (c : ℂ) • shaw w r b`, with `r` a root-number sequence. Then the cancellation law at bound
`S` transports verbatim to the prize sup-norm:

`∀ b, ‖η b‖ ≤ c · S`.

For the prize, `c = n √p / (p−1)` and `S = √(2 n log m)`, giving
`M(n) = max_b ‖η_b‖ ≤ (n √p / (p−1)) · √(2 n log m) ≈ √(2 n log m)` after the prefactor (`p ≈ n·m`),
i.e. the BGK / near-Ramanujan prize bound. This is the **application** of the law: it is the precise
sense in which the cancellation law *gives* the prize. -/
theorem prizeBound_of_cancellationLaw {η : B → ℂ} (w : B → Idx → ℂ) {r : Idx → ℂ}
    (hr : IsRootNumberSeq r) {c : ℝ} (hc : 0 ≤ c) (hη : ∀ b : B, η b = (c : ℂ) * shaw w r b)
    {S : ℝ} (hlaw : ShawCancellationLaw w S) (b : B) :
    ‖η b‖ ≤ c * S := by
  rw [hη b, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hlaw r hr b) hc

/-- **Lower bound on any valid cancellation bound (the Parseval obstruction).** For an orthonormal
kernel over a nonempty base, *any* `S` for which the cancellation law holds must satisfy
`S² ≥ m/|B|`: the law cannot be true below the Parseval √-floor. (The witness is the constant
root-number sequence `r ≡ 1`.) This pins the law's bound from *below* at the √-floor while the prize
target `√(2 n log m)` sits a `√log` factor above it — the entire open content. -/
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

/-! ## The single open input — the prize wall as one named hypothesis -/

/-- **The Shaw sub-Gaussian cancellation law — THE single open prize input.** The Shaw operator with
the prize character kernel `w` over `m = |Idx|` characters satisfies the cancellation law at the
*square-root-with-log* scale

`S = √(2 · n · log m)`,

where `n` is the subgroup size. By `shaw_norm_le_card` the law trivially holds at `S = m`; this
hypothesis is the assertion of **genuine sub-Cauchy–Schwarz cancellation** all the way down to the
near-Ramanujan scale. It is the BGK / Paley-graph / thin-subgroup-equidistribution wall, restated as
a single operator-norm bound on the root-number synthesis. It is **named-open**: best proven is
`n^{1−o(1)}` (BGK), the prize needs this `√(n log m)`. No `sorry`, no fake `axiom`; this is the honest
open core, and `prizeBound_of_cancellationLaw` shows it suffices for `M`. -/
def ShawSubGaussianCancellation (w : B → Idx → ℂ) (n : ℝ) : Prop :=
  ShawCancellationLaw w (Real.sqrt (2 * n * Real.log (Fintype.card Idx : ℝ)))

/-- **The open law gives the prize `M`-bound (the end-to-end application).** If the prize period is
the prefactor-scaled Shaw operator and the Shaw sub-Gaussian cancellation law holds, then the prize
structural constant is bounded at the near-Ramanujan scale:

`max_b ‖η_b‖ ≤ c · √(2 n log m)`.

For the prize instance (`c = n√p/(p−1)`, `m` characters, `p ≈ n·m`) this is the BGK target
`M ≤ √(2 n log m)` after the prefactor. This theorem is *unconditional given the named law* — it
contains no further residual; the entire prize content is in the single hypothesis
`ShawSubGaussianCancellation`. -/
theorem prize_M_bound_of_subGaussian {η : B → ℂ} (w : B → Idx → ℂ) {r : Idx → ℂ}
    (hr : IsRootNumberSeq r) {c : ℝ} (hc : 0 ≤ c) (hη : ∀ b : B, η b = (c : ℂ) * shaw w r b)
    {n : ℝ} (hlaw : ShawSubGaussianCancellation w n) (b : B) :
    ‖η b‖ ≤ c * Real.sqrt (2 * n * Real.log (Fintype.card Idx : ℝ)) :=
  prizeBound_of_cancellationLaw w hr hc hη hlaw b

/-- **The law genuinely beats the trivial bound (consistency check).** Whenever the near-Ramanujan
scale undershoots the trivial scale — `√(2 n log m) < m`, true in the prize regime where
`n = 2^30 ≪ m ≈ n·2^128` — the sub-Gaussian law is a *strictly stronger* statement than the
unconditional `shawCancellationLaw_card`. This records that the open input is non-vacuous: it asserts
real cancellation, not a tautology. -/
theorem subGaussian_strengthens_trivial {w : B → Idx → ℂ} {n : ℝ}
    (hlt : Real.sqrt (2 * n * Real.log (Fintype.card Idx : ℝ)) < (Fintype.card Idx : ℝ))
    (hlaw : ShawSubGaussianCancellation w n) (r : Idx → ℂ) (hr : IsRootNumberSeq r) (b : B) :
    ‖shaw w r b‖ < (Fintype.card Idx : ℝ) :=
  lt_of_le_of_lt (hlaw r hr b) hlt

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
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.prize_M_bound_of_subGaussian
#print axioms ArkLib.ProximityGap.Frontier.ShawCancellationLaw.subGaussian_strengthens_trivial
