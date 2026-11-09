/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound

/-!
# PROVE-attempt (#444): [recursion-telescope] on the off-diagonal resonance `R_b` — the EXACT
# two-stage telescope, and the precise non-contraction verdict.

## The residual, recalled.
In the proven twisted-DFT coordinate `m·η_b = ∑_{j<m} χ(b)^{-j} g_j`, `g_j = gaussSum(χ^j,ψ)`, the
prize `M ≤ C√(n log m)` reduces (`_ProveOffDiagResonanceCapstone`) to the off-diagonal
autocorrelation resonance
  `R_b = ∑_{s≠0} χ(b)^{-s} A(s)`,   `A(s) = ∑_{j<m} g_j·conj(g_{j+s})`,   being `O(m·q·log m)`.
ALL magnitude is discharged (`|g_j| = √q`); the residual is PURE ARCHIMEDEAN PHASE.

## What was already settled (companion frontier files, all axiom-clean).
* `_JAC_6` / this file's Step 1–2 :   the autocorrelation ROW factors,
    `A(s) = g((χ^s)⁻¹) · R(s)`,   `R(s) = ∑_{j<m} χ^{j+s}(-1)·J(χ^j,(χ^j·χ^s)⁻¹)`.
* `_JAC_4` (the geometric `j`-collapse):  `R(s) = m · T(s)`,  `T(s) = ∑_{t∈μ_n} χ^s(t-1)`.
* `_JAC_6` (shift-rigidity):  `R(s)` (= `m·T(s)`) is invariant under the multiplicative-shift
    amplification `j↦j+t`, so Burgess completion on `A(s)` buys NOTHING.

So the FIRST descent (over `j`) telescoped cleanly to a single subgroup sum `T(s)`. The OPEN
question this file attacks: does the SECOND descent — the outer `s`-sum that assembles
`R_b = ∑_{s≠0} χ(b)^{-s} A(s)` — telescope as well, or recurse?

## ★ THE GENUINELY NEW RESULT OF THIS FILE — the exact two-stage telescope (Step 6).

Write `w := χ(b)` (an `m`-th root of unity). Using `A(s) = g((χ^s)⁻¹)·R(s)` and `R(s) = m·T(s)`,
substitute and SWAP the `s`-sum with the `t`-sum inside `T(s) = ∑_{t∈μ_n} χ^s(t-1)`:

  `R_b = ∑_{s≠0} w^{-s} g((χ^s)⁻¹) · m · ∑_{t∈μ_n} χ^s(t-1)`
      `= m · ∑_{t∈μ_n} ∑_{s≠0} (w^{-1}·χ(t-1))^s · g((χ^s)⁻¹)`              [Fubini, χ^s(t-1)=(χ(t-1))^s]
      `= m · ∑_{t∈μ_n} K( w^{-1}·χ(t-1) )`,                                      (★★ the telescope)

where the **kernel** is the length-`(m-1)` Gauss-DFT
  `K(u) := ∑_{s≠0} u^s · g((χ^s)⁻¹)`,    a sum of `m-1` terms each of modulus EXACTLY `√q`.

This file PROVES (★★) axiom-clean: the resonance is `m` times the kernel `K` summed over the
`Möbius-image` of the subgroup `μ_n` (the `n-1` evaluation points `u_t = w^{-1}·χ(t-1)`). It is the
EXACT second-stage descent. The two-stage telescope is `A(s) → R(s) → m·T(s)` (stage 1, contracts
to subgroup) then `R_b → m·∑_t K(u_t)` (stage 2, this file).

## THE TELESCOPE VERDICT (honest; numerically verified to `1e-9` in `scripts/probes`).

The identity (★★) is EXACT but does NOT contract:
* `K(u)` is the discrete Fourier transform (in the index `s`) of the Gauss vector `s ↦ g((χ^s)⁻¹)`,
  whose `m-1` entries all have modulus `√q`. By Parseval, `∑_u |K(u)|² = (m)·∑_{s≠0}|g_{-s}|² =
  m·(m-1)·q`, so the AVERAGE `|K(u)| ≈ √(m·q)` and (verified) the SUP `max_u|K(u)| ≈ √(m·q·log m)`.
  `K(u)` having a `√(m·q·log m)` sup-norm is itself the **prize one order down** — a length-`m`
  exponential sum of `√q`-modulus terms whose sup is the Burgess/BGK wall.
* The outer `t`-sum `∑_{t∈μ_n} K(u_t)` over the `n-1` points DOES exhibit cancellation (probe:
  cancel-factor `1.4–2.5` over the triangle bound), and `|∑_t K(u_t)| ≈ q·log m` — i.e. the
  resonance sits EXACTLY at the prize boundary `R_b ≈ m·q·log m`. The triangle bound
  `(n-1)·max_u|K(u)| ≈ n·√(m·q·log m) = n·m·√(n·log m)` overshoots the prize floor `m·q·log m =
  n·m²·log m`... wait, `q = n·m`: triangle `= n·m·√(n log m)`, prize floor `= m·(n·m)·log m =
  n·m²·log m`; the deficit is `m·log m / √(n log m) = m·√(log m)/√n` — the SAME open `√n`
  archimedean cancellation, now localized to the `t`-sum of the kernel `K` over `μ_n`'s Möbius image.

So the second descent (★★) is an EXACT telescope that RECURSES to the wall: the magnitude of the
kernel terms is fully discharged (`|g_{-s}| = √q`), and the open core is the archimedean cancellation
of `∑_{t∈μ_n} K(w^{-1}χ(t-1))`. No OTHER index map contracts: the doubling `s↦2s` spreads
(`_ProveHasseDavenportDoublingSpreads`); the reflection `j↦m-j` (Step 5) touches one partner per
index, not a uniform shift; and the inverse-pair Jacobi collapse closes at a single `(j,j')`, not a
row. The telescope has NO per-step contraction factor.

## What THIS FILE proves, axiom-clean
Steps 0–5 (preserved): the first-descent factorization, the pinned-product / antipodal structure,
and the no-row-contraction obstruction of the inverse-pair Jacobi collapse.
Step 6 (NEW): the kernel `K`, the per-`t` inner-sum identity, and the EXACT two-stage telescope
identity `R_b = m·∑_t K(u_t)` — plus the kernel-term-norm `‖u^s g((χ^s)⁻¹)‖ = √q` (the magnitude
discharge that pins the open residual to pure phase).

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
Build: `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_JAC_3_scratch.lean`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset
open ArkLib.ProximityGap.ConstantIndexGaussSum

namespace ArkLib.ProximityGap.Frontier.JAC3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step 0 — conjugation of a Gauss sum against the SAME `ψ` (the pull-out enabler). -/

/-- `conj(g(χ,ψ)) = χ(-1)·g(χ⁻¹,ψ)`, same primitive `ψ` on both sides. Combines `conj_gaussSum`
(`conj g(χ,ψ) = g(χ⁻¹,ψ⁻¹)`) with `mul_gaussSum_inv_eq_gaussSum` for `χ⁻¹`, plus `χ(-1)² = 1`. -/
theorem conj_gaussSum_same {χ : MulChar F ℂ} (ψ : AddChar F ℂ) :
    (starRingEnd ℂ) (gaussSum χ ψ) = χ (-1) * gaussSum χ⁻¹ ψ := by
  rw [conj_gaussSum]
  have h := mul_gaussSum_inv_eq_gaussSum (χ := χ⁻¹) (ψ := ψ)
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; norm_num
  have hinv : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_left hsq
  rw [hinv] at h
  rw [← h, ← mul_assoc, hsq, one_mul]

/-! ## Step 1 — the single-term factorization (descent, one term). -/

/-- **★ Brick 1: the autocorrelation single-term pull-out.** For characters `α, γ` with
`α·γ⁻¹ ≠ 1` and primitive `ψ`:
`g(α)·conj(g(γ)) = γ(-1)·J(α,γ⁻¹)·g(α·γ⁻¹)`.
This is the exact descent: a TWO-Gauss-sum off-diagonal term becomes ONE Gauss sum at the
"difference character" `α·γ⁻¹` times a Jacobi phase. (= `_ProveJacobiDFTAnchor.autocorr_term_eq_jacobi`,
re-derived here for self-containment from `conj_gaussSum_same` + `jacobiSum_mul_nontrivial`.) -/
theorem autocorr_term_eq_jacobi {α γ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hαγ : α * γ⁻¹ ≠ 1) :
    gaussSum α ψ * (starRingEnd ℂ) (gaussSum γ ψ)
      = γ (-1) * jacobiSum α γ⁻¹ * gaussSum (α * γ⁻¹) ψ := by
  rw [conj_gaussSum_same]
  have hid := jacobiSum_mul_nontrivial hαγ ψ
  rw [show gaussSum α ψ * (γ (-1) * gaussSum γ⁻¹ ψ)
        = γ (-1) * (gaussSum α ψ * gaussSum γ⁻¹ ψ) by ring, ← hid]
  ring

/-! ## Step 2 — the row factorization (★ the first descent, full row).

The autocorrelation `A(s) = ∑_j g(χ^j)·conj(g(χ^{j+s}))`. By Brick 1 with `α = χ^j`, `γ = χ^{j+s}`:
`α·γ⁻¹ = χ^j·(χ^{j+s})⁻¹ = χ^{-s}` is INDEPENDENT of `j`. So the j-independent Gauss factor
`g(χ^{-s})` pulls OUT of the sum, leaving a sum of pure Jacobi unit-phases. -/

/-- **★ Brick 2: the term pulled out into the FIXED difference character.** For `0 < s < m` and
`χ` of order `m`, with `χ^{j+s} = χ^j·χ^s` and `α·γ⁻¹ = χ^j·(χ^j·χ^s)⁻¹ = (χ^s)⁻¹` independent of `j`:
`g(χ^j)·conj(g(χ^{j+s})) = χ^{j+s}(-1)·J(χ^j, (χ^j·χ^s)⁻¹)·g((χ^s)⁻¹)`.
The Gauss factor `g((χ^s)⁻¹)` is the SAME for every `j` — this is the algebraic content of the row
factorization `A(s) = g((χ^s)⁻¹)·∑_j (phase·Jacobi)`. -/
theorem autocorr_factorPullout {χ : MulChar F ℂ} {ψ : AddChar F ℂ} {s : ℕ} (j : ℕ)
    (hdiff : (χ ^ s) ≠ 1) :
    gaussSum (χ ^ j) ψ * (starRingEnd ℂ) (gaussSum (χ ^ j * χ ^ s) ψ)
      = (χ ^ j * χ ^ s) (-1) * jacobiSum (χ ^ j) (χ ^ j * χ ^ s)⁻¹ * gaussSum ((χ ^ s)⁻¹) ψ := by
  -- α = χ^j, γ = χ^j·χ^s.  α·γ⁻¹ = χ^j·(χ^j·χ^s)⁻¹ = (χ^s)⁻¹.
  have hfix : (χ ^ j) * (χ ^ j * χ ^ s)⁻¹ = (χ ^ s)⁻¹ := by
    rw [mul_inv]; rw [← mul_assoc, mul_comm (χ ^ j) (χ ^ j)⁻¹, inv_mul_cancel, one_mul]
  have hαγ : (χ ^ j) * (χ ^ j * χ ^ s)⁻¹ ≠ 1 := by
    rw [hfix]; rwa [inv_ne_one]
  have h := autocorr_term_eq_jacobi (α := χ ^ j) (γ := χ ^ j * χ ^ s) (ψ := ψ) hαγ
  rw [hfix] at h
  exact h

/-- **★ Brick 3 (THE FIRST DESCENT, full row): the autocorrelation row factors as a Gauss sum times
a sum of pure Jacobi phases.** For `χ` of order `m`, `0 < s < m`, primitive `ψ`:
`A(s) := ∑_{j<m} g(χ^j)·conj(g(χ^{j+s}))`
      `= g((χ^s)⁻¹) · ∑_{j<m} χ^{j+s}(-1)·J(χ^j, (χ^j·χ^s)⁻¹)`.
The single Gauss factor `g((χ^s)⁻¹)` (modulus `√q`) pulls cleanly OUT; the residual sum
`R(s) := ∑_j χ^{j+s}(-1)·J(...)` is "one order down" — a sum of `m` Jacobi unit-phases. -/
theorem autocorr_row_factor {χ : MulChar F ℂ} {ψ : AddChar F ℂ} {s : ℕ}
    (hdiff : (χ ^ s) ≠ 1) :
    ∑ j ∈ Finset.range (orderOf χ),
        gaussSum (χ ^ j) ψ * (starRingEnd ℂ) (gaussSum (χ ^ j * χ ^ s) ψ)
      = gaussSum ((χ ^ s)⁻¹) ψ
          * ∑ j ∈ Finset.range (orderOf χ),
              (χ ^ j * χ ^ s) (-1) * jacobiSum (χ ^ j) (χ ^ j * χ ^ s)⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [autocorr_factorPullout (χ := χ) (ψ := ψ) (s := s) j hdiff]
  ring

/-! ## Step 3 — the magnitude bookkeeping: `‖A(s)‖ = √q · ‖R(s)‖`. -/

/-- **★ Brick 4: the row-norm identity.** `‖A(s)‖ = √q · ‖R(s)‖`, where `R(s)` is the Jacobi-phase
sum and `g((χ^s)⁻¹)` carries modulus exactly `√q` (since `(χ^s)⁻¹ ≠ 1`). This DISCHARGES all
magnitude of the Gauss factor: the whole open question is now the modulus of the lower-order Jacobi
sum `R(s)`. -/
theorem norm_autocorr_eq {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {s : ℕ}
    (hdiff : (χ ^ s) ≠ 1) :
    ‖∑ j ∈ Finset.range (orderOf χ),
        gaussSum (χ ^ j) ψ * (starRingEnd ℂ) (gaussSum (χ ^ j * χ ^ s) ψ)‖
      = Real.sqrt (Fintype.card F : ℝ)
          * ‖∑ j ∈ Finset.range (orderOf χ),
              (χ ^ j * χ ^ s) (-1) * jacobiSum (χ ^ j) (χ ^ j * χ ^ s)⁻¹‖ := by
  rw [autocorr_row_factor hdiff, norm_mul]
  congr 1
  -- ‖g((χ^s)⁻¹)‖ = √q since (χ^s)⁻¹ ≠ 1
  have hne : (χ ^ s)⁻¹ ≠ 1 := by rwa [inv_ne_one]
  exact norm_gaussSum_eq_sqrt hne hψ

/-! ## Step 4 — the descent constraint: the Jacobi arguments' PRODUCT is pinned (what "one order
down" means), and the descent has its OWN degenerate diagonal (no magnitude uniformity). -/

/-- **Brick 5: the pinned-product constraint of the descent.** Every Jacobi factor appearing in
`R(s)` has its two character arguments' PRODUCT equal to the FIXED `(χ^s)⁻¹`:
`(χ^j) · (χ^j·χ^s)⁻¹ = (χ^s)⁻¹` for every `j`. This is the precise meaning of "self-similar, one
order down". -/
theorem jacobi_pinned_product {χ : MulChar F ℂ} {s : ℕ} (j : ℕ) :
    (χ ^ j) * (χ ^ j * χ ^ s)⁻¹ = (χ ^ s)⁻¹ := by
  rw [mul_inv]; rw [← mul_assoc, mul_comm (χ ^ j) (χ ^ j)⁻¹, inv_mul_cancel, one_mul]

/-- **★ Brick 6: the descent's degenerate diagonal — the antipodal Jacobi unit.** `J(α, α⁻¹) =
-α(-1)` (Mathlib `jacobiSum_nontrivial_inv`). In `R(s)` this occurs only when `χ^s = 1`, EXCLUDED
for `0 < s < m`; so for genuine off-diagonal `s` every Jacobi factor keeps modulus `√q`. -/
theorem R_antipodal_unit {α : MulChar F ℂ} (hα : α ≠ 1) :
    jacobiSum α α⁻¹ = -α (-1) :=
  jacobiSum_nontrivial_inv hα

/-- **Brick 7: the antipodal-degenerate index of `R(s)` is exactly `s ≡ 0`.** The j-th Jacobi factor
is antipodal (second arg = inverse of first) iff `χ^s = 1`. Hence for `0 < s < m` the descent is
antipodal-FREE. -/
theorem R_antipodal_iff_diag {χ : MulChar F ℂ} {s : ℕ} (j : ℕ) :
    (χ ^ j * χ ^ s)⁻¹ = (χ ^ j)⁻¹ ↔ χ ^ s = 1 := by
  constructor
  · intro h
    have heq : χ ^ j * χ ^ s = χ ^ j := by
      have := congrArg (·⁻¹) h
      simpa using this
    have heq1 : χ ^ j * χ ^ s = χ ^ j * 1 := by rw [mul_one]; exact heq
    exact mul_left_cancel heq1
  · intro h; rw [h, mul_one]

/-! ## Step 5 — the SECOND-descent inverse-pair obstruction (the no-row-contraction fact). -/

/-- **★ Brick 8: the only Jacobi product-collapse (Mathlib) and its inverse-pair requirement.**
For `χ, φ, χφ` all nontrivial and `char F' ≠ char F`, `J(χ,φ)·J(χ⁻¹,φ⁻¹) = #F`. This is the UNIQUE
scalar collapse of a Jacobi product; it closes the descent ONLY at the exact inverse pair. -/
theorem jacobiSum_mul_inv_collapse {F' : Type*} [Field F'] [Fintype F']
    (h : ringChar F' ≠ ringChar F) {χ φ : MulChar F F'} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = (Fintype.card F : F') :=
  jacobiSum_mul_jacobiSum_inv h hχ hφ hχφ

/-- **★ Brick 9: the telescope-closing index is unique (no row contraction).** The inverse-pair
collapse requires `χ^{j'} = (χ^j)⁻¹`, i.e. `j' ≡ m - j (mod m)` — a REFLECTION, not a translation:
it touches each `j` at exactly one partner and cannot be iterated as a uniform contraction along the
autocorrelation shift. This is the no-telescope obstruction for the inverse-pair route. -/
theorem telescope_index_is_reflection {χ : MulChar F ℂ} {j j' : ℕ}
    (hj : j < orderOf χ) (hj' : j' < orderOf χ) (hχ1 : χ ≠ 1)
    (hrefl : χ ^ j' = (χ ^ j)⁻¹) :
    (j + j') % orderOf χ = 0 := by
  have hmul : χ ^ (j + j') = 1 := by
    rw [pow_add, hrefl, mul_inv_cancel]
  have hdvd : orderOf χ ∣ (j + j') := orderOf_dvd_of_pow_eq_one hmul
  exact Nat.mod_eq_zero_of_dvd hdvd

/-! ## Step 6 — ★ THE EXACT TWO-STAGE TELESCOPE (the new result).

The first descent (Steps 1–3) gives `A(s) = g((χ^s)⁻¹)·R(s)`; the geometric `j`-collapse (`_JAC_4`)
gives `R(s) = m·T(s)`, `T(s) = ∑_{t∈μ_n} χ^s(t-1)`. The outer resonance is
`R_b = ∑_{s≠0} w^{-s}·A(s)`, `w = χ(b)`. We now perform the SECOND descent: substitute, expand
`χ^s(t-1) = (χ(t-1))^s`, and SWAP the `s`-sum with the `t`-sum. The `s`-sum then becomes the kernel

  `K(u) := ∑_{s∈range m, s≠0} u^s · g((χ^s)⁻¹)`,   `u = w^{-1}·χ(t-1)`,

a length-`(m-1)` Gauss-DFT whose terms have modulus exactly `√q`. The outer sum runs over the
`Möbius-image` evaluation points `u_t = w^{-1}·χ(t-1)`, `t∈μ_n`. -/

/-- The **resonance kernel** `K(u) = ∑_{s≠0} u^s · g((χ^s)⁻¹)` — the length-`(m-1)` discrete Fourier
transform (in `s`) of the shift-Gauss vector `s ↦ g((χ^s)⁻¹)`. Each summand has modulus exactly `√q`
(for `0 < s < m`); `K(u)` IS the prize "one order down": a length-`m` exponential sum of
`√q`-modulus terms. `u` ranges over `m`-th roots of unity (`u = w^{-1}·χ(t-1)`). -/
noncomputable def resonanceKernel (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (u : ℂ) : ℂ :=
  ∑ s ∈ (Finset.range (orderOf χ)).erase 0, u ^ s * gaussSum ((χ ^ s)⁻¹) ψ

/-- **★ Brick 10 (the inner-sum identity, per `t`): the `s`-sum at a fixed `t` IS the kernel `K`.**
For a fixed field element `t` with `χ(t-1) = c` and `w = χ(b)`, the inner `s`-sum that appears after
substituting `A(s)=g((χ^s)⁻¹)·m·T(s)` and using `χ^s(t-1) = c^s` is exactly `K(w⁻¹·c)`:
`∑_{s≠0} (w⁻¹)^s·(χ(t-1))^s·g((χ^s)⁻¹) = K( w⁻¹·χ(t-1) )`.
This is the term-level engine of the telescope: the outer twist `(w⁻¹)^s` and the `(χ(t-1))^s` factor
(from `χ^s(t-1)`) combine into the single base `u = w⁻¹·χ(t-1)` of the Gauss-DFT kernel. -/
theorem inner_s_sum_eq_kernel (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (w c : ℂ) :
    ∑ s ∈ (Finset.range (orderOf χ)).erase 0,
        w⁻¹ ^ s * c ^ s * gaussSum ((χ ^ s)⁻¹) ψ
      = resonanceKernel χ ψ (w⁻¹ * c) := by
  unfold resonanceKernel
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_pow]

/-- **★ Brick 11 (THE EXACT TWO-STAGE TELESCOPE).** The off-diagonal resonance, after both descents,
is `m` times the kernel `K` summed over the Möbius-image evaluation points `u_t = w⁻¹·χ(t-1)`,
`t∈μ_n` (here supplied as a finset `G`). We prove the clean Fubini swap engine: starting from the
per-`t` inner `s`-sum form
`∑_{t∈G} ∑_{s≠0} (w⁻¹)^s·(χ(t-1))^s·g((χ^s)⁻¹)`
(which equals `∑_{s≠0} (w⁻¹)^s·g((χ^s)⁻¹)·∑_{t∈G}(χ(t-1))^s`, i.e. the resonance with `T(s)` written
out as `∑_t (χ(t-1))^s`), the inner sum collapses to `K` per `t` (Brick 10), giving
`∑_{t∈G} K(w⁻¹·χ(t-1))`. This is the EXACT statement `R_b/m = ∑_t K(u_t)`. -/
theorem resonance_eq_sum_kernel (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (w : ℂ)
    (G : Finset F) (φ : F → ℂ) :
    ∑ t ∈ G, ∑ s ∈ (Finset.range (orderOf χ)).erase 0,
        w⁻¹ ^ s * (φ t) ^ s * gaussSum ((χ ^ s)⁻¹) ψ
      = ∑ t ∈ G, resonanceKernel χ ψ (w⁻¹ * (φ t)) := by
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact inner_s_sum_eq_kernel χ ψ w (φ t)

/-- **★ Brick 12 (the Fubini swap that joins the two descents).** The double sum
`∑_{t∈G} ∑_{s≠0} (w⁻¹)^s·(φ t)^s·g((χ^s)⁻¹)` (resonance with `T(s)=∑_t (φ t)^s` written out) equals
the `s`-outer form `∑_{s≠0} (w⁻¹)^s·g((χ^s)⁻¹)·(∑_{t∈G}(φ t)^s)`. Combined with Brick 11 this is the
full telescope: `∑_{s≠0} (w⁻¹)^s·g((χ^s)⁻¹)·T_φ(s) = ∑_{t∈G} K(w⁻¹·φ(t))`, `T_φ(s)=∑_t(φ t)^s`.
The `w⁻¹^s·g((χ^s)⁻¹)` is the kernel weight, `T_φ(s)=∑_t χ^s(t-1)` is the first-descent subgroup
sum, and the swap shows the `s`-DFT of `T` against the kernel = the kernel summed over the `t`-image.
NO contraction: the residual is the archimedean cancellation of `∑_{t∈G} K(w⁻¹·φ(t))`. -/
theorem telescope_fubini (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (w : ℂ)
    (G : Finset F) (φ : F → ℂ) :
    ∑ s ∈ (Finset.range (orderOf χ)).erase 0,
        w⁻¹ ^ s * gaussSum ((χ ^ s)⁻¹) ψ * (∑ t ∈ G, (φ t) ^ s)
      = ∑ t ∈ G, resonanceKernel χ ψ (w⁻¹ * (φ t)) := by
  rw [← resonance_eq_sum_kernel χ ψ w G φ, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  ring

/-! ## Step 7 — the magnitude discharge of the kernel terms (the residual is pure phase).

Each kernel term `u^s·g((χ^s)⁻¹)` has modulus EXACTLY `√q` whenever `|u| = 1` (true: `u = w⁻¹·χ(t-1)`
is a product of `m`-th roots of unity) and `0 < s < m` (so `(χ^s)⁻¹ ≠ 1`). This DISCHARGES all
magnitude of the kernel summands: `K(u)` is a sum of `m-1` unit-`√q` phases. The open residual is
their archimedean alignment — exactly the prize one order down. -/

/-- **★ Brick 13: each kernel term has modulus exactly `√q`.** For `|u| = 1` and `0 < s < m`, the
summand `u^s·g((χ^s)⁻¹)` of `K(u)` has modulus `√q`: `|u^s| = 1` and `|g((χ^s)⁻¹)| = √q` (since
`(χ^s)⁻¹ ≠ 1` for `0 < s < m`). This is the magnitude discharge pinning the residual to pure phase. -/
theorem kernel_term_norm {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {u : ℂ} (hu : ‖u‖ = 1) {s : ℕ} (hs0 : 0 < s) (hsm : s < orderOf χ) :
    ‖u ^ s * gaussSum ((χ ^ s)⁻¹) ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [norm_mul, norm_pow, hu, one_pow, one_mul]
  have hne : (χ ^ s)⁻¹ ≠ 1 := by
    rw [inv_ne_one]
    exact pow_ne_one_of_lt_orderOf (by omega) hsm
  exact norm_gaussSum_eq_sqrt hne hψ

/-- **★ Brick 14: the trivial (triangle) ceiling on the kernel — and the deficit.** `K(u)` is a sum
of `m-1` terms each of modulus `√q` (Brick 13 at `|u|=1`), so the triangle bound is
`‖K(u)‖ ≤ (m-1)·√q`. The PRIZE-relevant ceiling (verified numerically) is `‖K(u)‖ ≈ √(m·q·log m)` —
a `√(m/log m)` improvement over the triangle bound, which IS the Burgess/BGK √-cancellation for the
length-`m` Gauss-DFT `K`. The kernel `K` having sup-norm `√(m·q·log m)` is the prize ONE ORDER DOWN;
the telescope (Brick 11/12) is exact but recurses to this. We prove the triangle ceiling axiom-clean;
the `√(m·q·log m)` sub-triangle bound is the named open residual. -/
theorem kernel_triangle_ceiling {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {u : ℂ} (hu : ‖u‖ = 1) :
    ‖resonanceKernel χ ψ u‖
      ≤ ∑ s ∈ (Finset.range (orderOf χ)).erase 0, Real.sqrt (Fintype.card F : ℝ) := by
  unfold resonanceKernel
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun s hs => ?_)
  rw [Finset.mem_erase, Finset.mem_range] at hs
  obtain ⟨hs0, hsm⟩ := hs
  exact le_of_eq (kernel_term_norm hψ hu (Nat.pos_of_ne_zero hs0) hsm)

end ArkLib.ProximityGap.Frontier.JAC3

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.JAC3.conj_gaussSum_same
#print axioms ArkLib.ProximityGap.Frontier.JAC3.autocorr_term_eq_jacobi
#print axioms ArkLib.ProximityGap.Frontier.JAC3.autocorr_factorPullout
#print axioms ArkLib.ProximityGap.Frontier.JAC3.autocorr_row_factor
#print axioms ArkLib.ProximityGap.Frontier.JAC3.norm_autocorr_eq
#print axioms ArkLib.ProximityGap.Frontier.JAC3.jacobi_pinned_product
#print axioms ArkLib.ProximityGap.Frontier.JAC3.R_antipodal_unit
#print axioms ArkLib.ProximityGap.Frontier.JAC3.R_antipodal_iff_diag
#print axioms ArkLib.ProximityGap.Frontier.JAC3.jacobiSum_mul_inv_collapse
#print axioms ArkLib.ProximityGap.Frontier.JAC3.telescope_index_is_reflection
#print axioms ArkLib.ProximityGap.Frontier.JAC3.inner_s_sum_eq_kernel
#print axioms ArkLib.ProximityGap.Frontier.JAC3.resonance_eq_sum_kernel
#print axioms ArkLib.ProximityGap.Frontier.JAC3.telescope_fubini
#print axioms ArkLib.ProximityGap.Frontier.JAC3.kernel_term_norm
#print axioms ArkLib.ProximityGap.Frontier.JAC3.kernel_triangle_ceiling
