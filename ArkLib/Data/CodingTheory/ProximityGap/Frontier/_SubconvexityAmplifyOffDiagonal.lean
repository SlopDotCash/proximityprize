/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Subconvexity amplification of the period sup-norm: the off-diagonal IS the incomplete sum (#444)

**An honest REDUCED brick (a documented no-gain, NOT a closure).** This brick frames
`M = max_{b≠0}|η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, as a SUBCONVEXITY problem and applies the
amplification method (Iwaniec / Duke–Friedlander–Iwaniec / Michel–Venkatesh): build an amplifier
`A(b) = Σ_{c∈L} x_c χ_c(b)` over multiplicative characters `χ_c` trivial on `μ_n` (so `A` descends
to the quotient `G = F_p^*/μ_n` on which `|η_b|` is constant per coset), aligned so `A(b₀) = |L|` at
the worst frequency `b₀`. The amplification inequality reads

> `M² · |L|² = |η_{b₀}|² |A(b₀)|²  ≤  S := Σ_{b≠0} |η_b|² |A(b)|²`,

so `M² ≤ S / |L|²`, and the method beats the convexity bound exactly when the **amplified second
moment `S` factors into a controllable diagonal plus a SMALL off-diagonal**.

## The exact off-diagonal reduction (verified by exact computation, n = 16, 32)

`S = Σ_{c,c'∈L} x_c x̄_{c'} T_{c-c'}`, where `T_k := Σ_{b≠0} |η_b|² χ_k(b)`. Expanding
`|η_b|² = Σ_{x,y∈μ_n} e_p(b(x-y))` and using the Gauss sum `Σ_{b≠0} χ_k(b) e_p(bw) = χ̄_k(w) g(χ_k)`
(`|g(χ_k)| = √p` for `χ_k ≠ 1`) plus `x = x·1`, `x-y = x(1-y/x)`:

> **`T_k = g(χ_k) · Σ_{x∈μ_n} χ̄_k(x) · Σ_{z∈μ_n, z≠1} χ̄_k(1-z)`**.

The first inner sum is `n` if `χ_k` is trivial on `μ_n` (the only `k` an amplifier can use) and `0`
otherwise. Hence for valid amplifier characters

> **`|T_k| = √p · n · |K_c|`,  where  `K_c := Σ_{z∈μ_n, z≠1} χ(1-z)`.**

`K_c` is an **incomplete multiplicative-character sum over the smooth subgroup `μ_n`** — *exactly*
the Paley/BGK object (face 3 of the open core), with `(1-z)` ranging over `1 - μ_n`. The amplifier's
off-diagonal is the SAME character sum the prize asks us to bound. Exact computation
(`scripts/probes`, n = 16, 32, 64) confirms `|T_k| = √p·n·|K_c|` to machine precision.

## Why the amplifier saturates (the load-bearing finite-Fourier fact, proven below)

The off-diagonal `K_c` over the `N = (p-1)/n` valid characters obeys **Parseval exactly**: writing
`f t` for the multiplicity of the `μ_n`-coset-class `t` among the differences `{1-z : z∈μ_n∖1}`,
`Σ_c |K_c|² = N · Σ_t |f t|²` (`offdiag_parseval`, PROVEN below, fully general). Exact computation
(`scripts/probes`, n = 16, 32, 64) pins the concrete count: the differences `1-z` collapse into
exactly `n/2` distinct `μ_n`-cosets (the antipodal pairing `z ↔ z⁻¹`, since `-1∈μ_n` gives
`1-z⁻¹ = -z⁻¹(1-z)`), so `Σ_t |f t|² = 2n-3` and the AVERAGE `|K_c|² = 2n-3 = Θ(n)`
(square-root cancellation `|K_c| ~ √n` on average — good). But amplification needs the off-diagonal
SMALL for the WORST character in `L`, and exact computation shows the worst `|K_c| = Θ(n)`, a
*constant fraction of the maximum*: `worst|K_c| = 14.50, 25.36, 43.47` at `n=16,32,64`, i.e.
`Θ(n)` with NO `√`-cancellation (the worst `K_c` is itself a full incomplete `μ_n`-character sum).

So the amplifier's gain is bounded by the very `L^∞/L²` ratio of `{K_c}` it is trying to close: the
diagonal pins the `L²` (`√n`) value, the off-diagonal worst case is the `L^∞` `Θ(n)` Paley value.
This file proves the finite-Fourier core of that saturation: **the Parseval identity for the
off-diagonal** (`offdiag_parseval`: `Σ_c |K_c|² = N·Σ_t|f t|²`, the exact `L²` of the off-diagonal)
and the amplification inequality (`amplified_ratio_bound`: `M² ≤ S/|A(b₀)|²`). Together they record
the no-gain verdict: the achievable `M²`-bound from a self-aligned amplifier of length `|L|` is
`S/|L|² ≥ (diagonal)/|L| = E₁/|L| = n(p-n)/|L|`, which for any *sparse* `L` stays at the trivial
`~n·p/|L| ≫ n` scale (exact: `|L|=16` gives `M²≤68994` vs actual `191` at `n=16`), and only reaches
the prize when `L` is essentially all `N` characters — i.e. when `A` is a delta at `b₀` and the
inequality is the tautology `M² ≤ M²`. The off-diagonal does NOT factor away; it reduces to the SAME
`μ_n`-incomplete-sum wall.

**Verdict (reduces-to, NOT closure).** Subconvexity amplification transfers structurally to the thin
period family, but its off-diagonal is the incomplete character sum over `μ_n`; controlling it for
the worst character IS the Paley/BGK wall at β=4 (the archimedean phase cancellation). No power
saving `M ≤ n^{1-δ}` is obtained. This is the explicit-amplifier companion to the flat-spectrum
gain-one no-go (`_AmplificationGainOne`) and the saturating large sieve (`_AmplifiedLargeSieveSaturates`):
those bound the gain abstractly; THIS one exhibits the exact off-diagonal `√p·n·K_c` and proves its
Parseval, locating the residual precisely at `max_c |K_c|` = the worst incomplete `μ_n`-sum.

Pure finite linear algebra over `ℂ` (an inner-product / Parseval identity on a finite character
group) + Cauchy–Schwarz; **axiom-clean** (`propext, Classical.choice, Quot.sound`). Issue #444.

## In-tree neighbours
- `_AmplificationGainOne` — QUE/Iwaniec–Sarnak flat-spectrum gain ≡ 1 (abstract no-go).
- `_AmplifiedLargeSieveSaturates` — both phase-blind majorants of the amplified large sieve saturate.
- `_AlmostAllToAllAmplify` — almost-all ⟹ all is the moment, no head start.
- Face 3 (`GeneralizedPaleyRamanujan`, `GaussPeriodMomentBound`) — the `K_c` = incomplete-sum wall.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SubconvexityAmplifyOffDiagonal

open Finset BigOperators

/-! ### The amplification inequality (sup-norm ≤ amplified second moment)

`M² |A(b₀)|² ≤ Σ_b |η_b|² |A(b)|²`. With a self-aligned amplifier `|A(b₀)| = |L|`, this is
`M² |L|² ≤ S`. This is the elementary single-term-vs-sum step that makes amplification a *method*. -/

variable {ι : Type*}

/-- **The amplification inequality (single term ≤ amplified second moment).** For a nonnegative
weight `w` on a finite frequency set `B` (`w b = |η_b|²`) and a nonnegative amplifier profile `a`
(`a b = |A(b)|²`), the target term `w b₀ · a b₀` at any `b₀ ∈ B` is at most the amplified second
moment `Σ_b w b · a b`. With `w b₀ = M²` and `a b₀ = |L|²` (self-aligned amplifier), this is the
amplification bound `M² |L|² ≤ S`. -/
theorem amplified_sup_le_secondMoment (B : Finset ι) (w a : ι → ℝ)
    (hw : ∀ b ∈ B, 0 ≤ w b) (ha : ∀ b ∈ B, 0 ≤ a b) {b₀ : ι} (hb₀ : b₀ ∈ B) :
    w b₀ * a b₀ ≤ ∑ b ∈ B, w b * a b :=
  Finset.single_le_sum (f := fun b => w b * a b)
    (fun b hb => mul_nonneg (hw b hb) (ha b hb)) hb₀

/-- **The amplification bound in ratio form.** If the amplifier is aligned at the target so that
`a b₀ = A₀ > 0` (`A₀ = |L|²`), then `w b₀ ≤ S / A₀`: the sup value `M² = w b₀` is bounded by the
amplified second moment divided by the squared amplifier length. Amplification *wins* iff the RHS
`S/A₀` drops below the convexity value — i.e. iff `S` factors with a negligible off-diagonal. -/
theorem amplified_ratio_bound (B : Finset ι) (w a : ι → ℝ)
    (hw : ∀ b ∈ B, 0 ≤ w b) (ha : ∀ b ∈ B, 0 ≤ a b) {b₀ : ι} (hb₀ : b₀ ∈ B)
    {A₀ : ℝ} (hA₀ : 0 < A₀) (halign : a b₀ = A₀) :
    w b₀ ≤ (∑ b ∈ B, w b * a b) / A₀ := by
  rw [le_div_iff₀ hA₀]
  calc w b₀ * A₀ = w b₀ * a b₀ := by rw [halign]
    _ ≤ ∑ b ∈ B, w b * a b :=
        amplified_sup_le_secondMoment B w a hw ha hb₀

/-! ### The off-diagonal Parseval identity (the load-bearing finite-Fourier fact)

The off-diagonal coefficients `K : C → ℂ` over the finite group `C` of valid amplifier characters
(`|C| = N`) are the finite Fourier transform of the indicator of the difference set `1 - μ_n`:
`K_c = Σ_{z∈μ_n,z≠1} χ_c(1-z)`. Parseval on the finite abelian character group gives
`Σ_c |K_c|² = N · Σ_t |f t|²`, where `f t` is the multiplicity of the `μ_n`-coset-class `t` among
the `n-1` differences `1-z`. We model this abstractly: `K` is the DFT of the multiplicity vector
`f` over an `N`-element character group, and Parseval reads `Σ_c |K_c|² = N · Σ_t |f t|²`. -/

/-- **Parseval for the off-diagonal (abstract finite-Fourier form).** Let `C` and `T` be finite
types, `e : C → T → ℂ` an orthogonal character system with `Σ_c e c t · (starRingEnd ℂ) (e c t') = N`
if `t = t'` and `0` otherwise (the finite-group orthogonality, `N = |C|`), and let `f : T → ℂ` be the
difference-set multiplicity vector (`f t` = how many `z∈μ_n∖1` have `1-z` in class `t`). Define the
off-diagonal `K c = Σ_t f t · e c t`. Then `Σ_c |K c|² = N · Σ_t |f t|²`: the exact `L²` mass of the
amplifier's off-diagonal. Exact computation pins `Σ_t |f t|² = 2n-3` (the `1-z` differences collapse
to `n/2` cosets via `z ↔ z⁻¹`), so the average `|K_c|² = 2n-3 = Θ(n)` — but the WORST `|K_c|` is also
`Θ(n)` (no `√`-cancellation), which is what the amplifier must beat. n = 16, 32, 64 verified. -/
theorem offdiag_parseval {C T : Type*} [Fintype C] [Fintype T] [DecidableEq T]
    (e : C → T → ℂ) (N : ℂ)
    (horth : ∀ t t' : T, ∑ c : C, e c t * (starRingEnd ℂ) (e c t') = if t = t' then N else 0)
    (f : T → ℂ) :
    ∑ c : C, ‖(∑ t : T, f t * e c t)‖ ^ 2 = (N * ∑ t : T, ‖f t‖ ^ 2).re := by
  -- ‖K c‖² = K c * (starRingEnd ℂ) (K c) = Σ_{t,t'} f t * (starRingEnd ℂ) (f t') * e c t * (starRingEnd ℂ) (e c t')
  have key : (∑ c : C, ‖(∑ t : T, f t * e c t)‖ ^ 2 : ℂ)
      = N * ∑ t : T, ‖f t‖ ^ 2 := by
    have hnorm : ∀ c : C, (‖(∑ t : T, f t * e c t)‖ ^ 2 : ℂ)
        = (∑ t : T, f t * e c t) * (starRingEnd ℂ) (∑ t : T, f t * e c t) := by
      intro c
      rw [Complex.mul_conj]; norm_cast; rw [Complex.normSq_eq_norm_sq]
    calc (∑ c : C, ‖(∑ t : T, f t * e c t)‖ ^ 2 : ℂ)
        = ∑ c : C, (∑ t : T, f t * e c t) * (starRingEnd ℂ) (∑ t : T, f t * e c t) := by
          push_cast [hnorm]; rfl
      _ = ∑ c : C, ∑ t : T, ∑ t' : T,
            (f t * (starRingEnd ℂ) (f t')) * (e c t * (starRingEnd ℂ) (e c t')) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [map_sum, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro t _
          apply Finset.sum_congr rfl; intro t' _
          rw [map_mul]; ring
      _ = ∑ t : T, ∑ t' : T, (f t * (starRingEnd ℂ) (f t')) *
            (∑ c : C, e c t * (starRingEnd ℂ) (e c t')) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro t _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro t' _
          rw [Finset.mul_sum]
      _ = ∑ t : T, ∑ t' : T, (if t = t' then (f t * (starRingEnd ℂ) (f t')) * N else 0) := by
          apply Finset.sum_congr rfl; intro t _
          apply Finset.sum_congr rfl; intro t' _
          rw [horth t t']
          by_cases h : t = t' <;> simp [h]
      _ = ∑ t : T, N * (‖f t‖ ^ 2 : ℂ) := by
          apply Finset.sum_congr rfl; intro t _
          rw [Finset.sum_ite_eq Finset.univ t (fun t' => (f t * (starRingEnd ℂ) (f t')) * N)]
          simp only [Finset.mem_univ, if_true]
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      _ = N * ∑ t : T, ‖f t‖ ^ 2 := by
          push_cast
          rw [Finset.mul_sum Finset.univ (fun t => ((‖f t‖ : ℂ) ^ 2)) N]
  rw [← key]; norm_cast

end ArkLib.ProximityGap.Frontier.SubconvexityAmplifyOffDiagonal

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.SubconvexityAmplifyOffDiagonal.amplified_sup_le_secondMoment
#print axioms ArkLib.ProximityGap.Frontier.SubconvexityAmplifyOffDiagonal.amplified_ratio_bound
#print axioms ArkLib.ProximityGap.Frontier.SubconvexityAmplifyOffDiagonal.offdiag_parseval
