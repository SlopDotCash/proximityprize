/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound

/-!
# PROVE-attempt `[second-moment-A]` (#444): the EXACT second moment of the COMPLEX autocorrelation `A(s)`

ANGLE `[second-moment-A]`. The prize residual (proven `_ProveOffDiagResonanceCapstone`) is: the
off-diagonal autocorrelation resonance of the FIXED complex Gauss-sum DFT vector
`g_j = gaussSum(χ^j, ψ)` (`|g_j| = √q` for `j ≠ 0`) is `O(m·q·log m)`, where the autocorrelation is

  `A(s) = ∑_{j<m} g_j · conj(g_{(j+s) mod m})`  — a sum of `m` terms each of modulus EXACTLY `q`.

THE TASK: compute `∑_s |A(s)|²` EXACTLY by Parseval (= a 4th moment of the `g_j`), combine with a
SUP control, and find the exact identity and the gap.

PRIOR `_JAC_1` did the second moment for the *combinatorial real* count `freq`/`autocorr` over `F`
(`∑_δ C_r(δ)² = E_{2r}`). THIS file does it for the **complex** Gauss-sum vector `g_j` over the cyclic
index `ZMod m` — a genuinely different object whose second moment IS the prize complex 4th moment of
the Gauss sums, NOT a phase-free integer additive-energy count (probe-verified: `∑_s|A(s)|²/q²` is
NOT an integer except in trivial `m=3` — the archimedean Jacobi phases carry real content).

## What this file PROVES (genuine new exact sub-steps, all targeted axiom-clean)

PART 1 — the complex Wiener–Khinchin identity (the exact 2nd moment, no √q loss, no analytic input):
* `cyclicAutocorr` / `cyclicConv` — the complex cyclic cross-correlation `A(s) = ∑_j g_j conj(g_{j+s})`
  and convolution `Conv(d) = ∑_j g_j g_{d-j}`, indexed over the cyclic group `ZMod m`.
* `sum_normSq_autocorr_eq_sum_normSq_conv` (★) — **the complex Wiener–Khinchin core**:
  `∑_s |A(s)|² = ∑_d |Conv(d)|²`, proven EXACTLY by the explicit linear-shear bijection
  `(s, j, j') ↦ (j + j' + s, j, j + s)` on `(ZMod m)³` (cross-correlation ℓ² = convolution ℓ², no
  Fourier, no √q loss). This is the complex analog of `_JAC_1.sum_corr_sq_eq_sum_conv_sq`.
* `autocorr_zero_eq_sum_normSq` — the diagonal `A(0) = ∑_j |g_j|²` (the Parseval floor, real ≥ 0).

PART 2 — the SUP control and the EXACT GAP (the honest verdict the angle forces):
* `normSq_autocorr_le_offdiag_sum` — **L²→sup**: for every `s ≠ 0`, `|A(s)|² ≤ ∑_{t≠0} |A(t)|²` (the
  single off-diagonal term is at most the off-diagonal L² mass). This is the only SUP control the 2nd
  moment supplies, and it costs the full off-diagonal mass: `max_{s≠0}|A(s)| ≤ √(off-diag L²)`.
* `offdiag_l2_eq` — `∑_{s≠0}|A(s)|² = (∑_d|Conv(d)|²) − |A(0)|²` (peel the diagonal from the total).

## EXACT RESIDUAL (stated, NOT closed) — does it SHRINK or RECURSE?

It **RECURSES to the trivial Parseval ceiling, off by √m** (probe-verified). The off-diagonal L²
mass is `∑_{s≠0}|A(s)|² ≈ (m−1)·(q√n)² = (m−1)·q²·n` (probe ratio ∈ [0.7, 2.0], slowly growing with
the same `√log m` excess). So the only SUP bound the 2nd moment yields is
`max_{s≠0}|A(s)| ≤ √(∑_{s≠0}|A(s)|²) ≈ √m·q·√n = q·√(mn) = q·√q` — **the trivial √q ceiling**, a `√m`
factor ABOVE the prize `max|A(s)| = O(q√(n log m))`. The exact 2nd moment forces only the *average*
off-diagonal small (the L² is `(m−1)×` the per-shift prize square); it says nothing about coherent
SUP alignment. Squeezing the L²→sup gap from `√(m−1)` to `√(log m)` IS the wall: it asks that the `m`
off-diagonal autocorrelations be near-equal (flat power spectrum), which is the BGK/Paley
phase-cancellation statement itself, NOT implied by the L² total.

NET: the second-moment angle is EXACT (the complex Wiener–Khinchin `∑_s|A(s)|² = ∑_d|Conv(d)|²` is a
genuine new identity with no √q loss), but it recurses to the wall: the L²→sup Cauchy–Schwarz loses
exactly the `√m` the prize must save. This file makes that gap EXACT. NOT a closure.

Axiom target: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
Build: `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_JAC_1_scratch.lean`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset
open scoped ComplexConjugate

namespace ArkLib.ProximityGap.Frontier.JAC1SecondMoment

/-! ## Part 1 — the complex cyclic cross-correlation, convolution, and the Wiener–Khinchin identity.

We work with an arbitrary complex vector `g : ZMod m → ℂ` (the Gauss-sum vector `g_j` is the
intended instance `g j = gaussSum (χ^(j.val)) ψ`). All cyclic shifts are addition in the finite
abelian group `ZMod m`, which makes the shear bijection clean (no `% m` bookkeeping). `m` must be
positive so that `ZMod m` is a `Fintype` (`NeZero m`). -/

variable {m : ℕ} [NeZero m]

/-- The complex cyclic cross-correlation (autocorrelation) at shift `s`:
`A(s) = ∑_j g_j · conj(g_{j+s})`. (For the Gauss-sum vector this is the off-diagonal autocorrelation
of the twisted-DFT coordinate, each summand of modulus `q`.) -/
noncomputable def cyclicAutocorr (g : ZMod m → ℂ) (s : ZMod m) : ℂ :=
  ∑ j : ZMod m, g j * conj (g (j + s))

/-- The complex cyclic convolution at index `d`: `Conv(d) = ∑_j g_j · g_{d−j}` (NO conjugation). -/
noncomputable def cyclicConv (g : ZMod m → ℂ) (d : ZMod m) : ℂ :=
  ∑ j : ZMod m, g j * g (d - j)

/-- **★ The complex Wiener–Khinchin identity: `∑_s |A(s)|² = ∑_d |Conv(d)|²`.**

For ANY complex vector `g : ZMod m → ℂ`, the second moment of the cyclic cross-correlation equals the
second moment of the cyclic convolution:

> `∑_s ‖A(s)‖² = ∑_d ‖Conv(d)‖²`.

This is the EXACT 2nd-moment Parseval identity for the COMPLEX autocorrelation (both equal
`(1/m)∑_t|ĝ(t)|⁴`, the 4th moment of the DFT), proven here EXACTLY by an explicit termwise linear
shear `(s, j, j') ↦ (j + j' + s, j, j + s)` on `(ZMod m)³` — NO Fourier, NO √q loss. Expanding both
sides over `(ZMod m)³`:
`‖A(s)‖² = ∑_{j,j'} g_j conj(g_{j+s}) conj(g_{j'}) g_{j'+s}` and
`‖Conv(d)‖² = ∑_{a,a'} g_a g_{d−a} conj(g_{a'}) conj(g_{d−a'})`;
the shear sends the cross-correlation cell to the convolution cell bijectively. This is the complex
analog of `_JAC_1.sum_corr_sq_eq_sum_conv_sq` (which handled the real count function). -/
theorem sum_normSq_autocorr_eq_sum_normSq_conv (g : ZMod m → ℂ) :
    ∑ s : ZMod m, ‖cyclicAutocorr g s‖ ^ 2 = ∑ d : ZMod m, ‖cyclicConv g d‖ ^ 2 := by
  -- Cast each `‖·‖²` to the COMPLEX `normSq`, prove the complex identity, cast back. The complex
  -- identity unfolds both sides to 3-fold sums over (ZMod m)³ and matches them by a shear bijection.
  have hcast : ∀ (z : ℂ), (‖z‖ ^ 2 : ℝ) = (Complex.normSq z : ℝ) := fun z =>
    (Complex.normSq_eq_norm_sq z).symm
  -- Reduce to the complex-valued identity by casting both sides through ℝ → ℂ.
  rw [show (∑ s : ZMod m, ‖cyclicAutocorr g s‖ ^ 2)
        = ∑ s : ZMod m, (Complex.normSq (cyclicAutocorr g s) : ℝ) from
      Finset.sum_congr rfl (fun s _ => hcast _),
    show (∑ d : ZMod m, ‖cyclicConv g d‖ ^ 2)
        = ∑ d : ZMod m, (Complex.normSq (cyclicConv g d) : ℝ) from
      Finset.sum_congr rfl (fun d _ => hcast _)]
  -- It suffices to prove the equality after the (injective) coercion ℝ → ℂ.
  have key : ∑ s : ZMod m, (Complex.normSq (cyclicAutocorr g s) : ℂ)
      = ∑ d : ZMod m, (Complex.normSq (cyclicConv g d) : ℂ) := by
    -- LHS: normSq(A s) = conj(A s)·(A s); unfold A s, distribute to a nested ∑_{j'} ∑_j, package
    -- the whole thing as a single sum over the triple type (s, j', j) : (ZMod m)³.
    have hLHS : ∑ s : ZMod m, (Complex.normSq (cyclicAutocorr g s) : ℂ)
        = ∑ p : ZMod m × ZMod m × ZMod m,
            conj (g p.2.1 * conj (g (p.2.1 + p.1))) * (g p.2.2 * conj (g (p.2.2 + p.1))) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Complex.normSq_eq_conj_mul_self]
      unfold cyclicAutocorr
      rw [map_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
    have hRHS : ∑ d : ZMod m, (Complex.normSq (cyclicConv g d) : ℂ)
        = ∑ q : ZMod m × ZMod m × ZMod m,
            conj (g q.2.1 * g (q.1 - q.2.1)) * (g q.2.2 * g (q.1 - q.2.2)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Complex.normSq_eq_conj_mul_self]
      unfold cyclicConv
      rw [map_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
    rw [hLHS, hRHS]
    -- The shear bijection on (ZMod m)³ : (s, j', j) ↦ (j' + j + s, j', j' + s).
    -- (here p.1 = s, p.2.1 = j' [conj index], p.2.2 = j [non-conj index]).
    let φ : ZMod m × ZMod m × ZMod m ≃ ZMod m × ZMod m × ZMod m :=
      { toFun := fun p => (p.2.1 + p.2.2 + p.1, p.2.1, p.2.1 + p.1)
        invFun := fun q => (q.2.2 - q.2.1, q.2.1, q.1 - q.2.2)
        left_inv := by
          rintro ⟨s, j', j⟩
          refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring
        right_inv := by
          rintro ⟨d, a', a⟩
          refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring }
    refine Fintype.sum_equiv φ _ _ ?_
    rintro ⟨s, j', j⟩
    -- φ (s,j',j) = (j'+j+s, j', j'+s); at q = φ(s,j',j):
    --   q.1 = j'+j+s, q.2.1 = j', q.1 - q.2.1 = j+s, q.2.2 = j'+s, q.1 - q.2.2 = j.
    show conj (g j' * conj (g (j' + s))) * (g j * conj (g (j + s)))
        = conj (g j' * g (j' + j + s - j')) * (g (j' + s) * g (j' + j + s - (j' + s)))
    rw [show j' + j + s - j' = j + s by ring, show j' + j + s - (j' + s) = j by ring]
    simp only [map_mul, Complex.conj_conj]
    ring
  -- Cast `key` back to ℝ.
  have := congrArg Complex.re key
  simpa only [Complex.re_sum, Complex.ofReal_re] using this

/-- **The diagonal autocorrelation is the Parseval floor: `A(0) = ∑_j ‖g_j‖²`** (real, ≥ 0).
The `s = 0` cyclic shift is the identity, so each diagonal term is `g_j · conj(g_j) = ‖g_j‖²`. For the
Gauss-sum vector this is `(m−1)q + 1` (the `j ≠ 0` entries contribute `q`, the DC entry `g_0 = -1`
contributes `1`). It is the dominant term of `∑_s|A(s)|²`. -/
theorem autocorr_zero_eq_sum_normSq (g : ZMod m → ℂ) :
    cyclicAutocorr g 0 = ∑ j : ZMod m, (‖g j‖ ^ 2 : ℂ) := by
  unfold cyclicAutocorr
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-! ## Part 2 — the SUP control and the EXACT GAP.

The 2nd moment supplies exactly one form of SUP control: any single off-diagonal `|A(s)|²` is bounded
by the off-diagonal L² total. Bounding the SUP this way costs `√(off-diag L²) ≈ √m·q·√n` — the
trivial √q ceiling, `√m` above the prize. We prove the L²→sup inequality and the exact off-diagonal
L² identity, then state the gap as a named residual. -/

/-- **★ L²→sup: a single off-diagonal autocorrelation is bounded by the off-diagonal L² mass.**
For every `s ≠ 0`, `‖A(s)‖² ≤ ∑_{t ∈ univ.erase 0} ‖A(t)‖²`. This is the ONLY SUP control the second
moment supplies; it gives `max_{s≠0}‖A(s)‖ ≤ √(off-diag L²)`. (A single nonneg term is at most the
sum of nonneg terms over a finset containing it.) -/
theorem normSq_autocorr_le_offdiag_sum (g : ZMod m → ℂ) {s : ZMod m} (hs : s ≠ 0) :
    ‖cyclicAutocorr g s‖ ^ 2 ≤ ∑ t ∈ (univ.erase (0 : ZMod m)), ‖cyclicAutocorr g t‖ ^ 2 := by
  refine Finset.single_le_sum (f := fun t => ‖cyclicAutocorr g t‖ ^ 2) (fun t _ => by positivity) ?_
  exact Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩

/-- **The off-diagonal L² mass: `∑_{s≠0}‖A(s)‖² = (∑_d‖Conv(d)‖²) − ‖A(0)‖²`.**
Peel the `s = 0` diagonal from the total `∑_s‖A(s)‖² = ∑_d‖Conv(d)‖²` (Wiener–Khinchin). The diagonal
`‖A(0)‖²` is the square of the Parseval floor `(∑_j‖g_j‖²)²`. -/
theorem offdiag_l2_eq (g : ZMod m → ℂ) :
    ∑ s ∈ (univ.erase (0 : ZMod m)), ‖cyclicAutocorr g s‖ ^ 2
      = (∑ d : ZMod m, ‖cyclicConv g d‖ ^ 2) - ‖cyclicAutocorr g 0‖ ^ 2 := by
  have htot : ∑ s : ZMod m, ‖cyclicAutocorr g s‖ ^ 2 = ∑ d : ZMod m, ‖cyclicConv g d‖ ^ 2 :=
    sum_normSq_autocorr_eq_sum_normSq_conv g
  have hsplit : ∑ s : ZMod m, ‖cyclicAutocorr g s‖ ^ 2
      = ‖cyclicAutocorr g 0‖ ^ 2 + ∑ s ∈ (univ.erase (0 : ZMod m)), ‖cyclicAutocorr g s‖ ^ 2 :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ 0)).symm
  rw [htot] at hsplit
  linarith [hsplit]

/-- **★ The SUP bound the second moment delivers: `max_{s≠0}‖A(s)‖² ≤ (∑_d‖Conv(d)‖²) − ‖A(0)‖²`.**
Combining the L²→sup inequality with the off-diagonal L² identity: for every `s ≠ 0`,
`‖A(s)‖² ≤ (∑_d‖Conv(d)‖²) − ‖A(0)‖²`. This is the complete, EXACT output of the [second-moment-A]
angle: the per-shift autocorrelation square is bounded by the off-diagonal L² mass. The probe shows
this mass is `≈ (m−1)·q²·n`, so the bound reads `‖A(s)‖² ≤ (m−1)·q²·n`, i.e.
`‖A(s)‖ ≤ √(m−1)·q·√n` — the trivial √q ceiling, `√(m−1)` ABOVE the prize `q·√(n log m)`. -/
theorem normSq_autocorr_le_total_sub_diag (g : ZMod m → ℂ) {s : ZMod m} (hs : s ≠ 0) :
    ‖cyclicAutocorr g s‖ ^ 2
      ≤ (∑ d : ZMod m, ‖cyclicConv g d‖ ^ 2) - ‖cyclicAutocorr g 0‖ ^ 2 := by
  rw [← offdiag_l2_eq g]
  exact normSq_autocorr_le_offdiag_sum g hs

/-! ## The named residual (the wall: the L²→sup `√m` gap).

The second moment is EXACT and phase-free for the TOTAL, but the SUP it controls is via Cauchy–Schwarz
over the `m−1` off-diagonal shifts, losing `√(m−1)`. The prize needs the off-diagonal autocorrelations
to be near-FLAT (each `≈` the L² average `√((m−1)q²n)/√(m−1) = q√n`, up to `√log m`) — a power-spectrum
flatness that is the BGK/Paley phase-cancellation statement, NOT implied by the L² total. We name it. -/

/-- **The named residual (the L²→sup gap = the wall).** `AutocorrL2SupGap C g` asserts the
off-diagonal autocorrelations are near-flat: every `‖A(s)‖²` (`s ≠ 0`) is within `C·log m` of the L²
average `(off-diag L²)/(m−1)`, i.e. `(m−1)·‖A(s)‖² ≤ C·log m·(off-diag L²)`. Equivalently, the prize
`max_{s≠0}‖A(s)‖ ≤ √(C log m)·(L² average per shift) = √(C log m)·q·√n`. This is OPEN (= the
power-spectrum flatness of the Gauss-sum autocorrelation = BGK/Paley); the 2nd moment supplies only
the trivial `C·(m−1)` (every term ≤ the whole L²), losing the `√m`. -/
def AutocorrL2SupGap (C : ℝ) (g : ZMod m → ℂ) : Prop :=
  ∀ s : ZMod m, s ≠ 0 →
    ((m : ℝ) - 1) * ‖cyclicAutocorr g s‖ ^ 2
      ≤ C * Real.log m * (∑ t ∈ (univ.erase (0 : ZMod m)), ‖cyclicAutocorr g t‖ ^ 2)

/-- **The residual SUFFICES to beat the trivial ceiling (sufficiency bridge, axiom-clean modulo the
named residual).** Assuming `AutocorrL2SupGap C` with `2 ≤ m`, every off-diagonal autocorrelation
square obeys the per-shift PRIZE-shape bound

> `‖A(s)‖² ≤ (C·log m / (m−1)) · (off-diag L²)`,

i.e. the off-diagonal L² mass DIVIDED by the number of shifts (the average per shift) times the
`log m` slack — the `√m`-removed bound. With the probe-measured `off-diag L² ≈ (m−1)·q²·n`, this reads
`‖A(s)‖² ≤ C·log m·q²·n`, i.e. `‖A(s)‖ ≤ √C·q·√(n log m)` — the PRIZE per-shift bound. So the residual
is exactly the `√(m−1) → √log m` contraction of the trivial L²→sup step (`normSq_autocorr_le_total_sub_diag`);
this brick shows it suffices and isolates it. Proven by dividing the `AutocorrL2SupGap` inequality by
`m − 1 > 0`. -/
theorem normSq_autocorr_le_of_gap {C : ℝ} (g : ZMod m → ℂ) (hm : 2 ≤ m)
    (hgap : AutocorrL2SupGap C g) {s : ZMod m} (hs : s ≠ 0) :
    ‖cyclicAutocorr g s‖ ^ 2
      ≤ (C * Real.log m / ((m : ℝ) - 1))
          * (∑ t ∈ (univ.erase (0 : ZMod m)), ‖cyclicAutocorr g t‖ ^ 2) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hraw := hgap s hs
  rw [div_mul_eq_mul_div, le_div_iff₀ hm1]
  calc ‖cyclicAutocorr g s‖ ^ 2 * ((m : ℝ) - 1)
      = ((m : ℝ) - 1) * ‖cyclicAutocorr g s‖ ^ 2 := by ring
    _ ≤ C * Real.log m * (∑ t ∈ (univ.erase (0 : ZMod m)), ‖cyclicAutocorr g t‖ ^ 2) := hraw

end ArkLib.ProximityGap.Frontier.JAC1SecondMoment

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JAC1SecondMoment.sum_normSq_autocorr_eq_sum_normSq_conv
#print axioms ArkLib.ProximityGap.Frontier.JAC1SecondMoment.autocorr_zero_eq_sum_normSq
#print axioms ArkLib.ProximityGap.Frontier.JAC1SecondMoment.normSq_autocorr_le_offdiag_sum
#print axioms ArkLib.ProximityGap.Frontier.JAC1SecondMoment.offdiag_l2_eq
#print axioms ArkLib.ProximityGap.Frontier.JAC1SecondMoment.normSq_autocorr_le_total_sub_diag
#print axioms ArkLib.ProximityGap.Frontier.JAC1SecondMoment.normSq_autocorr_le_of_gap
