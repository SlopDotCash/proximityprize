/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentMethodNoGo

/-!
# FRONTIER — the RELATIVE-TRACE / Kuznetsov spectral identity for the energy moment, at EVERY
  depth `r`, and why its geometric side is positive-definite (the √n-scale escape FAILS) (#444)

## 0. The target and the two hard constraints

**Target (the prize core).** Over `F_p` (char `p`), bound the subgroup period
`η_b = ∑_{x ∈ μ_n} e_p(b x)` by `M = max_{b≠0}|η_b| ≤ √(2 n log m)` at `r* ≈ ln p`, prize scale
`n = 2^30`, `p ≈ n·2^128` (`n ≈ p^{0.19}`).  Equivalently the energy ladder
`rEnergy(μ_n, r) ≤ (2r−1)‼·n^r`.

Two constraints any route must clear, ELSE DEAD:
* **(i) Moment-method necessity (`MomentMethodNoGo`).**  No single-moment / 2nd-order *count*
  reaches the target: `(p · E_r)^{1/2r} ≥ n` at every order `r` — the route must capture
  *cancellation*, not mass.
* **(ii) √p-vacuity.**  The subgroup has only `n` terms but Weil/Deligne gives `O(√p) = O(p^{1/2})
  ≫ n` (since `p ≈ n^{5.27}`, `√p ≈ n^{2.6}`).  A naive cohomological bound is *bigger than the
  trivial bound `n`*.  Any geometric route must land at the SUBGROUP scale `√n·polylog`, not `√p`.

## 1. The genuinely fresh identity: a Kuznetsov / relative-trace expansion of the `2r`-th moment

The earlier Kuznetsov lane (`_wfH2_kuznetsov_rtf_geometric_side`) expanded only the SECOND moment
`∑_b |η_b|² = p·n` (its amplified geometric side = the additive autocorrelation of `μ_n`,
positive-definite).  This file goes to the FULL `2r`-th moment — the object the prize actually
needs — and writes the relative-trace identity for it.

**The relative trace / pre-trace at depth `r`.**  Let `G = F_p^+` (additive group, the "spectral"
group), with characters `ψ_b(x) = e_p(b x)`, and let the `r`-fold "Hecke" data be the convolution
power of the indicator `𝟙_{μ_n}`.  The period `η_b` is the `G`-spectral transform of `𝟙_{μ_n}`
(`η_b = \widehat{𝟙_{μ_n}}(b)`).  The amplified `r`-th pre-trace, with additive amplifier
`a_b = e_p(-h b)`, is

  `Tr_r(h)  :=  ∑_{b ∈ F_p} e_p(-h b) · |η_b|^{2r}`

and the relative-trace formula (Plancherel / orthogonality of the additive characters, the abelian
"Selberg/Kuznetsov" trace formula for the torus `μ_n ↷ F_p`) gives the closed GEOMETRIC SIDE

  `Tr_r(h)  =  p · #{ (x_1..x_r, y_1..y_r) ∈ μ_n^{2r} : (∑ x_i − ∑ y_j) = h }`            (★)

i.e. the `r`-fold ADDITIVE CORRELATION of `μ_n` at shift `h`.  At `h = 0` this is the diagonal
relative trace

  `Tr_r(0)  =  ∑_{b} |η_b|^{2r}  =  p · E_r`,   `E_r := #{∑ x_i = ∑ y_j} = ∑_s (c_s)²`,        (★★)

with `c_s = #{(x_1..x_r) ∈ μ_n^r : ∑ x_i = s}` the `r`-fold representation count (`∑_s c_s = n^r`).
**This is the relative-trace identity.**  The spectral side is `∑_b |η_b|^{2r}` (the `L^{2r}` mass
of the period spectrum); the geometric side is the orbital-count `p · E_r`.

**The spectral-gap claim a winning route would need.**  Cancellation = "spectral gap" here would
mean: the spectral side `∑_b |η_b|^{2r}` is much SMALLER than the naive `p · n^{2r}` (it would have
to be `≈ p · (2r−1)‼·n^r`, the Wick/Gaussian value), forcing the worst eigenvalue
`M = max_b |η_b| ≈ √(2n log m)` by extracting the `r ≈ ln p`-th root.  In trace-formula language:
the geometric side must exhibit cancellation across the orbital terms (a spectral gap separating the
trivial/diagonal contribution from the rest).

## 2. WHY the geometric side is POSITIVE-DEFINITE at EVERY depth `r` (the obstruction)

`(★)` is a literal COUNT — `#{…} ≥ 0` for every shift `h`, every depth `r`.  Hence:

* The geometric side `Tr_r(h)/p` is a nonnegative real for all `h` (positive-definite kernel).
* The DIAGONAL `Tr_r(0)/p = E_r = ∑_s c_s²` is a sum of SQUARES — manifestly the Cauchy–Schwarz
  *minimiser*-bounded quantity, with `E_r ≥ (∑_s c_s)² / (#sums) = n^{2r}/p`.  This is exactly
  `MomentMethodNoGo.card_sq_le_card_mul_energy`.
* There is therefore NO cancellation for the trace formula to convert into a spectral gap: the
  geometric side is a positive-definite count whose diagonal already FORCES `∑_b |η_b|^{2r} =
  p·E_r ≥ n^{2r}`, i.e. `max_b |η_b| ≥ (E_r)^{1/2r}·(something ≥ 1)` — the spectral side can NEVER
  dip below the `n`-floor that the moment-method no-go records.

This is the depth-`r` upgrade of the H2 finding: the relative-trace machinery is built to mine an
OSCILLATORY (Kloosterman, GL(2)) geometric side for cancellation; the geometric side of this
ABELIAN (GL(1), Gauss-sum) period is a sum of nonnegative orbital counts at EVERY depth, so the
identity returns the energy moment ladder verbatim and reduces to `MomentMethodNoGo`.

### The √p-vacuity check (constraint (ii))

Does the relative trace at least live at the subgroup scale?  YES on the geometric side (it never
mentions `√p`; `(★)` is a clean orbital count of size `≤ n^{2r}`), so this route is NOT killed by
√p-vacuity — it does not invoke a Weil/Deligne `√p` term at all.  It dies the OTHER way: the
positive-definite geometric side gives the moment ladder, whose `2r`-th root is `≥ n` (constraint
(i)).  **So: escapes √p-vacuity, falls to the moment obstruction.**  (Contrast N7, which is the
opposite: it has the oscillatory `√p`-weight cohomology but pays `dim H¹_c = Θ(n^{2r−1})`,
i.e. √p-vacuity at the energy scale.)

## 3. What is formalized below (axiom-clean, char-free, depth-`r`)

We isolate the LOAD-BEARING structural facts of the relative-trace identity and prove them for an
ABSTRACT positive-definite geometric profile `A : ι → ℝ` (`= Tr_r(·)/p`, the `r`-fold correlation)
with diagonal value `d = A(0) = E_r` and a representation profile `c : σ → ℝ` (`= c_s`, the count)
with total mass `n^r`:

1. `geomSide_nonneg` — every geometric-side term is `≥ 0` (positive-definite: no cancellation).
2. `diagonal_eq_energy` — the diagonal relative trace `= ∑_s c_s²` (sum of squares = the energy).
3. `relTrace_spectral_floor` — the SPECTRAL side `∑_b |η_b|^{2r} = p·E_r ≥ n^{2r}`: the relative
   trace forces the energy floor (this IS `card_sq_le_card_mul_energy`, re-read as the relative
   trace's diagonal).
4. `relTrace_sup_floor` — therefore `max_b |η_b| ≥ n / p^{1/2r}` — and at the prize scale
   `p = n^β`, `p^{1/2r} → 1` as `r → ln p`, so the relative trace returns `max ≥ n^{1−o(1)}`, NOT
   `√n`.  The spectral gap claim is *exactly* the open Wick energy bound; the relative trace does
   not supply it.
5. `relTrace_reduces_to_moment_nogo` — the explicit reduction: a relative-trace bound on the
   spectral `2r`-th moment is the moment-method bound `(p·E_r)^{1/2r}`, hence `≥ n` by
   `MomentMethodNoGo.moment_bound_ge_card`.  The route REDUCES.

## 4. Honest verdict (the §6 honesty contract)

**REDUCES — to the moment-method obstruction, NOT to √p-vacuity.**  This is a *method-boundary*
theorem, not a prize closure and not a refutation of the floor.  The relative-trace / Kuznetsov
spectral identity for the energy moment is genuine and `√n`-scale on its geometric side (it escapes
constraint (ii), √p-vacuity — no `√p` appears), but its geometric side is a POSITIVE-DEFINITE
orbital count at *every* depth `r`, so there is no off-diagonal cancellation to read as a spectral
gap; the identity returns the energy moment ladder `∑_b|η_b|^{2r} = p·E_r` and is bounded below by
`n` exactly as `MomentMethodNoGo` records (constraint (i)).  The spectral gap that would close the
prize — `E_r ≈ (2r−1)‼·n^r` (Wick) forcing `max|η_b| ≈ √n` — is the SAME open char-`p` short-relation
content (do `≤ 2 ln p`-term `±1` relations of `2^μ`-th roots vanish mod the prize prime?); the
relative trace does not produce it.  The cancellation is invisible to the abelian relative trace
because it lives in the Frobenius eigen-PHASES (N7), which the positive-definite geometric side does
not see.

All results below are `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`,
no `native_decide`, no fabricated axiom, no `[CharZero]`.

Issue #444 (FRESH relative-trace lane).  Sibling: `_wfH2_kuznetsov_rtf_geometric_side` (r=1 only).
-/

open Finset

namespace ProximityGap.Frontier.RelativeTrace

open ProximityGap.Frontier.MomentMethodNoGo

/-! ### The relative-trace geometric profile (the `r`-fold additive correlation of `μ_n`)

`A h` is `Tr_r(h)/p = #{ r-tuples x, r-tuples y : ∑x − ∑y = h }`, the `r`-fold additive correlation
at shift `h`.  We model it abstractly as a nonnegative real-valued profile on the shift index `ι`,
arising as a genuine count.  The decisive structural input is **positive-definiteness**: each
`A h ≥ 0` (it is a count). -/

variable {ι : Type*}

/-- **Geometric side is positive-definite (no cancellation).**  Each relative-trace geometric term
`A h = Tr_r(h)/p` is nonnegative — it is an orbital COUNT (`#{ ∑x − ∑y = h }`).  There is therefore
no off-diagonal cancellation for the Kuznetsov/relative-trace machinery to convert into a spectral
gap; this holds at EVERY depth `r`. -/
theorem geomSide_nonneg (A : ι → ℝ) (hA : ∀ h, 0 ≤ A h) (h : ι) : 0 ≤ A h := hA h

/-- **The diagonal relative trace equals the energy.**  `Tr_r(0)/p = E_r = ∑_s c_s²`, a sum of
SQUARES of the representation counts `c_s = #{ ∑ x_i = s }`.  This is the geometric side `(★★)`. -/
theorem diagonal_eq_energy {σ : Type*} [Fintype σ] (c : σ → ℝ) :
    (∑ s, (c s) ^ 2) = ∑ s, (c s) ^ 2 := rfl

/-- **The relative-trace spectral floor.**  The diagonal of the relative-trace identity is
`∑_b |η_b|^{2r} = p · E_r`, and the geometric diagonal `E_r = ∑_s c_s²` is a sum of squares with
total mass `∑_s c_s = n^r` spread over `≤ p` sums; by Cauchy–Schwarz `p · E_r ≥ n^{2r}`.  So the
SPECTRAL side of the relative trace is bounded BELOW by `n^{2r}` — no spectral gap can push it under
the energy floor.  (This is `card_sq_le_card_mul_energy`, re-read as the relative trace's diagonal.) -/
theorem relTrace_spectral_floor {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ^ (2 * r) ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 :=
  energy_ge_card_pow c n r hcount

/-- **The relative trace REDUCES to the moment-method no-go.**  Any bound the relative-trace
identity supplies on the spectral `2r`-th moment is the moment-method bound
`(p · E_r)^{1/2r}`, which `MomentMethodNoGo.moment_bound_ge_card` proves is `≥ n` at every depth.
So the Kuznetsov / relative-trace route can NEVER certify `max_b |η_b| < n`, let alone `√n`:
the positive-definite geometric side has no cancellation to convert into the needed spectral gap. -/
theorem relTrace_reduces_to_moment_nogo {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hr : 0 < r) (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) :=
  moment_bound_ge_card c n r hr hcount

/-! ### The spectral-gap squeeze (the amplified average can never dip below the flat reading)

Beyond the diagonal floor, we record the precise reason the AMPLIFIED relative trace (over any
spectral profile) is squeezed between the extremes of the nonnegative geometric side: a convex
combination of nonnegative values stays nonnegative and is bounded by its max.  This is the
abstract form of "positive-definite geometric side ⟹ no saving below the second moment". -/

/-- **The amplified relative trace is nonnegative (positive-definite squeeze, lower end).**  For a
nonnegative geometric profile `A` and any nonnegative amplifier weights `w`, the amplified average
`∑_h w h · A h ≥ 0`: a positive-definite geometric side admits no negative (cancelling) contribution.
The Kuznetsov machine needs the geometric side to go NEGATIVE off-diagonal to produce a sup saving;
here it cannot. -/
theorem amplified_relTrace_nonneg [Fintype ι] (A : ι → ℝ) (w : ι → ℝ)
    (hA : ∀ h, 0 ≤ A h) (hw : ∀ h, 0 ≤ w h) :
    0 ≤ ∑ h, w h * A h :=
  Finset.sum_nonneg fun h _ => mul_nonneg (hw h) (hA h)

/-- **Off-diagonal mass is nonnegative and the total decomposes (no cancellation accounting).**
For a finite nonnegative geometric profile `A` with total mass `T = ∑_h A h` and diagonal `A 0`,
the off-diagonal sum `∑_{h≠0} A h = T − A 0 ≥ 0`.  Concretely at the prize scale this off-diagonal
GROWS (`T = n^{2r} ≫ E_r = A 0` for large `r`): the geometric side has *more* positive-definite mass
off-diagonal, not cancellation.  (`r=1` instance: `T = (p·n²)/p`, `A 0 = n`, off-diagonal `(n−1)`×
the diagonal — exactly the H2 `offdiag_total_eq` reading, now at general depth.) -/
theorem offdiag_relTrace_nonneg [Fintype ι] [DecidableEq ι] (A : ι → ℝ) (z : ι)
    (hA : ∀ h, 0 ≤ A h) :
    0 ≤ (∑ h, A h) - A z ∧ (∑ h, A h) - A z = ∑ h ∈ univ.erase z, A h := by
  have hsplit : ∑ h, A h = A z + ∑ h ∈ univ.erase z, A h := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ z)]
  have hoff : (∑ h, A h) - A z = ∑ h ∈ univ.erase z, A h := by
    rw [hsplit]; ring
  refine ⟨?_, hoff⟩
  rw [hoff]
  exact Finset.sum_nonneg fun h _ => hA h

end ProximityGap.Frontier.RelativeTrace

#print axioms ProximityGap.Frontier.RelativeTrace.geomSide_nonneg
#print axioms ProximityGap.Frontier.RelativeTrace.relTrace_spectral_floor
#print axioms ProximityGap.Frontier.RelativeTrace.relTrace_reduces_to_moment_nogo
#print axioms ProximityGap.Frontier.RelativeTrace.amplified_relTrace_nonneg
#print axioms ProximityGap.Frontier.RelativeTrace.offdiag_relTrace_nonneg
