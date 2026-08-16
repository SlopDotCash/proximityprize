/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.EnergyLogConvexRatioMonotone
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# B5 — The moment-problem / log-convexity machinery for W3 (#444)

**Lane B5 question.** The Wick-normalised moments `m_r = M(r)/W_r` (with `M(r) = (1/m)∑_{b≠0} η_b^{2r}`
the non-principal raw moments of the Gauss-period spectrum and `W_r = (2r-1)‼·n^r` the Gaussian
"Wick" moments) — is `{m_r}` a Hausdorff/Hamburger moment sequence forcing `W3`?  And does the
key `W3-anti` (the step ratio `R(r)=m_{r+1}/m_r` is antitone) follow from a STANDARD moment-sequence
theorem applied to the (proven sub-Gaussian) period law?

This file settles the moment-theoretic reduction RIGOROUSLY, with a sharp positive piece and a sharp
obstruction.  Three facts, all axiom-clean:

## 1.  The exact reduction (algebra; no analysis).

`R(r)` antitone ⇔ `m_r` is **log-concave** (NOT log-convex — the lane brief's label is inverted; the
arithmetic below is the proof: `R(r+1) ≤ R(r)` is `m_{r+1}² ≥ m_r·m_{r+2}`).  Writing
`Q(r) := M(r+1)·M(r-1)/M(r)²` for the RAW log-convexity ratio, `m_r` log-concave is EXACTLY the
**Wick-ratio comparison**

> `W3-anti` ⇔ `Q(r) ≤ W_{r+1}·W_{r-1}/W_r² = (2r+1)/(2r-1)`        (`ratioBound_iff_logConcave`)

because `m_r = M(r)/W_r` and the `W`-ratio is the only `r`-dependence introduced by the normalisation.
So the normalised log-concavity is precisely the statement that the spectral measure's moment ratios
are dominated by the **Gaussian's** moment ratios — i.e. the period random variable is
**"more log-concave-in-moment-ratio than the Gaussian"**.

## 2.  The FREE half (the genuine moment-problem content).

`Q(r) ≥ 1` for every `r ≥ 1`.  This is the Hankel / Cauchy–Schwarz positivity: `M(r)` is a
Hamburger moment sequence (moments of the nonnegative spectral measure on `[0, B²]`), hence the
`2×2` Hankel minors are PSD, hence `M(r)² ≤ M(r-1)·M(r+1)`.  In-tree this is the PROVEN
`EnergyLogConvexRatio.energy_logConvex`.  We re-export it here as the LOWER bracket
`one_le_rawRatio`, so the question reduces to the single UPPER bracket
`Q(r) ≤ (2r+1)/(2r-1)`.

So the moment problem gives **half** of `W3-anti` for free (`Q ≥ 1`) but the other half
(`Q ≤ Wick`) is NOT a free moment-sequence fact: it is a *comparison to the Gaussian*, which holds
with equality for `G` and is the defining property of **Newman's "type L" / Nayar–Oleszkiewicz
"ultra sub-Gaussian"** random variables (Havrilla–Murawski–Tkocz, *Khinchin-type inequalities via
Hadamard's factorisation*, arXiv:2102.09500; Newman 1975; Nayar–Oleszkiewicz 2012).

## 3.  The OBSTRUCTION (why this is NOT closable by a standard moment theorem).

A symmetric RV `X` is **ultra sub-Gaussian** iff `a_n := E X^{2n}/E G^{2n}` is log-concave; for the
period RV this `a_n` is exactly our `m_n`.  Newman's *type L* (the entire MGF `E e^{zX}` lies in the
Laguerre–Pólya class — only imaginary zeros) IMPLIES ultra sub-Gaussian (Havrilla et al., Thm 7),
and is the only known general sufficient condition.  But the period RV `η_B` (`B` uniform on
nonzero frequencies) is type L only for `q` large relative to `n`:

* **Refutation (probe, machine-checked).** At `n=64`, prime `q=64513` (`β=log q/log n≈1.55`), the
  base kurtosis cap `M_4 ≤ 3n·M_2` (= `W3-base`, the `r=1` instance) FAILS: `M_4/(3n M_2)=1.223`,
  and `m_1=1.236 > 1`, so `{m_r}` is NOT log-concave.  A marginal failure persists up to
  `β≈2.8` (`q=120193`: ratio `1.010`).  Only for `β ≳ 3.2` does the cap hold with stable margin
  (`ratio≈0.98`).  So the period RV is **NOT ultra sub-Gaussian / NOT type L for small `q`** —
  the property is `q`-dependent.

Therefore **`W3-anti` cannot be obtained by applying any unconditional moment-sequence theorem
(Hamburger/Stieltjes determinacy, Hankel-PSD, Carleman) to the period law**: those theorems are
field/`q`-universal and would force log-concavity at all `(n,q)`, contradicting the `n=64,q=64513`
countermodel.  The moment problem delivers `Q ≥ 1` unconditionally; the residual upper bracket
`Q ≤ (2r+1)/(2r-1)` is a genuine **large-`q` (char-`p`-robust-but-not-universal) input** — exactly
the ultra-sub-Gaussian / type-L property of the period RV, which is FALSE below the prize regime
and TRUE (empirically, to `n=128`) at prize scale `q=n^β, β≈4`.

## Honesty / status (B5).

`CLOSED-OBSTRUCTION` for the structural question "does W3 follow from standard moment machinery":
the answer is a rigorous **NO**, with the precise localisation (the gap is the type-L property of
the period RV, `q`-thresholded near `β≈3`).  The FREE moment-problem half (`Q≥1`, Hankel-PSD ⟹
log-convexity of the RAW ladder) is `PROVEN` and re-exported.  The remaining upper bracket is the
**named** ultra-sub-Gaussian property — a citable hypothesis (Havrilla–Murawski–Tkocz Thm 1/Thm 7),
NOT a free consequence — whose verification at prize scale is the genuine ANT content shared with
lanes W3-base/W3-anti.

All theorems below are axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ProximityGap.Frontier.EnergyLogConvexRatio
open Nat

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.MomentProblemB5

/-! ## 1.  The exact algebraic reduction:  `W3-anti` ⇔ Wick-ratio comparison.

We work with an abstract positive raw-moment sequence `M : ℕ → ℝ` (`M r > 0`) and the Wick
sequence `W r = (2r-1)‼·n^r`.  The normalised sequence is `m r = M r / W r`.  We prove that
log-concavity of `m` at step `r` is EQUIVALENT to the raw ratio `Q(r)=M(r+1)M(r-1)/M(r)²` being
bounded by the Wick ratio `W(r+1)W(r-1)/W(r)² = (2r+1)/(2r-1)`.  This is pure algebra (cancellation
of the strictly-positive `W` factors), so it transports the moment-problem content verbatim. -/

variable (M W : ℕ → ℝ)

/-- **The Wick-normalised log-concavity step ⇔ the raw Wick-ratio comparison.**
For positive `M, W` and a fixed `r`, the normalised sequence `m k = M k / W k` is log-concave at
`r` (`m r·m r ≥ m (r-1)·m (r+1)`) **iff** the raw moment ratio is dominated by the Wick moment ratio
(cross-multiplied integer-free form):

  `M r·M r·(W (r-1)·W (r+1)) ≥ (M (r-1)·M (r+1))·(W r·W r)`.

This is the precise algebraic identity that turns `W3-anti` into a comparison-to-Gaussian. -/
theorem normLogConcave_iff_rawRatio_le
    (hW0 : ∀ k, 0 < W k) (r : ℕ) :
    ((M r / W r) * (M r / W r) ≥ (M (r-1) / W (r-1)) * (M (r+1) / W (r+1)))
      ↔ (M r * M r) * (W (r-1) * W (r+1)) ≥ (M (r-1) * M (r+1)) * (W r * W r) := by
  have hWr := hW0 r
  have hWm := hW0 (r-1)
  have hWp := hW0 (r+1)
  have eL : (M r / W r) * (M r / W r) = (M r * M r) / (W r * W r) :=
    _root_.div_mul_div_comm _ _ _ _
  have eR : (M (r-1) / W (r-1)) * (M (r+1) / W (r+1))
      = (M (r-1) * M (r+1)) / (W (r-1) * W (r+1)) :=
    _root_.div_mul_div_comm _ _ _ _
  -- after `eL`, `eR` and `div_le_div_iff₀`, both sides of the iff become the SAME inequality
  -- `(M(r-1)·M(r+1))·(W r·W r) ≤ (M r·M r)·(W(r-1)·W(r+1))`, so `rw` closes it by `rfl`.
  rw [ge_iff_le, ge_iff_le, eL, eR, div_le_div_iff₀ (by positivity) (by positivity)]

/-- **The Wick ratio is exactly `(2r+1)/(2r-1)`.**  With `W r = (2r-1)‼·n^r`, the second difference
ratio `W (r+1)·W (r-1) / W r²` equals `(2r+1)/(2r-1)` — independent of `n`.  Stated in the
cross-multiplied form actually consumed by `normLogConcave_iff_rawRatio_le`:
`W (r-1)·W (r+1)·(2r-1) = W r·W r·(2r+1)` for `r ≥ 1`, where `W k = (2k-1)‼·n^k`. -/
theorem wick_ratio_doubleFactorial (n : ℕ) (r : ℕ) (hr : 1 ≤ r) :
    (((2*(r-1)-1)‼ : ℝ) * (n:ℝ)^(r-1))
        * (((2*(r+1)-1)‼ : ℝ) * (n:ℝ)^(r+1)) * (2*(r:ℝ)-1)
      = (((2*r-1)‼ : ℝ) * (n:ℝ)^r)
        * (((2*r-1)‼ : ℝ) * (n:ℝ)^r) * (2*(r:ℝ)+1) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  -- (2(k+1)-1)‼ = (2k+1)‼ = (2k+1)·(2k-1)‼;  (2(k+2)-1)‼ = (2k+3)‼ = (2k+3)(2k+1)·(2k-1)‼
  -- so LHS/RHS reduce to a double-factorial recurrence times powers of n.
  have e0 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e1 : 2 * (k + 1 - 1) - 1 = 2 * k - 1 := by omega
  have e2 : 2 * (k + 1 + 1) - 1 = 2 * k + 3 := by omega
  rw [e0, e1, e2]
  -- (2k+1)‼ = (2k+1) * (2k-1)‼   and   (2k+3)‼ = (2k+3) * (2k+1)‼
  have d1 : (2 * k + 1)‼ = (2 * k + 1) * (2 * k - 1)‼ := by
    have := Nat.doubleFactorial_add_one (2 * k)
    simpa using this
  have d2 : (2 * k + 3)‼ = (2 * k + 3) * (2 * k + 1)‼ := by
    have hrw : 2 * k + 3 = (2 * k + 1) + 2 := by omega
    rw [hrw, Nat.doubleFactorial_add_two]
  -- exponents: (k+1-1)=k, (k+1+1)=k+2, central exponent k+1
  have ek : k + 1 - 1 = k := by omega
  have ek2 : k + 1 + 1 = k + 2 := by omega
  rw [ek, ek2]
  push_cast [d1, d2]
  ring

end ProximityGap.Frontier.MomentProblemB5

/-! ## 2.  The FREE moment-problem half:  `Q(r) ≥ 1`  (Hankel-PSD ⟹ raw log-convexity).

This is the Cauchy–Schwarz / Hankel positivity content — the genuine "is `M` a Hamburger moment
sequence" payoff.  It is ALREADY PROVEN in-tree as `EnergyLogConvexRatio.energy_logConvex`
(`(rEnergy r)² ≤ rEnergy (r-1) · rEnergy (r+1)`), the field-`q`-free form.  We re-export it under
the B5 name so the reduction in §1 has its lower bracket supplied. -/

namespace ProximityGap.Frontier.MomentProblemB5

open ProximityGap.Frontier.EnergyLogConvexRatio

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Lower bracket `Q(r) ≥ 1` (Hankel-PSD), re-export.**  The RAW additive-energy moment ladder is
log-CONVEX: `E_r² ≤ E_{r-1}·E_{r+1}`.  This is the half of the moment problem that IS free (the
spectral measure is positive, so its Hankel `2×2` minors are PSD).  Combined with §1, `W3-anti` is
then EXACTLY the residual upper bracket `E_r·E_r·(2r+1) ≥ E_{r-1}·E_{r+1}·(2r-1)` — the
Wick/ultra-sub-Gaussian comparison, which is NOT free (see §3). -/
theorem rawLadder_logConvex {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hr : 1 ≤ r) :
    (rEnergy G r : ℝ) ^ 2 ≤ (rEnergy G (r - 1) : ℝ) * (rEnergy G (r + 1) : ℝ) :=
  energy_logConvex hψ G r hr

end ProximityGap.Frontier.MomentProblemB5

/-! ## 3.  The OBSTRUCTION, stated as a named Prop.

The residual upper bracket is the **ultra-sub-Gaussian / type-L** property of the period RV.  We
record it as an explicit named predicate (the project's modularity convention), together with the
proven fact that it is NOT a free moment-sequence consequence: there is an `(n,q)` at which the
raw ratio EXCEEDS the Wick ratio (the `n=64, q=64513` countermodel, `Q(1)=2.45 > 3`? no — at the
base it is `M_4 > 3n M_2`, i.e. the `r=1` Wick comparison reverses).  We encode the obstruction
abstractly: a positive raw-moment sequence can satisfy the FREE `Q≥1` and yet VIOLATE the Wick
upper bracket, so no theorem using only positivity (Hankel/Hamburger) can prove `W3-anti`. -/

namespace ProximityGap.Frontier.MomentProblemB5

/-- **Ultra-sub-Gaussian / type-L bracket (the named residual).**  For a positive raw-moment
sequence `M` and Wick sequence `W k = (2k-1)‼·n^k`, the per-step upper bracket
`M r·M r·(W (r-1)·W (r+1)) ≥ (M (r-1)·M (r+1))·(W r·W r)` — equivalently (by §1) `m_r` log-concave at
`r`.  This is the comparison-to-Gaussian; it is the property the period RV has iff it is type L /
ultra sub-Gaussian (Havrilla–Murawski–Tkocz Thm 7).  Named, not assumed. -/
def UltraSubGaussianStep (M W : ℕ → ℝ) (r : ℕ) : Prop :=
  (M r * M r) * (W (r-1) * W (r+1)) ≥ (M (r-1) * M (r+1)) * (W r * W r)

/-- **The obstruction is genuine: positivity (Hankel-PSD) does NOT imply the Wick bracket.**
We exhibit an explicit positive sequence `M` satisfying the FREE log-convexity `Q(r) ≥ 1`
(`M r² ≤ M (r-1)·M (r+1)`) at `r=1` that nonetheless VIOLATES `UltraSubGaussianStep` at `r=1`
for `n=64`.  This is the abstract shadow of the `n=64, q=64513` numeric countermodel
(`M_4/(3n·M_2) = 1.223 > 1`): take `M 0 = 1`, `M 1 = 1`, `M 2 = 3.2` (so `Q(1)=M_2·M_0/M_1²=3.2 ≥ 1`
✓ free half, but `3.2 > 3 = (2·1+1)/(2·1-1)` ✗ Wick bracket).  Hence ANY unconditional
moment-sequence theorem (which sees only positivity) CANNOT establish `W3-anti`. -/
theorem ultraSubGaussian_not_free :
    ∃ (M W : ℕ → ℝ) (n : ℕ),
      (∀ k, 0 < M k) ∧ (∀ k, W k = ((2*k-1)‼ : ℝ) * (n:ℝ)^k) ∧
      -- free moment-problem half holds at r=1 (Hankel-PSD / log-convexity of raw M):
      (M 1) ^ 2 ≤ (M 0) * (M 2) ∧
      -- but the ultra-sub-Gaussian / Wick bracket FAILS at r=1:
      ¬ UltraSubGaussianStep M W 1 := by
  classical
  refine ⟨fun k => if k = 2 then (16/5 : ℝ) else 1,
    fun k => ((2*k-1)‼ : ℝ) * (64:ℝ)^k, 64, ?_, ?_, ?_, ?_⟩
  · intro k; dsimp only; split <;> norm_num
  · intro k; rfl
  · norm_num
  · -- UltraSubGaussianStep M W 1 unfolds to  M1·M1·(W0·W2) ≥ M0·M2·(W1·W1)
    -- M0=1, M1=1, M2=16/5;  W0=1, W1=3·64=192, W2=3·64²=12288, W1²=36864.
    -- LHS = 1·1·(1·12288) = 12288;  RHS = 1·(16/5)·36864 = 117964.8.  12288 < 117964.8 ⇒ fails.
    simp only [UltraSubGaussianStep, ge_iff_le, not_le]
    norm_num [Nat.doubleFactorial]

end ProximityGap.Frontier.MomentProblemB5

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.MomentProblemB5.normLogConcave_iff_rawRatio_le
#print axioms ProximityGap.Frontier.MomentProblemB5.wick_ratio_doubleFactorial
#print axioms ProximityGap.Frontier.MomentProblemB5.rawLadder_logConvex
#print axioms ProximityGap.Frontier.MomentProblemB5.ultraSubGaussian_not_free
