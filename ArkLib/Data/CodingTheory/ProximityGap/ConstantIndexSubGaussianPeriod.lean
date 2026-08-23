/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# The Constant-Index Sub-Gaussian Period Conjecture (#407)

This file isolates, as its own named conjecture, the **novel object** at the heart of the
proximity prize: the sup-norm of the Gaussian periods of a *constant-index* dyadic subgroup.
It is NOT BCHKS Conjecture 1.12 (the log-size subgroup subset-sumset attack, the opposite
regime and direction) and was confirmed absent from the literature as a stated conjecture; it
is the precise effective-uniformity gap left open by Rojas-León (arXiv:1010.0120, "Estimates
for exponential sums with a large automorphism group") and Garcia–Lorenz–Todd (arXiv:2112.13886,
"Moments of Gaussian Periods and Modified Fermat Curves", Ramanujan J. 2025).

## The object

Let `p` be an odd prime, `p = m·n + 1`, `g` a primitive root mod `p`, and
`η_a = Σ_{j=0}^{n-1} e_p(g^{m·j+a})` the `m` Gaussian periods (`a = 0,…,m-1`); equivalently
`η_b = Σ_{y ∈ μ_n} ψ(b·y)` for the dyadic multiplicative subgroup `μ_n` of order `n = 2^μ` and a
nontrivial additive character `ψ` (the in-tree `eta ψ G b`). The PRIZE regime is **constant index
`m` fixed** (`m ≈ 2^128`) while `n → p` (so `μ_n` is LARGE, `n ~ p`). The prize object is

  `M(n) = max_{b ≠ 0} ‖η_b‖`.

The classical Weil bound gives only `M(n) ≤ ((m-1)√p + 1)/m ≈ √m · √n` (the in-tree
`ConstantIndexGaussSum.eta_constIndex_norm_le`, PROVEN but vacuous at the prize: it is `√m`-lossy).
The conjecture below replaces the lossy `√m` by `√(2 log m)` — the genuine square-root cancellation
among the `m` Gauss-sum phases.

## The conjecture (NOVEL — stated here as its own Prop)

> **Constant-Index Sub-Gaussian Period Conjecture.**  Fix the index `m ≥ 2`. There is a constant
> `c` (absorbed; the sharp form is `c = 0`, slack only in `o(1)`) so that for every prime
> `p = m·n + 1` and every nonzero frequency `b`,
> `‖η_b‖ ≤ √(2 · n · log m)`,  where `n = |μ_n| = (p-1)/m`.

Equivalently `M(n)² ≤ 2 · n · log m`: the periods are **sub-Gaussian** with variance proxy `n` and
the index-`m` ensemble size enters only through the extreme-value `√(2 log m)` factor, exactly as
for `m` independent real Gaussians of variance `n`.

## Proven anchors (do NOT re-derive — cited, and the moment route reuses them in-tree)

* **Variance `Var(η_b) = n`.**  GLT Lemma 22: `Σ_{a} ‖η_a‖² = ((m-1)p + 1)/m`, i.e. each nonzero
  period has mean-square `≈ p/m = n`. In-tree this is the exact second-moment identity
  `SubgroupGaussSumSecondMoment.gaussSum_normSq_sum` (`Σ_b ‖η_b‖² = q·|G|`), the
  `sum ‖η‖² = p - n` gate. (Probe-verified integer-exactly across `m∈{3,4,5,8}`, all primes ≤ 400.)

* **`r = 2` char-`p` moment (Hasse–Weil).**  GLT Theorem 3 (`d = 3`):
  `V_4(p) = (1/27)(10p² + 4(4 - M_3)p + 1)` with `M_3 = #{x³+y³=z³ in ℙ²(𝔽_p)}`, and the explicit
  random-like bound `|27 V_4(p) - (6p² + 12p + 1)| ≤ 8 p^{3/2}` (their Eq. (5)). So the 4th moment is
  the real-Gaussian value `3n²` up to the Hasse–Weil error `O(p^{3/2})` — the conjecture holds at
  `r = 2` in the constant-index regime. (Probe-verified: the GLT formula and the `≤ 8p^{3/2}` bound
  hold to machine precision at every tested prime.)

* **`E_r(μ_n)` char-0 sub-Gaussian.**  The `r`-th additive energy of the `2^μ`-th roots of unity is
  `≤ (2r-1)‼ · n^r` for ALL `r` (Lam–Leung: vanishing `2^μ`-th-root sums are negation pairs; union
  bound over the `(2r-1)‼` perfect matchings). In-tree this is `GaussPeriodMomentBound.GaussianEnergyBound`,
  whose consumer `worstCaseIncompleteSumBound_of_energyBound` already lands the per-frequency bound at
  scale `(q·(2r-1)‼·n^r)^{1/r}`; minimizing over `r ≈ ln q` yields `√(2 n ln q)`. The OPEN residual is
  the **char-`p` transfer** of the char-0 energy bound to depth `r ≈ ln q` (proven for `n` small; open
  for the prize `n = 2^30`), i.e. the same effective-conductor wall as Rojas-León/GLT-via-Deligne.

## What this file proves (axiom-clean; the open core stays a named Prop)

The conjecture is a Prop, **never asserted**. The provable content is the **bridge**:

  `ConstantIndexSubGaussianPeriodBound ψ G m`   (the named bound `‖η_b‖ ≤ √(2 n log m)`)
    ⟹ `WorstCaseIncompleteSumBound ψ G (2 n log m)`   (the in-tree open residual, discharged)
    ⟹ the additive-energy budget `q·E(G) ≤ |G|⁴ + (2 n log m)·q·|G|`   (the δ\* floor consumer).

Everything between is machine-checked elementary real arithmetic over the in-tree
`addEnergy_le_of_worstCase`. The sub-Gaussian conjecture itself is the only open input, isolated
entirely in the hypothesis. Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.ConstantIndexSubGaussianPeriod

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The conjecture as a named Prop -/

/-- **The Constant-Index Sub-Gaussian Period bound** at index `m` (the prize core, #407).  For the
constant-index dyadic subgroup `G = μ_n` (`n = |G| = (q-1)/m`) and a primitive additive character
`ψ`, every nonzero Gaussian period is sub-Gaussian with variance proxy `n`:
  `‖η_b‖ ≤ √(2 · |G| · log m)`   for all `b ≠ 0`.
This is the NOVEL `√(2 log m)` extreme-value cancellation among the `m` Gauss-sum phases — strictly
sharper than the proven (but `√m`-lossy) Weil bound `‖η_b‖ ≤ ((m-1)√q + 1)/m`. Stated as a Prop and
never asserted; the consumers below are unconditional. -/
def ConstantIndexSubGaussianPeriodBound (ψ : AddChar F ℂ) (G : Finset F) (m : ℕ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ Real.sqrt (2 * (G.card : ℝ) * Real.log (m : ℝ))

/-! ## Bridge 1 — the conjecture discharges the in-tree open residual -/

/-- **The sub-Gaussian period bound discharges `WorstCaseIncompleteSumBound`.**  Squaring
`‖η_b‖ ≤ √(2 n log m)` gives `‖η_b‖² ≤ 2 n log m`, exactly the in-tree worst-case incomplete-sum
residual at scale `M = 2 · |G| · log m`.  (Requires `m ≥ 1` so the scale is nonnegative.) -/
theorem worstCaseIncompleteSumBound_of_subGaussian {ψ : AddChar F ℂ} {G : Finset F} {m : ℕ}
    (hm : 1 ≤ m) (h : ConstantIndexSubGaussianPeriodBound ψ G m) :
    WorstCaseIncompleteSumBound ψ G (2 * (G.card : ℝ) * Real.log (m : ℝ)) := by
  intro b hb
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hscale_nn : 0 ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ) := by
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    positivity
  have hb_le := h b hb
  have hb_nn : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
  calc ‖eta ψ G b‖ ^ 2
      ≤ (Real.sqrt (2 * (G.card : ℝ) * Real.log (m : ℝ))) ^ 2 := by
        apply pow_le_pow_left₀ hb_nn hb_le
    _ = 2 * (G.card : ℝ) * Real.log (m : ℝ) := Real.sq_sqrt hscale_nn

/-! ## Bridge 2 — the additive-energy budget (the δ\* floor consumer) -/

/-- **The sub-Gaussian period bound yields the δ\* additive-energy budget (end-to-end).**  Feeding
the discharged worst-case bound into the in-tree consumer `addEnergy_le_of_worstCase` gives the
unconditional envelope
  `q · E(G) ≤ |G|⁴ + (2 · |G| · log m) · (q · |G|)`,
the additive-energy budget that the δ\* ledger consumes (every smooth FRI/STIR domain has
`q ≥ |G|²`, so this collapses to `E(G) ≤ |G|² + (2 |G| log m)·|G| = O(n² log m)`).  This is the
proximity-prize floor, conditional ONLY on the named sub-Gaussian conjecture; everything between is
machine-checked. -/
theorem addEnergy_le_of_subGaussian {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {m : ℕ}
    (hm : 1 ≤ m) (h : ConstantIndexSubGaussianPeriodBound ψ G m) :
    (Fintype.card F : ℝ)
        * (ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (2 * (G.card : ℝ) * Real.log (m : ℝ)) * ((Fintype.card F : ℝ) * G.card) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hscale_nn : 0 ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ) := by
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    positivity
  exact addEnergy_le_of_worstCase hψ G hscale_nn
    (worstCaseIncompleteSumBound_of_subGaussian hm h)

/-- **The deployed-regime energy bound from the sub-Gaussian conjecture.**  In the smooth-domain
regime `q ≥ |G|²` (every FRI/STIR field), the conjecture gives the clean `O(n² log m)` energy bound
  `E(G) ≤ |G|² + (2 · |G| · log m) · |G|`,
i.e. `E(G) ≤ (1 + 2 log m)·|G|²` — the sub-Gaussian energy that pins the δ\* window at `Θ(1/log m)`. -/
theorem addEnergy_div_le_of_subGaussian {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {m : ℕ} (hm : 1 ≤ m) (h : ConstantIndexSubGaussianPeriodBound ψ G m)
    (hq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hqpos : 0 < Fintype.card F) :
    (ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 2 + (2 * (G.card : ℝ) * Real.log (m : ℝ)) * (G.card : ℝ) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hscale_nn : 0 ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ) := by
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    positivity
  exact addEnergy_le_div hψ G hscale_nn
    (worstCaseIncompleteSumBound_of_subGaussian hm h) hq hqpos

/-! ## The moment route lands the conjecture from the (char-0-proven) energy anchor -/

open ArkLib.ProximityGap.GaussPeriodMomentBound in
/-- **The energy anchor implies the sub-Gaussian residual, at the matched scale.**  This records
that the third proven anchor (`GaussianEnergyBound`, the char-0 sub-Gaussian energy
`E_r(μ_n) ≤ (2r-1)‼·n^r`) feeds the SAME in-tree open residual `WorstCaseIncompleteSumBound` — at the
moment scale `M_r = (q·(2r-1)‼·n^r)^{1/r}` — that the sub-Gaussian period conjecture discharges at
scale `2 n log m`.  Minimizing `M_r` over `r ≈ ln q` reaches `√(2 n ln q)`, the conjecture's bound
(with `log m ≈ log q` at constant index, since `q = m·n + 1` and `n` polynomial in `q`).  So the
moment route and the sub-Gaussian conjecture are two consumers of one open core; this lemma is the
explicit hand-off (pure re-export, no new content). -/
theorem worstCaseIncompleteSumBound_of_energyAnchor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r) (h : GaussianEnergyBound G r) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        ^ ((r : ℝ)⁻¹)) :=
  worstCaseIncompleteSumBound_of_energyBound hψ hr h

/-! ## Deep centered-moment residual -/

/--
The nontrivial `2r`-th moment of the Gaussian periods.

This is the `Σ_{b≠0} |η_b|^{2r}` side of the latest #407 deep-moment formulation.  The issue
comment writes the centered residual as `R_r`; this finite sum is the deployed period-side object
whose expected size is `≈ q · K^r · r! · |G|^r` at the decisive depth `r ≈ log q`.
-/
noncomputable def nontrivialPeriodMoment (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  ∑ b ∈ (Finset.univ.filter fun b : F => b ≠ 0), ‖eta ψ G b‖ ^ (2 * r)

/--
The sharpened deep-moment residual from the latest #407 discussion.

At the decisive moment depth `r ≈ log |F|`, prove the nontrivial period moment is bounded by
`q · K^r · r! · |G|^r`.  This is intentionally a `Prop`: it is the remaining analytic/arithmetic
input, not asserted here.
-/
def CenteredDeepMomentBound (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (K : ℝ) : Prop :=
  nontrivialPeriodMoment ψ G r
    ≤ (Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r

/--
A worst-case period bound gives the centered deep-moment residual after summing over nonzero
frequencies and checking the explicit scale inequality.

This is the reverse deterministic bridge to `worstCaseIncompleteSumBound_of_centeredDeepMomentBound`:
the L∞ residual and the centered-moment residual differ only by the stated counting/scale
normalization.  No analytic input is hidden here.
-/
theorem centeredDeepMomentBound_of_worstCase
    {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ} {K M : ℝ}
    (hM0 : 0 ≤ M) (h : WorstCaseIncompleteSumBound ψ G M)
    (hscale :
      (Fintype.card F : ℝ) * M ^ r
        ≤ (Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r) :
    CenteredDeepMomentBound ψ G r K := by
  classical
  unfold CenteredDeepMomentBound nontrivialPeriodMoment
  set s : Finset F := Finset.univ.filter fun b : F => b ≠ 0
  have hsum_le : ∑ b ∈ s, ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ _b ∈ s, M ^ r := by
    refine Finset.sum_le_sum ?_
    intro b hb
    have hb_ne : b ≠ 0 := by
      simpa [s] using hb
    calc ‖eta ψ G b‖ ^ (2 * r)
        = (‖eta ψ G b‖ ^ 2) ^ r := by rw [pow_mul]
      _ ≤ M ^ r := pow_le_pow_left₀ (sq_nonneg _) (h b hb_ne) r
  calc ∑ b ∈ s, ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ _b ∈ s, M ^ r := hsum_le
    _ = (s.card : ℝ) * M ^ r := by simp
    _ ≤ (Fintype.card F : ℝ) * M ^ r := by
        have hcard : (s.card : ℝ) ≤ (Fintype.card F : ℝ) := by
          exact_mod_cast Finset.card_le_univ (s := s)
        exact mul_le_mul_of_nonneg_right hcard (pow_nonneg hM0 r)
    _ ≤ (Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r := hscale

/-- A centered deep-moment bound controls every nonzero period at the same `2r`-th power. -/
theorem period_pow_le_of_centeredDeepMomentBound
    {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ} {K : ℝ} {b : F}
    (hb : b ≠ 0) (h : CenteredDeepMomentBound ψ G r K) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r := by
  classical
  have hmem : b ∈ (Finset.univ.filter fun b : F => b ≠ 0) := by
    simp [hb]
  have hterm_le : ‖eta ψ G b‖ ^ (2 * r) ≤ nontrivialPeriodMoment ψ G r := by
    simpa [nontrivialPeriodMoment] using
      (Finset.single_le_sum
        (s := Finset.univ.filter fun b : F => b ≠ 0)
        (f := fun b : F => ‖eta ψ G b‖ ^ (2 * r))
        (fun _ _ => pow_nonneg (norm_nonneg _) _) hmem)
  exact hterm_le.trans h

/--
Centered deep moments discharge the in-tree per-frequency residual.

This is the direct consumer for the latest #407 centered formulation: a bound on the nonzero
period moment at depth `r ≥ 1` yields `WorstCaseIncompleteSumBound` at the `r`-th-root scale
`(q · K^r · r! · |G|^r)^(1/r)`.  The centered moment hypothesis is still the open input.
-/
theorem worstCaseIncompleteSumBound_of_centeredDeepMomentBound
    {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ} {K : ℝ}
    (hr : 1 ≤ r) (hK : 0 ≤ K) (h : CenteredDeepMomentBound ψ G r K) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
        ^ ((r : ℝ)⁻¹)) := by
  intro b hb
  set X : ℝ := (Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r
    with hX
  have hXnonneg : 0 ≤ X := by
    rw [hX]
    positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]
    exact period_pow_le_of_centeredDeepMomentBound hb h
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

/--
Centered deep moments imply the named sub-Gaussian period conjecture once their root scale is below
the conjectural `2 |G| log m` variance proxy.

This keeps the #407 formulations synchronized: the deep centered-moment residual is the stronger
input, and the explicit scale inequality is the only arithmetic optimization needed to recover the
constant-index period statement.
-/
theorem subGaussian_of_centeredDeepMomentBound
    {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ} {K : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hK : 0 ≤ K) (h : CenteredDeepMomentBound ψ G r K)
    (hscale :
      (((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
          ^ ((r : ℝ)⁻¹))
        ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ)) :
    ConstantIndexSubGaussianPeriodBound ψ G m := by
  intro b hb
  have hwc := worstCaseIncompleteSumBound_of_centeredDeepMomentBound
    (ψ := ψ) (G := G) (r := r) (K := K) hr hK h
  have hsq :
      ‖eta ψ G b‖ ^ 2 ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ) :=
    (hwc b hb).trans hscale
  have htarget_nonneg : 0 ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ) :=
    (sq_nonneg ‖eta ψ G b‖).trans hsq
  have hsqrt_sq :
      (Real.sqrt (2 * (G.card : ℝ) * Real.log (m : ℝ))) ^ 2 =
        2 * (G.card : ℝ) * Real.log (m : ℝ) :=
    Real.sq_sqrt htarget_nonneg
  have heta_nonneg : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * (G.card : ℝ) * Real.log (m : ℝ)) :=
    Real.sqrt_nonneg _
  nlinarith [sq_nonneg (‖eta ψ G b‖ - Real.sqrt (2 * (G.card : ℝ) * Real.log (m : ℝ)))]

/--
The named sub-Gaussian conjecture also controls the centered moment family.

This closes the formal comparison in the opposite direction: if every nonzero period has squared
size at most `2 |G| log m`, then summing over all nonzero frequencies gives a centered moment bound
with `K = 2 log m` (and the extra `r!` factor only weakens the target).
-/
theorem centeredDeepMomentBound_of_subGaussian
    {ψ : AddChar F ℂ} {G : Finset F} {r m : ℕ}
    (hm : 1 ≤ m) (h : ConstantIndexSubGaussianPeriodBound ψ G m) :
    CenteredDeepMomentBound ψ G r (2 * Real.log (m : ℝ)) := by
  classical
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  have hscale_nonneg : 0 ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ) := by positivity
  have hterm :
      ∀ b ∈ (Finset.univ.filter fun b : F => b ≠ 0),
        ‖eta ψ G b‖ ^ (2 * r)
          ≤ ((2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r) := by
    intro b hb
    have hbne : b ≠ 0 := by simpa using (Finset.mem_filter.mp hb).2
    have hb_le := h b hbne
    have heta_nonneg : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
    have hsq : ‖eta ψ G b‖ ^ 2 ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ) := by
      calc ‖eta ψ G b‖ ^ 2
          ≤ (Real.sqrt (2 * (G.card : ℝ) * Real.log (m : ℝ))) ^ 2 := by
            apply pow_le_pow_left₀ heta_nonneg hb_le
        _ = 2 * (G.card : ℝ) * Real.log (m : ℝ) := Real.sq_sqrt hscale_nonneg
    have hpow : (‖eta ψ G b‖ ^ 2) ^ r
        ≤ (2 * (G.card : ℝ) * Real.log (m : ℝ)) ^ r :=
      pow_le_pow_left₀ (sq_nonneg _) hsq r
    have hfact : (1 : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mp (Nat.factorial_pos r)
    calc ‖eta ψ G b‖ ^ (2 * r)
        = (‖eta ψ G b‖ ^ 2) ^ r := by rw [pow_mul]
      _ ≤ (2 * (G.card : ℝ) * Real.log (m : ℝ)) ^ r := hpow
      _ = (2 * Real.log (m : ℝ)) ^ r * (G.card : ℝ) ^ r := by ring
      _ ≤ (2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r := by
        have hleft_nonneg : 0 ≤ (2 * Real.log (m : ℝ)) ^ r := by positivity
        have hcard_nonneg : 0 ≤ (G.card : ℝ) ^ r := by positivity
        calc
          (2 * Real.log (m : ℝ)) ^ r * (G.card : ℝ) ^ r
              = (2 * Real.log (m : ℝ)) ^ r * 1 * (G.card : ℝ) ^ r := by ring
          _ ≤ (2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfact hleft_nonneg) hcard_nonneg
  unfold CenteredDeepMomentBound nontrivialPeriodMoment
  calc
    ∑ b ∈ (Finset.univ.filter fun b : F => b ≠ 0), ‖eta ψ G b‖ ^ (2 * r)
        ≤ ∑ b ∈ (Finset.univ.filter fun b : F => b ≠ 0),
            ((2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r) :=
          Finset.sum_le_sum hterm
    _ = ((Finset.univ.filter fun b : F => b ≠ 0).card : ℝ)
        * ((2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card F : ℝ)
        * ((2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r) := by
          have hcard : ((Finset.univ.filter fun b : F => b ≠ 0).card : ℝ)
              ≤ (Fintype.card F : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          have hconst_nonneg :
              0 ≤ (2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r := by
            positivity
          exact mul_le_mul_of_nonneg_right hcard hconst_nonneg
    _ = (Fintype.card F : ℝ)
        * (2 * Real.log (m : ℝ)) ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r := by
          ring

/--
Centered deep moments give the downstream additive-energy budget.

This composes `worstCaseIncompleteSumBound_of_centeredDeepMomentBound` with the existing
`addEnergy_le_of_worstCase` consumer, so a future proof of the centered residual immediately feeds
the δ-star energy ledger.
-/
theorem addEnergy_le_of_centeredDeepMomentBound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ}
    (hr : 1 ≤ r) (hK : 0 ≤ K) (h : CenteredDeepMomentBound ψ G r K) :
    (Fintype.card F : ℝ)
        * (ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
            ^ ((r : ℝ)⁻¹))
          * ((Fintype.card F : ℝ) * G.card) := by
  set M : ℝ :=
    ((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
      ^ ((r : ℝ)⁻¹)
    with hM
  have hMnonneg : 0 ≤ M := by
    rw [hM]
    exact Real.rpow_nonneg (by positivity) _
  exact addEnergy_le_of_worstCase hψ G hMnonneg
    (worstCaseIncompleteSumBound_of_centeredDeepMomentBound hr hK h)

/--
Centered deep moments give the deployed-regime additive-energy budget.

When the field is large enough for `q ≥ |G|²`, the principal `|G|⁴/q` term collapses and the
centered residual contributes only the root-scale multiplier times `|G|`.
-/
theorem addEnergy_div_le_of_centeredDeepMomentBound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ}
    (hr : 1 ≤ r) (hK : 0 ≤ K) (h : CenteredDeepMomentBound ψ G r K)
    (hq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hqpos : 0 < Fintype.card F) :
    (ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 2
        + (((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
            ^ ((r : ℝ)⁻¹))
          * (G.card : ℝ) := by
  set M : ℝ :=
    ((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
      ^ ((r : ℝ)⁻¹)
    with hM
  have hMnonneg : 0 ≤ M := by
    rw [hM]
    exact Real.rpow_nonneg (by positivity) _
  exact addEnergy_le_div hψ G hMnonneg
    (worstCaseIncompleteSumBound_of_centeredDeepMomentBound hr hK h) hq hqpos

/--
Centered deep moments at the sub-Gaussian root scale give the same deployed energy budget as the
named constant-index period conjecture.

This is the direct #407 consumer: the centered deep-moment route reaches the `O(|G|² log m)` energy
ledger as soon as its optimized root scale is at most `2 |G| log m`.
-/
theorem addEnergy_div_le_of_centeredDeepMomentBound_subGaussianScale
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {K : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hK : 0 ≤ K) (h : CenteredDeepMomentBound ψ G r K)
    (hscale :
      (((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
          ^ ((r : ℝ)⁻¹))
        ≤ 2 * (G.card : ℝ) * Real.log (m : ℝ))
    (hq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hqpos : 0 < Fintype.card F) :
    (ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 2
        + (2 * (G.card : ℝ) * Real.log (m : ℝ)) * (G.card : ℝ) := by
  have hbase := addEnergy_div_le_of_centeredDeepMomentBound hψ hr hK h hq hqpos
  have htail :
      (((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
          ^ ((r : ℝ)⁻¹)) * (G.card : ℝ)
        ≤ (2 * (G.card : ℝ) * Real.log (m : ℝ)) * (G.card : ℝ) :=
    mul_le_mul_of_nonneg_right hscale (by positivity)
  exact hbase.trans (add_le_add (le_refl ((G.card : ℝ) ^ 2)) htail)

/-- A single nonzero period above the centered-moment budget refutes that deep-moment residual. -/
theorem not_centeredDeepMomentBound_of_period_pow_gt
    {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ} {K : ℝ} {b : F}
    (hb : b ≠ 0)
    (hbad :
      (Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r
        < ‖eta ψ G b‖ ^ (2 * r)) :
    ¬ CenteredDeepMomentBound ψ G r K := by
  intro h
  exact not_lt_of_ge (period_pow_le_of_centeredDeepMomentBound hb h) hbad

/--
Root-scale falsification hook for the centered residual.

This is the probe-facing form: if a measured nonzero period has squared norm above the
`r`-th-root scale certified by `CenteredDeepMomentBound`, then the centered residual is false.
-/
theorem not_centeredDeepMomentBound_of_period_sq_gt_rootScale
    {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ} {K : ℝ} {b : F}
    (hr : 1 ≤ r) (hK : 0 ≤ K) (hb : b ≠ 0)
    (hbad :
      (((Fintype.card F : ℝ) * K ^ r * (r.factorial : ℝ) * (G.card : ℝ) ^ r)
          ^ ((r : ℝ)⁻¹)) < ‖eta ψ G b‖ ^ 2) :
    ¬ CenteredDeepMomentBound ψ G r K := by
  intro h
  have hwc := worstCaseIncompleteSumBound_of_centeredDeepMomentBound
    (ψ := ψ) (G := G) (r := r) (K := K) hr hK h
  exact not_lt_of_ge (hwc b hb) hbad

/-! ## Refutation hook -/

/-- A measured nonzero period above the sub-Gaussian threshold refutes the conjecture at that
index — the honest falsification hook (no such violation found in any probe). -/
theorem not_subGaussian_of_period_gt {ψ : AddChar F ℂ} {G : Finset F} {m : ℕ} {b : F} (hb : b ≠ 0)
    (hbad : Real.sqrt (2 * (G.card : ℝ) * Real.log (m : ℝ)) < ‖eta ψ G b‖) :
    ¬ ConstantIndexSubGaussianPeriodBound ψ G m := by
  intro h
  exact not_lt_of_ge (h b hb) hbad

end ArkLib.ProximityGap.ConstantIndexSubGaussianPeriod

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
namespace ArkLib.ProximityGap.ConstantIndexSubGaussianPeriod

#print axioms worstCaseIncompleteSumBound_of_subGaussian
#print axioms addEnergy_le_of_subGaussian
#print axioms addEnergy_div_le_of_subGaussian
#print axioms worstCaseIncompleteSumBound_of_energyAnchor
#print axioms centeredDeepMomentBound_of_worstCase
#print axioms period_pow_le_of_centeredDeepMomentBound
#print axioms worstCaseIncompleteSumBound_of_centeredDeepMomentBound
#print axioms subGaussian_of_centeredDeepMomentBound
#print axioms centeredDeepMomentBound_of_subGaussian
#print axioms addEnergy_le_of_centeredDeepMomentBound
#print axioms addEnergy_div_le_of_centeredDeepMomentBound
#print axioms addEnergy_div_le_of_centeredDeepMomentBound_subGaussianScale
#print axioms not_centeredDeepMomentBound_of_period_pow_gt
#print axioms not_centeredDeepMomentBound_of_period_sq_gt_rootScale
#print axioms not_subGaussian_of_period_gt

end ArkLib.ProximityGap.ConstantIndexSubGaussianPeriod
