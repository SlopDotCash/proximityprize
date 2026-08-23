/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466, lane R3)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiBenedettoNearSidonImprovement

/-!
# The bilinear (3,3) + √p-DFT beat: `M ≤ n^{8/9+o(1)}` at β = 4 (#466, lane R3)

**Result (good-prime-conditional, exponent bookkeeping axiom-clean).** The round-1 P6
side-discovery, adversarially re-verified (paper re-derivation + exact `F_p` data,
`scripts/probes/probe_466_bilinear_dft_chain.py` / `_out_466_bilinear_dft_chain.txt`:
every theorem-step of the chain holds exactly at `n = 8, 16, 32`, multiple primes,
worst-coset `a`, actual executed pigeonhole):

* **Leg 1** (di Benedetto et al., arXiv:2003.06165, eq 5.2–5.6, `T₃`-based): one cube +
  ONE dyadic pigeonhole + Cauchy–Schwarz produce a popular sumset `X` with
  `|X| ≥ n⁶Δ⁶/(K·T₃·Δ₁²)`, every `x ∈ X` carrying `|Σ_{y∈μ_n} e_p(axy)| > nΔ₁`, and the
  dyadic level obeying `Δ₁ ≥ Δ³/K` (`Δ = M/n`, `K = p^{o(1)}` the tracked dyadic losses).
* **Leg 2** (NO second pigeonhole — this is the discovery): cube once more and finish with
  Cauchy–Schwarz over the frequency + the **exact Parseval completion**
  `Σ_{w∈F_p}|Σ_{x∈X} ε_x e_p(axw)|² = p|X|` (the √p DFT operator norm; the completion adds
  only nonnegative terms, so there is NO DC leak). This yields `|X|·(nΔ₁)⁶ ≤ p·T₃`,
  **dropping the Petridis–Shparlinski trilinear lemma entirely**.
* **Splice** (`master_of_legs`, PROVEN below): `n¹²Δ¹⁸ ≤ K⁵·p·T₃²` — `T₃` enters once per
  leg, hence squared; `Δ₁` has positive exponent on the left, so the pigeonhole *lower*
  bound `Δ₁ ≥ Δ³/K` substitutes in the valid direction.
* **Finish** (good prime: `T₃(μ_n) ≤ 15n³`): `M ≤ 15^{1/9}·n^{2/3}·p^{1/18}·p^{o(1)}`.
  At `p ≤ n^β`: exponent `θ(β) = (12+β)/18`, i.e. **saving `(6−β)/18`, dying at `β = 6`**;
  at the prize aspect ratio `β = 4`: **`M ≤ n^{8/9+o(1)}`**, beating the landed trilinear
  `23/24 = 0.9583` (`_AvJ_UnconditionalBeat`) — the bilinear saving `1/9 = 8/72` beats the
  trilinear `(7−β)/72 = 3/72` for all `β < 17/3`, with one FEWER external analytic input.

## What is proven here vs named

The **exponent algebra is PROVEN axiom-clean**: the splice `master_of_legs`, the moment
extraction `moment_of_master`, the 18-th-root extraction `charSum_exponent` (any `β`), the
`β = 4` value `8/9` (`charSum_beta4`, `assembled_beat_beta4`), the saving law `(6−β)/18`,
validity `β < 6`, the domination law over the trilinear chain (crossover exactly
`β = 17/3`), and the squaring step `leg2_of_bilinear_form`. The **analytic content is
NAMED** (consistent with `_AvT3a_DiBenedettoBeatAssembly.DiBenedettoThm31` /
`GoodPrimeEnergyTransfer`): `Leg1PopularSumset` (the published di Benedetto eq 5.2–5.6
output) and `Leg2DFTFinisher` (CS + Parseval completion — elementary, but its `F_p`-level
statement lives outside this real-arithmetic file). The good-prime energy input
`T₃ ≤ 15n³` is a hypothesis.

## ⚠️ Honest scope

* **GOOD-PRIME-CONDITIONAL.** `T₃(μ_n) ≤ 15n³` FAILS on the bad-prime set `D₃(n)`, which
  contains prize-regime primes at `n = 32` (`_AvJ_UnconditionalBeat`); the prize is
  for-all-`q`, so this is NOT prize closure. Same conditionality class as the landed 23/24.
* **HIGH side of the BGK wall.** `8/9 ≫ 1/2`; by `deltaStar_determination_all_or_nothing`
  a fixed power law cannot move δ* regardless. `isPrizeClosure := false`.
* **Dies at `β = 6`** (saving `(6−β)/18 ≤ 0`); the trilinear chain survives to `β = 7` and
  wins on `β ∈ (17/3, 7)`.

Issue #466, dossier v3 §"SIDE-DISCOVERY (live)". Axiom-clean
(`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real

namespace ArkLib.ProximityGap.Frontier.BilinearDFTBeat

/-! ## The exponent algebra (exact rationals) -/

/-- The bilinear (3,3)+DFT sup-norm exponent at aspect ratio `β` (`p = n^β`):
`θ(β) = (12+β)/18` (from `M¹⁸ ≤ n¹²⁺β·p^{o(1)}`). -/
def bilinearTheta (β : ℚ) : ℚ := (12 + β) / 18

/-- The bilinear power saving `1 − θ(β) = (6−β)/18`. -/
def bilinearSaving (β : ℚ) : ℚ := (6 - β) / 18

/-- The landed trilinear (di Benedetto near-Sidon, `Hexp = 7`) power saving `(7−β)/72`
(`_AvJ_UnconditionalBeat`: `23/24` at `β = 4`). -/
def trilinearSaving (β : ℚ) : ℚ := (7 - β) / 72

/-- Saving law: `θ(β) + saving(β) = 1`. -/
theorem theta_add_saving (β : ℚ) : bilinearTheta β + bilinearSaving β = 1 := by
  unfold bilinearTheta bilinearSaving; ring

/-- **The β = 4 headline: `θ(4) = 8/9`.** -/
theorem bilinearTheta_beta4 : bilinearTheta 4 = 8 / 9 := by
  unfold bilinearTheta; norm_num

/-- The β = 4 saving is `1/9`. -/
theorem bilinearSaving_beta4 : bilinearSaving 4 = 1 / 9 := by
  unfold bilinearSaving; norm_num

/-- **Validity law: the saving is positive exactly for `β < 6`** (the method dies at β=6). -/
theorem saving_pos_iff (β : ℚ) : 0 < bilinearSaving β ↔ β < 6 := by
  unfold bilinearSaving
  constructor <;> intro h <;> linarith

/-- The method dies exactly at `β = 6`. -/
theorem dies_at_beta6 : bilinearSaving 6 = 0 := by
  unfold bilinearSaving; norm_num

/-- **Domination law: the bilinear chain beats the landed trilinear chain exactly for
`β < 17/3`** (`(6−β)/18 > (7−β)/72 ⟺ 4(6−β) > 7−β ⟺ β < 17/3`). -/
theorem dominates_trilinear_iff (β : ℚ) :
    trilinearSaving β < bilinearSaving β ↔ β < 17 / 3 := by
  unfold trilinearSaving bilinearSaving
  constructor <;> intro h <;> linarith

/-- **At the prize aspect ratio β = 4 the bilinear chain strictly dominates the landed
trilinear 23/24**: saving `1/9 = 8/72 > 3/72 = 1/24`. -/
theorem dominates_at_beta4 : trilinearSaving 4 < bilinearSaving 4 :=
  (dominates_trilinear_iff 4).mpr (by norm_num)

/-- The trilinear chain at β = 4 is exactly the landed `23/24` exponent. -/
theorem trilinear_beta4_landed : (1 : ℚ) - trilinearSaving 4 = 23 / 24 := by
  unfold trilinearSaving; norm_num

/-- The β = 4 trilinear saving coincides with the landed `diBenedettoSaving 2 3 = 1/24`
(`_DiBenedettoNearSidonImprovement`) — the lineage weld. -/
theorem trilinearSaving_eq_diBenedetto :
    ((trilinearSaving 4 : ℚ) : ℝ) =
      ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving 2 3 := by
  unfold trilinearSaving ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving
  norm_num

/-- **Honesty brick: β = 4 exponent `8/9` is on the HIGH side of the BGK wall**
(`1/2 < 8/9 < 1`): a SOTA-direction gain, not a wall crossing. -/
theorem beta4_high_side_of_wall : (1 : ℚ) / 2 < bilinearTheta 4 ∧ bilinearTheta 4 < 1 := by
  rw [bilinearTheta_beta4]; norm_num

/-- The bilinear θ(4)=8/9 beats the landed trilinear exponent 23/24 (smaller is better). -/
theorem beta4_beats_landed : bilinearTheta 4 < 23 / 24 := by
  rw [bilinearTheta_beta4]; norm_num

/-- **NOT prize closure.** Good-prime-conditional, high side of the wall, and a fixed power
law cannot move δ* (`deltaStar_determination_all_or_nothing`). -/
def isPrizeClosure : Bool := false

/-! ## The named analytic content (the two legs, as `Prop`s over ℝ)

`n = |μ_n|`, `Δ = M/n` the normalized worst sup-norm, `Δ₁` the popular dyadic level,
`X = |X|` the popular-sumset size, `T₃` the cubic additive energy `T₃(μ_n)`, `p` the
characteristic, `K ≥ 1` the tracked `p^{o(1)}` dyadic/pigeonhole losses. -/

/-- **Named hypothesis (leg 1): the di Benedetto popular-sumset output**
(arXiv:2003.06165 eq 5.2–5.6 specialized to `μ_n`; published, audited in
`docs/kb/dibenedetto-audit-full-2026-06-15.md`, and verified exactly on `F_p` data with
`K = 4L` in the probe). The two conjuncts: the Cauchy–Schwarz sumset lower bound
`n⁶Δ⁶ ≤ K·T₃·Δ₁²·|X|` and the pigeonhole level bound `Δ³ ≤ K·Δ₁`. -/
def Leg1PopularSumset (n Δ Δ₁ X T₃ K : ℝ) : Prop :=
  n ^ 6 * Δ ^ 6 ≤ K * T₃ * Δ₁ ^ 2 * X ∧ Δ ^ 3 ≤ K * Δ₁

/-- **Named hypothesis (leg 2): the √p-DFT finisher** in squared form: `|X|·(nΔ₁)⁶ ≤ p·T₃`.
Derivation (elementary, verified exactly on `F_p` data): every `x ∈ X` has `|T(x)| > nΔ₁`,
so `|X|(nΔ₁)³ ≤ Σ_{x∈X}|T(x)³| = |Σ_w J₃(w)(Σ_{x∈X}ε_x e_p(axw))| ≤ ‖J₃‖₂·√(p|X|)` by
Cauchy–Schwarz over `w` plus the EXACT Parseval completion (adding nonnegative terms — no
DC leak; the √p is the DFT operator norm). Squaring and dividing by `|X|` gives this form
(`leg2_of_bilinear_form` below proves that squaring step). NO second pigeonhole and NO
Petridis–Shparlinski input. -/
def Leg2DFTFinisher (n Δ₁ X p T₃ : ℝ) : Prop :=
  X * (n * Δ₁) ^ 6 ≤ p * T₃

/-- **The squaring step of leg 2, proven**: from the bilinear-form bound
`|X|(nΔ₁)³ ≤ √(p·T₃·|X|)` (the raw CS + Parseval-completion output, with `‖J₃‖₂² = T₃`),
conclude the squared form `|X|(nΔ₁)⁶ ≤ p·T₃`. -/
theorem leg2_of_bilinear_form {n Δ₁ X p T₃ : ℝ} (hX : 0 < X) (hn : 0 ≤ n) (hΔ₁ : 0 ≤ Δ₁)
    (hpT : 0 ≤ p * T₃)
    (h : X * (n * Δ₁) ^ 3 ≤ Real.sqrt (p * T₃ * X)) :
    Leg2DFTFinisher n Δ₁ X p T₃ := by
  unfold Leg2DFTFinisher
  have hnd : (0 : ℝ) ≤ n * Δ₁ := mul_nonneg hn hΔ₁
  have hL : (0 : ℝ) ≤ X * (n * Δ₁) ^ 3 := mul_nonneg hX.le (by positivity)
  have hsq : (X * (n * Δ₁) ^ 3) ^ 2 ≤ p * T₃ * X := by
    have h2 : (X * (n * Δ₁) ^ 3) ^ 2 ≤ Real.sqrt (p * T₃ * X) ^ 2 :=
      pow_le_pow_left₀ hL h 2
    rwa [Real.sq_sqrt (mul_nonneg hpT hX.le)] at h2
  have key : X * (n * Δ₁) ^ 6 * X ≤ p * T₃ * X := by
    calc X * (n * Δ₁) ^ 6 * X = (X * (n * Δ₁) ^ 3) ^ 2 := by ring
      _ ≤ p * T₃ * X := hsq
  exact le_of_mul_le_mul_right key hX

/-! ## The splice (proven): legs ⟹ master inequality `n¹²Δ¹⁸ ≤ K⁵·p·T₃²` -/

/-- **The master inequality from the two legs (the splice, PROVEN).** Substituting the
leg-1 lower bound on `|X|` into the leg-2 upper bound eliminates `|X|`
(`n¹²Δ⁶Δ₁⁴ ≤ K·p·T₃²`), and the pigeonhole level bound `Δ³ ≤ K·Δ₁` — entering with
POSITIVE exponent on the left, so in the valid direction — collapses `Δ₁`:

  `n¹² · Δ¹⁸ ≤ K⁵ · (p · T₃²)`.

`T₃` appears squared: once from each leg. This is the arithmetic heart of the chain;
the classic splice losses (direction of `Δ₁`, DC term, `T₃` multiplicity) are all
machine-checked here. -/
theorem master_of_legs {n Δ Δ₁ X p T₃ K : ℝ}
    (hΔ : 0 ≤ Δ) (hΔ₁ : 0 < Δ₁) (hT₃ : 0 < T₃) (hK : 1 ≤ K)
    (h1 : Leg1PopularSumset n Δ Δ₁ X T₃ K)
    (h2 : Leg2DFTFinisher n Δ₁ X p T₃) :
    n ^ 12 * Δ ^ 18 ≤ K ^ 5 * (p * T₃ ^ 2) := by
  obtain ⟨hSize, hLevel⟩ := h1
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hfac : (0 : ℝ) ≤ K * T₃ * Δ₁ ^ 2 :=
    mul_nonneg (mul_nonneg hK0 hT₃.le) (sq_nonneg Δ₁)
  -- step 1: eliminate |X| by chaining the two legs
  have step1 : n ^ 12 * Δ ^ 6 * Δ₁ ^ 6 ≤ K * T₃ * Δ₁ ^ 2 * (p * T₃) := by
    calc n ^ 12 * Δ ^ 6 * Δ₁ ^ 6
        = (n ^ 6 * Δ ^ 6) * (n ^ 6 * Δ₁ ^ 6) := by ring
      _ ≤ (K * T₃ * Δ₁ ^ 2 * X) * (n ^ 6 * Δ₁ ^ 6) := by
          apply mul_le_mul_of_nonneg_right hSize
          have : (0 : ℝ) ≤ (n * Δ₁) ^ 6 := by positivity
          calc (0 : ℝ) ≤ (n * Δ₁) ^ 6 := this
            _ = n ^ 6 * Δ₁ ^ 6 := by ring
      _ = K * T₃ * Δ₁ ^ 2 * (X * (n * Δ₁) ^ 6) := by ring
      _ ≤ K * T₃ * Δ₁ ^ 2 * (p * T₃) := mul_le_mul_of_nonneg_left h2 hfac
  -- step 2: divide by Δ₁²
  have key : n ^ 12 * Δ ^ 6 * Δ₁ ^ 4 * Δ₁ ^ 2 ≤ K * (p * T₃ ^ 2) * Δ₁ ^ 2 := by
    calc n ^ 12 * Δ ^ 6 * Δ₁ ^ 4 * Δ₁ ^ 2 = n ^ 12 * Δ ^ 6 * Δ₁ ^ 6 := by ring
      _ ≤ K * T₃ * Δ₁ ^ 2 * (p * T₃) := step1
      _ = K * (p * T₃ ^ 2) * Δ₁ ^ 2 := by ring
  have step2 : n ^ 12 * Δ ^ 6 * Δ₁ ^ 4 ≤ K * (p * T₃ ^ 2) :=
    le_of_mul_le_mul_right key (by positivity)
  -- step 3: collapse Δ₁ via the pigeonhole LOWER bound (valid direction: Δ₁⁴ on the LEFT)
  have h30 : (0 : ℝ) ≤ Δ ^ 3 := by positivity
  have step3 : Δ ^ 12 ≤ K ^ 4 * Δ₁ ^ 4 := by
    calc Δ ^ 12 = (Δ ^ 3) ^ 4 := by ring
      _ ≤ (K * Δ₁) ^ 4 := pow_le_pow_left₀ h30 hLevel 4
      _ = K ^ 4 * Δ₁ ^ 4 := by ring
  -- assemble
  have hn12 : (0 : ℝ) ≤ n ^ 12 * Δ ^ 6 := by positivity
  calc n ^ 12 * Δ ^ 18 = (n ^ 12 * Δ ^ 6) * Δ ^ 12 := by ring
    _ ≤ (n ^ 12 * Δ ^ 6) * (K ^ 4 * Δ₁ ^ 4) := mul_le_mul_of_nonneg_left step3 hn12
    _ = K ^ 4 * (n ^ 12 * Δ ^ 6 * Δ₁ ^ 4) := by ring
    _ ≤ K ^ 4 * (K * (p * T₃ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left step2 (by positivity)
    _ = K ^ 5 * (p * T₃ ^ 2) := by ring

/-! ## The good-prime finish (proven): moment bound and 18-th-root extraction -/

/-- **The moment bound from the master inequality + the good-prime energy input.**
With `Δ = M/n` and `T₃ ≤ 15n³` (the good-prime cubic energy — the SAME named input as
`_AvT3a.GoodPrimeEnergyTransfer`; fails on `D₃(n)`):  `M¹⁸ ≤ 225·K·p·n¹²`. -/
theorem moment_of_master {n M p T₃ K : ℝ}
    (hn : 0 < n) (hT₃ : 0 ≤ T₃) (hp : 0 ≤ p) (hK : 0 ≤ K)
    (hMaster : n ^ 12 * (M / n) ^ 18 ≤ K * (p * T₃ ^ 2))
    (hGood : T₃ ≤ 15 * n ^ 3) :
    M ^ 18 ≤ 225 * K * p * n ^ 12 := by
  have hne : n ≠ 0 := ne_of_gt hn
  have hkey : M ^ 18 = n ^ 12 * (M / n) ^ 18 * n ^ 6 := by
    field_simp
  have hT2 : T₃ ^ 2 ≤ 225 * n ^ 6 := by
    calc T₃ ^ 2 ≤ (15 * n ^ 3) ^ 2 := pow_le_pow_left₀ hT₃ hGood 2
      _ = 225 * n ^ 6 := by ring
  calc M ^ 18 = n ^ 12 * (M / n) ^ 18 * n ^ 6 := hkey
    _ ≤ K * (p * T₃ ^ 2) * n ^ 6 := by
        apply mul_le_mul_of_nonneg_right hMaster (by positivity)
    _ ≤ K * (p * (225 * n ^ 6)) * n ^ 6 := by
        have hpt : p * T₃ ^ 2 ≤ p * (225 * n ^ 6) :=
          mul_le_mul_of_nonneg_left hT2 hp
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpt hK) (by positivity)
    _ = 225 * K * p * n ^ 12 := by ring

/-- **The 18-th-root extraction (any aspect ratio).** From the moment bound
`M¹⁸ ≤ 225·K·p·n¹²` and `p ≤ n^β`:

  `M ≤ (225·K)^{1/18} · n^{(12+β)/18}`

— the exponent `(12+β)/18 = 1 − (6−β)/18` (the saving law, real-exponent form). -/
theorem charSum_exponent {n M p K β : ℝ}
    (hn : 1 ≤ n) (hM : 0 ≤ M) (hK : 1 ≤ K) (hp : 0 ≤ p)
    (hMoment : M ^ 18 ≤ 225 * K * p * n ^ 12)
    (hβ : p ≤ n ^ β) :
    M ≤ (225 * K) ^ ((1 : ℝ) / 18) * n ^ ((12 + β) / 18) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn
  have hK0 : (0 : ℝ) ≤ 225 * K := by linarith
  -- collapse p ≤ n^β into the moment bound
  have h2 : M ^ 18 ≤ 225 * K * n ^ ((12 : ℝ) + β) := by
    have hstep : 225 * K * p * n ^ 12 ≤ 225 * K * n ^ β * n ^ 12 := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hK0) (by positivity)
    have hsplit : 225 * K * n ^ ((12 : ℝ) + β) = 225 * K * n ^ β * n ^ 12 := by
      rw [Real.rpow_add hn0, show ((12 : ℝ)) = ((12 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      ring
    rw [hsplit]
    exact le_trans hMoment hstep
  -- take 18-th roots
  have h3 : ((M ^ 18 : ℝ)) ^ ((1 : ℝ) / 18) ≤
      (225 * K * n ^ ((12 : ℝ) + β)) ^ ((1 : ℝ) / 18) :=
    Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  have hL : ((M : ℝ) ^ (18 : ℕ)) ^ ((1 : ℝ) / 18) = M := by
    rw [← Real.rpow_natCast M 18, ← Real.rpow_mul hM]
    norm_num
  have hR : (225 * K * n ^ ((12 : ℝ) + β)) ^ ((1 : ℝ) / 18)
      = (225 * K) ^ ((1 : ℝ) / 18) * n ^ (((12 : ℝ) + β) / 18) := by
    rw [Real.mul_rpow hK0 (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le,
      mul_one_div]
  rw [hL, hR] at h3
  exact h3

/-- The real-exponent saving law: `(12+β)/18 = 1 − (6−β)/18`. -/
theorem exponent_eq_one_sub_saving (β : ℝ) : (12 + β) / 18 = 1 - (6 - β) / 18 := by ring

/-- **The β = 4 headline extraction: `M ≤ (225·K)^{1/18} · n^{8/9}`.** -/
theorem charSum_beta4 {n M p K : ℝ}
    (hn : 1 ≤ n) (hM : 0 ≤ M) (hK : 1 ≤ K) (hp : 0 ≤ p)
    (hMoment : M ^ 18 ≤ 225 * K * p * n ^ 12)
    (hβ : p ≤ n ^ (4 : ℝ)) :
    M ≤ (225 * K) ^ ((1 : ℝ) / 18) * n ^ ((8 : ℝ) / 9) := by
  have h := charSum_exponent hn hM hK hp hMoment hβ
  rwa [show ((12 : ℝ) + 4) / 18 = (8 : ℝ) / 9 by norm_num] at h

/-! ## The full assembly -/

/-- **The assembled bilinear (3,3) + √p-DFT beat at β = 4 (good-prime-conditional).**
Given the two named analytic legs (`Leg1PopularSumset` with `Δ = M/n`, `Leg2DFTFinisher`),
the good-prime cubic-energy input `T₃ ≤ 15n³`, and the aspect-ratio bound `p ≤ n⁴`:

  `M ≤ (225·K⁵)^{1/18} · n^{8/9}`

i.e. `M ≤ n^{8/9+o(1)}` with `K = p^{o(1)}` the tracked dyadic losses. This beats the
landed trilinear `23/24` (`_AvJ_UnconditionalBeat.assembled_beat`) at the same
conditionality (good prime), with one fewer external analytic input (no
Petridis–Shparlinski). HIGH side of the wall; NOT prize closure. -/
theorem assembled_beat_beta4 {n M p T₃ Δ₁ X K : ℝ}
    (hn : 1 ≤ n) (hM : 0 ≤ M) (hΔ₁ : 0 < Δ₁) (hT₃ : 0 < T₃) (hp : 0 ≤ p) (hK : 1 ≤ K)
    (h1 : Leg1PopularSumset n (M / n) Δ₁ X T₃ K)
    (h2 : Leg2DFTFinisher n Δ₁ X p T₃)
    (hGood : T₃ ≤ 15 * n ^ 3)
    (hβ : p ≤ n ^ (4 : ℝ)) :
    M ≤ (225 * K ^ 5) ^ ((1 : ℝ) / 18) * n ^ ((8 : ℝ) / 9) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn
  have hΔ : (0 : ℝ) ≤ M / n := div_nonneg hM hn0.le
  have hK5 : (1 : ℝ) ≤ K ^ 5 := one_le_pow₀ hK
  have hMaster := master_of_legs hΔ hΔ₁ hT₃ hK h1 h2
  have hMoment := moment_of_master hn0 hT₃.le hp (by linarith : (0 : ℝ) ≤ K ^ 5)
    hMaster hGood
  exact charSum_beta4 hn hM hK5 hp hMoment hβ

end ArkLib.ProximityGap.Frontier.BilinearDFTBeat

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.theta_add_saving
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.bilinearTheta_beta4
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.bilinearSaving_beta4
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.saving_pos_iff
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.dies_at_beta6
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.dominates_trilinear_iff
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.dominates_at_beta4
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.trilinear_beta4_landed
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.trilinearSaving_eq_diBenedetto
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.beta4_high_side_of_wall
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.beta4_beats_landed
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.leg2_of_bilinear_form
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.master_of_legs
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.moment_of_master
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.charSum_exponent
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.exponent_eq_one_sub_saving
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.charSum_beta4
#print axioms ArkLib.ProximityGap.Frontier.BilinearDFTBeat.assembled_beat_beta4
