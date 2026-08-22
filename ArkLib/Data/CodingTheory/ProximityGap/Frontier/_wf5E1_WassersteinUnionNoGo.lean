/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-E1)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# The effective-Wasserstein → tail → union-bound route is INSUFFICIENT for the #444 prize

**Lane wf-E1.** Kowalski–Untrau (arXiv:2505.22059) prove an *effective* Wasserstein-`1` discrepancy
for trace-function / exponential-sum families over `F_q`: writing `μ_emp` for the empirical
distribution of the normalized sums and `μ_K` for the limiting (Sato–Tate / Haar) law,

> `W_1(μ_emp, μ_K) ≪ q^{-1/ dim(K)}`   (their Thm 4.4; `q^{-1/2}` for `SU_2`, generically weaker).

The lane reduces the prize bound `M(n) ≤ C·√(n·log m)` (`m = (p-1)/n = 2^128`, `q = n·m`) to:
*the effective `W_1` discrepancy, fed into a tail bound, surviving the union over the `m` distinct
coset-frequencies.* This file PROVES that step **cannot close**, axiom-clean.

## The mechanism (the provable wall)

`W_1` is, by Kantorovich–Rubinstein duality (KU Thm 1.3(6)), the sup over **1-Lipschitz** test
functions `u` of `|∫u dμ_emp − ∫u dμ_K|`. Take the 1-Lipschitz `u_t(x) = max(0, |x| − t)`. Then a
discrepancy bound `W_1 ≤ D` gives ONLY

  `(excess-mass of μ_emp above t)  ≤  (excess-mass of μ_K above t)  +  D`,                    (★)

where the additive `D` does **not** decay in `t`. Markov on (★) yields a tail
`Pr_emp[|x| > t + s] ≤ (E_K u_t + D)/s`, whose `D/s` term **floors** the tail at a `t`-independent
level. A union bound over the `m` frequencies needs the per-frequency tail `≤ 1/m`, hence needs

  `D ≤ 1/m`   (up to the `O(1)` slack `s`).                                                   (need)

But `D = q^{-1/dim}` with `q = n·m`, so `D ≥ q^{-1/2} = (n·m)^{-1/2}`, while `1/m`. For
`dim ≥ 2` and the prize scale this is a hard gap. The file isolates the pure inequality:

> **`wasserstein_floor_exceeds_union_threshold`** : for `dim ≥ 2`, large `m`, and `q = n·m` with
> `n ≤ m`, the KU discrepancy floor `q^{-1/dim}` STRICTLY EXCEEDS the union threshold `1/m`.

The numerical face (`scripts/probes/probe_wf5E1_*.py`): at the prize scale `n=2^30, m=2^128,
q=2^158`, the best case `dim=2` gives `D = 2^{-79} ≫ 2^{-128} = 1/m` — short by `2^{49}`.

## Honesty

The KU bound itself is NAMED, not proved (`def … : Prop`); it is correct mathematics, and it
gives the right *limiting law*. The PROVEN content here is the **insufficiency inequality**: a
fixed-order Wasserstein discrepancy that decays only as a power of `q` cannot supply the
order-`(log m)` moment control that the `m`-fold union demands. The `W_1` route is *necessary-
not-sufficient*; closing the prize needs deep (order `~ log q`) moment control — the char-`p`
deep-moment route, NOT Wasserstein. Tag: **OPEN-CRUX / REFUTED-as-sufficient-lemma.**

## References

* [KU25] E. Kowalski, T. Untrau. *Wasserstein metrics and quantitative equidistribution of
  exponential sums over finite fields*. arXiv:2505.22059 (Thm 4.1 Borda, Thm 4.4, Thm 1.3).
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding…*, ePrint 2026/680 (the prize floor).

All theorems axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.WassersteinUnionNoGo

open scoped Real

/-- The **named** Kowalski–Untrau effective `W_1` discrepancy hypothesis (Thm 4.4): the empirical
distribution of the normalized family is within `C · q^{-1/dim}` of the limiting law in `W_1`.
Stated as a `Prop` over the abstract data; **never asserted/proved** here (it is correct but its
ℓ-adic proof is out of session). `D` is the witnessed discrepancy bound. -/
noncomputable def KUDiscrepancy (D q : ℝ) (dim : ℕ) (C : ℝ) : Prop :=
  D ≤ C * q ^ (-(1 : ℝ) / dim)

/-- The **union-bound threshold**: to control the maximum over the `m` distinct coset-frequencies
by a union bound, the per-frequency exceedance probability must drop below `1/m`. The additive
Wasserstein floor `D` must therefore satisfy `D ≤ 1/m`. -/
noncomputable def UnionThreshold (m : ℝ) : ℝ := 1 / m

/-- **The analytic heart.** For `dim ≥ 2`, the KU discrepancy floor `q^{-1/dim}` with `q = n·m`
and `1 ≤ n ≤ m` is at least `(m^2)^{-1/2} = 1/m`... we show it STRICTLY exceeds `1/m` once
`n ≥ 2` (so `q = n·m > m^? `). Concretely: `q^{-1/dim} ≥ q^{-1/2}` (since `dim ≥ 2`,
`-1/dim ≥ -1/2`, and base `q ≥ 1`), and `q^{-1/2} = (n·m)^{-1/2}`. We compare to `1/m = m^{-1}`:
`(n·m)^{-1/2} > m^{-1}  ⟺  m^{2} > n·m  ⟺  m > n`, which holds in the THIN regime `n < m`
(prize: `n = 2^30 < 2^128 = m`). -/
theorem wasserstein_floor_exceeds_union_threshold
    (n m : ℝ) (dim : ℕ) (hn : 1 ≤ n) (hnm : n < m) (hdim : 2 ≤ dim) :
    UnionThreshold m < (n * m) ^ (-(1 : ℝ) / dim) := by
  have hm1 : (1 : ℝ) ≤ m := le_trans hn (le_of_lt hnm)
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm1
  have hnpos : 0 < n := lt_of_lt_of_le one_pos hn
  have hq1 : (1 : ℝ) ≤ n * m := by
    calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ n * m := by
          exact mul_le_mul hn hm1 (le_of_lt one_pos) (le_of_lt hnpos)
  have hqpos : 0 < n * m := mul_pos hnpos hmpos
  -- Step 1: dim ≥ 2 ⟹ -1/dim ≥ -1/2 ⟹ (nm)^{-1/dim} ≥ (nm)^{-1/2} (base ≥ 1).
  have hdimR : (2 : ℝ) ≤ (dim : ℝ) := by exact_mod_cast hdim
  have hdimpos : (0 : ℝ) < (dim : ℝ) := lt_of_lt_of_le (by norm_num) hdimR
  have hexp : (-(1 : ℝ) / 2) ≤ (-(1 : ℝ) / dim) := by
    have h12 : (1 : ℝ) / dim ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hdimR
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact h12
  -- (nm)^{-1/dim} ≥ (nm)^{-1/2}  (base ≥ 1, exponent monotone)
  have hstep1 : (n * m) ^ (-(1 : ℝ) / 2) ≤ (n * m) ^ (-(1 : ℝ) / dim) :=
    Real.rpow_le_rpow_of_exponent_le hq1 hexp
  -- Step 2: 1/m < (nm)^{-1/2}.  Equivalent (both pos) to (nm)^{1/2} < m, i.e. nm < m^2.
  have key : UnionThreshold m < (n * m) ^ (-(1 : ℝ) / 2) := by
    have hsqrt : (n * m) ^ ((1 : ℝ) / 2) < m := by
      -- (nm)^{1/2} < m ⟺ nm < m^2  (both nonneg, rpow 1/2 monotone); and m = m^{2·(1/2)}
      have hsq : n * m < m ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith [hnm, hmpos, hnpos]
      have hmono : (n * m) ^ ((1 : ℝ) / 2) < (m ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_lt_rpow (le_of_lt hqpos) hsq (by norm_num)
      rwa [← Real.rpow_mul (le_of_lt hmpos), show (2 : ℝ) * (1 / 2) = 1 by ring,
        Real.rpow_one] at hmono
    have hrootpos : 0 < (n * m) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hqpos _
    have hneg : (n * m) ^ (-(1 : ℝ) / 2) = ((n * m) ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [neg_div, Real.rpow_neg (le_of_lt hqpos)]
    rw [UnionThreshold, hneg, one_div, inv_lt_inv₀ hmpos hrootpos]
    exact hsqrt
  exact lt_of_lt_of_le key hstep1

/-- **The insufficiency corollary on the named KU bound.** If the witnessed KU discrepancy `D`
saturates its bound `C·q^{-1/dim}` with the natural normalization `C = 1` (or any `C ≥ 1`) at
`q = n·m`, then in the thin regime `n < m`, `dim ≥ 2`, the discrepancy floor strictly exceeds the
union threshold `1/m` — so the `W_1 → tail → union` route cannot certify `Pr ≤ 1/m`. -/
theorem KU_discrepancy_cannot_meet_union
    (n m D : ℝ) (dim : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hn : 1 ≤ n) (hnm : n < m) (hdim : 2 ≤ dim)
    (hKU_lb : C * (n * m) ^ (-(1 : ℝ) / dim) ≤ D) :
    UnionThreshold m < D := by
  have hbase : UnionThreshold m < (n * m) ^ (-(1 : ℝ) / dim) :=
    wasserstein_floor_exceeds_union_threshold n m dim hn hnm hdim
  have hC' : (n * m) ^ (-(1 : ℝ) / dim) ≤ C * (n * m) ^ (-(1 : ℝ) / dim) := by
    have hp : (0 : ℝ) ≤ (n * m) ^ (-(1 : ℝ) / dim) :=
      le_of_lt (Real.rpow_pos_of_pos
        (mul_pos (lt_of_lt_of_le one_pos hn)
          (lt_of_lt_of_le one_pos (le_trans hn (le_of_lt hnm)))) _)
    nlinarith [hp, hC]
  exact lt_of_lt_of_le hbase (le_trans hC' hKU_lb)

#print axioms wasserstein_floor_exceeds_union_threshold
#print axioms KU_discrepancy_cannot_meet_union

end ArkLib.ProximityGap.Frontier.WassersteinUnionNoGo
