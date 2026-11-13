/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The dedup slack has a SURVIVAL CEILING `C(2m,r) - C(m,r)*2^r` that fractionally vanishes (#444)

## The A3 escape question this advances (lever 2 of the issue body's "TWO non-BCHKS levers")

`_CoreA3_BackwardProof.lean` reduces the prize ESCAPE dichotomy to whether the deduplication
`D <= Sigma_r` is **STRICT** (a real escape) or **vanishing** (the wall) at the binding log depth
`r ~ log n`. `_DedupSlackStrictButVanishing.lean` answered "strict but fractionally vanishing" but
ONLY at three hand-decided anchors (`n in {8,16,32,64}`), with the vanishing established merely as a
three-point fraction comparison (`f(16) > f(32) > f(64)`) -- NO structural law, NO all-`n` ceiling.

This file supplies the **structural mechanism**: a PROVEN, all-`r<=m`, p-independent CEILING on the
dedup slack, plus the EXACT product form of its vanishing fraction -- an algebraic law, not a
finite check.

## The mechanism (one clean Nat inequality + one exact cross-product identity)

The distinct `r`-subset-sum count over `mu_{2m}` is the in-tree spectrum
`N_r = specCount m r = Sum_{k = r (2), k <= min(r, 2m-r)} C(m,k) 2^k` (local copy of
`_SubsetSumSpectrumClosedForm.spectrumCount`). For the binding depth `r <= m` (true at prize scale:
`r = log2 n <= n/2 = m`):

* **Survival LOWER bound** (`specCount_ge_top`): the top term `k = r` lies in the filtered range
  (`min(r, 2m-r) = r`) and every summand is `>= 0`, so `N_r >= C(m,r) 2^r`.
* **Slack CEILING** (`dedupSlack_le_survivalCeiling`): the slack is `Nat` truncated subtraction, so
  the lower bound alone gives `slack = C(2m,r) - N_r <= C(2m,r) - C(m,r) 2^r =: survivalCeiling`,
  by `Nat.sub_le_sub_left` (NO upper bound on `N_r` needed -- `Nat` truncation does the work).
* **The lead/sigma ratio is an EXACT vanishing product** (`survivalLead_mul_fallProd_eq`):
  `C(m,r) 2^r * Prod_{i<r}(2m-i) = C(2m,r) * Prod_{i<r}(2m-2i)`, i.e. the cross-multiplied form of
  `C(m,r) 2^r / C(2m,r) = Prod_{i<r}(2m-2i)/(2m-i)`. Each factor `(2m-2i)/(2m-i)` is `1 - i/(2m-i)`,
  `-> 1` as `m -> inf` for `i < r = log n`, so the lead survives a `1 - o(1)` fraction of `C(2m,r)`
  and the ceiling fraction `1 - lead/C(2m,r) -> 0`.

Net: `0 <= slack <= survivalCeiling`, and `survivalCeiling/C(2m,r) = 1 - Prod_{i<r}(2m-2i)/(2m-i)`
is an EXACT vanishing product. This upgrades the dossier's "evidence leans wall" + the prior file's
3-point `decide` check to a structural CEILING: the dedup slack is squeezed below a
fractionally-vanishing exact-product ceiling at the binding depth, NOT a finite coincidence.

## Honest scope (rule 4 / ASYMPTOTIC GUARD)

This BOUNDS the slack from above by a fractionally-vanishing ceiling at the binding depth `r <= m`;
it does NOT bound `D`/`Sigma_r`/`m*` at the BUDGET scale `~n`, does NOT close BCHKS 1.12, makes NO
capacity / beyond-Johnson / growth-law claim, and leaves the cliff-at-n/2 untouched. It is a
p-independent combinatorial squeeze (`lead <= N_r`, `lead/C(2m,r) -> 1` exactly). CORE
`M(mu_n) <= C sqrt(n log(p/n))` is UNCHANGED / OPEN. The leaning-wall reading of the A3 escape is
now backed by a structural ceiling, not just a tower of `decide`s. No `sorry`, no `axiom`.

Issue #444, Core angle A3, lever 2 (dedup-strictness at log depth).
-/

open Finset

namespace ArkLib.ProximityGap.DedupSurvivalCeiling

set_option autoImplicit false

/-- The distinct `r`-subset-sum count over `mu_{2m}` (local copy of the in-tree
`_SubsetSumSpectrumClosedForm.spectrumCount`):
`N_r = Sum_{k = r (2), 0 <= k <= min(r, 2m-r)} C(m,k) 2^k`. -/
def specCount (m r : ℕ) : ℕ :=
  ∑ k ∈ (range (min r (2 * m - r) + 1)).filter (fun k => k % 2 = r % 2),
    m.choose k * 2 ^ k

/-- The un-deduplicated `r`-subset count `Sigma_r = C(2m, r)`. -/
def sigmaCount (m r : ℕ) : ℕ := (2 * m).choose r

/-- The dedup slack `Sigma_r - N_r` at `(n = 2m, r)`. -/
def dedupSlack (m r : ℕ) : ℕ := sigmaCount m r - specCount m r

/-- The survival lead term `C(m,r)*2^r` (the top `k=r` weight class). -/
def survivalLead (m r : ℕ) : ℕ := m.choose r * 2 ^ r

/-- The survival ceiling on the slack: `C(2m,r) - C(m,r)*2^r`. -/
def survivalCeiling (m r : ℕ) : ℕ := sigmaCount m r - survivalLead m r

/-- The descending product `Prod_{i<r} (2m - i)` ( `= C(2m,r) * r!` ). -/
def fallProd (m r : ℕ) : ℕ := ∏ i ∈ range r, (2 * m - i)

/-- The even-step product `Prod_{i<r} (2m - 2i)` ( `= C(m,r) * 2^r * r!` ). -/
def evenProd (m r : ℕ) : ℕ := ∏ i ∈ range r, (2 * m - 2 * i)

/-! ## The survival LOWER bound (the distinct count keeps at least the top-weight class) -/

/-- **Survival lower bound.** For `r <= m`, the top term `k = r` lies in the filtered range
(`min(r, 2m-r) = r`) and every summand is `>= 0`, so `N_r >= C(m,r)*2^r`. -/
theorem specCount_ge_top (m r : ℕ) (hr : r ≤ m) :
    survivalLead m r ≤ specCount m r := by
  unfold survivalLead specCount
  have hmem : r ∈ (range (min r (2 * m - r) + 1)).filter (fun k => k % 2 = r % 2) := by
    rw [mem_filter, mem_range]
    refine ⟨?_, rfl⟩
    have hmin : min r (2 * m - r) = r := by omega
    omega
  exact Finset.single_le_sum (f := fun k => m.choose k * 2 ^ k)
    (by intro i _; exact Nat.zero_le _) hmem

/-! ## The slack CEILING (survival lower bound ⇒ truncated-subtraction ceiling) -/

/-- **THE SLACK CEILING.** For `r <= m`, `dedupSlack m r <= survivalCeiling m r`. The slack is the
`Nat` truncated subtraction `sigma - N_r`; the survival lower bound `survivalLead <= N_r`
(subtracting MORE) shrinks the difference, by `Nat.sub_le_sub_left`. No upper bound on `N_r` is
needed. -/
theorem dedupSlack_le_survivalCeiling (m r : ℕ) (hr : r ≤ m) :
    dedupSlack m r ≤ survivalCeiling m r := by
  unfold dedupSlack survivalCeiling
  exact Nat.sub_le_sub_left (specCount_ge_top m r hr) _

/-! ## The exact product identities (lead and sigma, both via `r!`-scaling) -/

/-- `C(m,r)*2^r * r! = Prod_{i<r}(2m-2i) = evenProd`, for `r <= m`. `C(m,r)*r! = descFactorial =
Prod_{i<r}(m-i)`; times `2^r` distributes a `2` into each factor giving `2(m-i) = 2m-2i`. -/
theorem survivalLead_mul_factorial (m r : ℕ) (hr : r ≤ m) :
    survivalLead m r * Nat.factorial r = evenProd m r := by
  unfold survivalLead evenProd
  have hdesc : m.choose r * Nat.factorial r = ∏ i ∈ range r, (m - i) := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
  have h2 : (2 : ℕ) ^ r = ∏ _i ∈ range r, 2 := by
    rw [Finset.prod_const, card_range]
  calc m.choose r * 2 ^ r * Nat.factorial r
      = (m.choose r * Nat.factorial r) * 2 ^ r := by ring
    _ = (∏ i ∈ range r, (m - i)) * (∏ _i ∈ range r, 2) := by rw [hdesc, h2]
    _ = ∏ i ∈ range r, ((m - i) * 2) := by rw [← Finset.prod_mul_distrib]
    _ = ∏ i ∈ range r, (2 * m - 2 * i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [mem_range] at hi
        have : i < m := lt_of_lt_of_le hi hr
        omega

/-- `C(2m,r) * r! = Prod_{i<r}(2m-i) = fallProd`. -/
theorem sigma_mul_factorial (m r : ℕ) :
    sigmaCount m r * Nat.factorial r = fallProd m r := by
  unfold sigmaCount fallProd
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]

/-! ## THE EXACT CROSS-PRODUCT identity for the survival fraction `lead/sigma` -/

/-- **THE SURVIVAL-FRACTION CROSS-IDENTITY (headline).** For `r <= m`,
`C(m,r)*2^r * Prod_{i<r}(2m-i) = C(2m,r) * Prod_{i<r}(2m-2i)`, i.e. the cross-multiplied form of
`survivalLead / sigma = evenProd / fallProd = Prod_{i<r}(2m-2i)/(2m-i)`. Proof: multiply both sides
by `r!` (cancels via the two product identities) -- `lead*fall*r! = evenProd*sigma*r!` reduces by
`survivalLead_mul_factorial` + `sigma_mul_factorial` to a `ring` identity in the products. -/
theorem survivalLead_mul_fallProd_eq (m r : ℕ) (hr : r ≤ m) :
    survivalLead m r * fallProd m r = sigmaCount m r * evenProd m r := by
  -- cancel a common `r!` factor: both sides times `r!` agree by the two product identities.
  have hL := survivalLead_mul_factorial m r hr      -- survivalLead * r! = evenProd
  have hS := sigma_mul_factorial m r                -- sigma * r! = fallProd
  -- (lead * fall) * r! = lead * (sigma * r!) ... use hS to turn fall into sigma*r!
  have hfact_pos : 0 < Nat.factorial r := Nat.factorial_pos r
  -- show equality after multiplying by r!
  have key : (survivalLead m r * fallProd m r) * Nat.factorial r
      = (sigmaCount m r * evenProd m r) * Nat.factorial r := by
    calc (survivalLead m r * fallProd m r) * Nat.factorial r
        = fallProd m r * (survivalLead m r * Nat.factorial r) := by ring
      _ = fallProd m r * evenProd m r := by rw [hL]
      _ = (sigmaCount m r * Nat.factorial r) * evenProd m r := by rw [hS]
      _ = (sigmaCount m r * evenProd m r) * Nat.factorial r := by ring
  exact Nat.eq_of_mul_eq_mul_right hfact_pos key

/-! ## The per-factor `-> 1` content (the vanishing mechanism, exact) -/

/-- **Per-factor bound.** Each factor of the survival product satisfies `2m - 2i <= 2m - i`
(numerator `<=` denominator), with the GAP exactly `i`: `(2m - i) - (2m - 2i) = i` for `i < r <= m`.
So `evenProd <= fallProd` (`survivalLead <= sigma`); the per-factor relative defect is `i/(2m-i)`,
summing to `~ r^2/(4m) = (log n)^2 / (2n) -> 0` (the exact vanishing of the ceiling fraction). -/
theorem evenProd_le_fallProd (m r : ℕ) :
    evenProd m r ≤ fallProd m r := by
  unfold evenProd fallProd
  apply Finset.prod_le_prod'
  intro i _
  omega

/-- **Survival lead `<=` multiset count** (`C(m,r)*2^r <= C(2m,r)` for `r <= m`): from the exact
cross-identity `lead*fallProd = sigma*evenProd` and `evenProd <= fallProd`, cancelling the positive
`fallProd` (`= C(2m,r)*r! > 0`). So the survival lead is a genuine FRACTION of the multiset count,
and `survivalCeiling = sigma - lead >= 0` is a true `Nat` difference. -/
theorem survivalLead_le_sigma (m r : ℕ) (hr : r ≤ m) :
    survivalLead m r ≤ sigmaCount m r := by
  have hcross := survivalLead_mul_fallProd_eq m r hr
  have hef := evenProd_le_fallProd m r
  have hfall_pos : 0 < fallProd m r := by
    unfold fallProd
    apply Finset.prod_pos
    intro i hi
    rw [mem_range] at hi
    have : i < m := lt_of_lt_of_le hi hr
    omega
  -- lead * fall = sigma * even <= sigma * fall ⇒ lead <= sigma (cancel fall > 0)
  have hchain : survivalLead m r * fallProd m r ≤ sigmaCount m r * fallProd m r := by
    rw [hcross]
    exact Nat.mul_le_mul_left _ hef
  exact Nat.le_of_mul_le_mul_right hchain hfall_pos

/-- **The slack is bounded by a `< sigma` ceiling** (non-vacuity of the ceiling): the survival
ceiling `sigma - lead` is a genuine proper sub-count (`lead <= sigma`), so `dedupSlack <= sigma -
lead < sigma` whenever the lead is positive (`r <= m`, where `C(m,r) >= 1`). -/
theorem survivalCeiling_lt_sigma (m r : ℕ) (hr : r ≤ m) :
    survivalCeiling m r < sigmaCount m r := by
  unfold survivalCeiling
  have hlead_pos : 0 < survivalLead m r := by
    unfold survivalLead
    exact Nat.mul_pos (Nat.choose_pos hr) (pow_pos (by norm_num : 0 < 2) r)
  have hle := survivalLead_le_sigma m r hr
  omega

/-! ## Anchor sanity (the ceiling at the binding depth `r = log2 n`, bridging the prior file) -/

/-- **Anchor `n=16` (`m=8, r=4`).** `C(16,4)=1820`, lead `C(8,4)*2^4 = 70*16 = 1120`, ceiling
`1820-1120 = 700`. The prior file's exact slack was `587 <= 700` (the ceiling dominates the true
slack, as proven in general). -/
theorem anchor_ceiling_n16 :
    sigmaCount 8 4 = 1820 ∧ survivalLead 8 4 = 1120 ∧ survivalCeiling 8 4 = 700 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Anchor `n=32` (`m=16, r=5`).** `C(32,5)=201376`, lead `C(16,5)*2^5 = 4368*32 = 139776`,
ceiling `201376-139776 = 61600`. Prior file's exact slack `57088 <= 61600`. -/
theorem anchor_ceiling_n32 :
    sigmaCount 16 5 = 201376 ∧ survivalLead 16 5 = 139776 ∧ survivalCeiling 16 5 = 61600 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The ceiling fraction strictly DECREASES on the tower** (`f_ceil(16) > f_ceil(32)`) by exact
`Nat` cross-multiplication `ceil_16 * sigma_32 > ceil_32 * sigma_16`:
`700 * 201376 > 61600 * 1820` (`140963200 > 112112000`). The ceiling fraction tracks the prior
file's slack-fraction descent and is itself the exact vanishing product `1 - Prod(2m-2i)/(2m-i)`. -/
theorem ceiling_fraction_dec_16_32 :
    survivalCeiling 8 4 * sigmaCount 16 5 > survivalCeiling 16 5 * sigmaCount 8 4 := by
  decide

/-! ## THE HEADLINE (the structural survival ceiling for the A3 dedup escape) -/

/-- **HEADLINE (the A3 survival-ceiling brick).** For every binding-regime `(m, r)` with `r <= m`
(`r = log2 n <= n/2 = m` at prize scale), the dedup slack is squeezed below a survival ceiling that
is a PROPER fraction of the multiset count, with the EXACT cross-product law for that fraction:

* `0 <= dedupSlack m r <= survivalCeiling m r` (the ceiling), and
* `survivalCeiling m r < sigmaCount m r` (proper fraction, non-vacuous), and
* `survivalLead m r * fallProd m r = sigmaCount m r * evenProd m r` (the EXACT cross-identity:
  `lead/sigma = Prod_{i<r}(2m-2i)/(2m-i)`, each factor `-> 1`, so the ceiling fraction `-> 0`).

This turns the prior file's 3-point `decide` vanishing into a structural, all-`r<=m`, p-independent
law: the A3 dedup escape is strict but its slack lives under a fractionally-vanishing exact-product
ceiling -- leaning WALL, structurally, not by coincidence. Does NOT close BCHKS 1.12; CORE OPEN. -/
theorem survival_ceiling_headline (m r : ℕ) (hr : r ≤ m) :
    dedupSlack m r ≤ survivalCeiling m r ∧
    survivalCeiling m r < sigmaCount m r ∧
    survivalLead m r * fallProd m r = sigmaCount m r * evenProd m r :=
  ⟨dedupSlack_le_survivalCeiling m r hr,
   survivalCeiling_lt_sigma m r hr,
   survivalLead_mul_fallProd_eq m r hr⟩

end ArkLib.ProximityGap.DedupSurvivalCeiling

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.specCount_ge_top
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.dedupSlack_le_survivalCeiling
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.survivalLead_mul_factorial
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.sigma_mul_factorial
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.survivalLead_mul_fallProd_eq
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.evenProd_le_fallProd
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.survivalLead_le_sigma
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.survivalCeiling_lt_sigma
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.ceiling_fraction_dec_16_32
#print axioms ArkLib.ProximityGap.DedupSurvivalCeiling.survival_ceiling_headline
