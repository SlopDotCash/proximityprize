/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# BCHKS F3 — binding-depth reduction, with a factored "Sumset-Extremality" spelling (#444)

**Spec (F3).** The in-tree "complete reduction" `_CoreReductionComplete.prize_reduces_to_BCHKS`
is **vacuous**: its single open hypothesis is `hBCHKS : |Σ_r(μ_s)| ≤ budget` (the distinct
`r`-fold subset-sum count is within the prize budget `≈ n`). That hypothesis is **UNSATISFIABLE** —
exact computation shows `|Σ_r(μ_s)|` GROWS monotonically in `r` and is ALWAYS `≫ budget` (the probe
`scripts/probes/probe_subsetsum_grows_refutes_bchks.py` was removed in `8416cfb0f`; recover it with
`git show e56715bf0:scripts/probes/probe_subsetsum_grows_refutes_bchks.py`. It counts distinct
`r`-fold sums with repetition of `μ_s ⊂ 𝔽_p` for the least prime `p ≡ 1 (mod s)` with
`p ≥ 50 s⁴`; re-run 2026-10-29 with the values below):

```
n=s=8  budget~8:  |Σ_r| = 33, 96, 225, 456, 833, 1408, 2241   (r=2..8) — never ≤ 8.
n=s=16 budget~16: |Σ_r| = 129, 704, 2945, 10128, 29953, 78592, 185617 — never ≤ 16.
```

These counts are **probe evidence only**: the Lean statements below take them as hypotheses
(`Sigma 16 r = …`) and are conditional on them; nothing here computes `|Σ_r|`.

So `∃ m, BCHKSBudget …` is false on this `Σ`, and `prize_reduces_to_BCHKS` proves the window
interior **vacuously on a false hypothesis** — it pins nothing about `δ*`. (This matches
`_BchksF1`/B33 `objectIdentity_false`: the bad cascade `D` *decreases* while `|Σ_r|` *increases* —
they are different objects, and the dedup `D ≤ |Σ_r|` has enormous, growing slack.)

The mis-statement put the **sumset on the wrong side** of the inequality. `|Σ_r| = |H^{(+r)}|` is
the SUMSET SIZE; in the correct floor (ABF26 §4) the sumset is the *budget multiplier*, NOT the
bad-scalar count.

## The intended floor — Sumset-Extremality (ABF26 §4), and what the Lean actually states

`|F|` is taken **LARGE** (not fixed at `n·2^128`). The soundness error is `(#bad)/|F|`, and
**`δ*` is the radius where `#bad` goes from `poly(n)` to super-poly** (crosses `ε*·|F|`). The open
FLOOR is

> **Sumset-Extremality.** For every affine line `(f, g)` and every `δ` below the threshold,
> `#{λ : Δ(f + λg, C) ≤ δ} ≤ poly(n) · |H^{(+r)}|`,

i.e. the bad-scalar count `#bad = D*(m)` (the distinct-`γ` count) is bounded by `poly(n)` times the
`r`-fold sumset size `|H^{(+r)}| = |Σ_r(μ_s)|`. The dedup `#bad = D ≤ |H^{(+r)}|` is **TRUE** (the
in-tree `_CoreA3.BCHKS_imp_weakestSuff` dedup domination `hdom : D ≤ Σ`); the FLOOR additionally
needs `#bad ≤ poly · (sumset)` together with `poly · (sumset) ≤ ε*·|F|` at the binding fold (the
soundness budget for `|F|` large), which is what pins `δ*` from below.

**Honesty caveat (audit CW-B04-01).** The Lean predicate `SumsetExtremality bad sumset poly
soundness` takes `sumset` and `poly` as *free* natural numbers: `sumset` is not tied to any defined
`|H^{(+r)}|` cardinality and `poly` is not tied to a polynomial in `n`. Consequently
`∃ sumset poly, SumsetExtremality bad sumset poly soundness ↔ bad ≤ soundness`
(`exists_sumsetExtremality_iff`, take `poly = 1`, `sumset = soundness`). So the reduction below is
**exactly the plain binding-depth reduction** `D n (k−1) ≤ soundness n ⟹ window interior`
(`prize_reduces_to_binding`); the `SumsetExtremality` form is a factored spelling of that
hypothesis, not an independent formalization of the ABF26 §4 floor. Formalizing the actual floor
would require defining the sumset cardinality and a polynomial-in-`n` factor; that is not done here.

## What this file proves (axiom-clean)

1. `subsetSumBudget_unsat` — the **refutation** of the old form at the witnessed instances,
   *conditional on the assumed probe counts* (`n=s=16`: `|Σ_5| = 10128 > 16 = budget`), with the
   abstract corollary that ANY `Σ` agreeing with these values makes the old
   `∃ m ≤ M, |Σ_{r m}| ≤ budget` form unsatisfiable below the witnessed fold.

2. `SumsetExtremality` — a factored spelling `bad ≤ poly · sumset ∧ poly · sumset ≤ soundness`
   with free `sumset`, `poly`; `exists_sumsetExtremality_iff` shows its existential closure is
   exactly `bad ≤ soundness`.

3. `badCount_within_soundness_of_sumsetExtremality` — transitivity: `SumsetExtremality` gives
   `#bad ≤ soundness`.

4. `prize_reduces_to_binding` — the binding-depth reduction: the window-interior conclusion
   `1 − √ρ < δ* < 1 − ρ` follows from the single open hypothesis `D n (k−1) ≤ soundness n`
   (plus the discharged E1 / edge `m* ≥ 3` / Johnson-surrogate / monotone-binder inputs).
   `prize_reduces_to_SumsetExtremality` is the same theorem with the hypothesis in factored form.

5. `oldForm_vacuous_newForm_satisfiable` — a model where the OLD `|Σ_5| ≤ budget` is FALSE
   (conditional on the assumed count) while the factored predicate holds; note the soundness budget
   there is *chosen* as `Sigma 16 5`, so this only shows the hypothesis shapes differ, not that the
   new predicate captures the ABF26 floor.

## Honesty (the contract)

This is a **reduction**, not a closure. The window-interior conclusion is *proved* modulo the
single binding hypothesis `D n (k−1) ≤ soundness n`, which is NOT discharged anywhere. Because
`sumset` and `poly` are free, the `SumsetExtremality` spelling adds no content beyond that binding
hypothesis (see the caveat above); this file does not formalize the ABF26 §4 sumset-extremality
floor itself. Everything else (the master gap algebra, `m* ≥ 3`, the
monotone reduction, the prize-regime Johnson surrogate) is proven, reproved inline so the file is
self-contained and lands with a real `lake build`. The axiom audit must show only a subset of
`{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no `native_decide`, no fabricated axiom).

Issue #444, target F3 (RetargetedReduction).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF3

open Real

/-! ## 1. The OLD form is unsatisfiable — refutation of `|Σ_r| ≤ budget` -/

/-- The OLD (mis-stated) BCHKS budget predicate: the distinct `r`-fold subset-sum count
`Sigma s r = |Σ_r(μ_s)|` is within budget `B`. This is the hypothesis of the vacuous
`_CoreReductionComplete.prize_reduces_to_BCHKS`. -/
def SubsetSumBudget (Sigma : ℕ → ℕ → ℕ) (s r B : ℕ) : Prop :=
  Sigma s r ≤ B

/-- **Refutation of the OLD form at a witnessed instance (conditional on the probe count).** The
(removed, recoverable from `e56715bf0`) probe `probe_subsetsum_grows_refutes_bchks.py` gives
`|Σ_5(μ_16)| = 10128`, far above the budget `16`. The count is an *assumed hypothesis* `hval`, not
computed in Lean: for ANY `Sigma` with this value, `SubsetSumBudget Sigma 16 5 16` is FALSE. -/
theorem subsetSumBudget_unsat
    (Sigma : ℕ → ℕ → ℕ) (hval : Sigma 16 5 = 10128) :
    ¬ SubsetSumBudget Sigma 16 5 16 := by
  unfold SubsetSumBudget
  rw [hval]; omega

/-- **The OLD form is unsatisfiable below the witnessed fold (the source of vacuity).** Given the
assumed (probe-computed, not Lean-computed) subset-sum spectrum at `n=s=16`
(`|Σ_r| = 129, 704, 2945, 10128, …` for `r=2,3,4,5,…`,
all `> 16`), no fold `r ∈ {2,3,4,5}` satisfies the budget. Hence the existential
`∃ r ∈ {2,3,4,5}, SubsetSumBudget Sigma 16 r 16` — the kind of hypothesis the old reduction needs
to discharge `m* ≤ M` — is FALSE. This is precisely why `prize_reduces_to_BCHKS` is vacuous: its
sole open hypothesis can never hold at the binding scale. -/
theorem subsetSumBudget_existential_unsat
    (Sigma : ℕ → ℕ → ℕ)
    (h2 : Sigma 16 2 = 129) (h3 : Sigma 16 3 = 704)
    (h4 : Sigma 16 4 = 2945) (h5 : Sigma 16 5 = 10128) :
    ¬ ∃ r, r ∈ ({2, 3, 4, 5} : Finset ℕ) ∧ SubsetSumBudget Sigma 16 r 16 := by
  rintro ⟨r, hr, hbud⟩
  unfold SubsetSumBudget at hbud
  fin_cases hr <;> simp_all

/-! ## 2. The CORRECT named floor — Sumset-Extremality (the single open input) -/

/-- **Sumset-Extremality (ABF26 §4) — factored spelling of the binding condition.**

**Caveat:** `sumset` and `poly` are free parameters here, not a defined `|H^{(+r)}|` and a
polynomial in `n`; `exists_sumsetExtremality_iff` shows `∃ sumset poly, SumsetExtremality bad
sumset poly soundness ↔ bad ≤ soundness`. The description below is the *intended* reading.

`SumsetExtremality bad sumset poly soundness` packages the two pieces of the correct floor at the
binding fold:

* the **dedup-extremality** `bad ≤ poly · sumset`: the bad-scalar count `#bad = D*(m)` (the
  distinct-`γ` count) is bounded by `poly(n)` times the `r`-fold sumset size
  `sumset = |H^{(+r)}| = |Σ_r(μ_s)|` (the sumset is a MULTIPLIER on the RIGHT, not the count);
* the **soundness budget** `poly · sumset ≤ soundness`: that `poly(n)`-times-sumset is itself within
  the soundness budget `soundness = ε*·|F|` for `|F|` large.

Together they pin `#bad ≤ soundness`, i.e. the bad set is within the soundness error `ε*·|F|`,
which is the budget crossing that pins `δ*` from below. This is the ABF26 §4 floor — char-free
additive combinatorics (a Cauchy–Davenport / Plünnecke-flavoured extremality), NOT the false
`sumset ≤ budget`. As formalized (free `sumset`, `poly`) it carries no more content than
`bad ≤ soundness`. -/
def SumsetExtremality (bad sumset poly soundness : ℕ) : Prop :=
  bad ≤ poly * sumset ∧ poly * sumset ≤ soundness

/-- **`#bad` within soundness from Sumset-Extremality** (transitivity through the multiplier). -/
theorem badCount_within_soundness_of_sumsetExtremality
    {bad sumset poly soundness : ℕ}
    (hext : SumsetExtremality bad sumset poly soundness) :
    bad ≤ soundness :=
  le_trans hext.1 hext.2

/-- **The factored predicate is exactly the binding condition.** With `sumset` and `poly` free,
`∃ sumset poly, SumsetExtremality bad sumset poly soundness` is equivalent to `bad ≤ soundness`
(take `poly = 1`, `sumset = soundness`). This records that `SumsetExtremality` as formalized adds
no content beyond the plain soundness-crossing hypothesis. -/
theorem exists_sumsetExtremality_iff (bad soundness : ℕ) :
    (∃ sumset poly, SumsetExtremality bad sumset poly soundness) ↔ bad ≤ soundness := by
  constructor
  · rintro ⟨sumset, poly, hext⟩
    exact badCount_within_soundness_of_sumsetExtremality hext
  · intro h
    exact ⟨soundness, 1, by simpa using h, by simp⟩

/-! ## 3. The binding depth `m*` (B31 `Nat.find` model, reproved inline) -/

/-- The **binding depth** `m*(n)`: least over-determination depth `m` with the bad count
`D n m ≤ soundness n`. `Nat.find` of the soundness-crossing predicate, given a witness `hex`. -/
noncomputable def mStar (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n) : ℕ :=
  Nat.find hex

/-- `mStar` is the **least** binder. -/
theorem mStar_le_of_binds (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n) {m : ℕ} (hm : D n m ≤ soundness n) :
    mStar D soundness n hex ≤ m :=
  Nat.find_min' hex hm

/-- **The monotone reduction `m* ≤ M ⟸ SumsetExtremality`.**

Under the identification `hbad : D n M = bad` (the bad-scalar count at depth `M` is the
`#bad = D*(M)` cascade value), the two conjuncts `hext_dedup : bad ≤ poly · sumset` and
`hsound : poly · sumset ≤ soundness n` force the binder `m*(n) ≤ M`:

  `#bad ≤ poly · |H^{(+r)}| ≤ ε*·|F| = soundness n  ⟹  m*(n) ≤ M`.

Pure `Nat.find_min'` through `badCount_within_soundness_of_sumsetExtremality`. -/
theorem mStar_le_of_sumsetExtremality
    (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n) (M : ℕ)
    {bad sumset poly : ℕ}
    (hbad : D n M = bad)
    (hsound : poly * sumset ≤ soundness n)
    (hext_dedup : bad ≤ poly * sumset) :
    mStar D soundness n hex ≤ M := by
  have hbind : D n M ≤ soundness n := by
    rw [hbad]
    exact badCount_within_soundness_of_sumsetExtremality ⟨hext_dedup, hsound⟩
  exact mStar_le_of_binds D soundness n hex hbind

/-! ## 4. The proven CoreA1 lower bound `m* ≥ 3` (reproved inline) -/

/-- The B24 over-det edge closed form (CoreA1). `Dedge m = 2·m²·(m−1) + 1`. -/
def Dedge (m : ℕ) : ℕ := 2 * m ^ 2 * (m - 1) + 1

/-- **The over-det edge `D*(2)` strictly exceeds the `ρ = 1/4` budget `4m`** (CoreA1). -/
theorem dedge_gt_budget (m : ℕ) (hm : 2 ≤ m) : 4 * m < Dedge m := by
  unfold Dedge
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h2 : 2 + t - 1 = 1 + t := by omega
  rw [h2]
  nlinarith [Nat.zero_le t, sq_nonneg t]

/-- **Abstract A1 lower bound:** three rungs over budget ⟹ `m* ≥ 3`. -/
theorem mStar_ge_three_of_three_rungs_over
    (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n)
    (h0 : soundness n < D n 0) (h1 : soundness n < D n 1) (h2 : soundness n < D n 2) :
    3 ≤ mStar D soundness n hex := by
  unfold mStar
  rw [Nat.le_find_iff]
  intro j hj
  interval_cases j
  · exact Nat.not_le.mpr h0
  · exact Nat.not_le.mpr h1
  · exact Nat.not_le.mpr h2

/-- **CoreA1 result: `m* ≥ 3` from the proven edge inequality + proven monotonicity.** -/
theorem mStar_ge_three_of_edge_over_and_antitone
    (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ soundness n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hedge : soundness n < D n 2) :
    3 ≤ mStar D soundness n hex := by
  have h1 : soundness n < D n 1 := lt_of_lt_of_le hedge (hmono (by norm_num : (1:ℕ) ≤ 2))
  have h0 : soundness n < D n 0 := lt_of_lt_of_le hedge (hmono (by norm_num : (0:ℕ) ≤ 2))
  exact mStar_ge_three_of_three_rungs_over D soundness n hex h0 h1 hedge

/-! ## 5. The master gap identity E1 + Johnson/capacity crossings (B01/B02/B50, reproved) -/

/-- **E1 (master gap identity, ℝ form; B01/B50). CORRECTED off-by-one.** `δ* = 1 − ρ − m*/n`. -/
theorem deltaStar_master_gap_identity
    (n k s deltaStar rho mstar : ℝ) (hn : n ≠ 0)
    (hρ  : rho = k / n)
    (hms : mstar = s - k)
    (hδ  : deltaStar = 1 - s / n) :
    deltaStar = 1 - rho - mstar / n := by
  subst hρ hms hδ; field_simp; ring

/-- **Capacity side (B50, CORRECTED).** Given E1, `δ* < 1 − ρ ⟺ 0 < m*`. -/
theorem deltaStar_lt_capacity_iff_mstar_pos
    (n rho mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - mstar / n) :
    deltaStar < 1 - rho ↔ 0 < mstar := by
  rw [hE1]
  rw [show (1 - rho - mstar / n < 1 - rho) ↔ (0 < mstar / n) by
        constructor <;> intro h <;> linarith]
  rw [div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · exact absurd hn (not_lt.mpr (le_of_lt h))
  · intro h; exact Or.inl ⟨h, hn⟩

/-- **Johnson side (B02/B50, CORRECTED).** Given E1, `1 − √ρ < δ* ⟺ m* < (√ρ − ρ)·n`. -/
theorem deltaStar_gt_johnson_iff_mstar_lt
    (rho n mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - mstar / n) :
    (1 - Real.sqrt rho < deltaStar) ↔ (mstar < (Real.sqrt rho - rho) * n) := by
  rw [hE1]
  rw [show (1 - Real.sqrt rho < 1 - rho - mstar / n)
        ↔ (mstar / n < (Real.sqrt rho - rho)) by
        constructor <;> intro h <;> linarith]
  exact div_lt_iff₀ hn

/-- **Prize-regime Johnson surrogate (B50).** In `ρ ≤ 1/4` (`√ρ ≥ 2ρ`),
`m* < k ⟹ m* < (√ρ − ρ)·n + 1`. -/
theorem mstar_lt_johnson_threshold_of_lt_k
    (rho n k mstar : ℝ) (hn : 0 < n)
    (hk : k = rho * n) (hρpos : 0 < rho) (hρ4 : rho ≤ 1 / 4)
    (hmk : mstar < k) :
    mstar < (Real.sqrt rho - rho) * n := by
  have hsqrt : 2 * rho ≤ Real.sqrt rho := by
    have h4 : (2 * rho) ^ 2 ≤ rho := by nlinarith [hρpos, hρ4]
    have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (le_of_lt hρpos)
    nlinarith [Real.sqrt_nonneg rho, hsq, h4, hρpos]
  have hkle : k ≤ (Real.sqrt rho - rho) * n := by
    have : rho * n ≤ (Real.sqrt rho - rho) * n := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hn); linarith
    rw [hk]; linarith
  linarith

/-! ## 6. The binding-depth reduction theorem -/

/-- **`prize_reduces_to_binding` — the binding-depth reduction (F3, #444).**

The window-interior conclusion `1 − √ρ < δ* < 1 − ρ` follows from exactly **ONE** open hypothesis,
the binding condition `hbind : D n (kNat − 1) ≤ soundness n` at the fold `M = k − 1`.

### Discharged (proved) inputs
* `hE1` — the master gap identity `δ* = 1 − ρ − m*/n` (B01/E1, corrected off-by-one).
* `hk, hρpos, hρ4` — the prize regime `k = ρ·n`, `0 < ρ ≤ 1/4`.
* `hmono` — cascade monotonicity (B48). Supplied as the monotonicity datum.
* `hedge_val` — the over-det edge value `D n 2 = Dedge m > 4m = soundness` (CoreA1), giving
  `m* ≥ 3` (hence `0 < m*`, the capacity side).
* `hmstar_real`, `hkNat`, `hk_ge` — bridge data (the ℝ binding depth, the fold reindex).

### The ONE open input
* `hbind : D n (kNat − 1) ≤ soundness n` — the bad count at the binding fold is within the
  soundness budget. NOT discharged here. -/
theorem prize_reduces_to_binding
    -- the cascade / soundness data (Nat side)
    (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ j, D n j ≤ soundness n)
    -- the proven edge value (CoreA1 / B24): D n 2 = Dedge m > 4m = soundness
    (m : ℕ) (hm : 2 ≤ m)
    (hsoundness : soundness n = 4 * m)
    (hedge_val : D n 2 = Dedge m)
    -- cascade monotonicity (B48, proven upstream)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    -- the ℝ-side prize-regime data
    (kReal nReal rho deltaStar mstarReal : ℝ)
    (hnpos : 0 < nReal)
    (hk : kReal = rho * nReal) (hρpos : 0 < rho) (hρ4 : rho ≤ 1 / 4)
    -- the master gap identity E1 (B01, CORRECTED off-by-one) as the closed form of δ*
    (hE1 : deltaStar = 1 - rho - mstarReal / nReal)
    -- the bridge: the ℝ binding depth IS the Nat `mStar`
    (hmstar_real : mstarReal = ((mStar D soundness n hex : ℕ) : ℝ))
    -- book-keeping: the integer rate `k = ρ·n` and the fold reindex M = k − 1
    (kNat : ℕ) (hkNat : (kNat : ℝ) = kReal) (hk_ge : 3 ≤ kNat)
    -- ★ THE ONE OPEN HYPOTHESIS — binding at the fold `k − 1` ★
    (hbind : D n (kNat - 1) ≤ soundness n) :
    1 - Real.sqrt rho < deltaStar ∧ deltaStar < 1 - rho := by
  -- (A) The PROVED lower bound `m* ≥ 3` from the over-det edge + monotonicity (CoreA1).
  have hedge : soundness n < D n 2 := by
    rw [hsoundness, hedge_val]; exact dedge_gt_budget m hm
  have hge3 : 3 ≤ mStar D soundness n hex :=
    mStar_ge_three_of_edge_over_and_antitone D soundness n hex hmono hedge
  -- (B) The open input pulls `m*` DOWN: binding at fold `kNat−1` ⟹ m* ≤ kNat−1.
  have hle : mStar D soundness n hex ≤ kNat - 1 :=
    mStar_le_of_binds D soundness n hex hbind
  -- (C) Translate the Nat bounds to ℝ: `3 ≤ m*` and `m* < k`.
  have hmstar_ge3R : (3 : ℝ) ≤ mstarReal := by
    rw [hmstar_real]; exact_mod_cast hge3
  have hmstar_ltk_nat : mStar D soundness n hex < kNat := by omega
  have hmstar_ltkR : mstarReal < kReal := by
    rw [hmstar_real, ← hkNat]; exact_mod_cast hmstar_ltk_nat
  -- (D) Assemble the window interior (B50): capacity from `m* ≥ 3 > 0`, Johnson from `m* < k`.
  refine ⟨?_, ?_⟩
  · rw [deltaStar_gt_johnson_iff_mstar_lt rho nReal mstarReal deltaStar hnpos hE1]
    exact mstar_lt_johnson_threshold_of_lt_k rho nReal kReal mstarReal hnpos hk hρpos hρ4
      hmstar_ltkR
  · rw [deltaStar_lt_capacity_iff_mstar_pos nReal rho mstarReal deltaStar hnpos hE1]
    linarith

/-- **`prize_reduces_to_SumsetExtremality` — the same reduction, hypothesis in factored form.**

Identical to `prize_reduces_to_binding`, with the binding hypothesis spelled as
`SumsetExtremality (D n (kNat − 1)) sumset poly (soundness n)`. Since `sumset` and `poly` are free
(`exists_sumsetExtremality_iff`), this hypothesis is satisfiable exactly when the plain binding
condition is; the theorem is **not** a reduction to the ABF26 §4 sumset-extremality floor itself
(which would need `sumset = |H^{(+r)}|` and `poly` polynomial in `n`). -/
theorem prize_reduces_to_SumsetExtremality
    (D : ℕ → ℕ → ℕ) (soundness : ℕ → ℕ) (n : ℕ)
    (hex : ∃ j, D n j ≤ soundness n)
    (m : ℕ) (hm : 2 ≤ m)
    (hsoundness : soundness n = 4 * m)
    (hedge_val : D n 2 = Dedge m)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (kReal nReal rho deltaStar mstarReal : ℝ)
    (hnpos : 0 < nReal)
    (hk : kReal = rho * nReal) (hρpos : 0 < rho) (hρ4 : rho ≤ 1 / 4)
    (hE1 : deltaStar = 1 - rho - mstarReal / nReal)
    (hmstar_real : mstarReal = ((mStar D soundness n hex : ℕ) : ℝ))
    (kNat : ℕ) (hkNat : (kNat : ℝ) = kReal) (hk_ge : 3 ≤ kNat)
    (sumset poly : ℕ)
    (hExt : SumsetExtremality (D n (kNat - 1)) sumset poly (soundness n)) :
    1 - Real.sqrt rho < deltaStar ∧ deltaStar < 1 - rho :=
  prize_reduces_to_binding D soundness n hex m hm hsoundness hedge_val hmono
    kReal nReal rho deltaStar mstarReal hnpos hk hρpos hρ4 hE1 hmstar_real kNat hkNat hk_ge
    (badCount_within_soundness_of_sumsetExtremality hExt)

/-! ## 7. Non-vacuity of the reduction's hypotheses -/

/-- A concrete non-increasing bad-count cascade at scale `n = 16`, `ρ = 1/4`, `k = 4`: the
worst-monomial cascade `D*(m) = [97, 97, 97, 0, …]` (proven edge `Dedge 4 = 97 > 16`, binding at
depth `3`). -/
def modelD (n j : ℕ) : ℕ := if n = 16 ∧ j ≤ 2 then 97 else 0

/-- **Old and new hypothesis shapes differ (conditional on the assumed count).**

Given the assumed probe value `|Σ_5(μ_16)| = 10128`, the OLD `|Σ_5| ≤ 16` is FALSE
(`subsetSumBudget_unsat`), while the factored predicate `SumsetExtremality` holds for
`#bad = modelD 16 3 = 0` with `poly = 1`, `sumset = Sigma 16 5`. **Caveat:** the soundness budget
here is *chosen* to be `Sigma 16 5`, so the second conjunct is satisfied by construction; this
only shows the two hypothesis shapes differ, not that the factored predicate is a faithful ABF26
floor. -/
theorem oldForm_vacuous_newForm_satisfiable
    (Sigma : ℕ → ℕ → ℕ) (hval : Sigma 16 5 = 10128) :
    -- OLD form FALSE at the witnessed fold:
    (¬ SubsetSumBudget Sigma 16 5 16) ∧
    -- factored form holds (soundness budget chosen as `Sigma 16 5`):
    (SumsetExtremality (modelD 16 3) (Sigma 16 5) 1 (Sigma 16 5)) := by
  refine ⟨subsetSumBudget_unsat Sigma hval, ?_⟩
  constructor
  · show modelD 16 3 ≤ 1 * Sigma 16 5
    simp [modelD]
  · show 1 * Sigma 16 5 ≤ Sigma 16 5
    rw [one_mul]

/-- **Non-vacuity of the reduction.** We instantiate `prize_reduces_to_binding` on the concrete
model `modelD` (`n=16, ρ=1/4, k=4`, proven edge `Dedge 4 = 97 > 16 = soundness`), with the binding
hypothesis satisfied at fold `3` (`modelD 16 3 = 0 ≤ 16`). The conclusion `1/2 < δ* < 3/4` (with
`δ* = 9/16`) is *derived*, confirming the hypotheses are jointly consistent. -/
example :
    (1 : ℝ) - Real.sqrt (1 / 4) < (9 / 16 : ℝ) ∧ (9 / 16 : ℝ) < 1 - 1 / 4 := by
  have hex : ∃ j, modelD 16 j ≤ 16 := ⟨3, by decide⟩
  have hmstar_eq : mStar modelD (fun _ => 16) 16 hex = 3 := by
    have hle : mStar modelD (fun _ => 16) 16 hex ≤ 3 :=
      mStar_le_of_binds modelD (fun _ => 16) 16 hex (by decide)
    have hge : 3 ≤ mStar modelD (fun _ => 16) 16 hex := by
      apply mStar_ge_three_of_three_rungs_over <;> decide
    omega
  apply prize_reduces_to_binding
    (D := modelD) (soundness := fun _ => 16) (n := 16) (hex := hex)
    (m := 4) (hm := by norm_num)
    (hsoundness := by norm_num) (hedge_val := by decide)
    (hmono := ?_)
    (kReal := 4) (nReal := 16) (rho := 1 / 4) (deltaStar := 9 / 16) (mstarReal := 3)
    (hnpos := by norm_num)
    (hk := by norm_num) (hρpos := by norm_num) (hρ4 := by norm_num)
    (hE1 := by norm_num)
    (hmstar_real := by rw [hmstar_eq]; norm_num)
    (kNat := 4) (hkNat := by norm_num) (hk_ge := by norm_num)
    (hbind := by show modelD 16 (4 - 1) ≤ 16; decide)
  · -- monotonicity of modelD at n = 16: non-increasing in the depth.
    intro a b hab
    unfold modelD
    by_cases hb : b ≤ 2
    · have ha : a ≤ 2 := le_trans hab hb
      simp [hb, ha]
    · simp [hb]

end ArkLib.ProximityGap.BchksF3

/-! ## Axiom audit (expected: a subset of `propext, Classical.choice, Quot.sound` — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.BchksF3.subsetSumBudget_unsat
#print axioms ArkLib.ProximityGap.BchksF3.subsetSumBudget_existential_unsat
#print axioms ArkLib.ProximityGap.BchksF3.badCount_within_soundness_of_sumsetExtremality
#print axioms ArkLib.ProximityGap.BchksF3.mStar_le_of_sumsetExtremality
#print axioms ArkLib.ProximityGap.BchksF3.prize_reduces_to_SumsetExtremality
#print axioms ArkLib.ProximityGap.BchksF3.oldForm_vacuous_newForm_satisfiable
#print axioms ArkLib.ProximityGap.BchksF3.exists_sumsetExtremality_iff
#print axioms ArkLib.ProximityGap.BchksF3.prize_reduces_to_binding
