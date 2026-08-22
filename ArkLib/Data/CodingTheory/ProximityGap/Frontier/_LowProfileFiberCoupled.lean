/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R2B_LargeZeroWitnessSplit

/-!
# LANE S1 (#466): the z-COUPLED low-profile sum carries a q-power — REFUTED, next split named

The weld's `hlow` production obligation, after the per-fiber uniqueness of `_LowProfileFiberBound`
and the witness split of `_R2B_LargeZeroWitnessSplit`, reduces the bad-scalar count on a
large-zero-SAFE line to the **z-coupled threshold-choose sum**
(`lineBadScalars_card_le_thresholdChoose_sum` / `mcaEvent_filter_card_le_thresholdChoose_sum`):

  `#bad ≤ Σ_{t<a} (if t + s < a then 0 else choose(z,t)) · ⌊s/(a−t)⌋`,   `z = #zeroSet(u₁)`,
  `s = #support(u₁)`,

which is the best the *per-fiber* method yields: each stratum is bounded via
`#stratum(t) ≤ choose(z,t)·D(t)` with `D(t) ≤ 1` (uniqueness / MDS endpoint), so the sum above is
exactly the **coupled** budget `Σ_t choose(z,t)·D(t)·⌊s/(a−t)⌋` at its best case `D(t)=1`.

Round-4 (lane L1) killed the *uncoupled* envelope `(max_t D(t))·Σ_t choose(z,t)⌊s/(a−t)⌋`.  The
surviving question (dossier v3 §15 survivor 1): **does the z-coupling — coefficients `choose(z,t)`
that depend on `t` — keep the sum sub-`q` where the uncoupled envelope did not?**

## Verdict: NO.  The coupled sum still carries a `q`-power.  (Machine countermodel below.)

`scripts/probes/probe_466_lowprofile_coupled.py` (`_out_466_lowprofile_coupled.txt`, n=8,16, three
generic primes + the generalized-Fermat resonant family p∈{17,257}) measures, on large-zero-safe
lines:
* `W_true = Σ_t #stratum(t)·⌊s/(a−t)⌋` — the ACTUAL weld weight — stays `≤ Λ·s` (poly; `≤ 46` at
  n=16, tracking the appearing-list size `Λ`);
* `W_coup = Σ_t choose(z,t)·D(t)·⌊s/(a−t)⌋` — the provable coupled bound — EXPLODES: the
  `coup/true` ratio grows `2× → 18× → 120× → 715×`, driven by a **single realized codeword** at a
  high stratum `t` where `choose(z,t)` is a central binomial but the **occupancy**
  `#{S : exact fiber ≠ ∅}/choose(z,t) → 0` (e.g. `1/715`).  Concretely `(n,a,z,s)=(16,5,13,3)`,
  `Λ=1`, `W_true=3`, but the threshold-choose bound `= 2509`.

The coupling does NOT rescue the sum: `choose(z,t)` is a `q`-power (central binomial at prize
`z,t = Θ(n)`) and `D(t) ≥ 1` is *realized* at the top stratum, so the bound is
`≥ choose(z, a−1)`, exponential in the block length, while `W_true` is poly.  The gap is precisely
the occupancy — the choose-decomposition `#stratum(t) ≤ choose(z,t)·D(t)` overcounts by the number
of EMPTY `t`-subsets, and on the small (Johnson-radius) appearing ball almost all are empty.

This file proves, axiom-clean:

1. `thresholdChooseSum_eq_inTree` — the abstract sum IS the literal RHS of the in-tree bound (`rfl`).
2. `top_term_le_thresholdChooseSum` — the sum is `≥ choose(z, a−1)·s` (drop to the top stratum).
3. `two_pow_lt_centralBinom` / `two_pow_lt_thresholdChooseSum_family` — on the realized diagonal
   family `z = 2m`, `a = m+1` the sum is `> 2^m`: **exponential in the length**, i.e. a `q`-power.
4. `thresholdChooseSum_probe_16` — the exact probe instance `thresholdChooseSum 5 13 3 = 2509`.
5. `thresholdChooseSum_unbounded` — **no budget `B` bounds the coupled sum**: `∀ B, ∃ instance`
   with the bound `> B` (the precise sense in which the coupling fails to be sub-`q`).
6. `trueWeight_le_list_card_mul` — the DECOUPLING: the true weld weight is `≤ Λ·s`, poly in the
   appearing-list size — the two objects are not the same, the coupled bound is not tight.

**Next split (named).**  The only sub-`q` object is the true stratum count itself,
`#stratum(t) = Σ_S D_exact(S) ≤ Λ = #lineAppearingCodewords` — the punctured list size.  Named here
`PuncturedListBudget`.  The map `docs/kb/deltastar-466b-hlow-map-2026-07-01.md` §3 proves this is
the SAME beyond-Johnson list-size problem as the far branch (H1): Johnson-equivalent-hard.  So the
per-fiber weld route is closed; the only remaining weld path is a direct punctured-list bound, not
any refinement of the `choose(z,t)·D(t)` decomposition.

Issue #466, dossier v3 §15 survivor 1.  Probe: `scripts/probes/probe_466_lowprofile_coupled.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.LowProfileCoupled

open ProximityGap ProximityGap.SpikeFloor ProximityGap.Ownership
open ProximityGap.LargeZeroWitnessSplit

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 0. The coupled / threshold-choose sum (the object the weld's `hlow` must fit into) -/

/-- The **z-coupled threshold-choose sum** — the provable per-fiber upper bound on the bad-scalar
count of a large-zero-safe line (best case `D(t) = 1`).  `z = #zeroSet(u₁)`, `s = #support(u₁)`. -/
def thresholdChooseSum (a z s : ℕ) : ℕ :=
  ∑ t ∈ Finset.range a, (if t + s < a then 0 else z.choose t) * (s / (a - t))

/-- **Faithfulness.**  `thresholdChooseSum` is *definitionally* the RHS of the in-tree bound
`ProximityGap.LargeZeroWitnessSplit.lineBadScalars_card_le_thresholdChoose_sum`. -/
theorem thresholdChooseSum_eq_inTree (a : ℕ) (u₁ : Fin n → F) :
    thresholdChooseSum a (directionZeroSet u₁).card (directionSupportSet u₁).card
      = ∑ t ∈ Finset.range a,
          (if t + (directionSupportSet u₁).card < a then 0
            else (directionZeroSet u₁).card.choose t) *
            ((directionSupportSet u₁).card / (a - t)) := rfl

/-- The literal in-tree bad-scalar bound, re-expressed through `thresholdChooseSum`: on a
very-large-zero (`k + s ≤ a`) safe line the bad count is `≤ thresholdChooseSum a z s`. -/
theorem lineBadScalars_card_le_thresholdChooseSum
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hks : k + (directionSupportSet u₁).card ≤ a) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ thresholdChooseSum a (directionZeroSet u₁).card (directionSupportSet u₁).card := by
  rw [thresholdChooseSum_eq_inTree]
  exact lineBadScalars_card_le_thresholdChoose_sum dom hk a u₀ u₁ hsafe hks

/-! ### 1. The sum is at least the top-stratum central binomial term -/

/-- **Lower bound: drop to the top stratum `t = a−1`.**  For `1 ≤ a`, `1 ≤ s` the top term is
`choose(z, a−1)·s` (the `if` is false and `a − (a−1) = 1`, so `⌊s/1⌋ = s`), hence
`choose(z, a−1)·s ≤ thresholdChooseSum a z s`.  This is the term produced by a SINGLE realized
codeword at zero-agreement level `a−1`. -/
theorem top_term_le_thresholdChooseSum {a z s : ℕ} (ha : 1 ≤ a) (hs : 1 ≤ s) :
    z.choose (a - 1) * s ≤ thresholdChooseSum a z s := by
  have hmem : a - 1 ∈ Finset.range a := Finset.mem_range.mpr (by omega)
  have hval : (if (a - 1) + s < a then 0 else z.choose (a - 1)) * (s / (a - (a - 1)))
      = z.choose (a - 1) * s := by
    have hif : ¬ ((a - 1) + s < a) := by omega
    have hsub : a - (a - 1) = 1 := by omega
    rw [if_neg hif, hsub, Nat.div_one]
  calc z.choose (a - 1) * s
      = (if (a - 1) + s < a then 0 else z.choose (a - 1)) * (s / (a - (a - 1))) := hval.symm
    _ ≤ thresholdChooseSum a z s :=
        Finset.single_le_sum (f := fun t => (if t + s < a then 0 else z.choose t) * (s / (a - t)))
          (fun i _ => Nat.zero_le _) hmem

/-! ### 2. The exponential (q-power) lower bound on the realized diagonal family -/

/-- `2^m < centralBinom m` for `m ≥ 4`: from `Nat.four_pow_lt_mul_centralBinom` and `m ≤ 2^m`. -/
theorem two_pow_lt_centralBinom {m : ℕ} (hm : 4 ≤ m) : 2 ^ m < Nat.centralBinom m := by
  have h1 : 4 ^ m < m * Nat.centralBinom m := Nat.four_pow_lt_mul_centralBinom m hm
  have hle : m ≤ 2 ^ m := (Nat.lt_two_pow_self).le
  have h4 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have h2 : m * 2 ^ m ≤ 4 ^ m := by
    rw [h4]; exact Nat.mul_le_mul_right _ hle
  have h3 : m * 2 ^ m < m * Nat.centralBinom m := lt_of_le_of_lt h2 h1
  exact lt_of_mul_lt_mul_left h3 (Nat.zero_le m)

/-- **The coupled sum is exponential in the block length.**  On the realized diagonal family
`z = 2m`, `a = m+1` (so `t_top = a−1 = m`, `choose(2m, m) = centralBinom m`), the coupled /
threshold-choose bound exceeds `2^m` for `m ≥ 4`, `s ≥ 1`.  Since `n = 2m + s` here, `m = Θ(n)`:
the bound is `≥ 2^{Θ(n)}`, a `q`-power — the z-coupling does NOT make it sub-`q`. -/
theorem two_pow_lt_thresholdChooseSum_family {m s : ℕ} (hm : 4 ≤ m) (hs : 1 ≤ s) :
    2 ^ m < thresholdChooseSum (m + 1) (2 * m) s := by
  have htop : (2 * m).choose ((m + 1) - 1) * s ≤ thresholdChooseSum (m + 1) (2 * m) s :=
    top_term_le_thresholdChooseSum (by omega) hs
  have hcb : (2 * m).choose ((m + 1) - 1) = Nat.centralBinom m := by
    rw [show (m + 1) - 1 = m by omega, Nat.centralBinom]
  have hmul : Nat.centralBinom m ≤ (2 * m).choose ((m + 1) - 1) * s := by
    rw [hcb]; exact Nat.le_mul_of_pos_right _ hs
  calc 2 ^ m < Nat.centralBinom m := two_pow_lt_centralBinom hm
    _ ≤ (2 * m).choose ((m + 1) - 1) * s := hmul
    _ ≤ thresholdChooseSum (m + 1) (2 * m) s := htop

/-! ### 3. The exact probe instance (n = 16, a = 5, z = 13, s = 3) -/

/-- **Exact machine countermodel.**  `(n,a,z,s) = (16,5,13,3)`: the coupled / threshold-choose
bound is `2509`, whereas the probe finds a large-zero-safe line with appearing list `Λ = 1` and
TRUE weld weight `W_true = 3`.  A `836×` gap — the coupled route is nowhere near tight. -/
theorem thresholdChooseSum_probe_16 : thresholdChooseSum 5 13 3 = 2509 := by
  decide

/-- The exact instance dwarfs a generous poly budget `n² = 256` (n = 16). -/
theorem thresholdChooseSum_probe_16_gt_poly : (16 : ℕ) ^ 2 < thresholdChooseSum 5 13 3 := by
  rw [thresholdChooseSum_probe_16]; norm_num

/-! ### 4. No budget bounds the coupled sum: it is unbounded (the `q`-power, cleanly) -/

/-- **The refutation.**  For every budget `B` there is a realized diagonal-family instance on which
the coupled / threshold-choose bound strictly exceeds `B`.  So NO fixed budget — in particular no
`B_near = poly(n)` and no `q·ε*` — bounds the per-fiber coupled sum: the z-coupling does not make
it sub-`q`. -/
theorem thresholdChooseSum_unbounded (B : ℕ) :
    ∃ m, B < thresholdChooseSum (m + 1) (2 * m) 1 := by
  refine ⟨B + 4, ?_⟩
  have hexp : 2 ^ (B + 4) < thresholdChooseSum (B + 4 + 1) (2 * (B + 4)) 1 :=
    two_pow_lt_thresholdChooseSum_family (by omega) (le_refl 1)
  have hB : B < 2 ^ (B + 4) := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le
  exact lt_trans hB hexp

/-! ### 5. The decoupling: the TRUE weld weight is polynomial in the appearing-list size -/

/-- **The true weld weight is poly.**  For any stratum profile `stratum : ℕ → ℕ` whose total is
`≤ Λ` (the appearing-list size), the TRUE weld weight `Σ_t #stratum(t)·⌊s/(a−t)⌋` is `≤ Λ·s`.
Contrast the coupled bound `> 2^m` (§2): the two objects are decoupled by exactly the occupancy
factor `#stratum(t) ≤ choose(z,t)·D(t)`, which overcounts by the empty `t`-subsets. -/
theorem trueWeight_le_list_card_mul {a s Λ : ℕ} (stratum : ℕ → ℕ)
    (hsum : ∑ t ∈ Finset.range a, stratum t ≤ Λ) :
    ∑ t ∈ Finset.range a, stratum t * (s / (a - t)) ≤ Λ * s := by
  calc ∑ t ∈ Finset.range a, stratum t * (s / (a - t))
      ≤ ∑ t ∈ Finset.range a, stratum t * s := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        exact Nat.mul_le_mul_left _ (Nat.div_le_self s (a - t))
    _ = (∑ t ∈ Finset.range a, stratum t) * s := by rw [Finset.sum_mul]
    _ ≤ Λ * s := Nat.mul_le_mul_right _ hsum

/-! ### 6. The surviving sub-`q` object: `PuncturedListBudget` (Johnson-equivalent-hard) -/

/-- **The named next split.**  The only object that can discharge `hlow` sub-`q` is a direct bound
on the appearing-list size `Λ = #lineAppearingCodewords` on large-zero-safe lines — the punctured
list-decoding ball size (`hlow`-map §3).  This is NOT the coupled `choose(z,t)·D(t)` sum; by §3 of
`docs/kb/deltastar-466b-hlow-map-2026-07-01.md` it is the SAME beyond-Johnson list-size problem as
the far branch H1 (Johnson-equivalent-hard). -/
def PuncturedListBudget (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      (lineAppearingCodewords dom k a u₀ u₁).card ≤ B

/-- **`PuncturedListBudget` closes the true weight — the coupled sum never needed.**  Given the
punctured-list budget `Λ ≤ B`, the true weld weight is `≤ B·s`, bypassing the exploded coupled
bound entirely.  (`stratumProfile` = the exact strata `#stratum(t)`; its total is `Λ`, which
`PuncturedListBudget` bounds.  Stated abstractly since the profile-sum identity
`Σ_t #stratum(t) = Λ` is in-tree at `puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata`.)
-/
theorem trueWeight_le_of_puncturedListBudget
    {a s Λ B : ℕ} (stratum : ℕ → ℕ)
    (hprofile : ∑ t ∈ Finset.range a, stratum t = Λ) (hbudget : Λ ≤ B) :
    ∑ t ∈ Finset.range a, stratum t * (s / (a - t)) ≤ B * s := by
  have h := trueWeight_le_list_card_mul (a := a) (s := s) (Λ := Λ) stratum hprofile.le
  exact le_trans h (Nat.mul_le_mul_right _ hbudget)

open Classical in
/-- **Punctured weight from list size.**  The actual punctured zero-stratified line weight is
bounded by the appearing-list size times the moving support size.  This is the concrete in-tree
version of `trueWeight_le_list_card_mul`: it uses the codeword-weighted definition directly, so it
does not pass through the exploded `choose(z,t)·D(t)` envelope. -/
theorem puncturedZeroStratifiedLineWeight_le_lineAppearingCodewords_card_mul_support
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    puncturedZeroStratifiedLineWeight dom k a u₀ u₁
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card * (directionSupportSet u₁).card := by
  rw [puncturedZeroStratifiedLineWeight]
  calc
    ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (directionSupportSet u₁).card / (a - (directionZeroAgreementSet c u₀ u₁).card)
      ≤ ∑ _c ∈ lineAppearingCodewords dom k a u₀ u₁, (directionSupportSet u₁).card := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact Nat.div_le_self _ _
    _ = (lineAppearingCodewords dom k a u₀ u₁).card * (directionSupportSet u₁).card := by
        rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- A direct punctured-list budget gives a uniform punctured zero-stratified line budget, with
only the unavoidable support factor `≤ n`.  This is the weld-facing form of the surviving
`PuncturedListBudget` object. -/
theorem uniformPuncturedZeroStratifiedLineBudgeted_of_puncturedListBudget
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hbudget : PuncturedListBudget dom k a B) :
    UniformPuncturedZeroStratifiedLineBudgeted dom k a (B * n) := by
  intro u₀ u₁ hne hsafe
  have hlist := hbudget u₀ u₁ hne hsafe
  have hsupport : (directionSupportSet u₁).card ≤ n := by
    simpa using Finset.card_le_univ (directionSupportSet u₁)
  exact le_trans
    (puncturedZeroStratifiedLineWeight_le_lineAppearingCodewords_card_mul_support
      dom k a u₀ u₁)
    (Nat.mul_le_mul hlist hsupport)

open Classical in
/-- **Safe large-zero consumer from the surviving punctured-list object.**  If the direct
punctured-list budget holds on large-zero safe lines, then the large-zero safe bad-scalar branch
is bounded by `B * n`.  This is the positive replacement for the refuted coupled-sum route. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_puncturedListBudget
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hbudget : PuncturedListBudget dom k a B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a (B * n) := by
  intro u₀ u₁ hne hsafe
  exact le_trans
    (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight dom k a u₀ u₁ hsafe)
    ((uniformPuncturedZeroStratifiedLineBudgeted_of_puncturedListBudget dom k a B hbudget)
      u₀ u₁ hne hsafe)

open Classical in
/-- Failure-localization for the surviving large-zero route.  If the weld-facing safe
large-zero bad-scalar budget fails even after the unavoidable support factor `n`, then the direct
punctured-list budget is not available at level `B`. -/
theorem not_puncturedListBudget_of_not_largeZeroSafeLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hnot : ¬ LargeZeroSafeLineBadScalarsBudgeted dom k a (B * n)) :
    ¬ PuncturedListBudget dom k a B := by
  intro hbudget
  exact hnot (largeZeroSafeLineBadScalarsBudgeted_of_puncturedListBudget dom k a B hbudget)

open Classical in
/-- Witness form of the same localization: a concrete safe large-zero line whose bad-scalar count
exceeds `B*n` rules out the direct punctured-list budget `B`. -/
theorem not_puncturedListBudget_of_largeZeroSafe_badScalars_gt
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hne : ¬ SupportEligibleLineDirection a u₁)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hgt : B * n < (lineBadScalars dom k a u₀ u₁).card) :
    ¬ PuncturedListBudget dom k a B :=
  not_puncturedListBudget_of_not_largeZeroSafeLineBadScalarsBudgeted dom k a B
    (by
      intro hbudget
      exact not_lt_of_ge (hbudget u₀ u₁ hne hsafe) hgt)

end ProximityGap.LowProfileCoupled

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.LowProfileCoupled.thresholdChooseSum_eq_inTree
#print axioms ProximityGap.LowProfileCoupled.lineBadScalars_card_le_thresholdChooseSum
#print axioms ProximityGap.LowProfileCoupled.top_term_le_thresholdChooseSum
#print axioms ProximityGap.LowProfileCoupled.two_pow_lt_centralBinom
#print axioms ProximityGap.LowProfileCoupled.two_pow_lt_thresholdChooseSum_family
#print axioms ProximityGap.LowProfileCoupled.thresholdChooseSum_probe_16
#print axioms ProximityGap.LowProfileCoupled.thresholdChooseSum_probe_16_gt_poly
#print axioms ProximityGap.LowProfileCoupled.thresholdChooseSum_unbounded
#print axioms ProximityGap.LowProfileCoupled.trueWeight_le_list_card_mul
#print axioms ProximityGap.LowProfileCoupled.trueWeight_le_of_puncturedListBudget
#print axioms ProximityGap.LowProfileCoupled.puncturedZeroStratifiedLineWeight_le_lineAppearingCodewords_card_mul_support
#print axioms ProximityGap.LowProfileCoupled.uniformPuncturedZeroStratifiedLineBudgeted_of_puncturedListBudget
#print axioms ProximityGap.LowProfileCoupled.largeZeroSafeLineBadScalarsBudgeted_of_puncturedListBudget
#print axioms ProximityGap.LowProfileCoupled.not_puncturedListBudget_of_not_largeZeroSafeLineBadScalarsBudgeted
#print axioms ProximityGap.LowProfileCoupled.not_puncturedListBudget_of_largeZeroSafe_badScalars_gt
