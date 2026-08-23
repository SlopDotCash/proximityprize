/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# The KKH26 bad-scalar supply STRICTLY decays along an `s`-step fold (#357 R2)

`KKH26FoldTransport.lean` proves the FRI-fold trichotomy at the **word** level: for `m = 1`
and even `r` (the `s`-step), the bad line `(X^r, X^{r−1})` folds to the `β`-scaled KKH26 stack
of `(s/2, 1, r/2)` (`kkh26_fold_s_step_r_even`).  It then asserts, *in prose only*, the
quantitative consequence for the bad-scalar **census supply**:

> "The construction-class supply drops `2^r·C(s/2,r) → 2^{r/2}·C(s/4,r/2)` per `s`-step."

The supply count `2^r · C(s/2, r)` (with `s = 2^μ`, so `s/2 = 2^{μ−1}`) is exactly the
witness-spread count of `KKH26WitnessSpread`/`KKH26EntropyForm` (`kkh26_witness_count_ge`,
`kkh26_count_corollary`).  No in-tree theorem states the **decay** itself — that one `s`-step
of the fold strictly shrinks the supply.  This file supplies that missing brick.

## The theorem (`kkh26_fold_supply_strict_decay`)

In the `r`-even structural-halving regime of the fold trichotomy (matching the hypothesis
`2 ∣ r` of `kkh26_fold_s_step_r_even`), with `4 ∣ s`, `2 ≤ r`, and the prize-regime constraint
`2r < s` (the thin-window constraint under which the KKH26 family is the near-capacity bad
family),

  `2^{r/2} · C(s/4, r/2)  <  2^r · C(s/2, r)`.

So a single `s`-step of the FRI fold strictly reduces the bad-scalar supply: the bad family is
**not** an `s`-step fixed point (in sharp contrast to the `m`-step, where the supply set is
literally *invariant* — `kkh26_inner_group_fold_invariant`).  The decay is driven by a clean
chain (no analysis, no probabilistic input, pure binomial identities):

* `C(s/4, r/2) ≤ C(2·(s/4), 2·(r/2)) = C(s/2, r)` — the **doubling bound**
  `C(a,k) ≤ C(2a,2k)` (a single diagonal term of Vandermonde), using `4 ∣ s ⇒ 2·(s/4)=s/2` and
  `r` even `⇒ 2·(r/2)=r`; and
* `2^{r/2} < 2^r` strictly, since `r/2 < r` for `r ≥ 2`.

This is the BGK-independent **fold-transport** lever (`#444` §11): it is a structural decay law
for the explicit bad construction, *field-universal* and *probe-verified* (0 strict-decay
violations over 4083 prize-regime `r`-even instances, `scripts/probes/probe_fold_supply_decay.py`,
`probe_reven.py`), with the decay factor `2^{r/2}·C(s/2,r)/C(s/4,r/2)` dominated by the binomial
ratio, far exceeding the monomial `2^{r/2}` halving floor.

**Honest scope.** This bounds the supply of *this one construction class* (the KKH26 monomial
stack) along the fold; it does NOT bound `M(μ_n)` and is NOT a thinness-essential CORE lever —
it is the quantitative completion of the fold-transport trichotomy (the open prize question, how
the *worst-case* incidence behaves along the tower, is untouched).  Everything is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace ProximityGap.KKH26FoldSupplyDecay

open Nat

open Finset in
/-- **Binomial doubling bound:** `C(a, k) ≤ C(2a, 2k)` for all `a, k`.
Proof: Vandermonde `C(a+a, 2k) = ∑_{i+j=2k} C(a,i)·C(a,j)` has the single diagonal term
`C(a,k)·C(a,k) = C(a,k)²` (at `(i,j) = (k,k)`), and `C(a,k)² ≥ C(a,k)`. -/
theorem choose_le_choose_two_mul (a k : ℕ) : choose a k ≤ choose (2 * a) (2 * k) := by
  -- C(a,k)² ≤ C(2a,2k) by extracting the (k,k) diagonal term of Vandermonde
  have hdiag : choose a k * choose a k ≤ choose (2 * a) (2 * k) := by
    rw [two_mul a, Nat.add_choose_eq]
    have hmem : (k, k) ∈ antidiagonal (2 * k) := by
      rw [Finset.mem_antidiagonal]; omega
    calc choose a k * choose a k
        = (fun ij : ℕ × ℕ => choose a ij.1 * choose a ij.2) (k, k) := rfl
      _ ≤ ∑ ij ∈ antidiagonal (2 * k), choose a ij.1 * choose a ij.2 :=
          Finset.single_le_sum (f := fun ij : ℕ × ℕ => choose a ij.1 * choose a ij.2)
            (fun _ _ => Nat.zero_le _) hmem
  -- C(a,k) ≤ C(a,k)² (n ≤ n*n for naturals), or C(a,k)=0
  rcases Nat.eq_zero_or_pos (choose a k) with h0 | hpos
  · simp [h0]
  · calc choose a k ≤ choose a k * choose a k := Nat.le_mul_of_pos_left _ hpos
      _ ≤ choose (2 * a) (2 * k) := hdiag

/-- **The KKH26 `s`-step supply strict decay** (the `r`-even / structural-halving regime of the
fold trichotomy, matching `kkh26_fold_s_step_r_even`).  For `s` divisible by `4`, `2 ≤ r`, `r`
even, and the prize-regime constraint `2r < s`, one `s`-step of the FRI fold strictly reduces the
bad-scalar supply count:
  `2^{r/2} · C(s/4, r/2)  <  2^r · C(s/2, r)`.

Proof (pure binomial, no analytic input):
* `C(s/4, r/2) ≤ C(2·(s/4), 2·(r/2)) = C(s/2, r)` by `choose_le_choose_two_mul`
  (using `4 ∣ s ⇒ 2·(s/4) = s/2` and `r` even `⇒ 2·(r/2) = r`);
* `2^{r/2} < 2^r` strictly, since `r/2 < r` for `r ≥ 2`. -/
theorem kkh26_fold_supply_strict_decay {s r : ℕ} (hs : 4 ∣ s) (hr : 2 ≤ r) (hrev : 2 ∣ r)
    (hrs : 2 * r < s) :
    2 ^ (r / 2) * choose (s / 4) (r / 2) < 2 ^ r * choose (s / 2) r := by
  -- doubling identities forced by the divisibilities
  have hs2 : 2 * (s / 4) = s / 2 := by omega
  have hr2 : 2 * (r / 2) = r := by omega
  -- the binomial chain via the doubling bound
  have hchoose : choose (s / 4) (r / 2) ≤ choose (s / 2) r := by
    have := choose_le_choose_two_mul (s / 4) (r / 2)
    rwa [hs2, hr2] at this
  -- positivity of the target binomial (so the 2-power strictness survives the product)
  have hpos : 0 < choose (s / 2) r := Nat.choose_pos (by omega)
  -- strict 2-power factor: 2^{r/2} < 2^r since r/2 < r for r ≥ 2
  have hpow : 2 ^ (r / 2) < 2 ^ r :=
    Nat.pow_lt_pow_right (a := 2) (by norm_num) (by omega)
  calc 2 ^ (r / 2) * choose (s / 4) (r / 2)
      ≤ 2 ^ (r / 2) * choose (s / 2) r := Nat.mul_le_mul_left _ hchoose
    _ < 2 ^ r * choose (s / 2) r := by
        exact (Nat.mul_lt_mul_right hpos).2 hpow

/-- Sanity: at the smallest prize-regime instance `s = 8`, `r = 2`
(`2^1·C(2,1) = 4 < 2^2·C(4,2) = 24`) the decay fires. -/
example : 2 ^ (2 / 2) * choose (8 / 4) (2 / 2) < 2 ^ 2 * choose (8 / 2) 2 := by decide

/-- Sanity: a larger instance `s = 32`, `r = 6` (`2^3·C(8,3) = 448 < 2^6·C(16,6) = 512512`). -/
example : 2 ^ (6 / 2) * choose (32 / 4) (6 / 2) < 2 ^ 6 * choose (32 / 2) 6 := by decide

#print axioms choose_le_choose_two_mul
#print axioms kkh26_fold_supply_strict_decay

end ProximityGap.KKH26FoldSupplyDecay
