/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-A3)
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic

/-!
# Deterministic Salem–Zygmund assembly: moment control ⇒ sup control (#444 lane A3)

THE PRIZE OBJECT.  `M(n) = max_{b ≠ 0 (mod p)} |S_b|`, `S_b = ∑_{x ∈ μ_n} e_p(b x)`, the worst
Gauss period of the thin 2-power subgroup `μ_n` (`n = 2^μ`, `n ∣ p − 1`, `p = n^β` prime,
`β ≈ 4–5`).  Target: `M(n) ≤ C √(n log(p/n))`, `C` absolute.

## Lane A3 strategy (ALIEN: information / deterministic Salem–Zygmund)

Classical Salem–Zygmund bounds the sup of a *lacunary* trigonometric polynomial by a sub-Gaussian
moment-generating-function estimate.  The 2-power subgroup `μ_n` is *maximally lacunary*
(`h^{n/2}=−1`, so every cyclotomic factor of `x^n−1` is a binomial); the deterministic analogue
should hold.

The reduction (verified numerically in `probe_wf5A3_moment_mgf_equiv.py`,
`probe_wf5A3_mgf_to_max.py`): writing `Z_b := S_b/√n` over the family `b ∈ I` of the `m = (p−1)/n`
coset representatives, the prize bound follows from the **deterministic deep-moment ceiling**

  `(MOM)   (1/m) ∑_{b ∈ I} Z_b^{2r} ≤ (2r−1)‼     for all r ≤ ⌈log p⌉`.

This `(MOM)` is *exactly* the char-`p` deep-moment statement of the meta-theorem's unique permitted
route (`E_{2r}(μ_n) ≤ (2r−1)‼ · n^r`), the OPEN CRUX.  The pre-screen (probes) shows
`(1/m) ∑ Z_b^{2r} / (2r−1)‼ ≤ 1` strictly, with the ratio rising to `1` as `n → ∞`, at every depth.

## What THIS file proves (axiom-clean)

The **deterministic assembly** `(MOM) ⇒ sup bound`: given a finite family `Z : I → ℝ` and a real
moment bound `μ₂ᵣ` on its `2r`-th empirical moment, *every* member of the family is bounded by the
Markov–union quantity.  This is the elementary, randomness-free engine that turns the open moment
input into the prize.  Specifically:

* `card_large_le_of_moment` — Markov on the `2r`-th moment: the number of `b` with `|Z_b| > t` is
  `≤ (∑_b Z_b^{2r}) / t^{2r}`.
* `sup_le_of_moment_bound` — the assembly: if the total `2r`-th moment is `< t^{2r}`, then *every*
  `|Z_b| ≤ t`.  (Strict total moment below `t^{2r}` ⇒ the Markov count is `< 1` ⇒ `= 0`.)

Substituting `∑_b Z_b^{2r} = m · (2r−1)‼` (the `(MOM)` ceiling) and `t^{2r} = m·(2r−1)‼·e`
(Stirling-optimized at `r ≈ log m`) gives `M ≤ √(2e) · √(n log(p/n))` — the prize, `C = √(2e)`.

This module is self-contained (no `sorry`, no project axioms beyond Lean's three).
The ONLY open input is `(MOM)` itself, fed here as an explicit hypothesis.
-/

namespace ArkLib.ProximityGap.Frontier.SalemZygmundA3

open Finset BigOperators

variable {ι : Type*}

/-- **Markov on the `2r`-th moment (count form).**  For a finite family `Z : ι → ℝ` indexed by
`I`, the number of indices `b` with `t ^ (2r) < Z b ^ (2r)` (i.e. `t < |Z b|` when `t ≥ 0`) is at
most `(∑_{b ∈ I} (Z b)^(2r)) / t^(2r)`.  Pure counting: each such `b` contributes `> t^(2r)` to a
sum of nonnegative terms. -/
theorem card_large_le_of_moment (Z : ι → ℝ) (I : Finset ι) (r : ℕ) (t : ℝ) :
    ((I.filter (fun b => t ^ (2 * r) < Z b ^ (2 * r))).card : ℝ) * t ^ (2 * r)
      ≤ ∑ b ∈ I, Z b ^ (2 * r) := by
  classical
  set Big := I.filter (fun b => t ^ (2 * r) < Z b ^ (2 * r)) with hBig
  have hsubset : Big ⊆ I := filter_subset _ _
  -- ∑ over I ≥ ∑ over Big (all terms nonneg), and ∑ over Big ≥ |Big| · t^(2r)
  have hnonneg : ∀ b ∈ I, 0 ≤ Z b ^ (2 * r) := by
    intro b _; exact even_two_mul r |>.pow_nonneg _
  have hstep1 : ∑ b ∈ Big, Z b ^ (2 * r) ≤ ∑ b ∈ I, Z b ^ (2 * r) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun b hb _ => hnonneg b hb)
  have hstep2 : (Big.card : ℝ) * t ^ (2 * r) ≤ ∑ b ∈ Big, Z b ^ (2 * r) := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum Big _ _ ?_
    intro b hb
    rw [hBig, mem_filter] at hb
    exact le_of_lt hb.2
  calc (Big.card : ℝ) * t ^ (2 * r) ≤ ∑ b ∈ Big, Z b ^ (2 * r) := hstep2
    _ ≤ ∑ b ∈ I, Z b ^ (2 * r) := hstep1

/-- **The deterministic Salem–Zygmund assembly.**  If the *total* `2r`-th moment of the family is
strictly below `t ^ (2r)`, then EVERY member satisfies `|Z b| ≤ t`.

Mechanism: by `card_large_le_of_moment`, the count of indices exceeding `t` times `t^(2r)` is below
`t^(2r)`, so the count is `< 1`, hence `0`; an empty exceedance set means all `|Z b| ≤ t`.

Feeding `∑_{b ∈ I} (Z b)^(2r) ≤ m · (2r−1)‼` (the open char-`p` moment ceiling `(MOM)`) and the
Stirling-optimal `t` gives the prize bound `M ≤ √(2e)·√(n log(p/n))`. -/
theorem sup_le_of_moment_bound (Z : ι → ℝ) (I : Finset ι) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hmom : ∑ b ∈ I, Z b ^ (2 * r) < t ^ (2 * r)) :
    ∀ b ∈ I, Z b ^ (2 * r) ≤ t ^ (2 * r) := by
  classical
  set Big := I.filter (fun b => t ^ (2 * r) < Z b ^ (2 * r)) with hBig
  have htpow : (0 : ℝ) < t ^ (2 * r) := pow_pos ht _
  -- The Markov count times t^(2r) is ≤ total moment < t^(2r), so count < 1, so count = 0.
  have hcount : (Big.card : ℝ) * t ^ (2 * r) < t ^ (2 * r) :=
    lt_of_le_of_lt (card_large_le_of_moment Z I r t) hmom
  have hcard_lt : (Big.card : ℝ) < 1 := by
    have h1 : (Big.card : ℝ) * t ^ (2 * r) < 1 * t ^ (2 * r) := by rwa [one_mul]
    exact lt_of_mul_lt_mul_right h1 (le_of_lt htpow)
  have hcard0 : Big.card = 0 := by
    have : Big.card < 1 := by exact_mod_cast hcard_lt
    omega
  have hempty : Big = ∅ := card_eq_zero.mp hcard0
  -- every b in I is therefore NOT in the exceedance set: Z b ^(2r) ≤ t^(2r)
  intro b hb
  by_contra hlt
  rw [not_le] at hlt
  have : b ∈ Big := by rw [hBig, mem_filter]; exact ⟨hb, hlt⟩
  rw [hempty] at this
  exact absurd this (notMem_empty b)

/-- **Sup bound in absolute-value form.**  Under the strict total-moment hypothesis, every member
has `|Z b| ≤ t`.  (Specialization of `sup_le_of_moment_bound` via monotonicity of even powers /
`abs`.) -/
theorem abs_le_of_moment_bound (Z : ι → ℝ) (I : Finset ι) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hmom : ∑ b ∈ I, Z b ^ (2 * r) < t ^ (2 * r)) :
    ∀ b ∈ I, |Z b| ≤ t := by
  intro b hb
  have hpow : Z b ^ (2 * r) ≤ t ^ (2 * r) := sup_le_of_moment_bound Z I r t ht hmom b hb
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- r = 0: hmom reads (∑ 1) < 1 over the nonempty I — contradiction, so this case is vacuous.
    subst hr0
    simp only [Nat.mul_zero, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at hmom
    have : (1 : ℝ) ≤ (I.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨b, hb⟩
    exact absurd hmom (not_lt.mpr this)
  · have h2r : 2 * r ≠ 0 := by omega
    -- |Z b| ^ (2r) = |Z b ^ (2r)| = Z b ^ (2r) (even power is nonneg) ≤ t ^ (2r).
    have heq : |Z b| ^ (2 * r) = Z b ^ (2 * r) := by
      rw [← abs_pow, abs_of_nonneg (even_two_mul r |>.pow_nonneg _)]
    have habs : |Z b| ^ (2 * r) ≤ t ^ (2 * r) := by rw [heq]; exact hpow
    exact le_of_pow_le_pow_left₀ h2r (le_of_lt ht) habs

end ArkLib.ProximityGap.Frontier.SalemZygmundA3
