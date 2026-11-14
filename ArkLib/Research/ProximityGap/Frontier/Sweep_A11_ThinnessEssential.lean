/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Sweep_A11 — Thinness-essential necessary condition: the Gauss-period floor is REGIME-GATED

**Actionable A11 (merged 407-T18).** Formalize the regime-gating fact that the prize-conjecture
floor

> `(FLOOR n p)` :  `B(μ_n)² ≤ 2·n·log p`,  where `B(μ_n) = max_{b≠0} ‖Σ_{x∈μ_n} e_p(bx)‖`

is **FALSE in a "thick" subgroup window** and **TRUE in the thin prize window**, and derive the
corollary that **any thickness-monotone proof method is excluded**.

## The data (probe `scripts/probes/sweep_A11_thinness.py`, exact FFT, p = 65537 = 2^16+1)

At the worst structured prime (Fermat `p = 65537`, `v₂(p−1) = 16`), varying subgroup size `n = 2^μ`:

| regime          | n         | β = log_n p | R = B/√(2 n log p) | floor |
|-----------------|-----------|-------------|--------------------|-------|
| THIN (prize)    | 4, 8, 16  | 8.0,5.3,4.0 | 0.42, 0.59, 0.73   | TRUE  |
| intermediate    | 32        | 3.2         | 0.95               | true  |
| **thick**       | **64**    | **2.67**    | **1.16**           | **FALSE** |
| **thick**       | **128**   | **2.29**    | **1.05**           | **FALSE** |
| very thick      | 256…      | ≤ 2         | < 1                | true  |

So `(FLOOR)` is **violated** in the intermediate-thickness window `β ∈ (≈2.3, ≈3.2)` at structured
2-power primes, but **holds** in the thin prize regime (`β ≥ 4`, `n ≤ p^{1/4}`) even at the worst
Fermat prime. The optimal conjecture is therefore NOT "for all subgroup sizes" — that is FALSE — it
is specifically a **thin-subgroup** statement.

## What is proven here (axiom-clean, real arithmetic)

Two **pivotal exact witnesses**, with rational `B`-bounds backed by the probe (`B(μ₆₄)=43.633`,
`B(μ₁₆)=13.838`) and the rational bracket `11 < log 65537 < 12` (proven via `exp_one_lt/gt_d9`):

* `floor_false_at_thick` — at `n = 64`, `B ≥ 43` ⟹ `B² = 1849 > 1536 ≥ 2·64·log p`: **floor FALSE**.
* `floor_true_at_thin`   — at `n = 16`, `B ≤ 14` ⟹ `B² = 196 ≤ 352 ≤ 2·16·log p`: **floor TRUE**.

The witness `B`-bounds are the only *analytic* inputs (the Gauss-period magnitudes; certified
numerically by the probe). Everything else — the `log` bracket and both regime-gating inequalities
— is exact, machine-checked real arithmetic.

## The method-exclusion corollary (fully proven logic)

We model a proof "method" as the predicate `Cert n : Prop` = "the method certifies `(FLOOR)` at
subgroup size `n`". A method is:
* **sound** if certifying implies the floor actually holds (`Cert n → FLOOR n`);
* **thickness-monotone** if certifying a thin `n₀` forces certifying every thicker `n ≥ n₀`
  (`Cert n₀ → ∀ n ≥ n₀, Cert n`) — the defining property of every thickness-uniform technique
  (di Benedetto / generic sum-product / large sieve: their bound is monotone in `|H|`).

`thicknessMonotone_method_cannot_certify_thin`: **no sound, thickness-monotone method can certify
the floor at the thin prize witness `n = 16`** — because monotonicity would carry the certificate up
to the thick witness `n = 64`, where soundness then forces the floor, contradicting
`floor_false_at_thick`. This is a genuine *necessary condition on any proof of the prize floor*: it
must be thinness-essential (must FAIL at thicker subgroups), excluding the entire class of
thickness-monotone arguments.

## Honesty

`(FLOOR)` itself in the prize regime is the open BGK/Paley wall and is NOT proven here. This brick
proves the *regime-gating* (false thick / true thin at the worst structured prime) and the
*method-exclusion* corollary — a constraint on the solution, not the solution. The witness
`B`-bounds are honest named analytic inputs (probe-certified), exactly as `B(μ_n)` is throughout the
cone. No fabricated closure. Cross-checked by `scripts/probes/sweep_A11_thinness.py`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026/680.
- Issue #407 comment 2026-06-14T21:04:01Z (the regime-gating measurement, 407-T18).
- di Benedetto et al. 2020 (2003.06165) Thm 3.1 — the thickness-monotone subgroup bound this excludes.
-/

namespace ArkLib.ProximityGap.Sweep_A11

open Real

/-- The Fermat prime of the worst-case witnesses, `65537 = 2^16 + 1` (`v₂(p−1) = 16`). -/
def p : ℝ := 65537

/-- **The floor predicate (squared, sqrt-free form).** `(FLOOR n B)` says the Gauss-period maximum
`B = max_{b≠0}‖η_b‖` over `μ_n ⊂ F_p^×` obeys the prize conjecture `B ≤ √(2 n log p)`, i.e.
`B² ≤ 2 n log p`. (We carry `B` as a parameter — its value is the open analytic quantity.) -/
def FloorHolds (n B : ℝ) : Prop := B ^ 2 ≤ 2 * n * Real.log p

/-! ### The rational bracket `11 < log 65537 < 12` (exact, via `exp_one_lt/gt_d9`). -/

/-- `exp 11 < 65537`, hence the lower bracket. Proof: `exp 11 = (exp 1)^11 < 2.7182818286^11`
(`exp_one_lt_d9`), and `2.7182818286^11 < 65537` by `norm_num`. -/
theorem eleven_lt_logp : (11 : ℝ) < Real.log p := by
  rw [show p = (65537 : ℝ) from rfl, Real.lt_log_iff_exp_lt (by norm_num)]
  have h11 : Real.exp 11 = (Real.exp 1) ^ (11 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h11]
  calc (Real.exp 1) ^ (11 : ℕ)
      ≤ (2.7182818286 : ℝ) ^ (11 : ℕ) :=
        pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 11
    _ < 65537 := by norm_num

/-- `65537 < exp 12`, hence the upper bracket. Proof: `exp 12 = (exp 1)^12 > 2.7182818283^12`
(`exp_one_gt_d9`), and `65537 < 2.7182818283^12` by `norm_num`. -/
theorem logp_lt_twelve : Real.log p < 12 := by
  rw [show p = (65537 : ℝ) from rfl, Real.log_lt_iff_lt_exp (by norm_num)]
  have h12 : Real.exp 12 = (Real.exp 1) ^ (12 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h12]
  calc (65537 : ℝ)
      < (2.7182818283 : ℝ) ^ (12 : ℕ) := by norm_num
    _ ≤ (Real.exp 1) ^ (12 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 12

/-! ### The two pivotal regime-gating witnesses. -/

/-- **THICK witness — the floor is FALSE at `n = 64`.** The Gauss-period maximum over `μ₆₄ ⊂ F₆₅₅₃₇`
is `B(μ₆₄) = 43.633…` (probe `sweep_A11_thinness.py`); take the honest rational lower bound
`B ≥ 43`. Then `B² ≥ 1849`, while `2·64·log p < 2·64·12 = 1536`. So `B² > 2·64·log p`:
the prize floor is **violated** in the thick regime (`β = log₆₄ 65537 ≈ 2.67`). -/
theorem floor_false_at_thick {B : ℝ} (hB : (43 : ℝ) ≤ B) : ¬ FloorHolds 64 B := by
  unfold FloorHolds
  intro hfloor
  -- 2 * 64 * log p < 2 * 64 * 12 = 1536
  have hlog : 2 * (64 : ℝ) * Real.log p < 1536 := by
    have := logp_lt_twelve
    nlinarith [this]
  -- B² ≥ 43² = 1849
  have hBsq : (1849 : ℝ) ≤ B ^ 2 := by nlinarith [hB]
  -- contradiction: 1849 ≤ B² ≤ 2·64·log p < 1536
  linarith [hfloor, hlog, hBsq]

/-- **THIN witness — the floor is TRUE at `n = 16`.** The Gauss-period maximum over `μ₁₆ ⊂ F₆₅₅₃₇`
is `B(μ₁₆) = 13.838…` (probe); take the honest rational upper bound `B ≤ 14`. Then `B² ≤ 196`,
while `2·16·log p > 2·16·11 = 352`. So `B² ≤ 2·16·log p`: the prize floor **holds** in the thin
regime (`β = log₁₆ 65537 = 4`, exactly the prize edge `n = p^{1/4}`). -/
theorem floor_true_at_thin {B : ℝ} (hB0 : (0 : ℝ) ≤ B) (hB : B ≤ (14 : ℝ)) :
    FloorHolds 16 B := by
  unfold FloorHolds
  -- 2 * 16 * log p > 2 * 16 * 11 = 352
  have hlog : (352 : ℝ) < 2 * (16 : ℝ) * Real.log p := by
    have := eleven_lt_logp
    nlinarith [this]
  -- B² ≤ 14² = 196
  have hBsq : B ^ 2 ≤ (196 : ℝ) := by nlinarith [hB, hB0]
  linarith [hBsq, hlog]

/-- **Regime-gating, packaged.** At the single worst structured prime `p = 65537`, the prize floor
predicate `FloorHolds n B` is simultaneously FALSE at the thick witness (`n = 64`, any `B ≥ 43`) and
TRUE at the thin witness (`n = 16`, any `0 ≤ B ≤ 14`). Hence `(FLOOR)` is **not** uniform over
subgroup sizes — it is a thin-subgroup statement. -/
theorem regime_gated {Bthick Bthin : ℝ}
    (hThick : (43 : ℝ) ≤ Bthick) (hThin0 : (0 : ℝ) ≤ Bthin) (hThin : Bthin ≤ (14 : ℝ)) :
    (¬ FloorHolds 64 Bthick) ∧ FloorHolds 16 Bthin :=
  ⟨floor_false_at_thick hThick, floor_true_at_thin hThin0 hThin⟩

/-! ### The method-exclusion corollary (fully proven logic).

We model a proof "method" by the family of subgroup sizes at which it certifies the floor. -/

/-- A method's certificate predicate: `Cert n` holds iff the method certifies `(FLOOR)` at `μ_n`. -/
structure FloorMethod where
  /-- "the method certifies the floor at subgroup size `n`". -/
  Cert : ℝ → Prop
  /-- The values of `B` the method certifies the floor *for* at each size (the analytic profile). -/
  Bval : ℝ → ℝ
  /-- **Soundness:** a certificate at `n` means the floor genuinely holds (for the method's `B`). -/
  sound : ∀ n, Cert n → FloorHolds n (Bval n)

/-- **Thickness-monotone** method: certifying any thin size `n₀` forces certifying every *thicker*
(`larger n`) size. This is the defining property of every thickness-uniform technique
(di Benedetto / generic sum-product / large sieve — whose subgroup bound improves monotonically as
`|H|` grows). -/
def ThicknessMonotone (M : FloorMethod) : Prop :=
  ∀ n₀ n, M.Cert n₀ → n₀ ≤ n → M.Cert n

/-- **THE EXCLUSION THEOREM.** Suppose a sound, thickness-monotone method has, at the thick witness
`n = 64`, the genuine prize Gauss-period magnitude `B(μ₆₄) ≥ 43` (the actual analytic value).
Then it **cannot** certify the floor at the thin prize witness `n = 16`.

Proof: if it certified `n = 16`, thickness-monotonicity (`16 ≤ 64`) would carry the certificate to
`n = 64`; soundness would then force `FloorHolds 64 (Bval 64)`; but `Bval 64 ≥ 43` makes that
contradict `floor_false_at_thick`. Hence the floor cannot be established by any thickness-monotone
method — a correct proof must be **thinness-essential** (must fail at the thicker `μ₆₄`). -/
theorem thicknessMonotone_method_cannot_certify_thin
    (M : FloorMethod) (hmono : ThicknessMonotone M)
    (hBthick : (43 : ℝ) ≤ M.Bval 64) :
    ¬ M.Cert 16 := by
  intro hcert16
  -- monotone: certificate carries 16 → 64
  have hcert64 : M.Cert 64 := hmono 16 64 hcert16 (by norm_num)
  -- sound: floor holds at 64 for the method's B
  have hfloor64 : FloorHolds 64 (M.Bval 64) := M.sound 64 hcert64
  -- but the real Gauss period at μ₆₄ falsifies the floor
  exact floor_false_at_thick hBthick hfloor64

/-- **Contrapositive packaging:** every thickness-monotone method that certifies the thin prize
witness is UNSOUND at the thick witness — its certificate at `n = 16` propagates (by monotonicity)
to a *false* floor claim at `n = 64`. Equivalently: a sound method certifying the prize-thin floor
**must not be thickness-monotone**. -/
theorem certifying_thin_method_is_thinness_essential
    (M : FloorMethod) (hBthick : (43 : ℝ) ≤ M.Bval 64) (hcert16 : M.Cert 16) :
    ¬ ThicknessMonotone M := by
  intro hmono
  exact thicknessMonotone_method_cannot_certify_thin M hmono hBthick hcert16

end ArkLib.ProximityGap.Sweep_A11

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]` only). -/
#print axioms ArkLib.ProximityGap.Sweep_A11.eleven_lt_logp
#print axioms ArkLib.ProximityGap.Sweep_A11.logp_lt_twelve
#print axioms ArkLib.ProximityGap.Sweep_A11.floor_false_at_thick
#print axioms ArkLib.ProximityGap.Sweep_A11.floor_true_at_thin
#print axioms ArkLib.ProximityGap.Sweep_A11.regime_gated
#print axioms ArkLib.ProximityGap.Sweep_A11.thicknessMonotone_method_cannot_certify_thin
#print axioms ArkLib.ProximityGap.Sweep_A11.certifying_thin_method_is_thinness_essential
