/-
# di Benedetto is worse-than-trivial at the prize thinness (#444)

This brick pins the **di Benedetto retraction** (§5 of the thesis) to the *actual* prize parameter, machine-checked.
The user question — "did we figure out di Benedetto in the regime or not?" — has a definitive answer: **no, it gives
nothing at prize scale**, and here is the arithmetic certificate.

Setup.  Write `β = log p / log n` (thinness; `μ_n ⊂ F_p`).  di Benedetto's subgroup-sum bound, specialized to `μ_n`,
gives `M ≤ n^{exponent(β)}` with two parametrizations the campaign used:
* **Sidon-floor inputs** (the campaign's "0.9583 beat", `t = (2,3)`): `exponent_S(β) = 23/24 + β/72`
  (the `β/72` term *is* the dropped `p^{1/72}` prefactor written as `n^{β/72}`).
* **Published Burgess inputs** (`t = (49/20, 4)`): `exponent_P(β) = 2689/2880 + β/72`, recovering the headline
  saving `31/2880 = 1 − exponent_P(4)`.

A bound `M ≤ n^{exponent}` is useful only if `exponent < 1` (better than the trivial `M ≤ n`).  The prize lives at
`β = 158/30 ≈ 5.27` (`n = 2^{30}`, `p ≈ n·2^{128} = 2^{158}`).  We prove **both exponents exceed 1 there** — di
Benedetto is *worse than trivial* — and that the gap to the Paley target `½` is a full half-power.

Thresholds (also proved): `exponent_S(β) > 1 ⟺ β > 3`; `exponent_P(β) > 1 ⟺ β > 191/40 = 4.775`.  The "0.9583"
headline corresponds to a *thick* `β ≈ 1.78`, not the prize.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProximityGap.DiBenedettoPrizeRegimeVacuous

/-- Sidon-floor di Benedetto exponent in `n` (includes the `p^{1/72}` prefactor as `β/72`). -/
def exponentSidon (β : ℚ) : ℚ := 23 / 24 + β / 72

/-- Published-Burgess di Benedetto exponent in `n`. -/
def exponentPublished (β : ℚ) : ℚ := 2689 / 2880 + β / 72

/-- The prize thinness `β = log p / log n = 158/30` (`n = 2^{30}`, `p ≈ 2^{158}`). -/
def betaPrize : ℚ := 158 / 30

/-- **Sidon exponent exceeds 1 exactly when `β > 3`.**  So for any subgroup thinner than `β = 3`, the campaign's
"0.9583" specialization is worse than the trivial bound. -/
theorem sidon_exponent_gt_one_iff (β : ℚ) : 1 < exponentSidon β ↔ 3 < β := by
  unfold exponentSidon; constructor <;> intro h <;> linarith

/-- **Published exponent exceeds 1 exactly when `β > 191/40 = 4.775`** (the saving vanishes at the Burgess edge). -/
theorem published_exponent_gt_one_iff (β : ℚ) : 1 < exponentPublished β ↔ 191 / 40 < β := by
  unfold exponentPublished; constructor <;> intro h <;> linarith

/-- **The prize is past both thresholds.** `β = 158/30 ≈ 5.27 > 3` and `> 191/40`. -/
theorem prize_beta_past_thresholds : 3 < betaPrize ∧ 191 / 40 < betaPrize := by
  unfold betaPrize; constructor <;> norm_num

/-- **Headline verdict: di Benedetto is worse than trivial at the prize.**  Both exponents exceed 1 at
`β = 158/30`, so `M ≤ n^{exponent}` is *weaker* than the trivial `M ≤ n` — the route gives nothing in the prize
regime, either parametrization. -/
theorem diBenedetto_worse_than_trivial_at_prize :
    1 < exponentSidon betaPrize ∧ 1 < exponentPublished betaPrize := by
  refine ⟨?_, ?_⟩
  · rw [sidon_exponent_gt_one_iff]; exact prize_beta_past_thresholds.1
  · rw [published_exponent_gt_one_iff]; exact prize_beta_past_thresholds.2

/-- **The gap to the Paley target is a full half-power.**  The Paley/BGK goal is exponent `½`.  At the prize the
Sidon exponent is `> 1`, so the gap `exponent_S(β) − ½ > ½`: a full half-power of `n` separates di Benedetto at
prize scale from the prize exponent. -/
theorem gap_to_paley_exceeds_half : 1 / 2 < exponentSidon betaPrize - 1 / 2 := by
  have h : 1 < exponentSidon betaPrize := diBenedetto_worse_than_trivial_at_prize.1
  linarith

/-- **The "0.9583 beat" is a thick-subgroup phenomenon.**  At `β = 178/100 ≈ 1.78` the Sidon exponent is
`< 1` (a genuine saving), confirming the headline lives far from the prize's `β ≈ 5.27`. -/
theorem beat_is_thick_subgroup : exponentSidon (178 / 100) < 1 := by
  unfold exponentSidon; norm_num

end ProximityGap.DiBenedettoPrizeRegimeVacuous
