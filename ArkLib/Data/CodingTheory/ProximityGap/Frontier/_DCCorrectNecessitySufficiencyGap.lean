/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sol
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DCCorrectMomentCeilingAtFloor

/-!
# The trivial-counting necessity is `~e^r ≈ q`-fold weaker than sufficiency (#444 / #407)

The DC-correct cluster gives two bounds on the DC-subtracted moment `S_r = q·E_r − |G|^{2r}`:

* **Sufficiency** (`_DCCorrectSupCapstone.worstPeriod_le_prizeFloor_dc`): the prize sup
floor FOLLOWS
  from the open hypothesis `S_r ≤ q·(2r·|G|)^r` (the char-`p`/BGK core).
* **Necessity** (`_DCCorrectMomentCeilingAtFloor.dcSubtractedMoment_le_prizeFloorCeiling`):
the prize
  sup floor FORCES `S_r ≤ (q−1)·(e·2r·|G|)^r = (q−1)·e^r·(2r·|G|)^r`.

These are NOT the same threshold. This file records the exact gap between them, so no one
mistakes the
trivial counting necessity for a step toward the prize:

> `necessityCeiling_ge_sufficiencyThreshold` : `(q−1)·e^r·B ≥ ((q−1)/q)·e^r · (q·B)` and in
particular,
> for `r ≥ 1` and `q ≥ 2`, the necessity ceiling `(q−1)·e^r·B` strictly EXCEEDS the sufficiency
> threshold `q·B` by a factor `≥ ((q−1)/q)·e^r` (which is `≈ e^r`, and at `r ≈ log q` is `≈ q`).

So the necessity bound is `~e^r`-fold LOOSER than the threshold the prize needs: it is automatically
satisfied with room to spare and carries NONE of the prize content. ALL the content is in the
sufficiency hypothesis `S_r ≤ q·B` (the genuinely-open `S_r/(q) ≤ Wick` = char-`p` energy wall).

> `necessity_does_not_imply_sufficiency` : the necessity ceiling `(q−1)·e^r·B` does NOT entail the
> sufficiency threshold `q·B` — exhibited by the gap factor being `> 1` for `r ≥ 1`, `q ≥
2`, `B > 0`.

**Honest status.** This is a constant-gap accounting lemma, NOT progress on CORE. It guards against
reading the elementary necessity counting bound as prize progress: the necessity is `~q×`
too weak, and
the open core is entirely the sufficiency side. No CORE / cancellation / completion /
anti-concentration
/ moment-saving / capacity claim. Prize CORE stays OPEN.

Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.DCCorrectNecessitySufficiencyGap

/-- **The necessity ceiling exceeds the sufficiency threshold by `≥ ((q−1)/q)·e^r`.** With base
`B = (2r·|G|)^r > 0`, the necessity ceiling `(q−1)·e^r·B` and the sufficiency threshold
`q·B` satisfy
`q·B ≤ (q−1)·e^r·B` once `q ≥ ((q−1)/q)·e^r·q`, i.e. once `e^r ≥ q/(q−1)`. For `r ≥ 1` (so
`e^r ≥ e > 2 ≥
q/(q−1)` whenever `q ≥ 2`), the necessity ceiling is strictly the LARGER bound — the necessity is
automatically met with `~e^r` room and is not the binding constraint. -/
theorem necessityCeiling_ge_sufficiencyThreshold {q B : ℝ} {r : ℕ}
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hB : 0 < B) :
    q * B ≤ (q - 1) * (Real.exp 1) ^ r * B := by
  have hqpos : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  -- e^r ≥ e^1 = e > 2 ≥ q/(q−1)  ⟹  (q−1)·e^r ≥ (q−1)·e ≥ q
  have hexp_ge : (Real.exp 1) ^ r ≥ Real.exp 1 := by
    calc Real.exp 1 = (Real.exp 1) ^ 1 := (pow_one _).symm
      _ ≤ (Real.exp 1) ^ r := pow_le_pow_right₀ (Real.one_le_exp (by norm_num)) hr
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  -- (q−1)·e^r ≥ (q−1)·e ≥ (q−1)·2 ≥ q  (since q ≥ 2 ⟹ 2q−2 ≥ q)
  have hchain : q ≤ (q - 1) * (Real.exp 1) ^ r := by
    calc q ≤ (q - 1) * 2 := by linarith
      _ ≤ (q - 1) * Real.exp 1 := by nlinarith [he2, hq1]
      _ ≤ (q - 1) * (Real.exp 1) ^ r := by nlinarith [hexp_ge, hq1]
  exact mul_le_mul_of_nonneg_right hchain (le_of_lt hB)

/-- **Necessity does NOT imply sufficiency.** The necessity ceiling `(q−1)·e^r·B` strictly
exceeds the
sufficiency threshold `q·B` (gap factor `> 1`) for `q ≥ 2`, `r ≥ 1`, `B > 0` — so a witness
obeying the
(weak) necessity ceiling need not obey the (strong) sufficiency threshold. The prize content
is entirely
on the sufficiency side; the counting necessity is `~e^r ≈ q`-fold too loose to be the
binding bound. -/
theorem necessity_does_not_imply_sufficiency {q B : ℝ} {r : ℕ}
    (hq : 2 ≤ q) (hr : 1 ≤ r) (hB : 0 < B) :
    q * B < (q - 1) * (Real.exp 1) ^ r * B := by
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hexp_ge : Real.exp 1 ≤ (Real.exp 1) ^ r := by
    calc Real.exp 1 = (Real.exp 1) ^ 1 := (pow_one _).symm
      _ ≤ (Real.exp 1) ^ r := pow_le_pow_right₀ (Real.one_le_exp (by norm_num)) hr
  -- strict: (q−1)·e^r > (q−1)·2 ≥ q  (q≥2 ⟹ 2q−2 ≥ q, with strictness from e>2)
  have hchain : q < (q - 1) * (Real.exp 1) ^ r := by
    have h1 : (q - 1) * 2 < (q - 1) * Real.exp 1 := by nlinarith [he2, hq1]
    have h2 : (q - 1) * Real.exp 1 ≤ (q - 1) * (Real.exp 1) ^ r := by nlinarith [hexp_ge, hq1]
    have h3 : q ≤ (q - 1) * 2 := by linarith
    linarith
  exact mul_lt_mul_of_pos_right hchain hB

end ArkLib.ProximityGap.Frontier.DCCorrectNecessitySufficiencyGap

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.DCCorrectNecessitySufficiencyGap in
#print axioms necessityCeiling_ge_sufficiencyThreshold
open ArkLib.ProximityGap.Frontier.DCCorrectNecessitySufficiencyGap in
#print axioms necessity_does_not_imply_sufficiency
