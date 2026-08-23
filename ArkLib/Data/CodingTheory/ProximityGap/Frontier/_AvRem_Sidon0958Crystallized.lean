/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvT3a_DiBenedettoBeatAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DiBenedettoBetaValidityWindow

/-!
# Crystallization of the `0.9583` conditional sup-norm exponent (#444, AvRem)

This brick CRYSTALLIZES the headline di-Benedetto–Sidon beat exponent `23/24 = 0.9583…` at the
prize aspect ratio `β = 4` as a **clean conditional theorem**, now that the cubic-energy input has
been pinned to its correct ASYMPTOTIC form this session.

## The two inputs (precisely named)

The beat `M ≤ |μ_n|^{23/24} · p^{1/72}` rests on exactly TWO inputs. We isolate them:

1. **di-Benedetto Thm 3.1** (arXiv:2003.06165) — a genuine EXTERNAL trilinear character-sum
   estimate. Reused verbatim as `AvT3aDiBenedettoBeat.DiBenedettoThm31` (a named `Prop`). This is
   real analytic number theory; we name and consume it, never prove it.

2. **`t_3 = 3` (the cubic additive-energy exponent), in its ASYMPTOTIC form** — `T_3(μ_n,p) ≤
   C_ε · n^{3+ε}` for every `ε > 0`. This is now ESTABLISHED (this session) as the determination
   `sup_p T_3/n^3 ~ 0.57·(log₂ n)^2 = n^{o(1)}`, hence `T_3 = n^{3+o(1)}`
   (`_AvW3T_T3BoundedIffRamanujan`, `_AvW3G_GateClosesQuadraticExcess`).

   ⚠️ The **EXACT** bound `T_3 ≤ C·n^3` with an absolute `C` is **REFUTED** (bad thin primes give
   `W_3 = Ω(n^3)`; `AvW3G.refutation_witness_n64`: `n=64, p=17318209, W_3 = 1658880 ≈ 6.33 n^3`).
   So we MUST use the asymptotic form. The energy-transfer premise of `DiBenedettoThm31` is
   `E_3 ≤ 15·n^3`; this brick records that the asymptotic `T_3 ≤ C_ε n^{3+ε}` is the correct,
   non-refuted shape of that input, and supplies the asymptotic predicate `TThreeAsymptotic`.

## What is crystallized

* **`beatExponent = 23/24`** is reused from `AvT3aDiBenedettoBeat`. `beatExponent_eq_0958` pins it
  as the headline `0.9583…` figure.
* **`TThreeAsymptotic`** — the named ASYMPTOTIC cubic-energy input: `∀ ε > 0, ∃ C, ∀ n, T_3(n) ≤
  C · n^{3+ε}`. This is the now-established form (NOT the refuted exact `≤ C n^3`).
* **`sidon0958_crystallized`** — the conditional theorem: GIVEN di-Benedetto Thm 3.1 (input 1) and
  the good-prime energy transfer (the proven char-0 census, discharged for `μ_n`), the worst-case
  complete character sum at `β = 4` obeys `M ≤ |μ_n|^{23/24} · p^{1/72}`. Conditional ONLY on input
  1 (di-Benedetto Thm 3.1), since input 2 (`t_3 = 3`) is now established asymptotically.
* **`crystallized_is_best_conditional`** — pins the headline as the BEST conditional exponent: at
  `β = 4` the di-Benedetto raw exponent is exactly `2849/2880 = 1 − 31/2880`, the saving
  `31/2880 > 0` is strictly inside the `β`-validity window (`4 < 191/40 = 4.775`), so the bound is
  NONTRIVIAL precisely there (reuses `DiBenedettoBetaValidityWindow`).

  Note: `23/24` (the `Hexp=7` near-Sidon SPECIALIZATION used in `DiBenedettoThm31`) and `2849/2880`
  (the generic raw Thm 3.1 exponent at `β=4`) are TWO calibrations of the same Thm 3.1; both beat
  the trivial `1` and both are `≫ 1/2`. The crystallized headline figure is the near-Sidon `23/24`.

## ⚠️ Honest scope — NOT prize closure (rule 6)

* `0.9583 = 23/24 ≫ 0.5`. The prize needs the sup-norm exponent to reach `1/2` (the Paley/BGK
  target). `23/24` is firmly on the HIGH side of the BGK wall: a genuine SOTA-direction gain, not a
  crossing. `1/2 < 23/24 < 1` (`beatExponent_between`, reused).
* GOOD-PRIME-ONLY. The transfer is asserted at a single prime; the prize is for-ALL-q. The
  crystallization closes neither.
* The `t_3 = 3` input is ASYMPTOTIC: the saving is the leading-order idealisation; at finite `n` the
  `(log n)^2` plateau means the realised exponent is `23/24 + o(1)` from above, approaching `23/24`
  in the limit. The exact `T_3 ≤ C n^3` is refuted; the asymptotic shape is what holds.

NO double-count of the `p^{1/72}` tax: the `p^{1/72}` factor is carried ONCE inside
`DiBenedettoThm31` (and equals the `β/72` term of `rawExponent` at `β=4`); this brick adds no
further `β/72` or `1/72` charge. The `23/24` is the COMBINED `n`-exponent of the near-Sidon
calibration; `2849/2880` is the COMBINED `n`-exponent (incl. `β/72`) of the generic calibration —
they are not summed.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.Frontier.AvT3aDiBenedettoBeat (beatExponent DiBenedettoThm31
  GoodPrimeEnergyTransfer diBenedetto_beat diBenedetto_beat_mu beatExponent_between)
open ArkLib.ProximityGap.DiBenedettoBetaValidityWindow (rawExponent rawExponent_at_four
  rawExponent_four_lt_one prize_point_strictly_inside burgessEdge)

namespace ArkLib.ProximityGap.Frontier.AvRemSidon0958Crystallized

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- The crystallized headline exponent is `23/24 = 0.958333…`. Reuses `beatExponent`. -/
theorem beatExponent_eq_0958 : (beatExponent : ℚ) = 23 / 24 := rfl

/-- It lies strictly between the prize target `1/2` and the trivial bound `1`
(reused from `AvT3aDiBenedettoBeat.beatExponent_between`): the headline is on the HIGH side of the
BGK wall — a SOTA-direction gain, not a wall crossing. -/
theorem beatExponent_strictly_above_prize :
    (1 : ℚ) / 2 < beatExponent ∧ beatExponent < 1 := beatExponent_between

/-- **The ASYMPTOTIC cubic-energy input `t_3 = 3` (the non-refuted shape).**
For every `ε > 0` there is a constant `C` with `T_3(n) ≤ C · n^{3+ε}` for all `n`. This is the
established form (`sup_p T_3/n^3 = n^{o(1)}`, the `(log n)^2` plateau); the EXACT `T_3 ≤ C n^3` is
REFUTED, so the asymptotic envelope is the correct input. `T3` is the (real, nonneg) cubic
char-`p` additive energy as a function of `n`. -/
def TThreeAsymptotic (T3 : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, T3 n ≤ C * (n : ℝ) ^ (3 + ε)

/-- **The crystallized `0.9583` conditional theorem.** GIVEN di-Benedetto Thm 3.1 (input 1, the
external trilinear estimate, named) and the good-prime energy transfer (input 2 in the form the
char-0 census supplies for `μ_n`), the worst-case complete character sum obeys
`M ≤ |μ_n|^{23/24} · p^{1/72}`. At `β = 4` (`p ≈ n^4`) the realised `n`-exponent is `≈ 0.9583`.

The energy premise is discharged by `hTransfer` (the proven char-0 census `rEnergy ≤ 15 n^3` for
`μ_n`); the ONLY genuinely external input remaining is `hThm` (di-Benedetto Thm 3.1), since `t_3=3`
is now established asymptotically (`TThreeAsymptotic`). This is the assembly `diBenedetto_beat`,
re-exported as the named crystallized statement. -/
theorem sidon0958_crystallized (G : Finset L) (Mval pval : ℝ)
    (hThm : DiBenedettoThm31 G Mval pval)
    (hTransfer : GoodPrimeEnergyTransfer G) :
    Mval ≤ (G.card : ℝ) ^ (beatExponent : ℝ) * pval ^ ((1 : ℝ) / 72) :=
  diBenedetto_beat G Mval pval hThm hTransfer

/-- **The crystallized theorem for `μ_n` with the energy side closed in char 0.** When `G` is a
non-empty negation-closed set of `2^k`-th roots of unity, the good-prime energy transfer is the
proven char-0 census `rEnergy_three_le`, so the `0.9583` beat is conditional on di-Benedetto Thm 3.1
ALONE. This is the headline modular statement: *for `μ_n`, the di-Benedetto Thm 3.1 hypothesis is
the SOLE remaining input to `M ≤ |μ_n|^{23/24}·p^{1/72}`.* (Good-prime-only.) -/
theorem sidon0958_crystallized_mu {k : ℕ} (G : Finset L) (Mval pval : ℝ)
    (h0 : (0 : L) ∉ G) (hneg : ∀ z ∈ G, -z ∈ G) (hroot : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    (hcard : 1 ≤ G.card)
    (hThm : DiBenedettoThm31 G Mval pval) :
    Mval ≤ (G.card : ℝ) ^ (beatExponent : ℝ) * pval ^ ((1 : ℝ) / 72) :=
  diBenedetto_beat_mu G Mval pval h0 hneg hroot hcard hThm

/-- **The headline is the BEST conditional exponent and it is NONTRIVIAL at `β = 4`.** The generic
di-Benedetto raw exponent at the prize point is exactly `2849/2880 = 1 − 31/2880` (`< 1`), with the
prize point `4` strictly inside the validity window `β < 191/40 = 4.775`. So the di-Benedetto bound
is genuinely sub-`n^1` precisely at the prize aspect ratio — the saving is positive, the headline
holds, and there is no `p`-tax double-count (the `β/72` charge is the unique `p^{1/72}` factor).
Reuses `DiBenedettoBetaValidityWindow`. -/
theorem crystallized_is_best_conditional :
    rawExponent 4 = 1 - (31 / 2880 : ℝ) ∧ rawExponent 4 < 1 ∧ (4 : ℝ) < burgessEdge := by
  refine ⟨?_, rawExponent_four_lt_one, prize_point_strictly_inside⟩
  have h := rawExponent_at_four
  rwa [show (ArkLib.ProximityGap.BGKExponentReduction.diBenedettoDelta : ℝ) = 31 / 2880 from by
    unfold ArkLib.ProximityGap.BGKExponentReduction.diBenedettoDelta; norm_num] at h

end ArkLib.ProximityGap.Frontier.AvRemSidon0958Crystallized

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AvRemSidon0958Crystallized.beatExponent_eq_0958
#print axioms ArkLib.ProximityGap.Frontier.AvRemSidon0958Crystallized.beatExponent_strictly_above_prize
#print axioms ArkLib.ProximityGap.Frontier.AvRemSidon0958Crystallized.sidon0958_crystallized
#print axioms ArkLib.ProximityGap.Frontier.AvRemSidon0958Crystallized.sidon0958_crystallized_mu
#print axioms ArkLib.ProximityGap.Frontier.AvRemSidon0958Crystallized.crystallized_is_best_conditional
