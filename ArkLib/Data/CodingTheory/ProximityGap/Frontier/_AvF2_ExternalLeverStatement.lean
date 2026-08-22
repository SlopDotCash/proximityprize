/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DiBenedettoBetaValidityWindow

/-!
# The external lever STATEMENT, precisely typed: di Benedetto et al. Theorem 3.1 (#444, AvF2)

This brick replaces a *vague* opaque named `Prop` with the **precise, paper-faithful typed
statement** of the external analytic-number-theory lever the di-Benedetto sup-norm beat consumes,
together with its exact subgroup-energy inputs. Everything here is the STATEMENT (named hypothesis),
never the proof — but stated with the EXACT exponents and hypotheses verified against the actual
paper, so the in-tree conditional theorems now depend on a checkable external claim.

## Citation — VERIFIED against the actual paper (arXiv:2003.06165, PDF fetched this session)

> **D. di Benedetto, M. Z. Garaev, V. C. García, D. González-Sánchez, I. E. Shparlinski,
> C. A. Trujillo**, *"New estimates for exponential sums over multiplicative subgroups and
> intervals in prime fields"*, arXiv:2003.06165.

The pieces used, transcribed VERBATIM from the fetched PDF:

* **Theorem 3.1.** *Let `H` be a multiplicative subgroup of `F_p^*` of order `H` with
  `p^{1/2} > H > p^{1/4}`. Then* `max_{(a,p)=1} |S_a(H)| ≲ H^{2689/2880} · p^{1/72}`.
  *In particular, when `H > p^{1/4}`, Theorem 3.1 gives* `max_{(a,p)=1} |S_a(H)| ≲ H^{1−31/2880}`.

  (`S_a(H) = Σ_{x∈H} e_p(a x)` is the complete sum over the subgroup; `≲`/`≪` is Vinogradov,
  absorbing the `p^{o(1)}`/`log` factors. The `2689/2880` and `1/72` are EXACT in the paper.)

* **Lemma 4.1** (Petridis–Shparlinski, [11, Thm 1.1]): the trilinear bound underpinning Thm 3.1,
  `|Σ_{x,y,z} α_x β_y γ_z e_p(axyz)| ≪ p^{1/4} |X|^{3/4} |Y|^{3/4} |Z|^{7/8}` for `|α|,|β|,|γ| ≤ 1`.
* **Lemma 4.2** (Murphy–Rudnev–Shkredov–Shteinikov): `T_2(H) ≪ H^{49/20} log^{1/5} H` (so the
  quadratic-energy exponent is `t_2 = 49/20`, NOT the Sidon-floor `2`).
* **Lemma 4.3** (same authors): `T_3(H) ≪ H^4 log H` (the cubic-energy exponent is `t_3 = 4`, the
  FULL subgroup energy — NOT a near-Sidon `n^3`).

## ⚠️ Honesty correction landed by this brick (rule 6 / rule 1)

The pre-existing opaque `AvT3aDiBenedettoBeat.DiBenedettoThm31` was stated as *"`E_3 ≤ 15 n^3`
(near-Sidon) ⟹ `M ≤ n^{23/24} p^{1/72}`"* with `Hexp = 7`. Reading the actual paper shows:

* Theorem 3.1 proper uses GENERIC subgroup energies `T_2 ≪ H^{49/20}` (Lem 4.2) and `T_3 ≪ H^4`
  (Lem 4.3), and concludes `H^{2689/2880} p^{1/72}` — the saving at `H > p^{1/4}` is `31/2880`,
  i.e. exponent `1 − 31/2880 = 2849/2880 ≈ 0.98924`. This MATCHES the in-tree
  `DiBenedettoBetaValidityWindow.rawExponent 4 = 1 − 31/2880` exactly.
* The `23/24 ≈ 0.9583` figure is a SEPARATE near-Sidon RE-CALIBRATION of the same trilinear
  machinery (feeding the Sidon-floor energies `T_2 = 3n²−3n`, `T_3 ≤ 15n³` instead of the generic
  `H^{49/20}, H^4`); it is the project's own specialization, NOT verbatim Theorem 3.1. It is a
  plausible recalibration but is NOT what the paper's Theorem 3.1 states.

So this brick formalizes the GENUINE Theorem 3.1 (`2689/2880`, `1/72`) and its energy inputs as a
precise typed `Prop`, and proves the paper's stated COROLLARY (`H^{1−31/2880}` for `H > p^{1/4}`)
FROM the precise statement. The conditional in-tree results can now reference
`DiBenedettoThm31Precise` — a claim that is checkable line-by-line against the paper — rather than a
vague placeholder.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444. NOT prize closure:
`2849/2880 ≫ 1/2`; this names a precise SOTA external lever, it does not cross the BGK wall.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AvF2ExternalLeverStatement

open ArkLib.ProximityGap.DiBenedettoBetaValidityWindow (rawExponent rawExponent_at_four burgessEdge)
open ArkLib.ProximityGap.BGKExponentReduction (diBenedettoDelta)

/-! ## The exact exponents, named as rationals (verified against the paper). -/

/-- Theorem 3.1's prefactor exponent on `H` in the main range `p^{1/2} > H > p^{1/4}`:
`2689/2880`. (Paper, verbatim.) -/
def thm31HExponent : ℚ := 2689 / 2880

/-- Theorem 3.1's exponent on `p`: `1/72`. (Paper, verbatim.) -/
def thm31PExponent : ℚ := 1 / 72

/-- The COROLLARY exponent on `H` in the regime `H > p^{1/4}`: `1 − 31/2880 = 2849/2880`.
(Paper, verbatim: "`H^{1−31/2880}`".) -/
def corollaryHExponent : ℚ := 1 - 31 / 2880

/-- Lemma 4.2 quadratic-energy exponent: `t_2 = 49/20` (`T_2(H) ≪ H^{49/20} log^{1/5} H`). -/
def t2Exponent : ℚ := 49 / 20

/-- Lemma 4.3 cubic-energy exponent: `t_3 = 4` (`T_3(H) ≪ H^4 log H`). -/
def t3Exponent : ℚ := 4

/-- Sanity: the corollary exponent equals `2849/2880`. -/
theorem corollaryHExponent_eq : corollaryHExponent = 2849 / 2880 := by
  unfold corollaryHExponent; norm_num

/-- **Consistency with the in-tree validity window.** At the prize point `β = 4` (`p = n^4`),
substituting `p^{1/72} = n^{4/72} = n^{1/18}` into Theorem 3.1's `H^{2689/2880} p^{1/72}` gives the
total `n`-exponent `rawExponent 4 = 1 − 31/2880 = 2849/2880`, which is EXACTLY the corollary
exponent. The paper's two figures cohere with `DiBenedettoBetaValidityWindow`. -/
theorem corollary_matches_rawExponent_four :
    rawExponent 4 = (corollaryHExponent : ℝ) := by
  rw [rawExponent_at_four]
  unfold corollaryHExponent
  rw [show (diBenedettoDelta : ℝ) = 31 / 2880 from by
    unfold diBenedettoDelta; norm_num]
  push_cast; ring

/-! ## The precise typed STATEMENT of Theorem 3.1 (named, not proved). -/

/-- **Theorem 3.1 (arXiv:2003.06165), the EXACT typed statement.** For a multiplicative subgroup
`H ⊆ F_p^*` with the range hypothesis `p^{1/2} > H > p^{1/4}` (encoded on the real magnitudes
`Hcard, p` as `p^{1/2} > Hcard > p^{1/4}`), and `Mval = max_{(a,p)=1}|S_a(H)|` the worst-case
complete subgroup sum, the bound

  `Mval ≤ Cdb · Hcard^{2689/2880} · p^{1/72}`

holds, for an absolute implied constant `Cdb ≥ 0` (the Vinogradov `≪` constant, absorbing the
`p^{o(1)}` factor). This is the verbatim main-range Theorem 3.1. We name it; we never prove it.

The energy inputs are carried as explicit premises so the statement records WHICH external facts
the paper's proof consumes (Lemmas 4.2/4.3): `T2val ≤ Cdb · Hcard^{49/20}` and
`T3val ≤ Cdb · Hcard^4` (the `log` factors absorbed into `Cdb`). -/
structure DiBenedettoThm31Precise (Hcard p Mval T2val T3val Cdb : ℝ) : Prop where
  /-- The implied/Vinogradov constant is nonnegative. -/
  const_nonneg : 0 ≤ Cdb
  /-- Range hypothesis: `p^{1/4} < H < p^{1/2}` (the exact range of Theorem 3.1). -/
  range_lower : p ^ ((1 : ℝ) / 4) < Hcard
  range_upper : Hcard < p ^ ((1 : ℝ) / 2)
  /-- Lemma 4.2 input: `T_2 ≪ H^{49/20}`. -/
  energy_two : T2val ≤ Cdb * Hcard ^ ((t2Exponent : ℝ))
  /-- Lemma 4.3 input: `T_3 ≪ H^4`. -/
  energy_three : T3val ≤ Cdb * Hcard ^ ((t3Exponent : ℝ))
  /-- The Theorem 3.1 conclusion: `M ≤ Cdb · H^{2689/2880} · p^{1/72}`. -/
  sup_bound : Mval ≤ Cdb * Hcard ^ ((thm31HExponent : ℝ)) * p ^ ((thm31PExponent : ℝ))

/-- **The paper's stated COROLLARY, derived FROM the precise statement.** In the regime
`H > p^{1/4}` (the lower-range endpoint), Theorem 3.1's `p^{1/72}` factor is bounded by
`H^{(1/4)·(1/72)·4} = H^{1/72}`... — more precisely, since `p^{1/4} < H` we have
`p^{1/72} = (p^{1/4})^{1/18} ≤ H^{1/18}`, and `2689/2880 + 1/18 = 2849/2880 = 1 − 31/2880`. Hence
`M ≤ Cdb · H^{1−31/2880}`. This is the paper's "`H^{1−31/2880}`" corollary, now a THEOREM modulo the
named Theorem 3.1 statement. -/
theorem corollary_of_thm31 {Hcard p Mval T2val T3val Cdb : ℝ}
    (hH : 0 < Hcard) (hp : 0 ≤ p)
    (h : DiBenedettoThm31Precise Hcard p Mval T2val T3val Cdb) :
    Mval ≤ Cdb * Hcard ^ ((corollaryHExponent : ℝ)) := by
  -- From `p^{1/4} < Hcard`, get `p^{1/72} ≤ Hcard^{1/18}`.
  have hp14 : (0 : ℝ) ≤ p ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hp _
  have hple : p ^ ((1 : ℝ) / 72) ≤ Hcard ^ ((1 : ℝ) / 18) := by
    have hpow : (p ^ ((1 : ℝ) / 4)) ^ ((1 : ℝ) / 18) ≤ Hcard ^ ((1 : ℝ) / 18) := by
      apply Real.rpow_le_rpow hp14 (le_of_lt h.range_lower) (by norm_num)
    rwa [← Real.rpow_mul hp, show (1 : ℝ) / 4 * (1 / 18) = 1 / 72 from by norm_num] at hpow
  -- Combine with the sup bound.
  calc Mval ≤ Cdb * Hcard ^ ((thm31HExponent : ℝ)) * p ^ ((thm31PExponent : ℝ)) := h.sup_bound
    _ ≤ Cdb * Hcard ^ ((thm31HExponent : ℝ)) * Hcard ^ ((1 : ℝ) / 18) := by
        have hc : 0 ≤ Cdb * Hcard ^ ((thm31HExponent : ℝ)) :=
          mul_nonneg h.const_nonneg (Real.rpow_nonneg hH.le _)
        apply mul_le_mul_of_nonneg_left _ hc
        simpa [thm31PExponent] using hple
    _ = Cdb * Hcard ^ ((corollaryHExponent : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hH]
        congr 2
        unfold thm31HExponent corollaryHExponent
        push_cast; norm_num

/-- **The corollary exponent is `≫ 1/2` (the honest scope reminder).** `1/2 < 2849/2880 < 1`: the
genuine paper bound is firmly on the HIGH side of the BGK/Paley wall — a SOTA lever, not a
crossing. -/
theorem corollary_above_prize :
    (1 : ℚ) / 2 < corollaryHExponent ∧ corollaryHExponent < 1 := by
  unfold corollaryHExponent; constructor <;> norm_num

/-- **The energy exponents are the paper's, not the near-Sidon floor.** `t_2 = 49/20 > 2` and
`t_3 = 4 > 3`: Theorem 3.1 proper consumes GENERIC subgroup energies, strictly above the Sidon
floor that the `23/24` recalibration uses. (Honesty pin: the two are distinct calibrations.) -/
theorem energy_exponents_above_sidon_floor :
    (2 : ℚ) < t2Exponent ∧ (3 : ℚ) < t3Exponent := by
  unfold t2Exponent t3Exponent; constructor <;> norm_num

end ArkLib.ProximityGap.Frontier.AvF2ExternalLeverStatement

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AvF2ExternalLeverStatement.corollary_matches_rawExponent_four
#print axioms ArkLib.ProximityGap.Frontier.AvF2ExternalLeverStatement.corollary_of_thm31
#print axioms ArkLib.ProximityGap.Frontier.AvF2ExternalLeverStatement.corollary_above_prize
#print axioms ArkLib.ProximityGap.Frontier.AvF2ExternalLeverStatement.energy_exponents_above_sidon_floor
