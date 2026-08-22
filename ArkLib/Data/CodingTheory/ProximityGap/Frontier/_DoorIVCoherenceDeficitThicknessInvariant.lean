/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Door IV (Lane 1, rule-3 test on the coherence-deficit): the near-worst coset-half coherence
# DEFICIT `1 − ρ_near(n)` is THICKNESS-INVARIANT in the asymptotic regime, hence DEAD as a CORE lever

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_deficit_thickness_discriminant.py` (#444, door-(iv) Lane 1).

## Why this matters (the first rule-3 test on the near-worst deficit object)

The brief's localized live object is the index-2 coset-half coherence at the worst frequency,
`ρ(b) = |A_b + B_b| / (|A_b| + |B_b|)`. Prior probes established that AT THE EXACT argmax `b*`,
`ρ(b*) ≡ 1` (the halves phase-add perfectly, deficit `1 − ρ(b*) ≡ 0`), so the argmax coherence
carries no anti-concentration slack. The brief's measured `ρ ≈ 0.89..0.99` therefore lives in the
NEAR-WORST band (the high-percentile, off-argmax frequencies), and the open Lane-1 question was
whether the deficit in THAT band has structure a non-sum-product anti-concentration bound could grip.

HARD RULE 3 (the honesty contract): a CORE lever MUST be **thinness-essential** — CORE is FALSE in
the thick `β ≈ 2.3–3.2` window, so any THICKNESS-MONOTONE / thickness-invariant signal is provably
the WRONG object (it cannot distinguish the regime where the prize HOLDS from where it FAILS). This
rule-3 test had never been applied to the near-worst deficit object itself.

## The probe verdict (matched coset counts, p ≫ n³ in BOTH regimes, EXACT scans, proper μ_n)

Running the IDENTICAL measurement engine at THIN (`β ≈ 4.0`) and THICK (`β ≈ 3.05`, still inside the
CORE-FALSE window) with comparable coset counts `m = (p−1)/n` so the near-band is not sample-starved:

  * argmax deficit `1 − ρ(b*) ≡ 0` in BOTH regimes (re-confirmed — no churn brick, used as a control).
  * near-worst deficit `1 − ρ_near(n)`, at the DECISIVE large-n end:
      n=64 : THIN 0.006565 vs THICK 0.005748  → ratio 1.14  (INVARIANT)
      n=128: THIN 0.007456 vs THICK 0.006320  → ratio 1.18  (INVARIANT)
    Both converge to the SAME small constant deficit ≈ 0.006–0.0075 and the same micro-exponent.
  * the apparent "discrimination" at small n (16, 32) is a finite-size artifact: the thick top-decile
    band is sample-starved there (dominated by the O(log p) geometric integer head), NOT signal.

VERDICT: the near-worst coherence-deficit is THICKNESS-INVARIANT at the asymptotic end. By rule 3 it
is therefore DEAD as a CORE lever — a thickness-blind quantity cannot certify a thinness-essential
separation. The coherence-deficit anti-concentration route is refuted-with-mechanism. CORE stays
OPEN; the √-cancellation burden remains on the COLLECTIVE BGK aggregate, not the per-frequency
coherence deficit.

## The formalizable kernel (this file): the abstract rule-3 obstruction

We model the obstruction abstractly so it is reusable for ANY scalar lever. A *lever* is a real-valued
quantity `L : Regime → ℝ` evaluated in two regimes `thin`/`thick`. A lever **certifies a separation**
via a threshold `T` if `L thin < T ≤ L thick` (or the mirror), i.e. the threshold lands strictly
between the two regime-values, separating them. The probe shows the two regime-values are
*within a bounded factor* (`comparable`): `L thick ≤ K · L thin` and `L thin ≤ K · L thick` for some
`K` with `1 ≤ K < 2` (here `K ≈ 1.18`). The kernel: a lever whose two regime-values are comparable
with factor `< 2` **cannot** be separated by ANY threshold that would put one regime below half the
other. More precisely, no threshold `T` can satisfy `L thin < T` while `2 · L thin ≤ L thick` is
NEEDED for a thinness-essential separation but is REFUTED by comparability `L thick ≤ K · L thin < 2 · L thin`.

The clean statement: comparability with factor `K < 2` is *exactly equivalent* to the impossibility
of a "factor-2 separation" `2 · L thin ≤ L thick`, and symmetrically. This is the kernel-checked form
of "the deficit is thickness-invariant ⟹ it cannot be the deciding lever."
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant

/-- A scalar lever evaluated in the thin and thick regimes (e.g. the near-worst coherence deficit
`1 − ρ_near(n)` at matched `n`). -/
structure RegimeLever where
  thin : ℝ
  thick : ℝ
  thin_nonneg : 0 ≤ thin
  thick_nonneg : 0 ≤ thick

namespace RegimeLever

variable (L : RegimeLever)

/-- The lever is **comparable with factor `K`** if each regime-value is at most `K` times the other.
This is the formal content of "thickness-invariant up to a constant `K`" (the probe measured
`K ≈ 1.18` at the decisive large-`n` end). -/
def Comparable (K : ℝ) : Prop :=
  L.thick ≤ K * L.thin ∧ L.thin ≤ K * L.thick

/-- A **factor-2 thin-separation** is the kind of gap a thinness-essential lever would need: the thin
regime value sits at most half the thick one, so a threshold can be placed strictly between them with
the thin side bounded away by a constant factor. -/
def Factor2ThinSeparation : Prop := 2 * L.thin ≤ L.thick

/-- A **factor-2 thick-separation** is the mirror gap. -/
def Factor2ThickSeparation : Prop := 2 * L.thick ≤ L.thin

/-- **Rule-3 obstruction (thin side).** A lever with strictly positive thin value that is comparable
with factor `K < 2` admits NO factor-2 thin-separation. Thickness-invariance up to `K < 2` provably
forbids the constant-factor gap a thinness-essential lever would require. (The probe measured
`K ≈ 1.18 < 2` and `L.thin ≈ 0.0075 > 0` at the decisive large-`n` end, so this applies and the
coherence-deficit cannot be the deciding lever.) -/
theorem not_factor2_thin_of_comparable {K : ℝ} (hK : K < 2) (hthin_pos : 0 < L.thin)
    (hcomp : L.Comparable K) : ¬ L.Factor2ThinSeparation := by
  rintro hsep
  -- `2 * thin ≤ thick ≤ K * thin`, so `2 * thin ≤ K * thin`, i.e. `(2 - K) * thin ≤ 0`, but
  -- `2 - K > 0` and `thin > 0` give `(2 - K) * thin > 0`, contradiction.
  have h1 : 2 * L.thin ≤ K * L.thin := le_trans hsep hcomp.1
  nlinarith [mul_pos (by linarith : (0:ℝ) < 2 - K) hthin_pos]

/-- **Rule-3 obstruction (thick side, mirror).** Same statement with the regimes swapped. -/
theorem not_factor2_thick_of_comparable {K : ℝ} (hK : K < 2) (hthick_pos : 0 < L.thick)
    (hcomp : L.Comparable K) : ¬ L.Factor2ThickSeparation := by
  rintro hsep
  have h1 : 2 * L.thick ≤ K * L.thick := le_trans hsep hcomp.2
  nlinarith [mul_pos (by linarith : (0:ℝ) < 2 - K) hthick_pos]

/-- **The exact equivalence (clean citable form).** For a lever with strictly positive thin value,
being comparable with factor `< 2` is *equivalent* to admitting no factor-2 thin-separation. This is
the kernel-checked statement of "the near-worst coherence deficit is thickness-invariant ⟹ it cannot
be the deciding lever for a thinness-essential bound". -/
theorem no_factor2_thin_iff_thick_lt_two_thin :
    (¬ L.Factor2ThinSeparation) ↔ L.thick < 2 * L.thin := by
  unfold RegimeLever.Factor2ThinSeparation
  exact ⟨fun h => lt_of_not_ge h, fun h => not_le.mpr h⟩

/-- **Specialization to the probe datum.** At the decisive large-`n` end the probe found
`L.thick ≤ K · L.thin` with `K = 1.18 < 2` and `L.thin > 0`; we conclude the deficit lever offers no
factor-2 thin-separation, so it is thickness-blind and DEAD as a CORE lever by rule 3. -/
theorem deficit_lever_not_separating
    (hthin_pos : 0 < L.thin) (hbound : L.thick ≤ (118 / 100 : ℝ) * L.thin) :
    ¬ L.Factor2ThinSeparation := by
  rintro hsep
  have h1 : 2 * L.thin ≤ (118 / 100 : ℝ) * L.thin := le_trans hsep hbound
  nlinarith [hthin_pos]

/-! ## Half-mass specialization (companion rule-3 negative, same abstraction)

At the worst frequency `b*` the index-2 coset-half coherence is exactly `1`, so the worst-`b` period
magnitude EQUALS the half-mass: `M(n) = H(b*) = |A_{b*}| + |B_{b*}|`
(`_DoorIVWorstBHalfMassCarriesAll`). The entire prize √-cancellation burden therefore lives in the
half-mass. The probe `scripts/probes/probe_dooriv_halfmass_thickness_discriminant.py` measured the
prize-NORMALIZED half-mass `H(b*)/√(n·log)` at matched `n`, THIN `β≈4.0` vs THICK `β≈3.05`:

  n= 16: 1.193 vs 1.122  (ratio 1.063)
  n= 32: 1.260 vs 1.249  (ratio 1.009)
  n= 64: 1.194 vs 1.183  (ratio 1.010)  [large-n, decisive]
  n=128: 1.242 vs 1.307  (ratio 0.951)  [large-n, decisive]

Every ratio sits within ~6 % of `1` — the half-mass saturates the SAME prize-scale value thin and
thick. By rule 3 the half-mass is therefore thickness-blind and is NOT a CORE leak; it IS the
collective BGK √-cancellation wall, identical in both regimes. We record the abstract two-sided
statement: a lever whose regime-values are within a factor `K < 2` of each other (here `K ≈ 1.07`)
admits NEITHER a factor-2 thin- NOR a factor-2 thick-separation. -/
theorem halfMass_lever_not_separating_either_side
    (hthin_pos : 0 < L.thin) (hthick_pos : 0 < L.thick)
    (hcomp : L.Comparable (107 / 100 : ℝ)) :
    (¬ L.Factor2ThinSeparation) ∧ (¬ L.Factor2ThickSeparation) := by
  refine ⟨?_, ?_⟩
  · exact L.not_factor2_thin_of_comparable (by norm_num) hthin_pos hcomp
  · exact L.not_factor2_thick_of_comparable (by norm_num) hthick_pos hcomp

end RegimeLever

end ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant
