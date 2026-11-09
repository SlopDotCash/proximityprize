/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Research.ProximityGap.MCAPlateauWindow
import ArkLib.Research.ProximityGap.MCAEndpointLower

/-!
# A general-`δ` two-sided value bracket for the MCA error of an RS code

This file consolidates the two proven, unconditional, axiom-clean quantitative bounds on the
mutual-correlated-agreement error `ε_mca(RS[F, domain, k], δ)` into a single citable
two-sided bracket valid at **every** sub-plateau radius `δ`:

  `(⌊δ·n⌋+1)/q  ≤  ε_mca(RS[F, domain, k], δ)  ≤  C(n, max(⌈(1-δ)·n⌉, k+1))/q`.

* **Lower bound** (`epsMCA_ge_linear_floor`). The explicit `t`-spike construction
  (`epsMCA_ge_spike`, `MCAEndpointLower`) is admissible with `t = ⌊δ·n⌋+1` for every radius
  whose floor index still fits below the code dimension. This packages the spike floor as a
  single *linear-in-`δ`* staircase lower bound, removing the per-call admissibility bookkeeping.
* **Upper bound** (`epsMCA_le_choose_div`, `MCAPlateauWindow`). The canonical-witness window
  count, an unconditional union bound holding for all `δ`.

## The honest open core (ABF26 §1, issue #232)

The ratio of the two endpoints is `C(n, max(⌈(1-δ)n⌉, k+1)) / (⌊δ·n⌋+1)`, which is
*exponential* in `n` in the Johnson→capacity window. Heuristically, for the deployed prize
parameters (`q < 2²⁵⁶`, `ε* = 2⁻¹²⁸`, `k ≤ 2⁴⁰`, smooth power-of-two domain) one expects these
two proven bounds to straddle `ε*` over much of the interior: the window upper bound exceeds
`ε*` well below the Johnson radius, while the linear lower bound `(⌊δ·n⌋+1)/q` stays tiny on its
whole domain of validity. **This straddle claim is not formalized here** (no theorem in this file
instantiates the deployed parameters); note also that the lower bound is only stated for
`⌊δ·n⌋+1+k ≤ n`, i.e. strictly below capacity, so it says nothing at or above capacity. Neither
in-tree bound is tight enough to certify the crossover `δ*`, which is exactly the
new-mathematics content of the Grand MCA Challenge (the strong Johnson-range upper bound
`poly(n)/q` and the strong near-capacity superpolynomial lower bound, neither of which is
currently known for explicit smooth-domain RS codes; see
`MutualCorrAgreement.mca_johnson_bound_CONJECTURE` and the §3 state of the art).

(An earlier `epsMCA_bracket_gap_excludes_pin` merely returned `epsMCA_bracket` together with
its own straddle hypotheses verbatim; it added no content and has been removed.)

This file therefore does **not** claim the prize; it states precisely, and machine-checks, the
two-sided bracket that the proven theory delivers and the exact sense in which it falls short.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code ReedSolomon
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Linear staircase floor on `ε_mca` across the whole sub-plateau range.**

For every RS code and every radius `δ` whose floor index fits below the code dimension
(`⌊δ·n⌋+1+k ≤ n`) over a field large enough to host the spike (`⌊δ·n⌋+1 ≤ q`), the explicit
`t`-spike with `t = ⌊δ·n⌋+1` is admissible, giving

  `(⌊δ·n⌋+1)/q ≤ ε_mca(RS[F, domain, k], δ)`.

No `δ ≤ 1` hypothesis is needed: the admissibility hypothesis `hk` already forces `δ` small
enough that `⌊δ·n⌋ < n`. The spike-radius side condition `(1-δ)·n ≤ n - t + 1` holds because
`⌊δ·n⌋ ≤ δ·n` (`Nat.floor_le`). This is the linear lower-bound endpoint of `epsMCA_bracket`. -/
theorem epsMCA_ge_linear_floor (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hk : ⌊(δ : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ + 1 + k ≤ Fintype.card ι)
    (hq : ⌊(δ : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card F) :
    ((⌊(δ : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ := by
  set n := Fintype.card ι with hn
  set fl := ⌊(δ : ℝ≥0) * (n : ℝ≥0)⌋₊ with hfl
  have hfl_le_dn : (fl : ℝ≥0) ≤ (δ : ℝ≥0) * (n : ℝ≥0) := Nat.floor_le (by positivity)
  have hfl_le_n : fl ≤ n := by omega
  have hspike : ((1 - δ) * (n : ℝ≥0) : ℝ≥0) ≤ ((n - (fl + 1) + 1 : ℕ) : ℝ≥0) := by
    have hnat : n - (fl + 1) + 1 = n - fl := by omega
    rw [hnat]
    have hlhs : ((1 - δ) * (n : ℝ≥0)) = (n : ℝ≥0) - (δ : ℝ≥0) * (n : ℝ≥0) := by
      rw [tsub_mul, one_mul]
    rw [hlhs]
    have hsplit : (n : ℝ≥0) = ((n - fl : ℕ) : ℝ≥0) + (fl : ℝ≥0) := by
      rw [← Nat.cast_add]; congr 1; omega
    have hcast : ((n - fl : ℕ) : ℝ≥0) = (n : ℝ≥0) - (fl : ℝ≥0) := by
      rw [hsplit, add_tsub_cancel_right]
    rw [hcast]
    exact tsub_le_tsub_left hfl_le_dn _
  exact epsMCA_ge_spike (F := F) domain k (fl + 1) δ hk hq hspike

/-- **General-`δ` two-sided value bracket for the MCA error of an RS code.**

For every radius `δ` strictly below the plateau (`⌊δ·n⌋+1+k ≤ n`) over a field large enough to
host the spike (`⌊δ·n⌋+1 ≤ q`):

  `(⌊δ·n⌋+1)/q  ≤  ε_mca(RS[F, domain, k], δ)  ≤  C(n, max(⌈(1-δ)·n⌉, k+1))/q`.

The lower bound is the linear spike floor (`epsMCA_ge_linear_floor`); the upper bound is the
canonical-witness window count (`epsMCA_le_choose_div`). Both endpoints are unconditional and
axiom-clean. The exponential gap between them is exactly the open Johnson→capacity region of
the Grand MCA Challenge. -/
theorem epsMCA_bracket (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hk : ⌊(δ : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ + 1 + k ≤ Fintype.card ι)
    (hq : ⌊(δ : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card F) :
    ((⌊(δ : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ∧
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ≤
      ((Fintype.card ι).choose
          (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊) (k + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) :=
  ⟨epsMCA_ge_linear_floor domain k δ hk hq, epsMCA_le_choose_div domain k δ⟩

end ProximityGap

#print axioms ProximityGap.epsMCA_ge_linear_floor
#print axioms ProximityGap.epsMCA_bracket
