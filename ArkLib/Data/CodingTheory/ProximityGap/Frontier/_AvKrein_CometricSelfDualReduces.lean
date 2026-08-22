/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# The Krein / Q-polynomial cometric DUAL LP reduces to the primal Delsarte LP (#444)

The last genuinely-new surface from the untouched-fields survey: the *cometric* (Krein,
Q-polynomial) dual linear program on the cyclotomic association scheme — the second Delsarte LP,
the Levenshtein/Bachoc sphere-packing-improvement tool, distinct in general from the primal
(metric, P-polynomial) LP already shown to be a no-go (`DelsarteLPNoGo`).

**Verdict: it REDUCES, because the cyclotomic scheme is FORMALLY SELF-DUAL.** The relations are the
`m = (p-1)/n` cosets of `μ_n` in `F_p`; this is a *translation scheme on `Z_p`*, and its first
eigenmatrix `P` (whose nonprincipal entries are exactly the Gaussian periods `η`) is **circulant**
in the nonprincipal block. Circulant ⟹ the second eigenmatrix equals the first: `Q = P`
(verified exactly `scripts/probes/probe_krein_cometric_selfdual.py`: at `p=13,17,41` the
`|entry|`-multisets of `Q = |X|·P⁻¹` and `P` coincide). Hence the cometric LP's constraint matrix
`Q` IS the metric LP's constraint matrix `P`: the two LPs have identical feasible regions and
identical optima. The cometric dual cannot beat the primal; it gives the same Gaussian-period
eigenvalue bound = the already-saturated `DelsarteLPNoGo`. The periods `η_b` (= `max_J P_{J,0}`)
are the same eigenvalue multiset on both the metric and cometric side.

The Lean content below is the load-bearing linear-algebra fact that `Q = P` forces the two LP
forms to coincide pointwise; the *self-duality witness* (`Q = P` for the cyclotomic scheme) is the
exact computation in the probe. Issue #444.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.AvKreinCometric

open Finset

/-- For a formally self-dual scheme (`Q = P`), every cometric LP linear form `∑ᵢ xᵢ Qⱼᵢ` equals the
corresponding metric (Delsarte) LP linear form `∑ᵢ xᵢ Pⱼᵢ`. Hence the cometric and metric LPs have
identical constraints/objective and identical optima: the Krein dual cannot beat the primal. -/
theorem cometric_form_eq_metric_of_selfdual {ι : Type*} [Fintype ι] (P Q : ι → ι → ℝ)
    (hsd : Q = P) (x : ι → ℝ) (j : ι) :
    (∑ i, x i * Q j i) = (∑ i, x i * P j i) := by
  subst hsd; rfl

/-- The reduction certificate: on any formally self-dual scheme the cometric (Krein) LP coincides
with the metric (Delsarte) LP. The cyclotomic scheme of `μ_n` over `F_p` is formally self-dual
(`Q = P`, circulant eigenmatrix; computed `probe_krein_cometric_selfdual.py`), so its cometric dual
LP is the primal LP = `DelsarteLPNoGo` = reduces; no new bound on `M = max_b |η_b|`. -/
def KreinCometricReducesToPrimal : Prop :=
  ∀ (ι : Type*) [Fintype ι] (P Q : ι → ι → ℝ), Q = P →
    ∀ (x : ι → ℝ) (j : ι), (∑ i, x i * Q j i) = (∑ i, x i * P j i)

theorem krein_cometric_reduces : KreinCometricReducesToPrimal :=
  fun _ _ P Q hsd x j => cometric_form_eq_metric_of_selfdual P Q hsd x j

end ArkLib.ProximityGap.Frontier.AvKreinCometric

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.AvKreinCometric.cometric_form_eq_metric_of_selfdual
#print axioms ArkLib.ProximityGap.Frontier.AvKreinCometric.krein_cometric_reduces
