/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# G80D: Bourgain–Demeter decoupling cannot fire on the dyadic coset tower — the caps are
dilates, the bilinear step collapses, and the decoupling gain IS the decorrelation atom

The last heavy modern engine unwalked by name: `l²`-decoupling / induction on scales
(Bourgain–Demeter–Guth).  Its shape fits the prize perfectly — square-root cancellation in
`L^{2r}` norms of exponential sums with only `C^ε`-class losses (the tolerable class, cf.
G78) — so an honest map of WHY it cannot fire is owed.

**Setup.**  The dyadic tower decomposes `μ_n = μ_{n/2} ∪ g·μ_{n/2}` and hence
`η_b^{(n)} = η_b^{(n/2)} + η_{bg}^{(n/2)}` (in-tree: `_Attack01DyadicButterfly.eta_split_of_
disjoint_coset`).  Decoupling would treat the two halves as "caps" and gain from their
transversality in the bilinear step.  But the two caps are exact MULTIPLICATIVE DILATES of
one another: the second piece, as a function of `b`, is `f(b·g)` where `f = η^{(n/2)}`.
There is no curvature/transversality input available — algebraically the caps are parallel.

**What this file proves (axiom-clean, general finite field / weight function).**

* `sum_comp_mulRight` — dilation invariance of frequency sums: `Σ_b Φ(b·u) = Σ_b Φ(b)` for
  any unit `u`.  Every mixed norm the induction could form is a LAG CORRELATION.
* `bilinear_lag_le_energy` — the bilinear object collapses to the linear energy with NO
  decoupling gain: `Σ_b |A(b)·A(bu)| ≤ Σ_b A(b)²`, every lag `u`.
* `decoupling_defect_identity` (HEADLINE) — the EXACT defect:
  `Σ_b A(b)² − Σ_b A(b)·A(bu) = ½·Σ_b (A(b) − A(bu))²`.
  The decoupling gain over the trivial bound at lag `u` is IDENTICALLY the lag-`u`
  decorrelation mass of the magnitude field.

**Verdict.**  For the Gauss-period magnitude field `A(b) = |η_b^{(n/2)}|`, a decoupling
constant beating trivial ⟺ a positive lower bound on `Σ_b (A(b) − A(bg))²` — certifying
decorrelation of the coset magnitude field at multiplicative lag `g`.  That is verbatim the
measured-but-uncertified INDEPENDENCE form of the core (dossier §2.4: the `{log|η_b|}` field
is measured independent-Gaussian; the prize is certifying it).  Decoupling does not bypass
the atom; its induction-on-scales gain is a linear-algebra gauge of the atom.  Combined with
the loss-class result (G78) this completes the pattern: BOTH modern constant-loss engines
(KM sifting, BD decoupling) fail at exactly the same point — not strength, but a circular
hypothesis: some non-Fourier certificate of decorrelation/anti-concentration for the
geometric-progression structure.

HONEST SCOPE.  Precise ROUTE map with exact identities; NOT a closure; does not exclude a
future non-`l²`, non-bilinear decoupling scheme (none is known even in the archimedean
literature for parallel caps).  CORE remains OPEN / ON-BGK.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G80DDecouplingParallelCapCollapse

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Dilation invariance of frequency sums.**  Multiplicative relabeling by a unit is a
bijection of the frequency space: every mixed norm of the two dyadic caps is a lag
correlation of ONE cap. -/
theorem sum_comp_mulRight (u : Fˣ) (Φ : F → ℝ) :
    ∑ b : F, Φ (b * (u : F)) = ∑ b : F, Φ b := by
  classical
  exact Fintype.sum_equiv (Equiv.mulRight₀ (u : F) u.ne_zero) _ _ (fun b => rfl)

/-- **The bilinear step collapses.**  For every multiplicative lag, the bilinear decoupling
object is dominated by the LINEAR energy — no transversality gain exists for dilate-caps. -/
theorem bilinear_lag_le_energy (u : Fˣ) (A : F → ℝ) :
    ∑ b : F, |A b * A (b * (u : F))| ≤ ∑ b : F, (A b) ^ 2 := by
  classical
  have hterm : ∀ b : F,
      |A b * A (b * (u : F))| ≤ ((A b) ^ 2 + (A (b * (u : F))) ^ 2) / 2 := by
    intro b
    rw [abs_mul]
    nlinarith [sq_nonneg (|A b| - |A (b * (u : F))|), sq_abs (A b),
      sq_abs (A (b * (u : F))), abs_nonneg (A b), abs_nonneg (A (b * (u : F)))]
  refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
  have hsplit : ∑ b : F, ((A b) ^ 2 + (A (b * (u : F))) ^ 2) / 2 =
      (∑ b : F, (A b) ^ 2) / 2 + (∑ b : F, (A (b * (u : F))) ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, add_div]
  rw [hsplit, sum_comp_mulRight u (fun b => (A b) ^ 2)]
  ring_nf
  exact le_refl _

/-- **HEADLINE: the exact decoupling defect.**  The gain of the bilinear step over the
trivial bound at lag `u` is IDENTICALLY the lag-`u` decorrelation mass of the field:
`Σ A² − Σ A(b)A(bu) = ½ Σ (A(b) − A(bu))²`.  Any decoupling improvement is verbatim a
decorrelation certificate — the independence atom. -/
theorem decoupling_defect_identity (u : Fˣ) (A : F → ℝ) :
    (∑ b : F, (A b) ^ 2) - ∑ b : F, A b * A (b * (u : F)) =
      (∑ b : F, (A b - A (b * (u : F))) ^ 2) / 2 := by
  classical
  have hexpand : ∑ b : F, (A b - A (b * (u : F))) ^ 2 =
      (∑ b : F, (A b) ^ 2) + (∑ b : F, (A (b * (u : F))) ^ 2) -
        2 * ∑ b : F, A b * A (b * (u : F)) := by
    have hpt : ∀ b : F, (A b - A (b * (u : F))) ^ 2 =
        (A b) ^ 2 + (A (b * (u : F))) ^ 2 - 2 * (A b * A (b * (u : F))) := by
      intro b; ring
    rw [Finset.sum_congr rfl fun b _ => hpt b]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexpand, sum_comp_mulRight u (fun b => (A b) ^ 2)]
  ring

end ArkLib.ProximityGap.Frontier.G80DDecouplingParallelCapCollapse

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80DDecouplingParallelCapCollapse.sum_comp_mulRight
#print axioms
  ArkLib.ProximityGap.Frontier.G80DDecouplingParallelCapCollapse.bilinear_lag_le_energy
#print axioms
  ArkLib.ProximityGap.Frontier.G80DDecouplingParallelCapCollapse.decoupling_defect_identity
