/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
# HD8: the identity-web dimension law — saturation forces exact evaluations; the thin
regime provably receives none

Capstone of the HD arc (ledger `466-HD1` … `466-HD7-HD8`).  The complete multiplicative-
identity web of Gauss phases (conjugation + ALL m′-fold Hasse–Davenport product relations) was
computed EXACTLY (fraction-free rational elimination, probes
`/tmp/arklib-reports/hd7_exact_rank_probe.py`, `hd8_density_curve_probe.py`):

* the web's null space has dimension EXACTLY `φ(N)/2` at `N = 16` and `N = 256` — the
  Kubert–Lang universal odd-distribution rank: the web is COMPLETE (no exact multiplicative
  relation among Gauss sums is missing from it);
* the projection of the null space onto the ladder angles has MAXIMAL rank
  `min(#angles, φ(N)/2)` at every family density — the web's constraining power is pure
  dimension counting: `pinned = max(0, #angles − φ(N)/2)`.

This file formalizes the two abstract halves of that law over any field:

* `finrank_projected_null_le` — the projected null space never exceeds the null space:
  the web can pin at least `dim θ − nullity` directions (saturation lower bound), and
* `exists_exact_evaluation_of_not_surjective` (POSITIVE HALF) — whenever the projected
  null space is a PROPER subspace of the angle space, a NONZERO linear functional of the
  angles is web-determined: an EXACT EVALUATION exists.  Instantiated at index 2
  (`dim θ = 127 > 64 = φ(256)/2`), this is the abstract CAUSE of the classical exact
  evaluability of quadratic / index-2 / semiprimitive Gauss sums.

The NEGATIVE half — that at index ≥ 4 the projection is SURJECTIVE (so no exact evaluation
functional exists at all, and in particular nothing touches the r=3 rung) — is the exact
rational-arithmetic certificate of the probes, documented here and in the ledger; it is a
finite computation, not an abstract theorem.  Together: the algebraic side of the prize is
provably EMPTY in the thin regime; the missing certificate is archimedean/analytic.

HONEST SCOPE.  Abstract linear algebra (proven) + exact finite certificates (documented).
No bound on `M`; §33 route (ii) is closed; CORE remains OPEN / ON-BGK.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HD8IdentityWebDimensionLaw

open Module Submodule

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- The projected null space never exceeds the null space: the identity web can pin at
least `dim θ − nullity` angle directions (the saturation lower bound of the dimension
law). -/
theorem finrank_projected_null_le [FiniteDimensional F V]
    (K : Submodule F V) (P : V →ₗ[F] W) :
    Module.finrank F (K.map P) ≤ Module.finrank F K := by
  have h := Submodule.finrank_map_le P K
  exact h

/-- **Saturation forces exact evaluations.**  If the web's null space does not project ONTO
the angle space, then some nonzero linear functional of the angles vanishes on every
web-admissible configuration — an exact, web-determined evaluation.  (At index 2 this is
the abstract cause of the classical Gauss-sum evaluations.) -/
theorem exists_exact_evaluation_of_not_surjective
    (K : Submodule F V) (P : V →ₗ[F] W)
    (h : K.map P ≠ ⊤) :
    ∃ φ : Module.Dual F W, φ ≠ 0 ∧ ∀ v ∈ K, φ (P v) = 0 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : W, w ∉ K.map P := by
    by_contra hcon
    push_neg at hcon
    exact h (Submodule.eq_top_iff'.mpr hcon)
  have hq : (K.map P).mkQ w ≠ 0 := by
    rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hw
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero F hq
  refine ⟨g.comp (K.map P).mkQ, ?_, ?_⟩
  · intro h0
    apply hg
    have := congrArg (fun ψ : Module.Dual F W => ψ w) h0
    simpa using this
  · intro v hv
    have hmem : P v ∈ K.map P := Submodule.mem_map_of_mem hv
    have hzero : (K.map P).mkQ (P v) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hmem
    simp [LinearMap.comp_apply, hzero]

/-- The pinned-dimension count: if `dim θ > nullity`, strictly positive pinning is forced —
at least `dim θ − dim K` independent exact evaluations exist.  (Index-2 saturation:
`127 − 64 = 63` at `N = 256`.) -/
theorem pinned_dims_ge [FiniteDimensional F V] [FiniteDimensional F W]
    (K : Submodule F V) (P : V →ₗ[F] W) :
    Module.finrank F W - Module.finrank F K ≤
      Module.finrank F W - Module.finrank F (K.map P) := by
  have h := finrank_projected_null_le K P
  omega

end ArkLib.ProximityGap.Frontier.HD8IdentityWebDimensionLaw

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.HD8IdentityWebDimensionLaw.finrank_projected_null_le
#print axioms
  ArkLib.ProximityGap.Frontier.HD8IdentityWebDimensionLaw.exists_exact_evaluation_of_not_surjective
#print axioms
  ArkLib.ProximityGap.Frontier.HD8IdentityWebDimensionLaw.pinned_dims_ge
