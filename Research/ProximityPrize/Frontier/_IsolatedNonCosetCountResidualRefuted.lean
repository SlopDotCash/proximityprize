/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._IsoSparsityMasonStothers

/-!
# `IsolatedNonCosetCountResidual` is false as stated

`IsolatedNonCosetCountResidual F k` quantifies over every `A O : F[X]` with
`natDegree < k` and every finite set `s ⊆ F` of roots of `A² − X·O²` at which `O ≠ 0`, and
asserts `s.card ≤ k + 1`. The set `s` is not required to lie in `μ_{n/2}`, and the formal
statement has no "not in a full sub-coset" hypothesis, so only the degree bound `deg P ≤ 2k − 1`
limits `s`, which is weaker than `k + 1` once `k ≥ 3`.

At `k = 3` over `ℚ`, take
`A = 15u² + 225u + 120` and `O = u² + 85u + 274`. Then `A(t²) = t·O(t²)` for `t = 1, …, 5`
(for instance `A(1) = O(1) = 360` and `A(4) = 1260 = 2·630 = 2·O(4)`), so
`P = A² − u·O²` vanishes at `u = 1, 4, 9, 16, 25` with `O ≠ 0` there. That is five isolated
roots against the claimed cap `k + 1 = 4`. The five roots are the whole root set of the
degree-5 polynomial `P`, so this is a genuine small instance, not a free-variable artefact.

This refutes the recorded statement only. The intended restriction to the halved subgroup
`μ_{n/2}` with sub-coset roots excluded, and the Kelley / BGK general-position count over `F_q`,
are not touched and remain open. It does not close #164.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ProximityGap.Frontier.IsoSparsityMasonStothers

/-- `A = 15u² + 225u + 120`. -/
def A₀ : ℚ[X] := C 15 * X ^ 2 + C 225 * X + C 120

/-- `O = u² + 85u + 274`. -/
def O₀ : ℚ[X] := X ^ 2 + C 85 * X + C 274

/-- The five isolated roots `1, 4, 9, 16, 25` of `A₀² − X · O₀²`, none a root of `O₀`. -/
theorem five_isolated_roots :
    ∀ x ∈ ({1, 4, 9, 16, 25} : Finset ℚ),
      (isoPoly A₀ O₀).IsRoot x ∧ O₀.eval x ≠ 0 := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    simp [isoPoly, A₀, O₀, IsRoot.def] <;> norm_num

/-- `IsolatedNonCosetCountResidual ℚ 3` is false: five isolated roots exceed the cap `4`. -/
theorem not_isolatedNonCosetCountResidual_rat_three :
    ¬ IsolatedNonCosetCountResidual ℚ 3 := by
  intro h
  have hA : A₀.natDegree < 3 := by
    unfold A₀; compute_degree!
  have hO : O₀.natDegree < 3 := by
    unfold O₀; compute_degree!
  have := h A₀ O₀ hA hO {1, 4, 9, 16, 25} five_isolated_roots
  norm_num at this

end ProximityGap.Frontier.IsoSparsityMasonStothers

open ProximityGap.Frontier.IsoSparsityMasonStothers in
#print axioms not_isolatedNonCosetCountResidual_rat_three
