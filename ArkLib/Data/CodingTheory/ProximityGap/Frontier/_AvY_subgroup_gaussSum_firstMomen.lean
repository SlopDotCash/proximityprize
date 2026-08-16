/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.Ring

set_option linter.style.longLine false

/-!
# Frontier (#444) — the subgroup Gauss-sum FIRST MOMENT, exactly, with NO Weil input.

Companion to `SubgroupGaussSumSecondMoment.lean`. The subgroup Gauss period at frequency `b` is
`η_b := ∑_{y∈G} ψ(b·y)`. The first moment over all frequencies is exact:

> `subgroup_gaussSum_firstMoment_eq_zero`:  if `0 ∉ G` then `∑_{b∈F} η_b = 0`.
> `subgroup_gaussSum_firstMoment`:  in general `∑_{b∈F} η_b = q·𝟙[0∈G]`.

Proof object: pure additive-character orthogonality (`AddChar.sum_mulShift`), no Weil, no open input.
Swap order of summation: `∑_b ∑_{y∈G} ψ(b·y) = ∑_{y∈G} ∑_b ψ(b·y)`; the inner sum is `q·[y=0]` by
orthogonality, so only a `y = 0` term survives.

This completes the moment ladder (1st, 2nd, 4th, 2r all exact) and discharges the implicit
"mean of `η_b` is `0`" / DC-isolation hypothesis: the nonzero spectrum is mean-zero, the only
nonvanishing first-order mass sits at `b = 0` (`η_0 = |G|`). Combined with the second moment it
gives the exact mean-zero variance picture: when `0 ∉ G`, `∑_{b≠0} η_b = -|G|·𝟙[…] = 0` and
`∑_{b≠0} ‖η_b‖² = q·|G| - |G|²`.

For `G = nthRootsFinset n 1` (the `2^μ`-th roots of unity), `0 ∉ G` is the standard
"roots of unity are units" fact (`nthRootsFinset` consists of `IsUnit` elements, hence nonzero).
-/

open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumFirstMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The subgroup Gauss sum at frequency `b`: `η_b = ∑_{y∈G} ψ(b·y)`. -/
noncomputable def eta (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℂ := ∑ y ∈ G, ψ (b * y)

/-- **First moment, general form: `∑_b η_b = q·𝟙[0∈G]`.** Pure additive-character orthogonality.
Swap the order of summation and apply `AddChar.sum_mulShift y`, which evaluates `∑_b ψ(b·y)` to
`q·[y = 0]`; only the `y = 0` term (present iff `0 ∈ G`) survives. -/
theorem subgroup_gaussSum_firstMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, eta ψ G b = if (0 : F) ∈ G then (Fintype.card F : ℂ) else 0 := by
  calc ∑ b : F, eta ψ G b
      = ∑ y ∈ G, ∑ b : F, ψ (b * y) := by
        simp only [eta]; rw [Finset.sum_comm]
    _ = ∑ y ∈ G, (if y = 0 then (Fintype.card F : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have h := AddChar.sum_mulShift (R := F) (R' := ℂ) y hψ
        simp only [mul_comm y] at h
        rw [h]; split_ifs <;> push_cast <;> ring
    _ = if (0 : F) ∈ G then (Fintype.card F : ℂ) else 0 := by
        rw [Finset.sum_ite_eq' G (0 : F) (fun _ => (Fintype.card F : ℂ))]

/-- **First moment with `0 ∉ G`: `∑_b η_b = 0`.** Every `y ∈ G` is nonzero, so each inner
orthogonality sum `∑_b ψ(b·y)` vanishes. The DC-isolation / mean-zero spectrum identity. -/
theorem subgroup_gaussSum_firstMoment_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : (0 : F) ∉ G) :
    ∑ b : F, eta ψ G b = 0 := by
  rw [subgroup_gaussSum_firstMoment hψ G, if_neg hG]

omit [Fintype F] [DecidableEq F] in
/-- For the prize subgroup `G = nthRootsFinset n 1` with `0 < n`, the hypothesis `0 ∉ G` holds:
roots of unity are units, hence nonzero. This discharges the side condition for the `2^μ`-th roots. -/
theorem zero_notMem_nthRootsFinset {n : ℕ} (hn : 0 < n) :
    (0 : F) ∉ Polynomial.nthRootsFinset n (1 : F) := by
  intro h
  rw [Polynomial.mem_nthRootsFinset hn] at h
  -- h : (0 : F) ^ n = 1
  rw [zero_pow hn.ne'] at h
  exact zero_ne_one h

/-- **First moment over the `2^μ`-th roots of unity vanishes: `∑_b η_b = 0`.** Specialization of
`subgroup_gaussSum_firstMoment_eq_zero` to `G = nthRootsFinset n 1`, the prize subgroup `μ_n`. -/
theorem nthRoots_gaussSum_firstMoment_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {n : ℕ} (hn : 0 < n) :
    ∑ b : F, eta ψ (Polynomial.nthRootsFinset n (1 : F)) b = 0 :=
  subgroup_gaussSum_firstMoment_eq_zero hψ _ (zero_notMem_nthRootsFinset hn)

end ArkLib.ProximityGap.SubgroupGaussSumFirstMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFirstMoment.subgroup_gaussSum_firstMoment
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFirstMoment.subgroup_gaussSum_firstMoment_eq_zero
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFirstMoment.zero_notMem_nthRootsFinset
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFirstMoment.nthRoots_gaussSum_firstMoment_eq_zero
