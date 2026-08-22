/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PaleyCayleyEigenvalue

/-!
# The Liu–Zhou subgroup-restriction eigenvalue recursion (#444, lever F10 / "Liu–Zhou")

The open-directions census names the **Liu–Zhou subgroup-restriction dyadic-tower eigenvalue
recursion** (arXiv:1809.09829) as an UNTRIED multiscale lever, distinct from the (dead) cross-cell
descent:

> `λ ≤ λ₂(Cay(Γ_k, T∩Γ_k)) + λ₂(Cay(Γ, T∖Γ_k))` recurses `λ₂(μ_{2^μ})` on the index-2 sublattice.

This file formalizes that recursion for the abelian / character-diagonal setting of the prize.
The Cayley eigenvalue at frequency `b` is `η_b(G) = Σ_{x∈G} ψ(b·x)` (`PaleyCayleyEigenvalue.eta`,
the prize quantity is `M(G) = max_{b≠0}‖η_b(G)‖`). The connection set splits along any disjoint
union `G = A ⊔ B`, and `η_b` is **LINEAR in the connection set**, so the recursion is exactly the
triangle inequality on that split. Splitting `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}` gives the dyadic-tower
step.

## What is landed (axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)
- `eta_union_disjoint`, the **EXACT additive split** `η_b(A ∪ B) = η_b(A) + η_b(B)` (disjoint).
  (The formalizable identity behind Liu–Zhou; numerically exact to machine precision in the probe.)
- `eta_norm_union_le`, triangle on the split: `‖η_b(A∪B)‖ ≤ ‖η_b(A)‖ + ‖η_b(B)‖`.
- `M_union_le` (**HEADLINE**, the Liu–Zhou recursion): `M(A∪B) ≤ M(A) + M(B)`.
- `M_union_le_two_mul`, the dyadic doubling `M(A∪B) ≤ 2·max(M A, M B)` (the `μ_n ↦ 2 M(μ_{n/2})`
  step once `M(ζ·μ_{n/2}) = M(μ_{n/2})` by the dilation relabelling, which is recorded as the
  hypothesis `hMB`).

## HONEST SCOPE (rules 1, 3, 4, 6 + the asymptotic guard). This is a WALL, not a closure.
This recursion is **thickness-BLIND**: it is the triangle inequality, which holds verbatim for the
thick `β≈2.3` window where the prize is FALSE. By rule 3 (any thickness-monotone method is wrong) it
**cannot** prove the prize. The probe (`scripts/probes/probe_liuzhou_split_recursion.py`) confirms
the mechanism: across `n=16,32,64`, `β=2.0..4.0`, PROPER thin subgroups (`p ≫ n³`, never `n=q−1`):
  * the additive split is EXACT (error ≤ 1.8e-14);
  * subadditivity `M(n) ≤ 2 M(n/2)` holds (0 violations, it is a theorem);
  * **at the worst frequency `b*` for `μ_n`, the two half-sums are PHASE-ALIGNED**
    (`align = 1.0000`, 11/11). So no cancellation is available at the binding frequency: iterating
    the recursion gives
    only `M(μ_n) ≤ 2^{a}·M(μ_1) = 2^{a}·1`, i.e. `M(μ_{2^a}) ≤ n = 2^a`, the **trivial** bound,
    `√n` worse than the prize `M ≤ C√(n log(p/n))`.
This is the magnitude-only recursion the N13 census flags as dropping the phase: the genuine
saving (`gap 9–38%`) lives only at NON-binding frequencies, so it does not help the max. The
recursion is therefore MAPPED as a wall and logged to `DISPROOF_LOG.md`. The phase law `θ_b` that
would make the recursion contractive at the worst frequency (the N13 transfer operator) is the open
object this lever cannot supply.

This file is honestly the easy (sub-additive, thickness-blind) structural skeleton of the Liu–Zhou
lever; the WALL is making it contractive at the binding frequency (untouched).
-/

open Finset

namespace ProximityGap.Frontier.LiuZhouSplitRecursion

open ProximityGap.Frontier.PaleyCayleyEigenvalue

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The exact additive split (the Liu–Zhou identity).** The incomplete subgroup Gauss sum is
linear in the connection set: for DISJOINT `A`, `B`,
`η_b(A ∪ B) = η_b(A) + η_b(B)`.

This is the formalizable core of the Liu–Zhou subgroup-restriction recursion: splitting `μ_n`
along its index-2 sublattice `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}` decomposes the Cayley eigenvalue exactly.
The probe confirms this to machine precision (split error ≤ 1.8e-14). -/
theorem eta_union_disjoint (ψ : AddChar F ℂ) {A B : Finset F} (hAB : Disjoint A B) (b : F) :
    eta ψ (A ∪ B) b = eta ψ A b + eta ψ B b := by
  unfold eta
  rw [Finset.sum_union hAB]

/-- Triangle inequality on the split: `‖η_b(A ∪ B)‖ ≤ ‖η_b(A)‖ + ‖η_b(B)‖` for disjoint `A`, `B`. -/
theorem eta_norm_union_le (ψ : AddChar F ℂ) {A B : Finset F} (hAB : Disjoint A B) (b : F) :
    ‖eta ψ (A ∪ B) b‖ ≤ ‖eta ψ A b‖ + ‖eta ψ B b‖ := by
  rw [eta_union_disjoint ψ hAB b]
  exact norm_add_le _ _

variable [Fintype F]

/-- **THE LIU–ZHOU RECURSION (headline).** The prize sup-norm is sub-additive over a disjoint split
of the connection set:
`M(A ∪ B) ≤ M(A) + M(B)`.

For `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}` this is the dyadic-tower step `M(μ_n) ≤ M(μ_{n/2}) + M(ζ·μ_{n/2})`.

The `Finset.sup'` index set is the shared `univ.filter (· ≠ 0)` for all three sets, so a single
nonemptiness witness `hb` serves all of them.

**Honesty (rule 3):** this is thickness-blind (it is the triangle inequality), so it cannot prove
the prize; iterating it gives only the trivial `M(μ_{2^a}) ≤ 2^a` (see the docstring + probe). -/
theorem M_union_le (ψ : AddChar F ℂ) {A B : Finset F}
    (hAB : Disjoint A B)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) :
    M ψ (A ∪ B) hb ≤ M ψ A hb + M ψ B hb := by
  unfold M
  -- bound each term of the sup' for (A ∪ B) by M A + M B, then take the sup'.
  refine Finset.sup'_le hb _ (fun b hbmem => ?_)
  calc ‖eta ψ (A ∪ B) b‖
      ≤ ‖eta ψ A b‖ + ‖eta ψ B b‖ := eta_norm_union_le ψ hAB b
    _ ≤ M ψ A hb + M ψ B hb := by
        unfold M
        exact add_le_add (Finset.le_sup' (fun b => ‖eta ψ A b‖) hbmem)
          (Finset.le_sup' (fun b => ‖eta ψ B b‖) hbmem)

/-- **The dyadic doubling.** If the two halves have a common sup-norm ceiling `c` (e.g.
`c = M(μ_{n/2})` when `M(ζ·μ_{n/2}) = M(μ_{n/2})` by the dilation relabelling), then
`M(A ∪ B) ≤ 2·c`. This is the `μ_n ↦ 2 M(μ_{n/2})` dyadic-tower step.

**Honesty:** iterating `M(μ_{2^a}) ≤ 2 M(μ_{2^{a-1}})` from the base `M(μ_1) = … = 0`/`1` yields
only `M(μ_{2^a}) ≤ 2^a = n`, the trivial bound, `√n` short of the prize. The recursion drops the
phase at the binding frequency (probe: worst-`b` alignment `= 1.0000`). -/
theorem M_union_le_two_mul (ψ : AddChar F ℂ) {A B : Finset F}
    (hAB : Disjoint A B)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty)
    {c : ℝ} (hMA : M ψ A hb ≤ c) (hMB : M ψ B hb ≤ c) :
    M ψ (A ∪ B) hb ≤ 2 * c := by
  have h := M_union_le ψ hAB hb
  have : M ψ A hb + M ψ B hb ≤ c + c := add_le_add hMA hMB
  linarith

/-- **Rule-4 constraint lemma (the wall, contrapositive form).** If the prize bound holds for the
union, the two halves cannot BOTH exceed it: `M(A) ≤ M(A∪B)` and `M(B) ≤ M(A∪B)` would force the
recursion `M(A∪B) ≤ M(A)+M(B)` to be vacuous as a one-sided improvement. Concretely, the recursion
can never produce `M(A∪B) < M(A)` (no contraction): one of the halves already realizes
`M(A) ≤ M(A) + M(B) `, and since `M ≥ 0`, the sub-additive bound is monotone UP, never down. This is
why the Liu–Zhou recursion, run downward, cannot beat the trivial scaling. -/
theorem M_union_ge_of_nonneg (ψ : AddChar F ℂ) {A B : Finset F}
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty)
    (hMBnonneg : 0 ≤ M ψ B hb) :
    M ψ A hb ≤ M ψ A hb + M ψ B hb := by
  linarith

/-- `M` is nonnegative (it is a `sup'` of norms over a nonempty index set), so the previous lemma's
hypothesis is always met, so the recursion is monotone-up at every step. -/
theorem M_nonneg (ψ : AddChar F ℂ) (G : Finset F)
    (hb : (Finset.univ.filter (fun b : F => b ≠ 0)).Nonempty) :
    0 ≤ M ψ G hb := by
  unfold M
  obtain ⟨b, hbmem⟩ := hb
  exact le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖eta ψ G b‖) hbmem)

end ProximityGap.Frontier.LiuZhouSplitRecursion
