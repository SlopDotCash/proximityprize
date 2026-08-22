/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15GaussDecompDiagonalSpike
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# LANE NSQRTP (#466 round 16): the FIRST unconditional theorem-level partial Problem B

Round 15 established (empirically + prose) that off the diagonal (`s₀ ∉ μ_n`) the signed
incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b)·ψ(b·s₀)` over a THICK index-`m` multiplicative
subgroup `H` satisfies the unconditional Gauss-sum bound `‖I_H(s₀)‖ ≤ n/m + n·√q·(m−1)/m ≤ n√q`
— beating the trivial `|H|·M` budget by `n^{3/2}/m` at prize scale.  This file makes that a
THEOREM, by gluing two in-tree bricks:

* `_R15GaussDecompDiagonalSpike.incidenceSum_eq_period_resummation`:
  `I_H(s₀) = ∑_{x∈G} η^H(s₀ − x)` (exact resummation; for `s₀ ∉ G` every shift `s₀ − x ≠ 0`);
* `ConstantIndexGaussSumBound.eta_constIndex_norm_le`:
  `‖η^{G_χ}(c)‖ ≤ ((m−1)√q + 1)/m` for every `c ≠ 0`, where `G_χ = {a : χ a = 1}` is the
  index-`m` subgroup cut out by a multiplicative character `χ` of order `m = orderOf χ ≥ 2`
  (classical Gauss sums, `‖g(χ^j, ψ_c)‖ = √q`).

Numerically verified FIRST (exact-shape probe `scratchpad/r16_probe.py`, kept at
`scripts/probes/probe_r16_unconditional_incidence.py`): identity + bound at
`(p,n,deg) = (41,8,2), (41,8,4), (97,8,2), (97,16,4), (113,16,2)`, including the edge cases
`s₀ = 0` (covered: `0 ∉ μ_n`) and `s₀ ∈ μ_n` (excluded: diagonal spike `≈ |H|`, structural —
see `_R15GaussDecompDiagonalSpike`).

Main results (all for `s₀ ∉ G`, arbitrary finite field `F`, `q = #F`, `n = |G|`):

* `incidence_offdiag_norm_le` — `‖I_{G_χ}(s₀)‖ ≤ n·((m−1)√q + 1)/m`
  (`= n/m + n·√q·(m−1)/m`, see `offdiag_bound_split`);
* `incidence_offdiag_norm_le_sqrt` — the headline `‖I_{G_χ}(s₀)‖ ≤ n·√q`;
* `orderOf_mul_card_Gchi` — `m·|G_χ| = q − 1`: `G_χ` IS the thick index-`m` subgroup;
* `exists_thick_subgroup_incidence_bound` — for every `d ≥ 2` with `d ∣ q − 1` there is a
  character of order `d`, hence a concrete index-`d` (thick, `|H| = (q−1)/d`) subgroup with the
  unconditional off-diagonal bound.

HONESTY: this does NOT touch corrected Problem B's `C·√|H|·M` target (that is `≈ n^{2.5}/√m`
at the prize while `n√q ≈ n³` there — a `√|H|/√q`-factor gap).  It is the unconditional
`n√q` PARTIAL bound: the first theorem-level nontrivial upper bound on the off-diagonal
incidence, strictly inside the trivial `|H|·M ≈ q·M/m` budget whenever `n·√q < |H|·M`.
The wall (square-root cancellation of the twisted thin sums `T_χ(s₀)`) is untouched.

Issue #466, lane NSQRTP (round 16).
-/

set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15GaussDecompDiagonalSpike

namespace ArkLib.ProximityGap.Frontier.R16UnconditionalIncidenceBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The unconditional off-diagonal incidence bound.**  For any evaluation set `G`, any
multiplicative character `χ` of order `m ≥ 2` cutting out the index-`m` subgroup
`G_χ = {a : χ a = 1}`, and any offset `s₀ ∉ G`:
`‖I_{G_χ}(s₀)‖ ≤ |G|·((m−1)√q + 1)/m`.  Resummation + per-shift Gauss-sum bound. -/
theorem incidence_offdiag_norm_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {χ : MulChar F ℂ} (hm : 2 ≤ orderOf χ) {s₀ : F} (hs₀ : s₀ ∉ G) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ)
        * (((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ)) := by
  rw [incidenceSum_eq_period_resummation ψ G (Gchi χ) s₀]
  refine le_trans (norm_sum_le G (fun x => eta ψ (Gchi χ) (s₀ - x))) ?_
  have hterm : ∀ x ∈ G, ‖eta ψ (Gchi χ) (s₀ - x)‖
      ≤ ((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ) := by
    intro x hx
    have hne : s₀ - x ≠ 0 := sub_ne_zero_of_ne (fun h => hs₀ (h ▸ hx))
    exact eta_constIndex_norm_le hψ hne hm
  calc ∑ x ∈ G, ‖eta ψ (Gchi χ) (s₀ - x)‖
      ≤ ∑ _x ∈ G,
          (((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (G.card : ℝ)
        * (((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The bound in the round-15 split form: `n·((m−1)√q + 1)/m = n/m + n·√q·(m−1)/m`. -/
theorem offdiag_bound_split {m : ℕ} (hm : 2 ≤ m) (n s : ℝ) :
    n * (((m - 1 : ℝ) * s + 1) / (m : ℝ)) = n / m + n * s * (m - 1) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- **Headline: `‖I_H(s₀ ∉ G)‖ ≤ n·√q` unconditionally** (any finite field, since `√q ≥ 1`). -/
theorem incidence_offdiag_norm_le_sqrt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {χ : MulChar F ℂ} (hm : 2 ≤ orderOf χ) {s₀ : F} (hs₀ : s₀ ∉ G) :
    ‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ (G.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
  refine le_trans (incidence_offdiag_norm_le hψ G hm hs₀) ?_
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Fintype.one_lt_card.le)
  have hmR : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  have hfrac : ((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ)
      ≤ Real.sqrt (Fintype.card F : ℝ) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (orderOf χ : ℝ))]
    nlinarith
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left hfrac hn

/-- `G_χ` is genuinely the THICK index-`m` subgroup: `m·|G_χ| = q − 1` (`m = orderOf χ`).
Double count `∑_a ∑_{j<m} (χ^j)(a)` both ways using `mulChar_pow_sum_all` and
`∑_a (χ^j)(a) = 0` for `χ^j ≠ 1`. -/
theorem orderOf_mul_card_Gchi {χ : MulChar F ℂ} (hm : 2 ≤ orderOf χ) :
    orderOf χ * (Gchi χ).card = Fintype.card F - 1 := by
  classical
  -- the double sum, way 1: rows are the indicator
  have hway1 : ∑ a : F, ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a
      = (orderOf χ : ℂ) * ((Gchi χ).card : ℂ) := by
    calc ∑ a : F, ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a
        = ∑ a : F, (if χ a = 1 then (orderOf χ : ℂ) else 0) :=
          Finset.sum_congr rfl (fun a _ => mulChar_pow_sum_all χ a)
      _ = ∑ a ∈ Gchi χ, (orderOf χ : ℂ) := by rw [Gchi, Finset.sum_filter]
      _ = (orderOf χ : ℂ) * ((Gchi χ).card : ℂ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- way 2: columns; only `j = 0` survives, contributing the number of units `q − 1`
  have hone : ∑ a : F, (1 : MulChar F ℂ) a = ((Fintype.card F - 1 : ℕ) : ℂ) := by
    have hval : ∀ a : F, (1 : MulChar F ℂ) a = 1 - (if a = 0 then 1 else 0) := by
      intro a
      rcases eq_or_ne a 0 with rfl | ha
      · rw [MulChar.map_nonunit (1 : MulChar F ℂ) not_isUnit_zero, if_pos rfl]; ring
      · rw [MulChar.one_apply ha.isUnit, if_neg ha]; ring
    rw [Finset.sum_congr rfl (fun a _ => hval a), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.sum_ite_eq' Finset.univ (0 : F) (fun _ => (1 : ℂ)),
      if_pos (Finset.mem_univ (0 : F)), Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hway2 : ∑ a : F, ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a
      = ((Fintype.card F - 1 : ℕ) : ℂ) := by
    rw [Finset.sum_comm]
    have hcols : ∀ j ∈ Finset.range (orderOf χ),
        ∑ a : F, (χ ^ j) a
          = if j = 0 then ((Fintype.card F - 1 : ℕ) : ℂ) else 0 := by
      intro j hj
      rcases eq_or_ne j 0 with rfl | hj0
      · rw [if_pos rfl, ← hone]
        exact Finset.sum_congr rfl (fun a _ => by rw [pow_zero])
      · rw [if_neg hj0]
        exact (χ ^ j).sum_eq_zero_of_ne_one
          (pow_ne_one_of_lt_orderOf hj0 (Finset.mem_range.mp hj))
    rw [Finset.sum_congr rfl hcols,
      Finset.sum_ite_eq' (Finset.range (orderOf χ)) 0
        (fun _ => ((Fintype.card F - 1 : ℕ) : ℂ))]
    exact if_pos (Finset.mem_range.mpr (by omega))
  -- compare and descend to ℕ
  have hC : ((orderOf χ : ℂ)) * (((Gchi χ).card : ℕ) : ℂ) = ((Fintype.card F - 1 : ℕ) : ℂ) := by
    rw [← hway1, hway2]
  exact_mod_cast hC

/-- **Existence form.**  For every `d ≥ 2` dividing `q − 1` there is a multiplicative character
of order `d`, hence a concrete THICK index-`d` subgroup `G_χ` (`|G_χ| = (q−1)/d`) for which the
off-diagonal incidence bound `‖I(s₀ ∉ G)‖ ≤ n·((d−1)√q + 1)/d ≤ n√q` holds unconditionally. -/
theorem exists_thick_subgroup_incidence_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {d : ℕ} (hd : 2 ≤ d) (hdvd : d ∣ Fintype.card F - 1) :
    ∃ χ : MulChar F ℂ, orderOf χ = d ∧ d * (Gchi χ).card = Fintype.card F - 1 ∧
      ∀ s₀ : F, s₀ ∉ G →
        ‖incidenceSum ψ G (Gchi χ) s₀‖
          ≤ (G.card : ℝ) * (((d - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (d : ℝ)) := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf F hdvd
    (Complex.isPrimitiveRoot_exp d (by omega))
  refine ⟨χ, hχ, ?_, ?_⟩
  · rw [← hχ]; exact orderOf_mul_card_Gchi (hχ ▸ hd)
  · intro s₀ hs₀
    have h := incidence_offdiag_norm_le hψ G (hχ ▸ hd) hs₀
    rwa [hχ] at h

#print axioms incidence_offdiag_norm_le
#print axioms incidence_offdiag_norm_le_sqrt
#print axioms orderOf_mul_card_Gchi
#print axioms exists_thick_subgroup_incidence_bound

end ArkLib.ProximityGap.Frontier.R16UnconditionalIncidenceBound
