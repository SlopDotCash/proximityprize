/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17QuadrupleWeilRung
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18FourthMomentTwist
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18SigmaGate

/-!
# LANE HSIG (#466 round 18): `hSig` discharged — Σ-equidistribution across index-`m` subgroups

Round 17's r = 2 rung (`_R17QuadrupleWeilRung.r2Rung_of_weil` and its consumers) carries the
probe-only input

  `hSig : n·q ≤ 2m·Σ`,  `Σ = ∑_{b∈H} ‖η_b‖²`,

i.e. the index-`m` subgroup `H` carries at least HALF its fair share `n(q−n)/m ≈ nq/m` of the
Parseval mass `∑_{b≠0}‖η_b‖² = n(q−n)`.  This file PROVES it, unconditionally, in a regime
strictly weaker than the round-17 Weil regime.

**The identity** (probe `scratchpad/probe_r18_sigma.py`, exact to 1e-9 at
p = 97…786433, n = 8/16/32, m = 2/4/8): for `χ` of order `m` cutting out
`H = G_χ = {b : χ(b) = 1}`,

  `m·Σ = (n·q − n²) + ∑_{j=1}^{m−1} A_j`,   `A_j = ∑_{b} χ^j(b)·‖η_b‖²`,

by the indicator decomposition `∑_{j<m} χ^j(b) = m·1_{H}(b)` (in-tree
`mulChar_pow_sum_all`).  Each twisted moment expands as
`A_j = ∑_{x≠y∈G} gaussSum(χ^j, ψ_{x−y})` — the diagonal dies because
`gaussSum(χ^j, 1) = ∑_b χ^j(b) = 0` — so `|A_j| ≤ n(n−1)√q` by
`norm_gaussSum_eq_sqrt`.  (No structure of `G` beyond `|G| = n` is used: this holds for EVERY
`G ⊆ F`, not just `μ_n`.  The probe shows the triangle bound can be SATURATED —
`max_j |A_j|/n(n−1)√q = 1.000` at the Fermat cell p = 65537, m = 8 — so the constant is
sharp, but in-regime the bound has a factor-2 room regardless.)

**The regime**: `q ≥ 16·m²·n²` (identical to the round-17 Weil-regime component
`q ≥ 16·n²·m²`; the true need is only `q ≳ 4m²n²`).  Then

  `m·Σ ≥ n·q − n² − (m−1)·n·(n−1)·√q ≥ n·q/2`.

**Consumer payoff** (`wickAwayAtWithConstant_two_of_gchi`): for `H = G_χ` the round-17 rung
now needs only THREE named inputs (`ChiDecompositionOff`, `GaussSumSizeBound`,
`FourthMomentTwistBound`) — `hSig`, the only probe-only one, is discharged.

No closure claimed: this is plumbing on the ceiling side of the r = 2 rung; the open core
(depth ~ln p moments / Paley) is untouched.  Issue #466, round 18, LANE HSIG.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.ConstantIndexGaussSum

namespace ArkLib.ProximityGap.Frontier.R18SigmaEquidistribution

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (1) The twisted second moment and its Gauss-sum expansion -/

/-- The `χ`-twisted second moment `A_χ = ∑_b χ(b)·η_b·conj(η_b)` expands exactly into
off-diagonal Gauss sums: `A_χ = ∑_{x,y∈G} gaussSum(χ, ψ_{x−y})` (the diagonal terms are
`gaussSum(χ, 1) = 0` for `χ ≠ 1`). -/
theorem twisted_secondMoment_eq_gaussSums (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F) :
    ∑ b : F, χ b * (eta ψ G b * conj' (eta ψ G b))
      = ∑ x ∈ G, ∑ y ∈ G, gaussSum χ (AddChar.mulShift ψ (x - y)) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, conj' (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  calc ∑ b : F, χ b * (eta ψ G b * conj' (eta ψ G b))
      = ∑ b : F, ∑ x ∈ G, ∑ y ∈ G, χ b * ψ (b * (x - y)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hconjeta : conj' (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
          rw [eta, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj (b * y))
        rw [hconjeta, eta, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have harg : b * x + -(b * y) = b * (x - y) := by ring
        rw [← AddChar.map_add_eq_mul, harg]
    _ = ∑ x ∈ G, ∑ y ∈ G, ∑ b : F, χ b * ψ (b * (x - y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ x ∈ G, ∑ y ∈ G, gaussSum χ (AddChar.mulShift ψ (x - y)) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [gaussSum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [AddChar.mulShift_apply, mul_comm (x - y) b]

/-- **Triangle bound on the twisted second moment**: for nontrivial `χ` and primitive `ψ`,
`‖∑_b χ(b)·‖η_b‖²‖ ≤ n(n−1)·√q` — only the `n(n−1)` off-diagonal pairs contribute, each a
Gauss sum of magnitude exactly `√q`. -/
theorem norm_twisted_secondMoment_le {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) :
    ‖∑ b : F, χ b * (eta ψ G b * conj' (eta ψ G b))‖
      ≤ (G.card : ℝ) * ((G.card : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
  classical
  rw [twisted_secondMoment_eq_gaussSums χ ψ G]
  have hterm : ∀ x ∈ G, ∀ y ∈ G,
      ‖gaussSum χ (AddChar.mulShift ψ (x - y))‖
        = if x = y then 0 else Real.sqrt (Fintype.card F : ℝ) := by
    intro x _ y _
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, sub_self, AddChar.mulShift_zero]
      have h0 : gaussSum χ (1 : AddChar F ℂ) = 0 := by
        rw [gaussSum]
        have h1 : ∀ b : F, χ b * (1 : AddChar F ℂ) b = χ b := by
          intro b; rw [AddChar.one_apply, mul_one]
        rw [Finset.sum_congr rfl (fun b _ => h1 b)]
        exact MulChar.sum_eq_zero_of_ne_one hχ
      rw [h0, norm_zero]
    · rw [if_neg hxy]
      exact norm_gaussSum_eq_sqrt hχ (mulShift_isPrimitive hψ (sub_ne_zero_of_ne hxy))
  have hle : ‖∑ x ∈ G, ∑ y ∈ G, gaussSum χ (AddChar.mulShift ψ (x - y))‖
      ≤ ∑ x ∈ G, ∑ y ∈ G, ‖gaussSum χ (AddChar.mulShift ψ (x - y))‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => norm_sum_le _ _))
  refine hle.trans ?_
  have hinner : ∀ x ∈ G, ∑ y ∈ G, ‖gaussSum χ (AddChar.mulShift ψ (x - y))‖
      = ((G.card : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
    intro x hx
    rw [Finset.sum_congr rfl (fun y hy => hterm x hx y hy)]
    rw [← Finset.add_sum_erase G _ hx, if_pos rfl, zero_add]
    have hstep : ∀ y ∈ G.erase x,
        (if x = y then (0 : ℝ) else Real.sqrt (Fintype.card F : ℝ))
          = Real.sqrt (Fintype.card F : ℝ) :=
      fun y hy => if_neg (fun h => (Finset.ne_of_mem_erase hy) h.symm)
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem hx]
    have hpos : 1 ≤ G.card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [Nat.cast_sub hpos, Nat.cast_one]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-! ### (2) The indicator decomposition of the subgroup mass -/

/-- **Indicator decomposition of Σ.**  For `χ` of order `m` cutting out `H = G_χ`:
`m·∑_{b∈G_χ} η_b·conj(η_b) = ∑_{j<m} ∑_b χ^j(b)·η_b·conj(η_b)`. -/
theorem sigma_indicator_decomp (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F) :
    (orderOf χ : ℂ) * ∑ b ∈ Gchi χ, eta ψ G b * conj' (eta ψ G b)
      = ∑ j ∈ Finset.range (orderOf χ),
          ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
  classical
  rw [Finset.sum_comm]
  symm
  calc ∑ b : F, ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))
      = ∑ b : F, (∑ j ∈ Finset.range (orderOf χ), (χ ^ j) b)
          * (eta ψ G b * conj' (eta ψ G b)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_); rw [Finset.sum_mul]
    _ = ∑ b : F, (if χ b = 1 then (orderOf χ : ℂ) else 0)
          * (eta ψ G b * conj' (eta ψ G b)) := by
        refine Finset.sum_congr rfl (fun b _ => by rw [mulChar_pow_sum_all])
    _ = ∑ b : F, if χ b = 1 then (orderOf χ : ℂ) * (eta ψ G b * conj' (eta ψ G b)) else 0 := by
        refine Finset.sum_congr rfl (fun b _ => ?_); simp only [ite_mul, zero_mul]
    _ = ∑ b ∈ Gchi χ, (orderOf χ : ℂ) * (eta ψ G b * conj' (eta ψ G b)) := by
        rw [Gchi, Finset.sum_filter]
    _ = (orderOf χ : ℂ) * ∑ b ∈ Gchi χ, eta ψ G b * conj' (eta ψ G b) := by
        rw [Finset.mul_sum]

/-! ### (3) The unconditional lower bound on Σ -/

/-- `η_0 = |G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  rw [eta]
  have h : ∀ y ∈ G, ψ (0 * y) = 1 := by
    intro y _; rw [zero_mul, AddChar.map_zero_eq_one]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The trivial-character term: `∑_b 1(b)·‖η_b‖² = n·q − n²` (Parseval minus the DC term). -/
theorem trivial_term_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b))
      = ((G.card : ℂ)) * (Fintype.card F : ℂ) - (G.card : ℂ) ^ 2 := by
  classical
  have hsplit : ∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b))
      = (∑ b : F, eta ψ G b * conj' (eta ψ G b))
        - eta ψ G 0 * conj' (eta ψ G 0) := by
    have hterm : ∀ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b))
        = (eta ψ G b * conj' (eta ψ G b))
          - (if b = 0 then eta ψ G b * conj' (eta ψ G b) else 0) := by
      intro b
      rcases eq_or_ne b 0 with rfl | hb
      · rw [MulChar.map_nonunit (1 : MulChar F ℂ) not_isUnit_zero, zero_mul, if_pos rfl]
        ring
      · rw [MulChar.one_apply hb.isUnit, one_mul, if_neg hb]; ring
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ 0 (fun b => eta ψ G b * conj' (eta ψ G b)),
      if_pos (Finset.mem_univ 0)]
  have hpars : (∑ b : F, eta ψ G b * conj' (eta ψ G b))
      = ((G.card : ℂ)) * (Fintype.card F : ℂ) := by
    have hnorm : ∀ b : F, eta ψ G b * conj' (eta ψ G b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      intro b; rw [RCLike.mul_conj]; norm_cast
    rw [Finset.sum_congr rfl (fun b _ => hnorm b), ← Complex.ofReal_sum,
      subgroup_gaussSum_secondMoment hψ G]
    push_cast; ring
  have hdc : eta ψ G 0 * conj' (eta ψ G 0) = (G.card : ℂ) ^ 2 := by
    rw [eta_zero, map_natCast, sq]
  rw [hsplit, hpars, hdc]

/-- **The Σ lower bound, unconditional**:
`n·q − n² − (m−1)·n(n−1)·√q ≤ m·Σ`, where `Σ = ∑_{b∈G_χ}‖η_b‖²`, `m = orderOf χ`. -/
theorem sigma_lower_bound {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hm : 1 ≤ orderOf χ) :
    (G.card : ℝ) * (Fintype.card F : ℝ) - (G.card : ℝ) ^ 2
        - ((orderOf χ : ℝ) - 1) * ((G.card : ℝ) * ((G.card : ℝ) - 1)
            * Real.sqrt (Fintype.card F : ℝ))
      ≤ (orderOf χ : ℝ) * ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 := by
  classical
  set m : ℕ := orderOf χ with hmdef
  set Sig : ℝ := ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 with hSigdef
  set n : ℝ := (G.card : ℝ) with hndef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  -- complex identity: m·Σ − (nq − n²) = ∑_{1≤j<m} A_j
  have hnorm : ∀ b : F, eta ψ G b * conj' (eta ψ G b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b; rw [RCLike.mul_conj]; norm_cast
  have hSigC : ∑ b ∈ Gchi χ, eta ψ G b * conj' (eta ψ G b) = ((Sig : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun b _ => hnorm b), ← Complex.ofReal_sum]
  have hdecomp := sigma_indicator_decomp χ ψ G
  have h0mem : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr hm
  have hsplit : ∑ j ∈ Finset.range m, ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))
      = (∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b)))
        + ∑ j ∈ (Finset.range m).erase 0,
            ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
    rw [← Finset.add_sum_erase _ _ h0mem, pow_zero]
  have htail_bound : ‖∑ j ∈ (Finset.range m).erase 0,
        ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))‖
      ≤ ((m : ℝ) - 1) * (n * (n - 1) * Real.sqrt q) := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ j ∈ (Finset.range m).erase 0,
        ‖∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))‖
          ≤ n * (n - 1) * Real.sqrt q := by
      intro j hj
      rw [Finset.mem_erase, Finset.mem_range] at hj
      exact norm_twisted_secondMoment_le (pow_ne_one_of_lt_orderOf hj.1 hj.2) hψ G
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem h0mem, Finset.card_range]
    have hm1 : 1 ≤ m := Finset.mem_range.mp h0mem
    rw [Nat.cast_sub hm1, Nat.cast_one]
  -- assemble over ℝ
  have hkey : ‖((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ)‖
      ≤ ((m : ℝ) - 1) * (n * (n - 1) * Real.sqrt q) := by
    have hcx : (((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ) : ℂ)
        = ∑ j ∈ (Finset.range m).erase 0,
            ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
      have hlhs : ((m : ℂ)) * ((Sig : ℝ) : ℂ)
          = (∑ b : F, (1 : MulChar F ℂ) b * (eta ψ G b * conj' (eta ψ G b)))
            + ∑ j ∈ (Finset.range m).erase 0,
                ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b)) := by
        rw [← hSigC, ← hsplit, ← hdecomp]
      rw [trivial_term_eq hψ G] at hlhs
      have : (((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ) : ℂ)
          = ((m : ℂ)) * ((Sig : ℝ) : ℂ)
            - (((G.card : ℂ)) * (Fintype.card F : ℂ) - (G.card : ℂ) ^ 2) := by
        push_cast [hndef, hqdef]; ring
      rw [this, hlhs]; ring
    calc ‖((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ)‖
        = ‖(((m : ℝ) * Sig - (n * q - n ^ 2) : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
      _ = ‖∑ j ∈ (Finset.range m).erase 0,
            ∑ b : F, (χ ^ j) b * (eta ψ G b * conj' (eta ψ G b))‖ := by rw [hcx]
      _ ≤ ((m : ℝ) - 1) * (n * (n - 1) * Real.sqrt q) := htail_bound
  have habs := abs_le.mp (by rwa [Real.norm_eq_abs] at hkey)
  linarith [habs.1]

/-! ### (4) The regime form: `hSig` discharged -/

/-- **`hSig` DISCHARGED for `H = G_χ`**: in the regime `16·m²·n² ≤ q` (part of the round-17
Weil regime), `n·q ≤ 2m·Σ`.  This is the exact hypothesis shape consumed by
`_R17QuadrupleWeilRung.r2Rung_of_weil` / `wickAwayAtWithConstant_two_of_weil`. -/
theorem hSig_of_regime {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    (G.card : ℝ) * (Fintype.card F : ℝ)
      ≤ 2 * (orderOf χ : ℝ) * ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 := by
  have hlow := sigma_lower_bound (χ := χ) hψ G (le_trans (by norm_num) hm)
  set m : ℝ := (orderOf χ : ℝ) with hmdef
  set n : ℝ := (G.card : ℝ) with hndef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set s : ℝ := Real.sqrt q with hsdef
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = q := Real.sq_sqrt hq0
  have hmR : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  -- 4mn ≤ s from (4mn)² ≤ q = s²
  have hmn : (4 * m * n) ≤ s := by
    have h1 : (4 * m * n) ^ 2 ≤ s ^ 2 := by rw [hssq]; nlinarith [hreg]
    have h2 : (0 : ℝ) ≤ 4 * m * n := by nlinarith
    nlinarith [h1, h2, hs0]
  -- n·q ≤ 2·(nq − n² − (m−1)n(n−1)s)  in this regime
  have hSig0 : (0 : ℝ) ≤ ∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2 := by positivity
  -- (m−1)(n−1)s ≤ mns ≤ (s/4)·s = q/4 ; n ≤ s/(8) ≤ q/4
  have hterm1 : (m - 1) * (n * (n - 1) * s) ≤ n * q / 4 := by
    -- (m−1)(n−1)s ≤ m·n·s ≤ (s/4)·s = q/4, multiplied by n
    have h1 : (m - 1) * (n - 1) * s ≤ m * n * s := by nlinarith
    have h2 : m * n * s ≤ s * s / 4 := by nlinarith [hmn, hs0]
    have h3 : s * s = q := by nlinarith [hssq]
    nlinarith [h1, h2, h3, hnR]
  have hterm2 : n ^ 2 ≤ n * q / 4 := by
    -- n ≤ s/(8m) ≤ s ≤ s²/4 = q/4 (s ≥ 8)
    have hs8 : (8 : ℝ) ≤ s := by nlinarith [hmn]
    have h1 : n ≤ s := by nlinarith [hmn]
    have h2 : s ≤ s * s / 4 := by nlinarith [hs8]
    have h3 : s * s = q := by nlinarith [hssq]
    nlinarith [h1, h2, h3, hnR]
  nlinarith [hlow, hterm1, hterm2]

/-! ### (4b) Abstract lower-envelope packaging -/

/-- The unconditional Σ-equidistribution estimate in the abstract `SigmaLowerEnvelope` form used
by `_R18SigmaGate`. -/
theorem sigmaLowerEnvelope_of_gchi {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (hm : 1 ≤ orderOf χ) :
    ArkLib.ProximityGap.Frontier.R18SigmaGate.SigmaLowerEnvelope
      (orderOf χ : ℝ) (G.card : ℝ) (Fintype.card F : ℝ)
      (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) := by
  exact sigma_lower_bound (χ := χ) hψ G hm

/-! ### (4c) Constant-threshold arithmetic -/

/-- Real-variable threshold for the R18 constant: if the numerator is at most `3m²`, then
`32A/m²/3 ≤ 1`. -/
theorem r18Constant_le_one_of_num_le {m A : ℝ} (hm : 0 < m)
    (hnum : 32 * A ≤ 3 * m ^ 2) :
    32 * A / m ^ 2 / 3 ≤ 1 := by
  rw [div_div]
  have hden : 0 < m ^ 2 * 3 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- A squared-size version of the R18 constant threshold.  It isolates the real arithmetic:
any lower bound strong enough to prove `32A ≤ 3m²` feeds the exact-rung gate. -/
theorem r18Constant_le_one_of_sq_ge {m A K : ℝ} (hm : 0 < m)
    (hA : 32 * A ≤ K ^ 2) (hK : K ^ 2 ≤ 3 * m ^ 2) :
    32 * A / m ^ 2 / 3 ≤ 1 :=
  r18Constant_le_one_of_num_le hm (le_trans hA hK)

/-- A convenient stronger threshold: bounding the numerator by `m²` is enough. -/
theorem r18Constant_le_one_of_num_le_sq {m A : ℝ} (hm : 0 < m)
    (hnum : 32 * A ≤ m ^ 2) :
    32 * A / m ^ 2 / 3 ≤ 1 := by
  refine r18Constant_le_one_of_num_le hm (le_trans hnum ?_)
  nlinarith [sq_nonneg m]

/-- Coarse but convenient quartic-Weil numerator bound: if `1 ≤ N` and `15N² ≤ m`, then
`32(6N⁴+1) ≤ m²`.  This packages the r18 exact-rung condition in the natural scale
`m ≳ |X|²`. -/
theorem quarticWeil_num_le_sq_of_fifteen_card_sq_le
    {N m : ℝ} (hN : 1 ≤ N) (hm : 15 * N ^ 2 ≤ m) :
    32 * (6 * N ^ 4 + 1) ≤ m ^ 2 := by
  have hN2_ge_one : 1 ≤ N ^ 2 := by nlinarith [sq_nonneg (N - 1)]
  have hN4_ge_one : 1 ≤ N ^ 4 := by
    have hN4_eq : N ^ 4 = (N ^ 2) ^ 2 := by ring
    rw [hN4_eq]
    nlinarith [sq_nonneg (N ^ 2 - 1)]
  have hnum : 32 * (6 * N ^ 4 + 1) ≤ 225 * N ^ 4 := by nlinarith
  have hsq : (15 * N ^ 2) ^ 2 ≤ m ^ 2 := by
    have hm0 : 0 ≤ m := by nlinarith [hN2_ge_one]
    nlinarith [hm, hm0, sq_nonneg (m - 15 * N ^ 2)]
  nlinarith [hnum, hsq]

/-- Generic `Cw` version of the coarse quartic numerator bound.  If `Cw ≤ 6`, the same
`15N² ≤ m` scale used by the fully quartic-Weil route bounds `32(CwN⁴+1)` by `m²`. -/
theorem generic_num_le_sq_of_fifteen_card_sq_le
    {Cw N m : ℝ} (hCw : Cw ≤ 6) (hN : 1 ≤ N) (hm : 15 * N ^ 2 ≤ m) :
    32 * (Cw * N ^ 4 + 1) ≤ m ^ 2 := by
  have hN4_nonneg : 0 ≤ N ^ 4 := by positivity
  have hnum_le : 32 * (Cw * N ^ 4 + 1) ≤ 32 * (6 * N ^ 4 + 1) := by
    nlinarith
  exact le_trans hnum_le (quarticWeil_num_le_sq_of_fifteen_card_sq_le hN hm)

/-! ### (5) Consumer wiring: the r = 2 rung at THREE named inputs -/

/-- **The raw round-17 r = 2 rung with `hSig` discharged** (for `H = G_χ`).  This is the
`incidenceMomentAway` companion to `wickAwayAtWithConstant_two_of_gchi`. -/
theorem r2Rung_of_gchi
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceMomentAway
        ψ G (Gchi χ) D 2
      ≤ (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2)
        * ((Fintype.card F : ℝ) * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2) :=
  ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.r2Rung_of_weil
    ψ G (Gchi χ) D X g (orderOf χ) (le_trans (by norm_num) hm) hCw hdec hg h4
    hq1 hnq (hSig_of_regime hψ G hm hn hreg)

/-- **The round-17 r = 2 rung with `hSig` discharged** (for `H = G_χ`): only the three named
inputs `ChiDecompositionOff`, `GaussSumSizeBound`, `FourthMomentTwistBound` remain (plus the
regime `16m²n² ≤ q`, `n² ≤ q` — both components of the round-17 Weil regime
`q ≥ max(n⁴, 16n²m²)`). -/
theorem wickAwayAtWithConstant_two_of_gchi
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.WickAwayAtWithConstant
      ψ G (Gchi χ) D 2
      (32 * (Cw * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3) :=
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.wickAwayAtWithConstant_two_of_weil
    ψ G (Gchi χ) D X g (orderOf χ) (le_trans (by norm_num) hm) hCw hdec hg h4 hq1 hnq
    (hSig_of_regime hψ G hm hn hreg)

/-- If the three-input R18 constant is at most `1`, the `Gχ` route proves the exact R15
away-Wick `r = 2` target. -/
theorem wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hC :
      32 * (Cw * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one
    G (Gchi χ) D 2 hC
    (wickAwayAtWithConstant_two_of_gchi ψ hψ G D X g χ hm hn hCw hdec hg h4 hq1 hnq hreg)

/-- If the three-input R18 constant is at most `1`, the `Gχ` route proves R15's raw fourth
moment-with-diagonal target. -/
theorem rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hC :
      32 * (Cw * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one
    G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_gchi ψ hψ G D X g χ hm hn hCw hdec hg h4 hq1 hnq hreg)

/-- Size-condition version of `wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one`.
It is often easier to prove the unnormalized numerator bound. -/
theorem wickForIncidenceAwayAt_two_of_gchi_of_num_le
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hnum : 32 * (Cw * (X.card : ℝ) ^ 4 + 1) ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one ψ hψ G D X g χ hm hn hCw
    (r18Constant_le_one_of_num_le (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg h4 hq1 hnq hreg

/-- Size-condition version of `rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_of_num_le
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hnum : 32 * (Cw * (X.card : ℝ) ^ 4 + 1) ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one ψ hψ G D X g χ hm hn hCw
    (r18Constant_le_one_of_num_le (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg h4 hq1 hnq hreg

/-- Strong square-bound version of `wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_of_num_le_sq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hnum : 32 * (Cw * (X.card : ℝ) ^ 4 + 1) ≤ ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one ψ hψ G D X g χ hm hn hCw
    (r18Constant_le_one_of_num_le_sq (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg h4 hq1 hnq hreg

/-- Strong square-bound version of `rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_of_num_le_sq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hnum : 32 * (Cw * (X.card : ℝ) ^ 4 + 1) ≤ ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one ψ hψ G D X g χ hm hn hCw
    (r18Constant_le_one_of_num_le_sq (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg h4 hq1 hnq hreg

/-- Generic `Cw` exact-rung consumer at the same family-size scale as the quartic-Weil
discharge.  The hypothesis `Cw ≤ 6` is the only constant input. -/
theorem wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw0 : 0 ≤ Cw) (hCw6 : Cw ≤ 6) (hX : X.Nonempty)
    (horder : 15 * ((X.card : ℝ) ^ 2) ≤ (orderOf χ : ℝ))
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_of_num_le_sq ψ hψ G D X g χ hm hn hCw0
    (generic_num_le_sq_of_fifteen_card_sq_le hCw6
      (by exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hX)) horder)
    hdec hg h4 hq1 hnq hreg

/-- Raw fourth-moment companion to
`wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw0 : 0 ≤ Cw) (hCw6 : Cw ≤ 6) (hX : X.Nonempty)
    (horder : 15 * ((X.card : ℝ) ^ 2) ≤ (orderOf χ : ℝ))
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_of_num_le_sq ψ hψ G D X g χ hm hn hCw0
    (generic_num_le_sq_of_fifteen_card_sq_le hCw6
      (by exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hX)) horder)
    hdec hg h4 hq1 hnq hreg

/-- Nat-order version of
`wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw0 : 0 ≤ Cw) (hCw6 : Cw ≤ 6) (hX : X.Nonempty)
    (horder : 15 * X.card ^ 2 ≤ orderOf χ)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order
    ψ hψ G D X g χ hm hn hCw0 hCw6 hX (by exact_mod_cast horder)
    hdec hg h4 hq1 hnq hreg

/-- Raw fourth-moment Nat-order companion to
`wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order_nat`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw : ℝ} (hCw0 : 0 ≤ Cw) (hCw6 : Cw ≤ 6) (hX : X.Nonempty)
    (horder : 15 * X.card ^ 2 ≤ orderOf χ)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order
    ψ hψ G D X g χ hm hn hCw0 hCw6 hX (by exact_mod_cast horder)
    hdec hg h4 hq1 hnq hreg

/-- Squared-size version of `wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_of_sq_ge
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw K : ℝ} (hCw : 0 ≤ Cw)
    (hA : 32 * (Cw * (X.card : ℝ) ^ 4 + 1) ≤ K ^ 2)
    (hK : K ^ 2 ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one ψ hψ G D X g χ hm hn hCw
    (r18Constant_le_one_of_sq_ge (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hA hK)
    hdec hg h4 hq1 hnq hreg

/-- Squared-size version of `rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_of_sq_ge
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {Cw K : ℝ} (hCw : 0 ≤ Cw)
    (hA : 32 * (Cw * (X.card : ℝ) ^ 4 + 1) ≤ K ^ 2)
    (hK : K ^ 2 ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (h4 : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one ψ hψ G D X g χ hm hn hCw
    (r18Constant_le_one_of_sq_ge (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hA hK)
    hdec hg h4 hq1 hnq hreg

/-- **The r = 2 rung with both R18 plumbing inputs discharged**: `hSig` comes from Σ-equidistribution
and `FourthMomentTwistBound` comes from the per-tuple quartic Weil input.  This is the raw
`incidenceMomentAway` companion to `wickAwayAtWithConstant_two_of_gchi_quarticWeil`. -/
theorem r2Rung_of_gchi_quarticWeil
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.incidenceMomentAway
        ψ G (Gchi χ) D 2
      ≤ (32 * (6 * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2)
        * ((Fintype.card F : ℝ) * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2) :=
  r2Rung_of_gchi ψ hψ G D X g χ hm hn
    (by norm_num)
    hdec hg
    (ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentTwistBound_of_quarticWeilInput
      G X hW hn4q)
    hq1 hnq hreg

/-- **The r = 2 rung with both R18 plumbing inputs discharged**: `hSig` comes from Σ-equidistribution
and `FourthMomentTwistBound` comes from the per-tuple quartic Weil input.  Remaining named inputs:
the χ-decomposition, Gauss-sum sizes, and the genuine Hasse/Weil quartic character-sum statement. -/
theorem wickAwayAtWithConstant_two_of_gchi_quarticWeil
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.WickAwayAtWithConstant
      ψ G (Gchi χ) D 2
      (32 * (6 * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3) :=
  wickAwayAtWithConstant_two_of_gchi ψ hψ G D X g χ hm hn
    (by norm_num)
    hdec hg
    (ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentTwistBound_of_quarticWeilInput
      G X hW hn4q)
    hq1 hnq hreg

/-- If the fully discharged quartic-Weil R18 constant is at most `1`, the route proves the exact
R15 away-Wick `r = 2` target. -/
theorem wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC :
      32 * (6 * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.wickForIncidenceAwayAt_of_wickAwayAtWithConstant_le_one
    G (Gchi χ) D 2 hC
    (wickAwayAtWithConstant_two_of_gchi_quarticWeil ψ hψ G D X g χ hm hn hdec hg hW
      hq1 hnq hn4q hreg)

/-- If the fully discharged quartic-Weil R18 constant is at most `1`, the route proves R15's raw
fourth-moment-with-diagonal target. -/
theorem rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hC :
      32 * (6 * (X.card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  ArkLib.ProximityGap.Frontier.R16DiagonalExactValue.rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one
    G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_gchi_quarticWeil ψ hψ G D X g χ hm hn hdec hg hW
      hq1 hnq hn4q hreg)

/-- Size-condition version of
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_num_le
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hnum : 32 * (6 * (X.card : ℝ) ^ 4 + 1) ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one ψ hψ G D X g χ hm hn
    (r18Constant_le_one_of_num_le (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg hW hq1 hnq hn4q hreg

/-- Size-condition version of
`rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_num_le
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hnum : 32 * (6 * (X.card : ℝ) ^ 4 + 1) ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one ψ hψ G D X g χ hm hn
    (r18Constant_le_one_of_num_le (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg hW hq1 hnq hn4q hreg

/-- Strong square-bound version of
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_num_le_sq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hnum : 32 * (6 * (X.card : ℝ) ^ 4 + 1) ≤ ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one ψ hψ G D X g χ hm hn
    (r18Constant_le_one_of_num_le_sq (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg hW hq1 hnq hn4q hreg

/-- Strong square-bound version of
`rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_num_le_sq
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hnum : 32 * (6 * (X.card : ℝ) ^ 4 + 1) ≤ ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one ψ hψ G D X g χ hm hn
    (r18Constant_le_one_of_num_le_sq (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hnum)
    hdec hg hW hq1 hnq hn4q hreg

/-- Quartic-Weil exact-rung consumer in the natural family-size scale: if
`15 * |X|² ≤ orderOf χ`, then the fully discharged R18 route proves the exact R15 `r = 2`
away-Wick target. -/
theorem wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_fifteen_card_sq_le_order
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hX : 1 ≤ X.card)
    (horder : 15 * ((X.card : ℝ) ^ 2) ≤ (orderOf χ : ℝ))
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_num_le_sq ψ hψ G D X g χ hm hn
    (quarticWeil_num_le_sq_of_fifteen_card_sq_le (by exact_mod_cast hX) horder)
    hdec hg hW hq1 hnq hn4q hreg

/-- Raw fourth-moment companion to
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_fifteen_card_sq_le_order`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_fifteen_card_sq_le_order
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hX : 1 ≤ X.card)
    (horder : 15 * ((X.card : ℝ) ^ 2) ≤ (orderOf χ : ℝ))
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_num_le_sq ψ hψ G D X g χ hm hn
    (quarticWeil_num_le_sq_of_fifteen_card_sq_le (by exact_mod_cast hX) horder)
    hdec hg hW hq1 hnq hn4q hreg

/-- Nonempty-family version of
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_fifteen_card_sq_le_order`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hX : X.Nonempty)
    (horder : 15 * ((X.card : ℝ) ^ 2) ≤ (orderOf χ : ℝ))
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_fifteen_card_sq_le_order
    ψ hψ G D X g χ hm hn (Nat.succ_le_of_lt (Finset.card_pos.mpr hX)) horder
    hdec hg hW hq1 hnq hn4q hreg

/-- Raw fourth-moment nonempty-family companion to
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hX : X.Nonempty)
    (horder : 15 * ((X.card : ℝ) ^ 2) ≤ (orderOf χ : ℝ))
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_fifteen_card_sq_le_order
    ψ hψ G D X g χ hm hn (Nat.succ_le_of_lt (Finset.card_pos.mpr hX)) horder
    hdec hg hW hq1 hnq hn4q hreg

/-- Nat-order version of
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hX : X.Nonempty)
    (horder : 15 * X.card ^ 2 ≤ orderOf χ)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order
    ψ hψ G D X g χ hm hn hX (by exact_mod_cast horder) hdec hg hW hq1 hnq hn4q hreg

/-- Raw fourth-moment Nat-order companion to
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hX : X.Nonempty)
    (horder : 15 * X.card ^ 2 ≤ orderOf χ)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order
    ψ hψ G D X g χ hm hn hX (by exact_mod_cast horder) hdec hg hW hq1 hnq hn4q hreg

/-- Squared-size version of
`wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one`. -/
theorem wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_sq_ge
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {K : ℝ}
    (hA : 32 * (6 * (X.card : ℝ) ^ 4 + 1) ≤ K ^ 2)
    (hK : K ^ 2 ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (Gchi χ) D 2 :=
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one ψ hψ G D X g χ hm hn
    (r18Constant_le_one_of_sq_ge (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hA hK)
    hdec hg hW hq1 hnq hn4q hreg

/-- Squared-size version of
`rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_sq_ge
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (G D : Finset F) (X : Finset (MulChar F ℂ))
    (g : MulChar F ℂ → ℂ) (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    {K : ℝ}
    (hA : 32 * (6 * (X.card : ℝ) ^ 4 + 1) ≤ K ^ 2)
    (hK : K ^ 2 ≤ 3 * ((orderOf χ : ℝ)) ^ 2)
    (hdec : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.ChiDecompositionOff
      ψ G (Gchi χ) D X g (orderOf χ))
    (hg : ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.GaussSumSizeBound X g)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.RawFourthMomentWithDiagonal
      ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one ψ hψ G D X g χ hm hn
    (r18Constant_le_one_of_sq_ge (by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm)
      hA hK)
    hdec hg hW hq1 hnq hn4q hreg

#print axioms twisted_secondMoment_eq_gaussSums
#print axioms norm_twisted_secondMoment_le
#print axioms sigma_indicator_decomp
#print axioms trivial_term_eq
#print axioms sigma_lower_bound
#print axioms hSig_of_regime
#print axioms sigmaLowerEnvelope_of_gchi
#print axioms r18Constant_le_one_of_num_le
#print axioms r18Constant_le_one_of_sq_ge
#print axioms r18Constant_le_one_of_num_le_sq
#print axioms quarticWeil_num_le_sq_of_fifteen_card_sq_le
#print axioms generic_num_le_sq_of_fifteen_card_sq_le
#print axioms r2Rung_of_gchi
#print axioms wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one
#print axioms rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one
#print axioms wickForIncidenceAwayAt_two_of_gchi_of_num_le
#print axioms rawFourthMomentWithDiagonal_of_gchi_of_num_le
#print axioms wickForIncidenceAwayAt_two_of_gchi_of_num_le_sq
#print axioms rawFourthMomentWithDiagonal_of_gchi_of_num_le_sq
#print axioms
  wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order
#print axioms
  rawFourthMomentWithDiagonal_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order
#print axioms
  wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order_nat
#print axioms
  rawFourthMomentWithDiagonal_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order_nat
#print axioms wickForIncidenceAwayAt_two_of_gchi_of_sq_ge
#print axioms rawFourthMomentWithDiagonal_of_gchi_of_sq_ge
#print axioms r2Rung_of_gchi_quarticWeil
#print axioms wickAwayAtWithConstant_two_of_gchi
#print axioms wickAwayAtWithConstant_two_of_gchi_quarticWeil
#print axioms wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one
#print axioms rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one
#print axioms wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_num_le
#print axioms rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_num_le
#print axioms wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_num_le_sq
#print axioms rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_num_le_sq
#print axioms wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_fifteen_card_sq_le_order
#print axioms rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_fifteen_card_sq_le_order
#print axioms
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order
#print axioms
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order
#print axioms
  wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms
  rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_sq_ge
#print axioms rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_sq_ge

end ArkLib.ProximityGap.Frontier.R18SigmaEquidistribution
