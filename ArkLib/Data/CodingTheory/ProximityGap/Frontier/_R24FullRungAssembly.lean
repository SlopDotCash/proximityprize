/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R21HigherDFaces
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22StepanovAssembly

/-!
# LANE FULLRUNG (#466 round 24): the order-d pipeline assembly + THE CONSTANT-ACCOUNTING
# AUDIT — what a completed `TripleLinearHasse` family actually buys the campaign

Round 23 fired the r=2 rung's quadratic (d = 2) face unconditionally
(`legendreCubicHasseC_unconditional`).  The remaining faces are the order-d ≥ 4 members:
per nondegenerate tuple, `‖∑_s χ((us+1)(vs+1))·conj χ(ws+1)‖ ≤ C(d)·√q` for `χ` of 2-power
order `d` — Weil for the superelliptic curve `y^d = L₁L₂L₃^{d−1}` (true constant 2, uniform
in d), or ELEMENTARY Stepanov with a possibly d-growing constant.  This file provides the
conditional pipeline for the elementary route at GENERIC per-order constants, and settles
the critical bookkeeping question: does `C(d)` growth break the rung at prize scale?

## PROVEN here (axiom-clean)

1. `TripleLinearHasseC` — the generic-constant order-d Hasse input (`C = 2` recovers the
   round-21 `TripleLinearHasse` definitionally, `tripleLinearHasseC_two_iff`).
2. `quarticWeilInputC_of_tripleLinearHasseC` — per character: constant `C` in, `C + 1` out.
3. `fourthMomentTwistBound_of_tripleLinearHasseC_family` — THE FAMILY WELD: per-character
   constants `Cd χ ≤ Cmax` give `FourthMomentTwistBound G X (4 + Cmax)`.  **The uniformity
   the rung needs is exactly `Cmax = sup_{d | m} C(d)`** — this theorem is where a d-growing
   elementary constant enters the rung arithmetic, and it enters ONLY through `Cw = 4 + Cmax`.
4. `class_fold_bound` — **the d-fold assembly arithmetic** (the norm-fold cost, exact):
   values in `{0} ∪ T` (`T` unit-modulus, `∑ T = 0`), per-class Stepanov count `≤ B`, zero
   fiber `≤ z`  ⟹  `‖∑_s val s‖ ≤ |T|·B − q + z`.  So the fold cost is ONE factor of `d`
   times the per-class EXCESS (`B = q/d + E ⟹ bound = d·E + z`): the elementary constant
   is `C(d) = d·(per-class excess coefficient)` — LINEAR in `d` times whatever the order-d
   dimension count pays per class, NOT an extra `d²` from the folding itself.
5. `tripleVal_zero_fiber_card_le_three` — the zero fiber of the triple-linear kernel is ≤ 3
   (unconditional, every tuple, every χ).
6. `DStepanovOutput` (the d-analogue of `S2Output`: one aux polynomial PER FIBER CLASS) +
   `classCount_le_of_dStepanovOutput` + `tripleLinearHasseC_of_dStepanovOutput` — the full
   conditional pipeline `DStepanovOutput → TripleLinearHasseC C → QuarticWeilInputC (C+1) →
   FourthMomentTwistBound (4 + Cmax)` with every constant explicit.
7. **`fullFamily_gate_impossible`** — THE AUDIT THEOREM: the normalized full-family rung
   gate `32(Cw·(m−1)⁴+1)/m²/3 ≤ 1` (the `hC` hypothesis of the round-19
   `*_of_chiFamily_of_constant_le_one` consumers, with `|chiFamily χ| = m−1`) is
   IMPOSSIBLE for every `m ≥ 2` and every `Cw ≥ 1` — including the sharp Weil `Cw = 6`.

## THE HONEST CONSTANT ACCOUNTING (the lane's main deliverable)

**(i) Where uniformity is needed.** `FourthMomentTwistBound G X Cw` demands ONE `Cw` for
every `χ' ∈ X`.  For the full family `X = chiFamily χ` (orders `d | m`, `d` up to `m`),
`Cw = 4 + sup_{d|m} C(d)`.  If elementary Stepanov gives `C(d) = Θ(d)` (linear, by (4):
d classes × per-class excess) the full-family `Cw = Θ(m)`; if the per-class dimension
count itself degrades with d, worse.  The Weil route gives `Cw = 6` uniform.

**(ii) What the growth hits.** The rung constant is `K(m) = 32(Cw·(m−1)⁴+1)/m²`.  With
Weil `Cw = 6`: `K = Θ(m²)`.  With elementary `Cw = Θ(m)`: `K = Θ(m³)`.  The `(m−1)⁴`
dominates EITHER WAY — the rung inequality `S₂ ≤ K·q·Σ²` holds parametrically at any
finite `K`, and no in-tree consumer of the parametric form requires `K = O(1)`.

**(iii) The decisive fact (theorem 7).** The only consumers that demand a small constant —
the normalized gate `K/3 ≤ 1` full-family consumers — are ALREADY impossible at the sharp
Weil constant `Cw = 6` (indeed at every `Cw ≥ 1`), for every `m ≥ 2`.  In-tree this was
half-known (`not_fifteen_chiFamily_card_sq_le_order`); here it is pinned at the gate
itself.  CONSEQUENCE: **polynomial growth of the elementary `C(d)` does not change which
consumers fire.**  Everything that fires with Weil's uniform 2 fires with elementary
`C(d) = poly(d)`; everything that needs the normalized full-family gate fails for both.
The elementary route is NOT disqualified by its constants.

**(iv) The live consumers at scale.** The gate consumers that CAN fire use a subfamily
`Y ⊆ chiFamily χ` with `15·|Y|² ≤ m` (so `|Y| ≤ √(m/15)`), where the needed moment bound
is only over `Y` — and in the 2-power tower there are exactly `~√(m/15)` characters of
order `≤ √(m/15)`, so `Y` can be chosen with `sup_{χ'∈Y} C(order χ') = C(O(√m))` — the
elementary growth is SQUARE-ROOTED on the live route.  (The `ChiDecompositionOff` for a
proper subfamily is that route's own named input; not discharged here.)

**(v) What completing `TripleLinearHasse` buys.**  It completes the r = 2 rung of the
corrected-B tower — the FIRST rung only.  The δ*-interchange to `approxB` at depth
`r ≈ ln q` needs ALL rungs `r = 2 … ⌈ln q⌉` (the 2r-point analogues, a DIFFERENT Weil
family per rung, with the deep-depth `AwaySupBound` open above them all), plus Problem A
(`WallHolds`).  The r = 2 rung is the validated architecture template, not the prize:
its completion is worth having exactly because the parametric-constant design (proven
end-to-end here and in r22/r23) transfers to every higher rung.  No closure claimed.

Issue #466, round 24, FULLRUNG lane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R24FullRungAssembly

open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R21HigherDFaces
open ArkLib.ProximityGap.Frontier.R22StepanovAssembly
open ArkLib.ProximityGap.Frontier.R20StepanovScaffold

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The generic-constant order-d Hasse input -/

/-- `TripleLinearHasse` with a GENERIC constant `C` (the round-21 Prop is the case
`C = 2`, the true Weil value; an elementary Stepanov route reaches some `C(d)`). -/
def TripleLinearHasseC (χ : MulChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ IsDegenerate z →
    ‖tripleSum χ (z.2.2 - z.1.1) (z.2.2 - z.1.2) (z.2.2 - z.2.1)‖
      ≤ C * Real.sqrt (Fintype.card F)

/-- At `C = 2` the generic Prop IS the round-21 `TripleLinearHasse` (definitional). -/
theorem tripleLinearHasseC_two_iff (χ : MulChar F ℂ) (G : Finset F) :
    TripleLinearHasseC χ G 2 ↔ TripleLinearHasse χ G :=
  Iff.rfl

/-- Constant monotonicity. -/
theorem tripleLinearHasseC_mono (χ : MulChar F ℂ) (G : Finset F) {C C' : ℝ}
    (hCC : C ≤ C') (h : TripleLinearHasseC χ G C) :
    TripleLinearHasseC χ G C' := by
  intro z hz hnd
  refine le_trans (h z hz hnd) ?_
  have hs : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  nlinarith

/-! ## 2. Per-character reduction: constant `C` in, `C + 1` out -/

/-- **Generic-constant round-21 reduction**: `TripleLinearHasseC χ G C` gives the
generic-constant quartic Weil face at `C + 1` (`‖quadTerm‖ = ‖tripleSum − 1‖ ≤ C√p + 1
≤ (C+1)√p`, using `√p ≥ 1`). -/
theorem quarticWeilInputC_of_tripleLinearHasseC (χ : MulChar F ℂ) (G : Finset F)
    {C : ℝ} (hH : TripleLinearHasseC χ G C) :
    QuarticWeilInputC χ G (C + 1) := by
  intro z hz hnd
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := z
  have hid := quadTerm_eq_tripleSum_sub_one χ a₁ a₂ b₁ b₂
  have hW := hH ((a₁, a₂), (b₁, b₂)) hz hnd
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) :=
    ArkLib.ProximityGap.Frontier.R20QuadFaceBridge.one_le_sqrt_card
  calc ‖quadTerm χ ((a₁, a₂), (b₁, b₂))‖
      = ‖tripleSum χ (b₂ - a₁) (b₂ - a₂) (b₂ - b₁) - 1‖ := by rw [hid]
    _ ≤ ‖tripleSum χ (b₂ - a₁) (b₂ - a₂) (b₂ - b₁)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ C * Real.sqrt (Fintype.card F) + 1 := by
        have h1 : ‖(1 : ℂ)‖ = 1 := by simp
        rw [h1]; linarith [hW]
    _ ≤ (C + 1) * Real.sqrt (Fintype.card F) := by nlinarith [hs1]

/-! ## 3. THE FAMILY WELD: the uniformity requirement made explicit -/

/-- **The family weld (where d-growth enters the rung)**: per-character triple-linear
Hasse constants `Cd χ' ≤ Cmax` over `X` give `FourthMomentTwistBound G X (4 + Cmax)`.
The rung needs ONE `Cw` for the whole family — i.e. `Cmax = sup_{d | m} C(d)` when `X`
is the full `chiFamily`.  This single theorem is the entire interface through which a
d-growing elementary Stepanov constant reaches `K(m) = 32(Cw(m−1)⁴+1)/m²`. -/
theorem fourthMomentTwistBound_of_tripleLinearHasseC_family
    (G : Finset F) (X : Finset (MulChar F ℂ)) (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (hCd0 : ∀ χ ∈ X, 0 ≤ Cd χ)
    (hCdmax : ∀ χ ∈ X, Cd χ ≤ Cmax)
    (hH : ∀ χ ∈ X, TripleLinearHasseC χ G (Cd χ))
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
      G X (4 + Cmax) := by
  intro χ hχ
  have hb := fourthMoment_le_of_quarticWeilInputC χ G
    (Cq := Cd χ + 1) (by linarith [hCd0 χ hχ])
    (quarticWeilInputC_of_tripleLinearHasseC χ G (hH χ hχ)) hp
  have hnn : (0 : ℝ) ≤ (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by positivity
  calc ∑ t : F,
        ‖ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.twistedThinSum χ G t‖ ^ 4
      = ∑ t : F, ‖shiftedCharSum χ G t‖ ^ 4 := by
        exact Finset.sum_congr rfl fun t _ => by
          rw [ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.norm_twistedThinSum_eq_shiftedCharSum]
    _ ≤ (3 + (Cd χ + 1)) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := hb
    _ ≤ (4 + Cmax) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
        have := hCdmax χ hχ
        nlinarith [hnn]

/-! ## 4. The d-fold assembly arithmetic (the norm-fold cost, exact) -/

/-- **THE d-FOLD BOUND** (abstract, the one new cost of the order-d family): if `val`
takes values in `{0} ∪ T` with `T` unit-modulus summing to zero (the d-th roots of
unity), each class fiber has `≤ B` points and the zero fiber `≤ z` points, then
`‖∑_s val s‖ ≤ |T|·B − q + z`.  With per-class Stepanov `B = q/d + E` this is `d·E + z`:
the fold costs ONE factor of `d` on the per-class EXCESS — the elementary order-d
constant is `C(d) = d·(per-class excess coefficient)`, linear in `d` from the fold. -/
theorem class_fold_bound {α : Type*} [Fintype α] [DecidableEq α]
    (val : α → ℂ) (T : Finset ℂ)
    (hT1 : ∀ c ∈ T, ‖c‖ = 1) (hT0 : (∑ c ∈ T, c) = 0)
    (hval : ∀ s, val s = 0 ∨ val s ∈ T)
    {B z : ℝ}
    (hB : ∀ c ∈ T, (((Finset.univ.filter fun s => val s = c).card : ℝ)) ≤ B)
    (hz : (((Finset.univ.filter fun s => val s = 0).card : ℝ)) ≤ z) :
    ‖∑ s, val s‖ ≤ (T.card : ℝ) * B - (Fintype.card α : ℝ) + z := by
  classical
  -- 0 ∉ T (unit modulus)
  have h0T : (0 : ℂ) ∉ T := by
    intro h
    have := hT1 0 h
    simp at this
  -- pointwise expansion over the class indicators
  have hpt : ∀ s, val s = ∑ c ∈ T, if val s = c then c else 0 := by
    intro s
    rcases hval s with h0 | hT
    · rw [h0]
      symm
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [if_neg]
      intro he
      exact h0T (he ▸ hc)
    · symm
      rw [Finset.sum_eq_single (val s)]
      · simp
      · intro c hc hne
        exact if_neg fun he => hne he.symm
      · intro habs
        exact absurd hT habs
  -- swap: ∑_s val s = ∑_{c∈T} c·N_c
  have hswap : (∑ s, val s)
      = ∑ c ∈ T, ((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℂ)) * c := by
    calc (∑ s, val s) = ∑ s, ∑ c ∈ T, if val s = c then c else 0 :=
          Finset.sum_congr rfl fun s _ => hpt s
      _ = ∑ c ∈ T, ∑ s, if val s = c then c else 0 := Finset.sum_comm
      _ = ∑ c ∈ T, ((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℂ)) * c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- subtract B per class (∑ c·B = 0)
  have hsub : (∑ s, val s)
      = ∑ c ∈ T, c * (((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ) : ℂ)
          - (B : ℂ)) := by
    have hzero : ∑ c ∈ T, c * (B : ℂ) = 0 := by
      rw [← Finset.sum_mul, hT0, zero_mul]
    calc (∑ s, val s)
        = ∑ c ∈ T, ((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℂ)) * c :=
          hswap
      _ = (∑ c ∈ T, c * (((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ) : ℂ)
            - (B : ℂ))) + ∑ c ∈ T, c * (B : ℂ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          push_cast
          ring
      _ = _ := by rw [hzero, add_zero]
  -- norm bound per class: ‖c(N_c − B)‖ = B − N_c
  have hnorm : ‖∑ s, val s‖
      ≤ ∑ c ∈ T, (B - (((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ)) := by
    rw [hsub]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun c hc => ?_)
    rw [norm_mul, hT1 c hc, one_mul]
    have hcast : (((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ) : ℂ) - (B : ℂ))
        = ((((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ)) - B : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hB c hc])]
    linarith
  -- total mass: q ≤ ∑_c N_c + z
  have hmass : (Fintype.card α : ℝ)
      ≤ (∑ c ∈ T, ((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ))) + z := by
    have hsubset : (Finset.univ : Finset α)
        ⊆ (Finset.univ.filter fun s => val s = 0)
          ∪ T.biUnion (fun c => Finset.univ.filter fun s => val s = c) := by
      intro s _
      rcases hval s with h0 | hT
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨val s, hT, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩)
    have hcard : Fintype.card α
        ≤ (Finset.univ.filter fun s => val s = 0).card
          + ∑ c ∈ T, (Finset.univ.filter fun s => val s = c).card := by
      calc Fintype.card α = (Finset.univ : Finset α).card := (Finset.card_univ).symm
        _ ≤ ((Finset.univ.filter fun s => val s = 0)
              ∪ T.biUnion (fun c => Finset.univ.filter fun s => val s = c)).card :=
            Finset.card_le_card hsubset
        _ ≤ (Finset.univ.filter fun s => val s = 0).card
              + (T.biUnion (fun c => Finset.univ.filter fun s => val s = c)).card :=
            Finset.card_union_le _ _
        _ ≤ _ := by
            have := Finset.card_biUnion_le
              (s := T) (t := fun c => Finset.univ.filter fun s => val s = c)
            omega
    have hcardR : (Fintype.card α : ℝ)
        ≤ (((Finset.univ.filter fun s => val s = 0).card : ℝ))
          + ∑ c ∈ T, ((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ)) := by
      exact_mod_cast hcard
    linarith
  calc ‖∑ s, val s‖
      ≤ ∑ c ∈ T, (B - (((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ)) := hnorm
    _ = (T.card : ℝ) * B
        - ∑ c ∈ T, ((((Finset.univ.filter fun s => val s = c).card : ℕ) : ℝ)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (T.card : ℝ) * B - (Fintype.card α : ℝ) + z := by linarith [hmass]

/-! ## 5. The triple-linear kernel's fiber structure -/

/-- The pointwise triple-linear kernel value (the summand of `tripleSum`). -/
noncomputable def tripleVal (χ : MulChar F ℂ) (u v w s : F) : ℂ :=
  χ ((u * s + 1) * (v * s + 1)) * conj' (χ (w * s + 1))

theorem tripleSum_eq_sum_tripleVal (χ : MulChar F ℂ) (u v w : F) :
    tripleSum χ u v w = ∑ s : F, tripleVal χ u v w s :=
  rfl

/-- **The zero fiber is ≤ 3** (unconditional): `tripleVal = 0` forces one of the three
linear factors to vanish, and each has at most one root. -/
theorem tripleVal_zero_fiber_card_le_three (χ : MulChar F ℂ) (u v w : F) :
    (((Finset.univ.filter fun s => tripleVal χ u v w s = 0).card : ℝ)) ≤ 3 := by
  classical
  have hsub : (Finset.univ.filter fun s => tripleVal χ u v w s = 0)
      ⊆ insert (-u⁻¹) (insert (-v⁻¹) ({-w⁻¹} : Finset F)) := by
    intro s hs
    have h0 : tripleVal χ u v w s = 0 := (Finset.mem_filter.mp hs).2
    -- if all three linear factors are nonzero, the value is a unit
    by_contra hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨hu, hv, hw⟩ := hmem
    have hlin : ∀ a : F, a * s + 1 = 0 → s = -a⁻¹ := by
      intro a h
      have ha0 : a ≠ 0 := by intro h'; rw [h'] at h; simp at h
      have hkey : s + a⁻¹ = a⁻¹ * (a * s + 1) := by
        rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
      rw [h, mul_zero] at hkey
      exact eq_neg_of_add_eq_zero_left hkey
    have hune : u * s + 1 ≠ 0 := fun h => hu (hlin u h)
    have hvne : v * s + 1 ≠ 0 := fun h => hv (hlin v h)
    have hwne : w * s + 1 ≠ 0 := fun h => hw (hlin w h)
    have hprod : (u * s + 1) * (v * s + 1) ≠ 0 := mul_ne_zero hune hvne
    have h1 : χ ((u * s + 1) * (v * s + 1)) * conj' (χ ((u * s + 1) * (v * s + 1))) = 1 :=
      mulChar_mul_conj χ hprod
    have h2 : χ (w * s + 1) * conj' (χ (w * s + 1)) = 1 :=
      mulChar_mul_conj χ hwne
    have hχ1 : χ ((u * s + 1) * (v * s + 1)) ≠ 0 := by
      intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
    have hχ2 : conj' (χ (w * s + 1)) ≠ 0 := by
      intro h; rw [h, mul_zero] at h2; exact zero_ne_one h2
    exact (mul_ne_zero hχ1 hχ2) h0
  have hcard : (Finset.univ.filter fun s => tripleVal χ u v w s = 0).card ≤ 3 := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_insert_le _ _) ?_
    have := Finset.card_insert_le (-v⁻¹) ({-w⁻¹} : Finset F)
    simp only [Finset.card_singleton] at this
    omega
  exact_mod_cast hcard

/-! ## 6. The d-analogue Stepanov interface and the conditional pipeline -/

/-- The order-d class fiber: points where the kernel takes the class value `c`. -/
noncomputable def NClassT (χ : MulChar F ℂ) (u v w : F) (c : ℂ) : Finset F :=
  Finset.univ.filter fun s => tripleVal χ u v w s = c

/-- **THE NAMED d-STEPANOV INTERFACE** (the d-analogue of `S2Output`, open input): for
every tuple and every class value `c ∈ T` (the d-th roots of unity hit by the kernel),
a NONZERO auxiliary polynomial vanishing to Hasse-order `m` on the class fiber with
total degree `≤ Dtot`.  The S2-lane machinery (`_R22StepanovS2`) is the `d = 2`,
`T = {1, −1}`-adjacent instance; the norm-fold construction mapped in
`_R22SuperellipticIndependence` is the route to producing this for 2-power `d ≥ 4`. -/
def DStepanovOutput (χ : MulChar F ℂ) (T : Finset ℂ) (m Dtot : ℕ) : Prop :=
  ∀ u v w : F, ∀ c ∈ T,
    ∃ P : F[X], P ≠ 0 ∧
      (∀ a ∈ NClassT χ u v w c, ∀ k < m, (Polynomial.hasseDeriv k P).eval a = 0) ∧
      P.natDegree ≤ Dtot

/-- `DStepanovOutput ⟹ m·#N_c ≤ Dtot` per class (the in-tree Stepanov engine verbatim). -/
theorem classCount_le_of_dStepanovOutput {T : Finset ℂ} {m Dtot : ℕ}
    (χ : MulChar F ℂ) (hS : DStepanovOutput χ T m Dtot)
    (u v w : F) {c : ℂ} (hc : c ∈ T) :
    m * (NClassT χ u v w c).card ≤ Dtot := by
  obtain ⟨P, hP0, hvan, hdeg⟩ := hS u v w c hc
  exact le_trans (hasseDeriv_stepanov_degree_count hP0 hvan) hdeg

/-- **The per-tuple order-d Stepanov bound**: class values (`T` unit-modulus, sum 0,
kernel values in `{0} ∪ T` — the character-order facts, supplied by the FACES lane),
`DStepanovOutput`, and the budget arithmetic
`|T|·(Dtot/m) − q + 3 ≤ C·√q` give `TripleLinearHasseC χ G C`.

With per-class `Dtot/m = q/d + E` (`|T| = d`) the budget reads `d·E + 3 ≤ C√q`:
**the elementary order-d constant is `C(d) = d·E/√q + o(1)` — linear in `d` times the
per-class excess coefficient.  The fold itself costs no `d²`.** -/
theorem tripleLinearHasseC_of_dStepanovOutput
    (χ : MulChar F ℂ) (G : Finset F) (T : Finset ℂ) {m Dtot : ℕ} {C : ℝ}
    (hm : 0 < m)
    (hT1 : ∀ c ∈ T, ‖c‖ = 1) (hT0 : (∑ c ∈ T, c) = 0)
    (hvals : ∀ u v w s : F, tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T)
    (hS : DStepanovOutput χ T m Dtot)
    (harith : (T.card : ℝ) * ((Dtot : ℝ) / (m : ℝ)) - (Fintype.card F : ℝ) + 3
      ≤ C * Real.sqrt (Fintype.card F)) :
    TripleLinearHasseC χ G C := by
  intro z _hz _hnd
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := z
  set u : F := b₂ - a₁
  set v : F := b₂ - a₂
  set w : F := b₂ - b₁
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hBc : ∀ c ∈ T, (((Finset.univ.filter fun s => tripleVal χ u v w s = c).card : ℝ))
      ≤ (Dtot : ℝ) / (m : ℝ) := by
    intro c hc
    have h := classCount_le_of_dStepanovOutput χ hS u v w hc
    have hR : (m : ℝ) * (((NClassT χ u v w c).card : ℝ)) ≤ (Dtot : ℝ) := by
      exact_mod_cast h
    rw [le_div_iff₀ hm']
    calc (((Finset.univ.filter fun s => tripleVal χ u v w s = c).card : ℝ)) * (m : ℝ)
        = (m : ℝ) * (((NClassT χ u v w c).card : ℝ)) := by rw [NClassT]; ring
      _ ≤ (Dtot : ℝ) := hR
  have hfold := class_fold_bound (val := fun s => tripleVal χ u v w s) T hT1 hT0
    (fun s => hvals u v w s) hBc (tripleVal_zero_fiber_card_le_three χ u v w)
  calc ‖tripleSum χ u v w‖
      = ‖∑ s : F, tripleVal χ u v w s‖ := by rw [tripleSum_eq_sum_tripleVal]
    _ ≤ (T.card : ℝ) * ((Dtot : ℝ) / (m : ℝ)) - (Fintype.card F : ℝ) + 3 := hfold
    _ ≤ C * Real.sqrt (Fintype.card F) := harith

/-! ## 7. THE AUDIT THEOREM: the normalized full-family gate is impossible -/

/-- **THE CONSTANT-ACCOUNTING AUDIT**: the normalized rung gate
`32(Cw·(m−1)⁴+1)/m²/3 ≤ 1` — the `hC` hypothesis of every full-family
(`|X| = |chiFamily χ| = m−1`) `*_of_constant_le_one` consumer in
`_R19ExplicitCharacterRung` — is IMPOSSIBLE for every `m ≥ 2` and every `Cw ≥ 1`,
INCLUDING the sharp Weil `Cw = 6`.  Consequence: polynomial growth of the elementary
per-order constant `C(d)` does not change which rung consumers fire — everything that
fires at Weil's uniform constant fires at any `poly(d)` elementary constant, and the
normalized full-family gate fires for neither.  The live gate consumers are the
subfamily-`Y` route (`15|Y|² ≤ m`), where the sup is over orders `≤ √(m/15)`. -/
theorem fullFamily_gate_impossible (m : ℕ) (hm : 2 ≤ m) {Cw : ℝ} (hCw : 1 ≤ Cw) :
    ¬ (32 * (Cw * (((m - 1 : ℕ) : ℝ)) ^ 4 + 1) / ((m : ℝ)) ^ 2 / 3 ≤ 1) := by
  intro h
  have hx : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    have h1 : 1 ≤ m := by omega
    push_cast [Nat.cast_sub h1]
    ring
  set x : ℝ := (m : ℝ) with hxdef
  rw [hcast, div_div] at h
  have h' : 32 * (Cw * (x - 1) ^ 4 + 1) ≤ x ^ 2 * 3 := by
    have := (div_le_one (by positivity : (0 : ℝ) < x ^ 2 * 3)).mp h
    linarith
  -- but 32·Cw·(x−1)⁴ + 32 > 3x² for x ≥ 2, Cw ≥ 1
  have hy : (1 : ℝ) ≤ x - 1 := by linarith
  have ht2 : (1 : ℝ) ≤ (x - 1) ^ 2 := by nlinarith
  have ht4 : (x - 1) ^ 2 ≤ (x - 1) ^ 4 := by nlinarith [sq_nonneg ((x - 1) ^ 2 - 1)]
  have hx2 : x ^ 2 ≤ 4 * (x - 1) ^ 2 := by nlinarith
  have hcw4 : (x - 1) ^ 4 ≤ Cw * (x - 1) ^ 4 := by
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ x - 1) 4]
  linarith

/-! ## 8. END-TO-END: the assembled conditional pipeline (all constants explicit) -/

/-- **THE PIPELINE (the lane deliverable)**: per-character `DStepanovOutput` supplies
(with class-value facts and budget arithmetic) the whole family's
`FourthMomentTwistBound G X (4 + Cmax)` — the r=2 rung at explicit weakened constant
`Cw = 4 + Cmax`, `Cmax = sup` of the per-character fold constants.  Every downstream
rung consumer takes `Cw` parametrically (r22 audit); the normalized full-family gate is
impossible at ANY `Cw ≥ 1` (`fullFamily_gate_impossible`), so nothing is lost. -/
theorem fourthMomentTwistBound_of_dStepanov_pipeline
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (T : MulChar F ℂ → Finset ℂ) (msteps Dtot : MulChar F ℂ → ℕ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (hm : ∀ χ ∈ X, 0 < msteps χ)
    (hT1 : ∀ χ ∈ X, ∀ c ∈ T χ, ‖c‖ = 1)
    (hT0 : ∀ χ ∈ X, (∑ c ∈ T χ, c) = 0)
    (hvals : ∀ χ ∈ X, ∀ u v w s : F,
      tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T χ)
    (hS : ∀ χ ∈ X, DStepanovOutput χ (T χ) (msteps χ) (Dtot χ))
    (harith : ∀ χ ∈ X,
      ((T χ).card : ℝ) * ((Dtot χ : ℝ) / (msteps χ : ℝ)) - (Fintype.card F : ℝ) + 3
        ≤ Cd χ * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ ∈ X, 0 ≤ Cd χ)
    (hCdmax : ∀ χ ∈ X, Cd χ ≤ Cmax)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
      G X (4 + Cmax) := by
  refine fourthMomentTwistBound_of_tripleLinearHasseC_family G X Cd hCd0 hCdmax
    (fun χ hχ => ?_) hp
  exact tripleLinearHasseC_of_dStepanovOutput χ G (T χ) (hm χ hχ)
    (hT1 χ hχ) (hT0 χ hχ) (hvals χ hχ) (hS χ hχ) (harith χ hχ)

end ArkLib.ProximityGap.Frontier.R24FullRungAssembly

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R24FullRungAssembly.tripleLinearHasseC_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R24FullRungAssembly.quarticWeilInputC_of_tripleLinearHasseC
#print axioms
  ArkLib.ProximityGap.Frontier.R24FullRungAssembly.fourthMomentTwistBound_of_tripleLinearHasseC_family
#print axioms ArkLib.ProximityGap.Frontier.R24FullRungAssembly.class_fold_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R24FullRungAssembly.tripleVal_zero_fiber_card_le_three
#print axioms
  ArkLib.ProximityGap.Frontier.R24FullRungAssembly.classCount_le_of_dStepanovOutput
#print axioms
  ArkLib.ProximityGap.Frontier.R24FullRungAssembly.tripleLinearHasseC_of_dStepanovOutput
#print axioms ArkLib.ProximityGap.Frontier.R24FullRungAssembly.fullFamily_gate_impossible
#print axioms
  ArkLib.ProximityGap.Frontier.R24FullRungAssembly.fourthMomentTwistBound_of_dStepanov_pipeline
