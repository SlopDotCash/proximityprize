/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import Mathlib.Analysis.Complex.Norm

/-!
# LANE R (#466 round 13): the signed hyperplane incidence sum — WORLD II certificate

The round-12 capstone (`_WallCapstone.lean`) localizes the prize to `WallHolds ∧
RealizedIncidenceBudget`, where the second conjunct is the naive-incidence glue and the honest note
says the genuine `M → δ*` step needs the **per-frequency √q·B cancellation**

  > `I_H(s₀) := ∑_{b ∈ H} conj(η_b) · ψ(b·s₀) ≲ √|H| · B`   over the frequency hyperplane `H`

(Paley / BCHKS Conj 1.12), which the wall's sup-norm bound `M = max_{b≠0}‖η_b‖` does **not** supply.
Round 13 settles rigorously whether that √-cancellation *follows* from `M` (World I: prize localizes
to `WallHolds` alone) or is a **distinct** open input (World II: prize = `WallHolds` ∧ a second Prop).

## The verdict: WORLD II — the sup-norm `M` controls the *average* over offsets, NOT the worst case.

This file isolates the exact quantitative reason. For an arbitrary frequency set `H ⊆ F`, define the
signed incidence sum `I_H(s₀) = ∑_{b∈H} conj(η_b) ψ(b·s₀)` (the general-hyperplane form of
`IncidencePeriodBridge.lineIncidence_period_sum`; the in-tree far-line incidence is the special case
`H = s₁^⊥`).  The **second-moment-over-offsets identity** proved here,

  > **`incidenceSum_sq_sum_offsets`** — `∑_{s₀ ∈ F} ‖I_H(s₀)‖² = q · ∑_{b ∈ H} ‖η_b‖²`,

is the *whole* of what `M` gives.  Dividing by `q`: the **average** over `s₀` of `‖I_H(s₀)‖²` is
exactly `∑_{b∈H}‖η_b‖² ≤ |H|·M²`, so the *average* offset has `‖I_H(s₀)‖ ≤ √|H|·M` — the √-cancelled
World-I scale.  But the far-coset adversary picks the **worst** `s₀`, and the worst can be `√|H|`
above the rms (a rare in-phase peak): probes `_out_466r13_incidence.txt` / `_mechanism.txt` measure
`worst‖I_H‖ ≈ |H|·M` (ratio `worst/(√|H|·M)` = 6.1 at |H|=2064, grows to 13.0 at |H|=32768 — i.e.
`∝ √|H|`, unbounded), while `worst/(|H|·M) ≈ 0.07–0.15` stays Θ(1).

**Why `M` cannot control the worst case (the counterexample-to-derivability).**  Replacing `{η_b}`
by any spectrum of *identical moduli* `‖η_b‖` but different phases leaves `M` and the whole RHS of
`incidenceSum_sq_sum_offsets` unchanged, yet collapses `worst‖I_H‖` from `≈|H|·M` down to the
√-scale (probe: ratio true/random-phase = 5.4 at |H|=2064, 13.2 at |H|=32768).  Hence
`worst_{s₀}‖I_H(s₀)‖` is **not a function of `M`** (nor of the moduli `{‖η_b‖}` at all): two spectra
with the *same* `M` have worst-case incidence differing by a factor `√|H|`.  The worst-case bound is
a genuinely finer object — a bound on the *signed/phased* hyperplane sum — that the sup-norm `M` (=
the wall's entire analytic payload, `WallHolds ⟹ M`) does not determine.

## Consequence for the capstone (honest statement, no closure claimed)

The prize does **NOT** localize to `WallHolds` alone.  It genuinely needs a **second, distinct**
open input, the worst-case hyperplane cancellation `∀ s₀, ‖I_H(s₀)‖ ≤ √|H|·M` (`= √q·B`,
Paley/BCHKS-1.12), which is not implied by `WallHolds` (the wall gives `M`, and `M` controls only
the *average* `I_H`, as this file's identity shows exactly).  `RealizedIncidenceBudget` in
`_WallCapstone.lean` is therefore correctly kept as a **separate named Prop**, not derivable from
`WallHolds`.  The prize is `WallHolds ∧ HyperplaneCancellation` — two inputs.

What this file lands axiom-clean: the second-moment identity that (i) makes the *average* World-I
bound rigorous and (ii) pins the *exact* place where `M` stops — the average/worst gap of size
`√|H|` that carries the phase information `M` lacks.

Issue #466, lane R (round 13).
-/

set_option autoImplicit false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R13HyperplaneSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The signed incidence sum over a frequency set `H`.**  `I_H(s₀) = ∑_{b∈H} conj(η_b) ψ(b·s₀)`.
For `H = {b : b·s₁ = 0}` this is exactly `IncidencePeriodBridge.lineIncidence_period_sum`'s RHS (the
far-line incidence); here `H` is arbitrary, modelling a genuine higher-dimensional frequency
hyperplane. -/
noncomputable def incidenceSum (ψ : AddChar F ℂ) (G : Finset F) (H : Finset F) (s₀ : F) : ℂ :=
  ∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)

/-- **The second-moment-over-offsets identity (WORLD-II certificate).**
`∑_{s₀ ∈ F} ‖I_H(s₀)‖² = q · ∑_{b ∈ H} ‖η_b‖²`.

This is the *whole* control the sup-norm `M` supplies over the signed hyperplane sum: dividing by
`q`, the **average** `(1/q)∑_{s₀}‖I_H(s₀)‖² = ∑_{b∈H}‖η_b‖² ≤ |H|·M²`, giving the World-I average
bound `‖I_H‖ ≤ √|H|·M`.  But the RHS is *phase-blind* (it depends only on the moduli `‖η_b‖`), so it
cannot see the worst-case in-phase peak the far-coset adversary selects — the worst `s₀` sits `√|H|`
above this rms (probes).  Hence `M` controls the average but **not** the worst case: WORLD II.

Proof: pure additive-character orthogonality (`AddChar.sum_mulShift`), the exact same mechanism as
`SubgroupGaussSumSecondMoment.subgroup_gaussSum_secondMoment` and
`IncidencePeriodBridge.incidence_l2_eq_period_l2`, here for a *general* frequency set `H`. -/
theorem incidenceSum_sq_sum_offsets {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (H : Finset F) :
    (∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2)
      = (Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  -- conj (ψ a) = ψ (-a)
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- Work over ℂ: ∑_{s₀} I(s₀)·conj(I(s₀)) = q · ∑_{b∈H} η_b·conj(η_b).
  -- First, ‖I‖² = I · conj I as a complex cast.
  have hnorm : ∀ s₀ : F,
      incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀)
        = ((‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ) := by
    intro s₀; rw [RCLike.mul_conj]; norm_cast
  -- Conjugate of the incidence sum expanded as a clean sum: conj I(s₀) = ∑_{b'} η_{b'} ψ(-(b'·s₀)).
  have hconjI : ∀ s₀ : F, (starRingEnd ℂ) (incidenceSum ψ G H s₀)
      = ∑ b' ∈ H, eta ψ G b' * ψ (-(b' * s₀)) := by
    intro s₀
    unfold incidenceSum
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [map_mul, Complex.conj_conj, hconj (b' * s₀)]
  -- The complex master identity.
  have hcomplex : (∑ s₀ : F,
      incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀))
        = (Fintype.card F : ℂ) * ∑ b ∈ H, eta ψ G b * (starRingEnd ℂ) (eta ψ G b) := by
    -- Expand each ‖I‖² into a double sum over (b, b') ∈ H × H; sum over s₀ collapses to q·[b = b'].
    calc ∑ s₀ : F, incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀)
        = ∑ s₀ : F, ∑ b ∈ H, ∑ b' ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ψ (s₀ * (b - b')) := by
          refine Finset.sum_congr rfl (fun s₀ _ => ?_)
          rw [hconjI s₀]
          unfold incidenceSum
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          refine Finset.sum_congr rfl (fun b' _ => ?_)
          have hpsi : ψ (b * s₀) * ψ (-(b' * s₀)) = ψ (s₀ * (b - b')) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1; ring
          calc (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀) * (eta ψ G b' * ψ (-(b' * s₀)))
              = ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (ψ (b * s₀) * ψ (-(b' * s₀))) := by
                ring
            _ = ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ψ (s₀ * (b - b')) := by rw [hpsi]
      _ = ∑ b ∈ H, ∑ b' ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ∑ s₀ : F, ψ (s₀ * (b - b')) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b' _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ b ∈ H,
            ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b) * (Fintype.card F : ℂ) := by
          refine Finset.sum_congr rfl (fun b hb => ?_)
          -- inner sum over b' ∈ H collapses at b' = b via sum_mulShift + sum_ite_eq'
          have hb' : ∀ b' ∈ H,
              ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * ∑ s₀ : F, ψ (s₀ * (b - b'))
                = (if b' = b then
                    ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (Fintype.card F : ℂ) else 0) := by
            intro b' _
            rw [AddChar.sum_mulShift (b - b') hψ]
            by_cases h : b = b'
            · subst h; simp
            · have hne : b - b' ≠ 0 := sub_ne_zero.mpr h
              rw [if_neg hne, if_neg (fun h' => h h'.symm)]
              simp
          rw [Finset.sum_congr rfl hb',
            Finset.sum_ite_eq' H b
              (fun b' => ((starRingEnd ℂ) (eta ψ G b) * eta ψ G b') * (Fintype.card F : ℂ))]
          rw [if_pos hb]
      _ = (Fintype.card F : ℂ) * ∑ b ∈ H, eta ψ G b * (starRingEnd ℂ) (eta ψ G b) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
  -- Cast back to the real second moment.
  have hcast : ((∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * ∑ b ∈ H, ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    rw [show (∑ s₀ : F, ((‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ))
          = ∑ s₀ : F, incidenceSum ψ G H s₀ * (starRingEnd ℂ) (incidenceSum ψ G H s₀) from
      Finset.sum_congr rfl (fun s₀ _ => (hnorm s₀).symm)]
    rw [hcomplex, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    congr 1
    rw [RCLike.mul_conj]; norm_cast
  have hreal : ((∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-- **World-I on AVERAGE (the derivable half): the average `‖I_H‖²` is bounded by `|H|·M²`.**
If every frequency in `H` has `‖η_b‖ ≤ M`, then `∑_{s₀}‖I_H(s₀)‖² ≤ q·|H|·M²`, i.e. the *average*
over offsets is `≤ |H|·M²`, so the *typical* offset has `‖I_H(s₀)‖ ≤ √|H|·M` (the √-cancelled World-I
scale).  This is the exact extent to which the wall's sup-norm bound `M` controls the signed
hyperplane sum — the AVERAGE only.  The worst-case (adversary's) offset is a *distinct*, strictly
larger functional (probes: `√|H|` above this), not implied by `M`. -/
theorem incidenceSum_sq_sum_le_of_supBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (H : Finset F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M) :
    (∑ s₀ : F, ‖incidenceSum ψ G H s₀‖ ^ 2)
      ≤ (Fintype.card F : ℝ) * ((H.card : ℝ) * M ^ 2) := by
  classical
  rw [incidenceSum_sq_sum_offsets hψ G H]
  have hsum : (∑ b ∈ H, ‖eta ψ G b‖ ^ 2) ≤ (H.card : ℝ) * M ^ 2 := by
    calc (∑ b ∈ H, ‖eta ψ G b‖ ^ 2)
        ≤ ∑ _b ∈ H, M ^ 2 := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          have h1 : ‖eta ψ G b‖ ≤ M := hM b hb
          have h0 : 0 ≤ ‖eta ψ G b‖ := norm_nonneg _
          nlinarith [h1, h0]
      _ = (H.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hsum hq

/-- **The pointwise triangle bound (the trivial worst-case scale).**  If every frequency in `H`
has `‖η_b‖ ≤ M`, then every individual offset satisfies
`‖I_H(s₀)‖ ≤ |H|·M`.

Together with `incidenceSum_sq_sum_le_of_supBound`, this pins the exact missing gain in the
prize-facing hyperplane-cancellation input: `M` gives the `√|H|·M` scale only on average, while
the unconditional pointwise consequence of the same sup-bound is the larger `|H|·M` triangle scale.
The open `HyperplaneCancellation` input is precisely the extra square-root cancellation between
these two bounds. -/
theorem incidenceSum_norm_le_card_mul_supBound {ψ : AddChar F ℂ}
    (G : Finset F) (H : Finset F) {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : ∀ b ∈ H, ‖eta ψ G b‖ ≤ M) (s₀ : F) :
    ‖incidenceSum ψ G H s₀‖ ≤ (H.card : ℝ) * M := by
  classical
  unfold incidenceSum
  calc
    ‖∑ b ∈ H, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)‖
        ≤ ∑ b ∈ H, ‖(starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)‖ := by
          exact norm_sum_le _ _
    _ = ∑ b ∈ H, ‖eta ψ G b‖ := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          simp [ψ.norm_apply]
    _ ≤ ∑ _b ∈ H, M := by
          exact Finset.sum_le_sum (fun b hb => hM b hb)
    _ = (H.card : ℝ) * M := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- **The triangle scale is sharp for coherent bounded coefficients.**  If the coefficients on
`H` all have the same phase and modulus `M`, then the triangle bound is attained exactly:
`‖∑_{b∈H} M‖ = |H|·M`.

This is deliberately stated for arbitrary coherent coefficients, not for Gauss periods.  It records
the formal obstruction to any route that tries to upgrade
`incidenceSum_norm_le_card_mul_supBound` to the square-root scale from only the hypotheses
`‖coefficient_b‖ ≤ M`: the improvement must use additional arithmetic/phase information about
the actual Gauss-period spectrum. -/
theorem coherent_coefficients_attain_triangle_scale (H : Finset F) {M : ℝ} (hM0 : 0 ≤ M) :
    ‖∑ _b ∈ H, (M : ℂ)‖ = (H.card : ℝ) * M := by
  classical
  have hcard_nonneg : (0 : ℝ) ≤ (H.card : ℝ) := by positivity
  have hprod_nonneg : 0 ≤ (H.card : ℝ) * M := mul_nonneg hcard_nonneg hM0
  have hsum : ∑ _b ∈ H, (M : ℂ) = (((H.card : ℝ) * M : ℝ) : ℂ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    norm_num [Complex.ofReal_mul]
  rw [hsum]
  exact Complex.norm_of_nonneg hprod_nonneg

end ArkLib.ProximityGap.Frontier.R13HyperplaneSecondMoment

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R13HyperplaneSecondMoment.incidenceSum_sq_sum_offsets
#print axioms
  ArkLib.ProximityGap.Frontier.R13HyperplaneSecondMoment.incidenceSum_sq_sum_le_of_supBound
#print axioms
  ArkLib.ProximityGap.Frontier.R13HyperplaneSecondMoment.incidenceSum_norm_le_card_mul_supBound
#print axioms
  ArkLib.ProximityGap.Frontier.R13HyperplaneSecondMoment.coherent_coefficients_attain_triangle_scale
