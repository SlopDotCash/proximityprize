/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCosetAmplification

/-!
# DQR-2/3: the exact two-scale period equation + the signed depth-14 dyadic ledger — #466

Opens the DQR renormalization angle of the 2026-07-11 centered attack matrix
(`deltastar-466-ten-by-ten-centered-attack-matrix`), cells DQR-2 (period two-scale equation)
and DQR-3 (centered-energy recursion), both previously ACTIVE with no landed content.

For the dyadic tower `G_{j+1} = G_j ⊔ a·G_j` (each level twice the last, e.g.
`μ_{2^{j+1}} = μ_{2^j} ⊔ a·μ_{2^j}` for any `a ∈ μ_{2^{j+1}} \ μ_{2^j}`):

* `eta_disjUnion` / `eta_smul_image` / `eta_two_scale` — **the exact two-scale equation**
  (DQR-2, now THEOREM): `η^{(j+1)}_b = η^{(j)}_b + η^{(j)}_{b·a}`. The relative phase of the
  matrix's formulation is absorbed exactly into the frequency dilation `b ↦ b·a`.

* `eta_im_zero` — **reality of the periods**: for multiplicatively closed `G` with `−1 ∈ G`,
  every `η_b` is a real number (`conj η_b = η_{−b} = η_b`). This is what makes the dyadic
  ledger SIGNED rather than absolute-valued: powers of `η` need no norm signs.

* `norm_pow_even_eq` — for real `η`, `‖η_b‖^{2r} = Re(η_b^{2r})`: even norm-moments ARE
  complex-analytic moments.

* `offZero_fourteenth_two_scale` — **the exact signed depth-14 dyadic ledger** (DQR-3, the
  recursion skeleton, now THEOREM): for the tower step `G' = G ⊔ aG`,

    `∑_{b≠0} η'^{14}_b = ∑_{k=0}^{14} C(14,k) · ∑_{b≠0} η_b^k · η_{b·a}^{14−k}`,

  an exact identity in ℂ with every term real. The `k = 0, 14` diagonal terms give twice the
  level-`j` moment (after frequency relabeling `b ↦ b·a⁻¹` on one side); the twelve cross
  terms `1 ≤ k ≤ 13` are the mixed moments whose sign structure is exactly the DQR-4/DQR-6
  contraction question. No absolute value is taken anywhere: the ledger preserves all
  cancellation, per the matrix's falsifier discipline (CTR-6/NWS-4 warn against absolute
  envelopes).

What this does NOT do: it does not prove contraction (DQR-4) — the cross-moment signs at the
production prime remain the open content. It converts the previously-informal recursion cell
into an exact machine-checked identity that any contraction argument must consume.
Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification

namespace ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The period is additive over disjoint unions of evaluation sets. -/
theorem eta_disjUnion (ψ : AddChar F ℂ) {G H : Finset F} (hdisj : Disjoint G H) (b : F) :
    eta ψ (G ∪ H) b = eta ψ G b + eta ψ H b := by
  unfold eta
  rw [Finset.sum_union hdisj]

/-- Dilating the evaluation set dilates the frequency: `η_{aG, b} = η_{G, b·a}` (`a ≠ 0`). -/
theorem eta_smul_image (ψ : AddChar F ℂ) (G : Finset F) {a : F} (ha : a ≠ 0) (b : F) :
    eta ψ (G.image (fun y => a * y)) b = eta ψ G (b * a) := by
  unfold eta
  rw [Finset.sum_image (fun y _ y' _ h => mul_left_cancel₀ ha h)]
  exact Finset.sum_congr rfl (fun y _ => by ring_nf)

/-- **The exact two-scale period equation (DQR-2).** For a dyadic tower step
`G' = G ⊔ a·G` (disjoint), every frequency satisfies `η'_b = η_b + η_{b·a}`. -/
theorem eta_two_scale (ψ : AddChar F ℂ) (G : Finset F) {a : F} (ha : a ≠ 0)
    (hdisj : Disjoint G (G.image (fun y => a * y))) (b : F) :
    eta ψ (G ∪ G.image (fun y => a * y)) b = eta ψ G b + eta ψ G (b * a) := by
  rw [eta_disjUnion ψ hdisj b, eta_smul_image ψ G ha b]

/-- **Reality of the periods**: multiplicatively closed `G` with `−1 ∈ G` has every `η_b`
real. (`conj η_b = η_{−b}`, and `−b ∈ b·G` so coset invariance closes it.) -/
theorem eta_im_zero {G : Finset F} (hG : MulClosed G) (hneg : (-1 : F) ∈ G)
    (ψ : AddChar F ℂ) (b : F) :
    (eta ψ G b).im = 0 := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : (starRingEnd ℂ) (eta ψ G b) = eta ψ G (b * -1) := by
    have hstep : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
      rw [eta, map_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
    rw [hstep, eta]
    exact Finset.sum_congr rfl (fun y _ => by ring_nf)
  have hcoset : eta ψ G (b * -1) = eta ψ G b := eta_mul_right hG ψ b hneg
  have hself : (starRingEnd ℂ) (eta ψ G b) = eta ψ G b := by rw [hconj, hcoset]
  have := Complex.conj_eq_iff_im.mp hself
  exact this

/-- Even norm-moments of a real period are complex-analytic moments:
`‖η_b‖^{2r} = Re (η_b^{2r})`. -/
theorem norm_pow_even_eq {z : ℂ} (hz : z.im = 0) (r : ℕ) :
    ‖z‖ ^ (2 * r) = (z ^ (2 * r)).re := by
  have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
  rw [hz', ← Complex.ofReal_pow, Complex.ofReal_re, Complex.norm_real]
  rw [pow_mul, pow_mul, Real.norm_eq_abs, sq_abs]

/-- **The exact signed depth-14 dyadic ledger (DQR-3 skeleton).** For a tower step
`G' = G ⊔ a·G` the off-zero fourteenth moment expands binomially with NO absolute values:

  `∑_{b≠0} (η'_b)^{14} = ∑_{k≤14} C(14,k) · ∑_{b≠0} η_b^k · η_{b·a}^{14−k}`.

Every quantity is a complex-analytic moment; when `G` is multiplicatively closed with
`−1 ∈ G` all terms are real, so this is the exact signed cross-moment decomposition that the
DQR-4 contraction question must consume. -/
theorem offZero_fourteenth_two_scale (ψ : AddChar F ℂ) (G : Finset F) {a : F} (ha : a ≠ 0)
    (hdisj : Disjoint G (G.image (fun y => a * y))) :
    ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ (G ∪ G.image (fun y => a * y)) b) ^ 14
      = ∑ k ∈ Finset.range 15, (Nat.choose 14 k : ℂ) *
          ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ (14 - k) := by
  have hterm : ∀ b ∈ Finset.univ.erase (0 : F),
      (eta ψ (G ∪ G.image (fun y => a * y)) b) ^ 14
        = ∑ k ∈ Finset.range 15, (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ (14 - k) *
            (Nat.choose 14 k : ℂ) := by
    intro b _
    rw [eta_two_scale ψ G ha hdisj b, add_pow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _ => by ring)

/-- **The exact pairing cross-correlation (new identity).** For any evaluation set `G` and
dilation `a` with `−a ∉ G·G⁻¹` — at a dyadic tower step, `−a ∉ G_j` since `−a ∈ aG_j` and the
cosets are disjoint — encoded pointwise as `y + a·z ≠ 0` on `G × G`:

  `∑_{b≠0} η_b · η_{b·a} = −|G|²`.

Consequence for the pair-and-sum renormalization flow: at every dyadic level the coset
involution `b ↦ b·a` pairs the spectrum with TOTAL cross-correlation exactly `−|G_j|²`
(per-pair average `−|G_j|/2` on the coset space) — the pairing is almost exactly orthogonal,
never coherent in the mean. Pure orthogonality; no open input. -/
theorem cross_correlation_exact {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (a : F)
    (hfree : ∀ y ∈ G, ∀ z ∈ G, y + a * z ≠ 0) :
    ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b * eta ψ G (b * a)
      = -((G.card : ℂ)) ^ 2 := by
  have hfull : ∑ b : F, eta ψ G b * eta ψ G (b * a) = 0 := by
    calc ∑ b : F, eta ψ G b * eta ψ G (b * a)
        = ∑ b : F, ∑ y ∈ G, ∑ z ∈ G, ψ (b * (y + a * z)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [eta, eta, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
          rw [← AddChar.map_add_eq_mul]
          ring_nf
      _ = ∑ y ∈ G, ∑ z ∈ G, ∑ b : F, ψ (b * (y + a * z)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
      _ = 0 := by
          refine Finset.sum_eq_zero (fun y hy => Finset.sum_eq_zero (fun z hz => ?_))
          rw [AddChar.sum_mulShift _ hψ]
          simp [hfree y hy z hz]
  have hzero : eta ψ G (0 : F) * eta ψ G ((0 : F) * a) = ((G.card : ℂ)) ^ 2 := by
    rw [zero_mul, ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.eta_zero]
    ring
  have hsplit : ∑ b : F, eta ψ G b * eta ψ G (b * a)
      = eta ψ G 0 * eta ψ G (0 * a)
        + ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b * eta ψ G (b * a) :=
    (Finset.add_sum_erase _ (fun b => eta ψ G b * eta ψ G (b * a)) (Finset.mem_univ 0)).symm
  rw [hsplit, hzero] at hfull
  linear_combination hfull

end ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion.eta_two_scale
#print axioms ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion.eta_im_zero
#print axioms ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion.norm_pow_even_eq
#print axioms
  ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion.offZero_fourteenth_two_scale
#print axioms
  ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion.cross_correlation_exact
