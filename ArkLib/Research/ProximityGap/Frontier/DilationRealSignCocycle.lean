/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment
import ArkLib.Data.CodingTheory.ProximityGap.CosetPeriodOrthogonal

/-!
# The dilation recursion is a REAL SIGN cocycle on the 2-power tower (#444)

This file **sharpens** the open L^∞-vs-L² gap of `SubgroupGaussSumDilationRecursion` by exploiting a
structural fact that file does not use: on the 2-power tower every subgroup `μ_{2^i}` (`i ≥ 1`) is
**negation-closed** (`-1 ∈ μ_{2^i}`), so by `eta_conj_eq` **every period `η_b(μ_{2^i})` is REAL**.

The recursion `eta_union_dilate` reads `η_b(G ⊔ ζ•G) = η_b(G) + η_{ζb}(G)`. When `G` is
negation-closed BOTH children are real numbers, so the "phase alignment" the open problem worries
about (`cos = 1` at the maximizer, an arbitrary complex angle) **collapses to a discrete SIGN**
`s_b := sgn(η_b(G) · η_{ζb}(G)) ∈ {+1, −1}`:

* **same sign** (`η_b(G)·η_{ζb}(G) ≥ 0`)  ⟹ the triangle bound is TIGHT: `|η_{i+1}| = |η_b| + |η_{ζb}|`
  (constructive doubling — the only way to keep the trivial `2·M` scaling).
* **opposite sign** (`η_b(G)·η_{ζb}(G) ≤ 0`) ⟹ genuine CANCELLATION:
  `|η_{i+1}| = | |η_b| − |η_{ζb}| | ≤ max(|η_b|, |η_{ζb}|) ≤ M` — the level does NOT double.

So the trivial `2·M` doubling is achieved at a level **iff** the two children agree in sign. The open
core (does any frequency keep the L^∞ on the `2`-scale all the way down the tower?) is thereby
reformulated from an arbitrary-phase cocycle to a **real ±1 sign cocycle**: a frequency stays on the
non-cancelling `2`-trajectory iff its descent signs are all `+`. This is a strictly sharper, fully
real localization of the residual BGK content; the open part is now exactly the sign-cocycle
large-deviation statement (no all-`+` descent path survives), not an arbitrary complex alignment.

PROBE (`scripts/probes/probe_dilation_cocycle.py`, `probe_dilation_realness.py`; exact `F_p`, proper
`μ_n = ⟨g^{(p−1)/n}⟩`, `n = 2^a`, `p ≫ n³`, NEVER `n = q−1`): `max|Im η_b(μ_{2^i})| < 7e-15` for
all `i ≥ 1` (reality confirmed to machine precision); the worst-frequency descent sign word is NOT
all-`+` in general (e.g. `n=32`: `+--++`, with a child magnitude dropping `1.41 → 0.59` at a `−`
rung — explicit per-level cancellation). The all-`+` (full-doubling) word is the non-generic case the
cocycle bound must exclude.

## Scope / honesty
This does NOT close CORE. It is a real-analysis structural sharpening of the recursion: it replaces
the arbitrary complex phase alignment with a discrete sign and proves the exact dichotomy
(same-sign ⟺ doubling, opposite-sign ⟹ cancellation to `≤ M`). The residual open content — that no
frequency has an all-same-sign descent on the tower — is the sign-cocycle reformulation of the BGK /
short-character-sum cancellation wall and stays OPEN. Thinness enters through the tower's
negation-closure (`-1 ∈ μ_{2^i}`, `i ≥ 1`), the structural input the reformulation rests on.

See `SubgroupGaussSumDilationRecursion` (the parent recursion) and `SubgroupGaussSumRawMoment`
(`eta_conj_eq`, the reality lemma).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

open scoped BigOperators
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A negation-closed `G` has a **real-valued** period: `η_b(G) = ((η_b(G)).re : ℂ)`. Repackages
`eta_conj_eq` (the `conj η_b = η_b` reality lemma) into the `re`-cast form used below. -/
theorem eta_eq_ofReal_re {ψ : AddChar F ℂ} (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    eta ψ G b = ((eta ψ G b).re : ℂ) := by
  have him : (eta ψ G b).im = 0 :=
    Complex.conj_eq_iff_im.mp (ArkLib.ProximityGap.SubgroupGaussSumRawMoment.eta_conj_eq G hG b)
  apply Complex.ext <;> simp [him]

/-- For a negation-closed `G`, the norm of a period equals the absolute value of its real part. -/
theorem norm_eta_eq_abs_re {ψ : AddChar F ℂ} (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    ‖eta ψ G b‖ = |(eta ψ G b).re| := by
  conv_lhs => rw [eta_eq_ofReal_re G hG b]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- The disjoint dilate union of a negation-closed `G` by a nonzero `ζ` is again negation-closed.
(`-(ζ·w) = ζ·(-w)` and `-w ∈ G`.) -/
theorem union_dilate_neg_closed (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) :
    ∀ z ∈ G ∪ dilate ζ G, -z ∈ G ∪ dilate ζ G := by
  intro z hz
  rcases Finset.mem_union.mp hz with h | h
  · exact Finset.mem_union_left _ (hG z h)
  · unfold dilate at h ⊢
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-w, hG w hw, by ring⟩)

/-- Real triangle cancellation: `|x + y| ≤ max |x| |y|` whenever `x·y ≤ 0`. -/
theorem abs_add_le_max_of_mul_nonpos {x y : ℝ} (h : x * y ≤ 0) :
    |x + y| ≤ max |x| |y| := by
  rcases le_total 0 x with hxs | hxs
  · rcases le_total 0 y with hys | hys
    · have : x * y = 0 := le_antisymm h (by positivity)
      rcases mul_eq_zero.mp this with hx0 | hy0
      · rw [hx0]; simp
      · rw [hy0]; simp
    · rw [abs_of_nonneg hxs, abs_of_nonpos hys]
      rcases le_total (x + y) 0 with hs | hs
      · rw [abs_of_nonpos hs]
        calc -(x + y) = -x + -y := by ring
          _ ≤ -y := by linarith
          _ ≤ max x (-y) := le_max_right _ _
      · rw [abs_of_nonneg hs]
        calc x + y ≤ x := by linarith
          _ ≤ max x (-y) := le_max_left _ _
  · rcases le_total 0 y with hys | hys
    · rw [abs_of_nonpos hxs, abs_of_nonneg hys]
      rcases le_total (x + y) 0 with hs | hs
      · rw [abs_of_nonpos hs]
        calc -(x + y) = -x + -y := by ring
          _ ≤ -x := by linarith
          _ ≤ max (-x) y := le_max_left _ _
      · rw [abs_of_nonneg hs]
        calc x + y ≤ y := by linarith
          _ ≤ max (-x) y := le_max_right _ _
    · have : x * y = 0 := le_antisymm h (by nlinarith)
      rcases mul_eq_zero.mp this with hx0 | hy0
      · rw [hx0]; simp
      · rw [hy0]; simp

/-- Real triangle equality: `|x + y| = |x| + |y|` whenever `x·y ≥ 0` (same sign). -/
theorem abs_add_eq_add_of_mul_nonneg {x y : ℝ} (h : 0 ≤ x * y) :
    |x + y| = |x| + |y| := by
  rcases le_total 0 x with hxs | hxs
  · rcases le_total 0 y with hys | hys
    · rw [abs_of_nonneg hxs, abs_of_nonneg hys, abs_of_nonneg (by linarith : (0:ℝ) ≤ x + y)]
    · -- x ≥ 0, y ≤ 0, x·y ≥ 0 ⟹ x·y = 0
      have hxy0 : x * y = 0 := le_antisymm (mul_nonpos_of_nonneg_of_nonpos hxs hys) h
      rcases mul_eq_zero.mp hxy0 with hx0 | hy0
      · rw [hx0]; simp
      · rw [hy0]; simp
  · rcases le_total 0 y with hys | hys
    · -- x ≤ 0, y ≥ 0, x·y ≥ 0 ⟹ x·y = 0
      have hxy0 : x * y = 0 := le_antisymm (mul_nonpos_of_nonpos_of_nonneg hxs hys) h
      rcases mul_eq_zero.mp hxy0 with hx0 | hy0
      · rw [hx0]; simp
      · rw [hy0]; simp
    · rw [abs_of_nonpos hxs, abs_of_nonpos hys, abs_of_nonpos (by linarith : x + y ≤ 0)]; ring

/-- **The real recursion.** For a negation-closed `G` and a nonzero dilation `ζ` with the dilate
disjoint, the union period's REAL PART is the exact real sum of the two children's real parts:
`(η_b(G ⊔ ζ•G)).re = (η_b(G)).re + (η_{ζb}(G)).re`. (Both children, and the union, are real.) -/
theorem union_re_eq {ψ : AddChar F ℂ} (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (dilate ζ G)) (b : F) :
    (eta ψ (G ∪ dilate ζ G) b).re = (eta ψ G b).re + (eta ψ G (ζ * b)).re := by
  rw [eta_union_dilate ψ G hζ hdisj b, Complex.add_re]

/-- **The sign dichotomy — cancellation branch.** If the two children have OPPOSITE sign
(`(η_b(G)).re · (η_{ζb}(G)).re ≤ 0`), the union period does NOT double; it is bounded by the larger
child: `‖η_b(G ⊔ ζ•G)‖ ≤ max ‖η_b(G)‖ ‖η_{ζb}(G)‖`. (Real cancellation `|x + y| ≤ max|x| |y|` when
`x·y ≤ 0`.) -/
theorem union_norm_le_max_of_opposite_sign {ψ : AddChar F ℂ} (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G)
    {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (b : F)
    (hopp : (eta ψ G b).re * (eta ψ G (ζ * b)).re ≤ 0) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ≤ max ‖eta ψ G b‖ ‖eta ψ G (ζ * b)‖ := by
  set x := (eta ψ G b).re with hx
  set y := (eta ψ G (ζ * b)).re with hy
  -- union norm = |x + y|
  have hunion : ‖eta ψ (G ∪ dilate ζ G) b‖ = |x + y| := by
    rw [norm_eta_eq_abs_re (G ∪ dilate ζ G) (union_dilate_neg_closed G hG hζ) b,
        union_re_eq G hG hζ hdisj b]
  -- |x + y| ≤ max |x| |y| when x·y ≤ 0
  have hxy : |x + y| ≤ max |x| |y| := abs_add_le_max_of_mul_nonpos hopp
  rw [hunion, norm_eta_eq_abs_re G hG b, norm_eta_eq_abs_re G hG (ζ * b)]
  exact hxy

/-- **The sign dichotomy — doubling branch (tightness).** If the two children have the SAME sign
(`0 ≤ (η_b(G)).re · (η_{ζb}(G)).re`), the triangle bound is TIGHT: the union period norm EQUALS the
sum of the children's norms, `‖η_b(G ⊔ ζ•G)‖ = ‖η_b(G)‖ + ‖η_{ζb}(G)‖`. So the only way a level keeps
the trivial `2·M` doubling is same-sign children. -/
theorem union_norm_eq_add_of_same_sign {ψ : AddChar F ℂ} (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G)
    {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (b : F)
    (hsame : 0 ≤ (eta ψ G b).re * (eta ψ G (ζ * b)).re) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ = ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖ := by
  set x := (eta ψ G b).re with hx
  set y := (eta ψ G (ζ * b)).re with hy
  rw [norm_eta_eq_abs_re (G ∪ dilate ζ G) (union_dilate_neg_closed G hG hζ) b,
      union_re_eq G hG hζ hdisj b,
      norm_eta_eq_abs_re G hG b, norm_eta_eq_abs_re G hG (ζ * b)]
  -- |x + y| = |x| + |y| when x·y ≥ 0
  exact abs_add_eq_add_of_mul_nonneg hsame

/-- **The trichotomy consumer for the tower bound.** Under a uniform bound `M` on the level-`i`
periods, the level-`(i+1)` period either CANCELS (opposite signs ⟹ `≤ M`, NOT doubling) or is at
most `2·M` (same signs ⟹ tight `= |η_b| + |η_{ζb}| ≤ 2M`). The `2·M` scaling is therefore confined
to the same-sign frequencies; this is the sign-cocycle form of the open L^∞ doubling. -/
theorem union_norm_le_M_of_opposite_sign {ψ : AddChar F ℂ} (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G)
    {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) {M : ℝ}
    (hM : ∀ c : F, ‖eta ψ G c‖ ≤ M) (b : F)
    (hopp : (eta ψ G b).re * (eta ψ G (ζ * b)).re ≤ 0) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ≤ M := by
  calc ‖eta ψ (G ∪ dilate ζ G) b‖
      ≤ max ‖eta ψ G b‖ ‖eta ψ G (ζ * b)‖ :=
        union_norm_le_max_of_opposite_sign G hG hζ hdisj b hopp
    _ ≤ M := max_le (hM b) (hM (ζ * b))

/-- **Same-sign branch under a child supremum.** If both child periods are bounded by `M`, then a
same-sign rung is still bounded by the trivial doubling envelope `2*M`. This is the formal
`2·M` half of the trichotomy advertised above. -/
theorem union_norm_le_two_mul_M_of_same_sign {ψ : AddChar F ℂ} (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {M : ℝ} (hM : ∀ c : F, ‖eta ψ G c‖ ≤ M) (b : F)
    (hsame : 0 ≤ (eta ψ G b).re * (eta ψ G (ζ * b)).re) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ≤ 2 * M := by
  rw [union_norm_eq_add_of_same_sign G hG hζ hdisj b hsame]
  nlinarith [hM b, hM (ζ * b)]

/-- **Exceedance forces a positive sign.** Under a uniform child-level bound `M`, any parent period
which exceeds `M` cannot lie on the cancellation branch. Hence it must have strictly positive child
real-product. This is the local caller-facing reduction of the open tower problem: every frequency
that grows past the previous-level supremum is trapped in the `+` sign cocycle. -/
theorem same_sign_of_M_lt_union_norm {ψ : AddChar F ℂ} (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {M : ℝ} (hM : ∀ c : F, ‖eta ψ G c‖ ≤ M) (b : F)
    (hbig : M < ‖eta ψ (G ∪ dilate ζ G) b‖) :
    0 < (eta ψ G b).re * (eta ψ G (ζ * b)).re := by
  by_contra hnot
  have hopp : (eta ψ G b).re * (eta ψ G (ζ * b)).re ≤ 0 := le_of_not_gt hnot
  exact (not_lt_of_ge (union_norm_le_M_of_opposite_sign G hG hζ hdisj hM b hopp)) hbig

/-- **The sign-balance law (the L²-budget identity that forces the cocycle).** For a negation-closed
`G` with disjoint dilate, the REAL signed cross-products sum to ZERO over all frequencies:
`∑_b (η_b(G)).re · (η_{ζb}(G)).re = 0`. This is the cross-orthogonality `coset_period_orthogonal`
(`∑_b η_b(G)·conj η_{ζb}(G) = 0`) with reality applied (`conj η_{ζb}(G) = η_{ζb}(G)`), read off the
real part. It is the EXACT reason the L² doubles by precisely `2` (the cross term vanishes), and it
constrains the sign cocycle: the `+`-sign (doubling) frequencies must be balanced against the
`−`-sign (cancelling) ones in the `|η|·|η|`-weighted aggregate — so a uniformly-`+` (full-doubling)
sign word over all frequencies is impossible. The open content is the WORST-CASE (single-frequency,
deep-descent) sign word, not this global average. -/
theorem sign_balance_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G)) :
    ∑ b : F, (eta ψ G b).re * (eta ψ G (ζ * b)).re = 0 := by
  -- reality: each summand's complex product is real and equals the real-part product.
  have hreal : ∀ b : F,
      eta ψ G b * (starRingEnd ℂ) (eta ψ G (ζ * b))
        = (((eta ψ G b).re * (eta ψ G (ζ * b)).re : ℝ) : ℂ) := by
    intro b
    rw [eta_eq_ofReal_re G hG b, eta_eq_ofReal_re G hG (ζ * b)]
    simp
  -- the cross-orthogonality (dilate uses the same `image (ζ * ·)` as `coset_period_orthogonal`).
  have horth :
      ∑ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G (ζ * b)) = 0 :=
    ArkLib.ProximityGap.CosetPeriodOrthogonal.coset_period_orthogonal hψ hdisj
  have hcast : (((∑ b : F, (eta ψ G b).re * (eta ψ G (ζ * b)).re) : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_sum, ← horth]
    exact Finset.sum_congr rfl (fun b _ => (hreal b).symm)
  exact_mod_cast hcast

/-- The dilated second moment is invariant: `∑_b ‖η_{ζb}(G)‖² = ∑_b ‖η_b(G)‖² = q·|G|`, by the
bijection `b ↦ ζb` (`ζ ≠ 0`). -/
theorem dilated_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) :
    ∑ b : F, ‖eta ψ G (ζ * b)‖ ^ 2 = (Fintype.card F : ℝ) * G.card := by
  have hbij : ∑ b : F, ‖eta ψ G (ζ * b)‖ ^ 2 = ∑ c : F, ‖eta ψ G c‖ ^ 2 := by
    apply Finset.sum_nbij' (fun b => ζ * b) (fun c => ζ⁻¹ * c)
    · intro b _; exact Finset.mem_univ _
    · intro c _; exact Finset.mem_univ _
    · intro b _; field_simp
    · intro c _; field_simp
    · intro b _; rfl
  rw [hbij, subgroup_gaussSum_secondMoment hψ G]

/-- **The total doubling-mass budget (Cauchy-Schwarz).** For a negation-closed `G` with nonzero
dilation, the total absolute cross-mass is bounded by the second moment:
`∑_b ‖η_b(G)‖·‖η_{ζb}(G)‖ ≤ q·|G|`. With the sign-balance law (which makes the signed cross sum to
`0`, so the `+`-mass equals the `−`-mass `= T`), this caps the doubling mass `T ≤ ½·q·|G|`. The
trivial `2`-scaling at a level can only be carried by a bounded total mass of frequencies, not by
all of them — quantifying the cocycle collapse. (Probe: realized `≈ 0.81·q·|G|`, and the all-`+`
descent set halves per level.) -/
theorem total_doublingMass_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) :
    ∑ b : F, ‖eta ψ G b‖ * ‖eta ψ G (ζ * b)‖ ≤ (Fintype.card F : ℝ) * G.card := by
  have hsq :
      (∑ b : F, ‖eta ψ G b‖ * ‖eta ψ G (ζ * b)‖) ^ 2
        ≤ (∑ b : F, ‖eta ψ G b‖ ^ 2) * ∑ b : F, ‖eta ψ G (ζ * b)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖eta ψ G b‖) (fun b => ‖eta ψ G (ζ * b)‖)
  rw [subgroup_gaussSum_secondMoment hψ G, dilated_secondMoment hψ G hζ] at hsq
  have hrhs : (Fintype.card F : ℝ) * G.card * ((Fintype.card F : ℝ) * G.card)
      = ((Fintype.card F : ℝ) * G.card) ^ 2 := by ring
  rw [hrhs] at hsq
  set S := ∑ b : F, ‖eta ψ G b‖ * ‖eta ψ G (ζ * b)‖ with hS
  set C := (Fintype.card F : ℝ) * G.card with hC
  have hnn : 0 ≤ S := Finset.sum_nonneg (fun b _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hrhsnn : 0 ≤ C := mul_nonneg (by positivity) (by positivity)
  -- from S^2 ≤ C^2, S ≥ 0, C ≥ 0 conclude S ≤ C
  nlinarith [hsq, hnn, hrhsnn, mul_nonneg hnn hrhsnn]

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
