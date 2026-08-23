/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The incidence = period identities (F1 = F2) — #407

This file makes the **far-line incidence** (face F1 of the open core,
`epsMCA_ge_far_incidence` / `LineIncidenceSpectral.lineIncidence_spectral`) *literally
equal*, term by term and in `L²`, to the **Gaussian-period spectrum** (face F2,
`SubgroupGaussSumSecondMoment.eta`, `η_b = ∑_{y∈G} ψ(b·y)`).

The syndrome space here is the field itself (`V = F`, one-dimensional), the geometry on
which the prize's far-coset attack lives.  The ball is the smooth subgroup `S = G = μ_n`,
the affine line is `γ ↦ s₀ + γ·s₁`, and the incidence is
`I(s₀, s₁) = #{γ ∈ F : s₀ + γ·s₁ ∈ G}`.

## The two identities

* **`lineIncidence_period_sum`** (a, the term-by-term Fourier-inversion form):

  > `I(s₀, s₁) = ∑_{b : b·s₁ = 0} conj(η_b) · ψ(b·s₀)`.

  The incidence equals a sum of *periods* `η_b`, restricted to the frequencies `b`
  annihilating the line's direction `s₁` (the spectral support of any γ-average).  Over
  `V = F` this support is `{0}` when `s₁ ≠ 0` (the line is all of `F`, incidence `= |G|`,
  matching `η₀ = |G|`) and *all* of `F` when `s₁ = 0` (the "line" is the point `s₀`,
  incidence `= q·[s₀∈G]`, the full Fourier inversion of `1_G`).  This is exactly the
  spectral mechanism of `LineIncidenceSpectral.lineIncidence_spectral` read off in the
  `η_b` basis: only the `s₁^⊥` frequencies survive the γ-average.

* **`incidence_l2_eq_period_l2`** (b, the L²/Parseval F1 = F2):

  > `∑_{s₀ ∈ F} I(s₀, 0)² = q · ∑_{b ∈ F} ‖η_b‖²`.

  Both sides equal `q²·|G|`: the left because `I(s₀,0) = q·[s₀∈G]` gives `q²·|G|`, the
  right because `∑_b ‖η_b‖² = q·|G|` (`subgroup_gaussSum_secondMoment`).  This is the
  L²-mass identity tying the incidence energy of the far-direction family to the total
  period energy — the quantitative skeleton of wall W4 (`charSum_l2_pairing`), now stated
  directly between the incidence count `I` and the period spectrum `η`.

Axiom-clean; pure additive-character orthogonality, no field-size or regime hypotheses.
Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.IncidencePeriodBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The far-line incidence over the field `V = F`.** The number of scalars `γ` for which
the point `s₀ + γ·s₁` of the affine line lands in the ball `G`. -/
noncomputable def lineIncidence (G : Finset F) (s₀ s₁ : F) : ℕ :=
  (Finset.univ.filter (fun γ : F => s₀ + γ * s₁ ∈ G)).card

set_option linter.unusedFintypeInType false in
omit [DecidableEq F] in
/-- `conj(η_b) = ∑_{y∈G} ψ(-(b·y))`. -/
theorem conj_eta {ψ : AddChar F ℂ} (G : Finset F) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [eta, map_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply]

/-- At the degenerate direction `s₁ = 0` the line is the constant point `s₀`, so the
incidence is `q·[s₀∈G]`. -/
theorem lineIncidence_zero_dir (G : Finset F) (s₀ : F) :
    lineIncidence G s₀ 0 = (if s₀ ∈ G then Fintype.card F else 0) := by
  classical
  unfold lineIncidence
  by_cases hmem : s₀ ∈ G
  · have : (Finset.univ.filter (fun γ : F => s₀ + γ * 0 ∈ G)) = Finset.univ := by
      apply Finset.filter_true_of_mem; intro γ _; simpa using hmem
    rw [this]; simp [hmem]
  · have : (Finset.univ.filter (fun γ : F => s₀ + γ * 0 ∈ G)) = ∅ := by
      apply Finset.filter_false_of_mem; intro γ _; simpa using hmem
    rw [this]; simp [hmem]

/-! ### Identity (a): incidence = period sum, term by term -/

/-- **The incidence–period term-by-term identity (F1 = F2, Fourier-inversion form).**
For a primitive additive character `ψ`, any ball `G`, and any affine line `s₀ + γ·s₁` in
`V = F`, the line–ball incidence equals the sum of periods over the frequencies `b`
annihilating the direction `s₁`:

  `I(s₀, s₁) = ∑_{b : b·s₁ = 0} conj(η_b) · ψ(b·s₀)`.

The trivial frequency `b = 0` always satisfies `b·s₁ = 0` and contributes the average
`η₀ = |G|`; the remaining `s₁^⊥` frequencies carry the spectral error.  This is the
mechanism of `LineIncidenceSpectral.lineIncidence_spectral` written in the `η_b` basis. -/
theorem lineIncidence_period_sum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) :
    (lineIncidence G s₀ s₁ : ℂ)
      = ∑ b ∈ Finset.univ.filter (fun b : F => b * s₁ = 0),
          (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀) := by
  classical
  -- Rewrite each summand of the RHS as a double sum over `y ∈ G`, then swap.
  have hterm : ∀ b ∈ Finset.univ.filter (fun b : F => b * s₁ = 0),
      (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)
        = ∑ y ∈ G, ψ (b * (s₀ - y)) := by
    intro b _
    rw [conj_eta, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [Finset.sum_congr rfl hterm]
  -- Swap the order: ∑_b ∑_{y∈G} = ∑_{y∈G} ∑_b
  rw [Finset.sum_comm]
  -- Now: ∑_{y∈G} ∑_{b: b·s₁=0} ψ(b·(s₀-y)).  Case on `s₁`.
  by_cases hs₁ : s₁ = 0
  · -- s₁ = 0: the constraint `b·s₁=0` is vacuous, so inner = ∑_{b∈F} ψ(b·(s₀-y)) = q·[s₀=y].
    subst hs₁
    have hfilt : (Finset.univ.filter (fun b : F => b * (0 : F) = 0)) = Finset.univ := by
      apply Finset.filter_true_of_mem; intro b _; simp
    rw [lineIncidence_zero_dir]
    -- inner sum over b (filter = univ): ∑_b ψ(b·(s₀-y)) = q·[s₀-y = 0]
    have hinner : ∀ y ∈ G, (∑ b ∈ Finset.univ.filter (fun b : F => b * (0:F) = 0),
        ψ (b * (s₀ - y))) = (if s₀ = y then (Fintype.card F : ℂ) else 0) := by
      intro y _
      rw [hfilt, AddChar.sum_mulShift (s₀ - y) hψ]
      simp only [sub_eq_zero]; split_ifs <;> simp
    rw [Finset.sum_congr rfl hinner]
    -- ∑_{y∈G} q·[s₀=y] = q·[s₀∈G]
    rw [Finset.sum_ite_eq G s₀ (fun _ => (Fintype.card F : ℂ))]
    by_cases hmem : s₀ ∈ G <;> simp [hmem]
  · -- s₁ ≠ 0: the constraint `b·s₁=0 ⟺ b=0`, so the filter is `{0}`, inner = ψ(0) = 1.
    have hfilt : (Finset.univ.filter (fun b : F => b * s₁ = 0)) = {0} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (mul_eq_zero.mp h).resolve_right hs₁
      · intro h; subst h; simp
    have hincid : lineIncidence G s₀ s₁ = G.card := by
      unfold lineIncidence
      -- γ ↦ s₀ + γ·s₁ is a bijection of F; its preimage of G has card |G|.
      have hinj : Function.Injective (fun γ : F => s₀ + γ * s₁) := by
        intro a b hab
        simp only at hab
        have : a * s₁ = b * s₁ := by linear_combination hab
        exact mul_right_cancel₀ hs₁ this
      rw [← Finset.card_image_of_injective _ hinj]
      congr 1
      ext z
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨γ, hγ, rfl⟩; exact hγ
      · intro hz
        refine ⟨(z - s₀) * s₁⁻¹, ?_, ?_⟩
        · have : (z - s₀) * s₁⁻¹ * s₁ = z - s₀ := by field_simp
          rw [this]; simpa using hz
        · have : (z - s₀) * s₁⁻¹ * s₁ = z - s₀ := by field_simp
          rw [this]; ring
    rw [hincid, hfilt]
    simp

/-! ### Identity (b): the L²/Parseval equality of incidence and period energy -/

/-- **The incidence–period L² identity (F1 = F2, Parseval form).** Summing the squared
incidence of the constant-direction family `s₁ = 0` over all offsets `s₀` equals `q` times
the total period energy:

  `∑_{s₀ ∈ F} I(s₀, 0)² = q · ∑_{b ∈ F} ‖η_b‖²`.

Both sides are `q²·|G|`: the left because `I(s₀,0) = q·[s₀∈G]`, the right because
`∑_b ‖η_b‖² = q·|G|` (`subgroup_gaussSum_secondMoment`).  This is the exact L²-mass
bridge between the far-line incidence energy and the Gaussian-period spectrum. -/
theorem incidence_l2_eq_period_l2 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) :
    (∑ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2)
      = (Fintype.card F : ℝ) * ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  classical
  -- RHS = q · (q·|G|) = q²·|G|
  rw [subgroup_gaussSum_secondMoment hψ G]
  -- LHS: I(s₀,0)² = q²·[s₀∈G], summed = q²·|G|
  have hL : ∀ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2
      = (if s₀ ∈ G then ((Fintype.card F : ℝ)) ^ 2 else 0) := by
    intro s₀
    rw [lineIncidence_zero_dir]
    by_cases hmem : s₀ ∈ G <;> simp [hmem]
  rw [Finset.sum_congr rfl (fun s₀ _ => hL s₀)]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

end ArkLib.ProximityGap.IncidencePeriodBridge

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence_period_sum
#print axioms ArkLib.ProximityGap.IncidencePeriodBridge.incidence_l2_eq_period_l2
