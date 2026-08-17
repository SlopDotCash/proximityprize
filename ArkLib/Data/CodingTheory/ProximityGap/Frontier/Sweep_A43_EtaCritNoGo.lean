/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
# Sweep_A43 — the η_crit no-go: the Action–Orbit / norm-bound route is vacuous at δ* (#444)

The even/odd descent (`Sweep_A40`) reduces the binding window list at radius `δ = 1−ρ−η` to a
dyadic lacunary count `#{size-s subsets T ⊆ μ_n : first c = ηn power sums vanish mod p}`. The
Action–Orbit norm bound (`Sweep_A10`, axiom-clean `badPrimeBound_core`) bounds a non-antipodal-
balanced defect `T` (`β_T = Σ_{x∈T} ζ^{idx(x)} ≠ 0`) by `p^{⌈c/2⌉} | N(β_T) ≤ s^{n/2}`. Even in
the **idealized** form that assumes full BGK √-cancellation `|σ_j(β_T)| ≤ √s` — the best the norm
route can ever give — the ceiling is `p ≤ s^{n/(2c)}`, i.e. the binding list is provably bounded
only when `log p > (1/2η)·log s`, equivalently `η > η_crit'` with (prize `log₂ p ≈ 128+μ`,
`n = 2^μ`, `s ≈ n`)

  `η_crit' = μ / (2·(128+μ))`.

But δ* sits at `η_{δ*} = c₀/μ` (KKH26: `η = Θ(1/log n)`, `c₀ = O(1)`). The no-go is the
**arithmetic fact** that `η_{δ*} < η_crit'` for every prize-scale `μ` and every realistic `c₀`,
so the norm route is **vacuous at δ\*** — it cannot pin δ\* *even if BGK were fully proven*.
(Numerically verified: defect conjugates have √-cancellation `|σ_j| ≈ √s`, and the corrected
exponent is `⌈c/2⌉` because only the odd residues mod `2^μ` are Galois automorphisms.)

This is a **no-go brick** (the route is structurally insufficient), not a δ\* result. Pure
arithmetic over `ℝ`; no `sorry`, no extra axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ArkLib.ProximityGap.Sweep_A43

/-- **The η_crit no-go kernel.** For prize scale `μ ≥ 25` and any KKH26 constant `0 < c₀ ≤ 2`,
the δ\* location `η_{δ*} = c₀/μ` is strictly below the idealized (full-BGK) norm-bound clean
threshold `η_crit' = μ/(2(128+μ))`. Hence the Action–Orbit / norm-bound route is vacuous at δ\*
even granting BGK √-cancellation: it is clean only for `η > η_crit'`, while δ\* needs `η = c₀/μ`. -/
theorem etacrit_norm_vacuous_at_deltastar (μ : ℕ) (hμ : 25 ≤ μ)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 2) :
    c₀ / (μ : ℝ) < (μ : ℝ) / (2 * (128 + (μ : ℝ))) := by
  have hμR : (25 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
  have hμpos : (0 : ℝ) < (μ : ℝ) := by linarith
  have hden : (0 : ℝ) < 2 * (128 + (μ : ℝ)) := by positivity
  -- numerator of `μ/(2(128+μ)) − c₀/μ` is positive
  have hbound : c₀ * (2 * (128 + (μ : ℝ))) ≤ 2 * (2 * (128 + (μ : ℝ))) :=
    mul_le_mul_of_nonneg_right hc₀' (by positivity)
  have hquad : 2 * (2 * (128 + (μ : ℝ))) < (μ : ℝ) * (μ : ℝ) := by
    nlinarith [hμR, mul_nonneg (show (0:ℝ) ≤ (μ:ℝ) - 25 by linarith)
                                (show (0:ℝ) ≤ (μ:ℝ) + 21 by linarith)]
  have hnum : 0 < (μ : ℝ) * (μ : ℝ) - c₀ * (2 * (128 + (μ : ℝ))) := by linarith
  have heq : (μ : ℝ) / (2 * (128 + (μ : ℝ))) - c₀ / (μ : ℝ)
      = ((μ : ℝ) * (μ : ℝ) - c₀ * (2 * (128 + (μ : ℝ)))) / ((μ : ℝ) * (2 * (128 + (μ : ℝ)))) := by
    field_simp
  have hpos : 0 < (μ : ℝ) / (2 * (128 + (μ : ℝ))) - c₀ / (μ : ℝ) := by
    rw [heq]; exact div_pos hnum (by positivity)
  linarith

/-- **The widening gap.** The slack `η_crit' − η_{δ*}` is strictly positive and increasing in `μ`
beyond prize scale: for `μ₂ > μ₁ ≥ 25` (and a fixed `c₀ ≤ 2`), the larger scale has a larger gap.
(Stated as the monotonicity of `η_crit' = μ/(2(128+μ))`, which → 1/2, while `η_{δ*} = c₀/μ` → 0.) -/
theorem etacrit_increasing (μ₁ μ₂ : ℕ) (h : μ₁ < μ₂) :
    (μ₁ : ℝ) / (2 * (128 + (μ₁ : ℝ))) < (μ₂ : ℝ) / (2 * (128 + (μ₂ : ℝ))) := by
  have h12 : (μ₁ : ℝ) < (μ₂ : ℝ) := by exact_mod_cast h
  have h1 : (0 : ℝ) ≤ (μ₁ : ℝ) := by positivity
  have d1 : (0 : ℝ) < 2 * (128 + (μ₁ : ℝ)) := by positivity
  have d2 : (0 : ℝ) < 2 * (128 + (μ₂ : ℝ)) := by positivity
  -- difference has numerator 128·(μ₂−μ₁) > 0
  have hnum : 0 < (μ₂ : ℝ) * (2 * (128 + (μ₁ : ℝ))) - (μ₁ : ℝ) * (2 * (128 + (μ₂ : ℝ))) := by
    nlinarith [h12, h1]
  have heq : (μ₂ : ℝ) / (2 * (128 + (μ₂ : ℝ))) - (μ₁ : ℝ) / (2 * (128 + (μ₁ : ℝ)))
      = ((μ₂ : ℝ) * (2 * (128 + (μ₁ : ℝ))) - (μ₁ : ℝ) * (2 * (128 + (μ₂ : ℝ))))
        / ((2 * (128 + (μ₁ : ℝ))) * (2 * (128 + (μ₂ : ℝ)))) := by
    field_simp
  have hpos : 0 < (μ₂ : ℝ) / (2 * (128 + (μ₂ : ℝ))) - (μ₁ : ℝ) / (2 * (128 + (μ₁ : ℝ))) := by
    rw [heq]; exact div_pos hnum (by positivity)
  linarith

end ArkLib.ProximityGap.Sweep_A43
