/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

/-!
# Issue #317 brick: `baseFoldMatrix` determinant is nonzero (fiber distinctness)

The base fold matrix is `[[x₁, −x₀], [−1, 1]]` where `x₀, x₁` are the two single-step
`qMap` fiber points of `y`.  By the closed fiber form (`qMap_total_fiber_one_level_eq`),
`x_k = (k : 𝔽q) • basis_x 0 + lift y`, so `x₁ − x₀ = basis_x 0 ≠ 0` and
`det = x₁ − x₀ ≠ 0`.  This is the mathematical crux of `FoldMatrixDetNeZeroResidual`:
the recursive determinant factorizes as `±(x₁−x₀)^{2^n} · det M₀ · det M₁` (block
factorization), so nonsingularity reduces to this brick by induction.
-/

namespace Binius.BinaryBasefold

open AdditiveNTT

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- **Single-step fiber separation.**  The two `qMap` fiber points of `y` differ by exactly
the first basis vector of the source domain: `x₁ − x₀ = basis_x 0`. -/
lemma qMap_total_fiber_one_sub (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 1
      - qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 0
      = sDomain_basis 𝔽q β h_ℓ_add_R_rate i (by omega) ⟨0, by omega⟩ := by
  have hiℓ : i.val < ℓ := by omega
  have h1 := qMap_total_fiber_one_level_eq 𝔽q β (i := ⟨i.val, hiℓ⟩)
    (h_i_add_1 := h_le) (y := y) (k := 1)
  have h0 := qMap_total_fiber_one_level_eq 𝔽q β (i := ⟨i.val, hiℓ⟩)
    (h_i_add_1 := h_le) (y := y) (k := 0)
  simp only at h1 h0
  rw [h1, h0]
  simp [Fin2ToF2]

/-- **Base fold matrix determinant, closed form**: `det = x₁ − x₀ = basis_x 0` (in `L`). -/
lemma baseFoldMatrix_det (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    (baseFoldMatrix 𝔽q β i h_i y).det
      = ((sDomain_basis 𝔽q β h_ℓ_add_R_rate i (by omega) ⟨0, by omega⟩ :
          sDomain 𝔽q β h_ℓ_add_R_rate i) : L) := by
  rw [Matrix.det_fin_two]
  show ((qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) 1 :
        sDomain 𝔽q β h_ℓ_add_R_rate i) : L) * 1
      - (-(qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) 0 :
        sDomain 𝔽q β h_ℓ_add_R_rate i) : L) * (-1) = _
  have hsub := qMap_total_fiber_one_sub 𝔽q β i h_i h_le y
  have hcoe := congrArg
    (fun v : sDomain 𝔽q β h_ℓ_add_R_rate i => (v : L)) hsub
  push_cast at hcoe ⊢
  ring_nf
  ring_nf at hcoe
  linear_combination hcoe

/-- **Issue #317 crux brick: the base fold matrix is nonsingular** (within the `≤ ℓ` range
demanded by `FoldMatrixDetNeZeroResidual`). -/
theorem baseFoldMatrix_det_ne_zero (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡)
    (h_le : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    (baseFoldMatrix 𝔽q β i h_i y).det ≠ 0 := by
  rw [baseFoldMatrix_det 𝔽q β i h_i h_le y]
  have hb := (sDomain_basis 𝔽q β h_ℓ_add_R_rate i
    (show i.val < ℓ + 𝓡 by omega)).ne_zero ⟨0, by omega⟩
  exact fun hc => hb (by exact_mod_cast Subtype.ext hc)

end

end Binius.BinaryBasefold
