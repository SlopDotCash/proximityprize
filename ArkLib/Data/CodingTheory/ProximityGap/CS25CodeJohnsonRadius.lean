/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSListDecoding

/-!
# General code list-decodability up to the Johnson radius (#82)

The code-agnostic Johnson-radius theorem behind `rs_johnson_radius`: any code `𝒞` with minimum
distance `≥ d` is list-decodable up to its Johnson radius.  If the Johnson radius condition
`A² > T·B` holds (`A = (n−e) − n/q`, `B = (n−d) − n/q`, `T = n(1−1/q)`), the Archimedean property
supplies an `ℓ` discharging the Johnson quadratic, and `card_finset_le_of_johnson` then bounds every
list by `ℓ`.  Specialising `hmin`/`d` to the Reed–Solomon minimum distance recovers
`rs_johnson_radius`.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **General code list-decodability up to the Johnson radius (#82).** Any code `𝒞` with minimum
distance `≥ d` is list-decodable up to its Johnson radius: if `A² > T·B`
(`A = (n−e) − n/q`, `B = (n−d) − n/q`, `T = n(1−1/q)`), then some `ℓ` bounds the number of codewords
within distance `e` of every word. -/
theorem code_johnson_radius (𝒞 : Finset (ι → F)) (e d : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hradius :
      (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))) :
    ∃ ℓ : ℕ, ∀ w : ι → F, closeCount 𝒞 e w ≤ ℓ := by
  set A := ((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) with hA
  set B := ((Fintype.card ι - d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) with hB
  set T := (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) with hT
  have hden : 0 < A ^ 2 - T * B := by linarith [hradius]
  obtain ⟨ℓ, hℓ⟩ := exists_nat_gt ((T ^ 2 - A ^ 2) / (A ^ 2 - T * B))
  rw [div_lt_iff₀ hden] at hℓ
  refine ⟨ℓ, fun w => ?_⟩
  have hsq : ((ℓ : ℝ) + 1) * A ^ 2 > T * (T + (ℓ : ℝ) * B) := by nlinarith [hℓ]
  rw [closeCount]
  refine card_finset_le_of_johnson (d := d) hq1 hn w _ ℓ ?_ ?_ hP hsq
  · intro x hx; rw [Finset.mem_filter] at hx; rw [hammingDist_comm]; exact hx.2
  · intro x hx y hy hxy
    rw [Finset.mem_filter] at hx hy
    exact hmin x hx.1 y hy.1 hxy

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.code_johnson_radius
