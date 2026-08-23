/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentUpper
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentHighDist

/-!
# CS25 covered fraction for general linear codes (#82)

Combining the CS25 Paley-Zygmund inequality `(|𝒞|·V)² ≤ |close|·E[N²]` with the general
second-moment upper bound `E[N²] ≤ |𝒞|·|near|·V` (`sum_closeCount_sq_le`, `ballInterCount_zero_eq`)
yields the **covered-fraction lower bound for any linear code**

  `|𝒞| · |B(0,r)| ≤ |{w : Δ₀(w,𝒞) ≤ r}| · |{v∈𝒞 : Δ₀(0,v) ≤ 2r}|`,

i.e. `|close| ≥ |𝒞|·V / |near|`.  In the high-distance regime `|near| = 1` and this
recovers the exact bound `|close| ≥ |𝒞|·V`; in general the near-codeword count
`|near| = ∑_{d≤2r} A_d` (bounded by the MDS weight enumerator `card_evalWeight_le`) controls the
variance loss in the CS25 `ε_ca` covered-fraction argument.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Covered fraction × near-codeword count (general linear code).**  `|𝒞|·V ≤ |close|·|near|`,
where `V = |B(0,r)|`, `close = {w : Δ₀(w,𝒞) ≤ r}`, `near = {v∈𝒞 : Δ₀(0,v) ≤ 2r}` (provided
`|𝒞|·V > 0`).  Paley-Zygmund combined with the general second-moment upper bound. -/
theorem card_close_mul_near_ge (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞)
    (hpos : 0 < 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
          * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card := by
  have hpz := sq_card_mul_volume_le_card_close_mul_sum_sq 𝒞 r
  have hub := sum_closeCount_sq_le 𝒞 r hsub hadd
  set V := (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card with hV
  set C := (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card with hC
  set N := (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card with hN
  have key : (𝒞.card * V) ^ 2 ≤ (C * N) * (𝒞.card * V) := by
    calc (𝒞.card * V) ^ 2 ≤ C * (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2) := hpz
      _ ≤ C * (𝒞.card * (N * ballInterCount r (0 : ι → F))) :=
          Nat.mul_le_mul (Nat.le_refl C) hub
      _ = C * (𝒞.card * (N * V)) := by rw [ballInterCount_zero_eq]
      _ = (C * N) * (𝒞.card * V) := by ring
  rw [sq] at key
  exact Nat.le_of_mul_le_mul_right key hpos

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.card_close_mul_near_ge
