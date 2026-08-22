/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import Mathlib.Tactic

/-!
# Constant-weight Plotkin bound

For a finite family `S : I -> Finset U` of constant-weight `t` subsets with
distinct pair intersections at most `lambda`, coverage Cauchy--Schwarz and
the exact diagonal contribution give

```text
M * t^2 <= |U| * (t + (M-1) * lambda),
```

where `M = |I|`.  Rearranging without weakening the diagonal yields the
constant-weight Plotkin form

```text
M * (t^2 - |U| * lambda) <= |U| * (t - lambda).
```

When the gap `t^2 - |U|*lambda` is positive, division gives an explicit
cardinality bound.  The statements also cover an empty index type; the proof
separates that case before using a member of the family to derive `t <= |U|`.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound

/-- **Exact-diagonal constant-weight Johnson inequality.**  Constant weight
keeps the diagonal term equal to `t`, rather than replacing it by the ambient
universe cardinality. -/
theorem constantWeight_johnson
    {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (S : I → Finset U) (t lambda : Nat)
    (hsize : ∀ i, (S i).card = t)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ lambda) :
    Fintype.card I * t ^ 2 ≤
      Fintype.card U *
        (t + (Fintype.card I - 1) * lambda) := by
  classical
  let M := Fintype.card I
  let v := Fintype.card U
  change M * t ^ 2 ≤ v * (t + (M - 1) * lambda)
  have hsum : (∑ i, (S i).card) = M * t := by
    simp only [hsize, sum_const, card_univ, smul_eq_mul, M]
  have hinner : ∀ i : I,
      (∑ j, (S i ∩ S j).card) ≤
        t + (M - 1) * lambda := by
    intro i
    rw [← add_sum_erase univ
      (fun j => (S i ∩ S j).card) (mem_univ i)]
    apply Nat.add_le_add
    · simpa only [inter_self] using (hsize i).le
    · calc
        ∑ j ∈ univ.erase i, (S i ∩ S j).card
            ≤ ∑ _j ∈ univ.erase i, lambda := by
              apply sum_le_sum
              intro j hj
              have hji : j ≠ i := (mem_erase.mp hj).1
              exact hpair i j hji.symm
        _ = (M - 1) * lambda := by
          simp [M, card_erase_of_mem]
  have hupper :
      (∑ i, ∑ j, (S i ∩ S j).card) ≤
        M * (t + (M - 1) * lambda) := by
    calc
      (∑ i, ∑ j, (S i ∩ S j).card)
          ≤ ∑ _i : I, (t + (M - 1) * lambda) :=
            sum_le_sum fun i _ => hinner i
      _ = M * (t + (M - 1) * lambda) := by simp [M]
  have hmass := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter S
  rw [hsum] at hmass
  have hkey : (M * t) ^ 2 ≤
      v * (M * (t + (M - 1) * lambda)) :=
    hmass.trans (Nat.mul_le_mul le_rfl hupper)
  have hleft : (M * t) ^ 2 = M * (M * t ^ 2) := by ring
  have hright : v * (M * (t + (M - 1) * lambda)) =
      M * (v * (t + (M - 1) * lambda)) := by ring
  rw [hleft, hright] at hkey
  by_cases hM : M = 0
  · simp [hM]
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    exact Nat.le_of_mul_le_mul_left hkey hMpos

/-- **Constant-weight Plotkin inequality.**  The exact Johnson form
rearranges to

`M * (t^2 - |U|*lambda) <= |U| * (t-lambda)`.

Both subtractions are natural-number subtractions.  If either prospective
gap is nonpositive, the result follows from the constant-weight constraint;
otherwise the proof performs the exact diagonal/off-diagonal cancellation. -/
theorem constantWeight_plotkin
    {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (S : I → Finset U) (t lambda : Nat)
    (hsize : ∀ i, (S i).card = t)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ lambda) :
    Fintype.card I * (t ^ 2 - Fintype.card U * lambda) ≤
      Fintype.card U * (t - lambda) := by
  classical
  let M := Fintype.card I
  let v := Fintype.card U
  change M * (t ^ 2 - v * lambda) ≤ v * (t - lambda)
  by_cases hM : M = 0
  · simp [hM]
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  letI : Nonempty I := Fintype.card_pos_iff.mp (by simpa only [M] using hMpos)
  let i : I := Classical.choice inferInstance
  have ht_le_v : t ≤ v := by
    have hcard : (S i).card ≤ (univ : Finset U).card :=
      card_le_card (subset_univ (S i))
    simpa only [hsize i, card_univ, v] using hcard
  by_cases hlambda : lambda ≤ t
  · by_cases hgap : v * lambda ≤ t ^ 2
    · have hJ := constantWeight_johnson S t lambda hsize hpair
      have hJ' : M * t ^ 2 ≤ v * (t + (M - 1) * lambda) := by
        simpa only [M, v] using hJ
      have hMsplit : (M - 1) + 1 = M := by omega
      have hdiag : M * (v * lambda) =
          v * ((M - 1) * lambda) + v * lambda := by
        calc
          M * (v * lambda) = v * (M * lambda) := by ring
          _ = v * (((M - 1) + 1) * lambda) := by rw [hMsplit]
          _ = v * ((M - 1) * lambda) + v * lambda := by ring
      have hleftSplit : M * t ^ 2 =
          M * (t ^ 2 - v * lambda) + M * (v * lambda) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hgap]
      have hrightSplit : v * t = v * (t - lambda) + v * lambda := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hlambda]
      rw [hleftSplit] at hJ'
      rw [hdiag, Nat.mul_add, hrightSplit] at hJ'
      omega
    · have hzero : t ^ 2 - v * lambda = 0 := by omega
      simp [hzero]
  · have ht_lambda : t ≤ lambda := by omega
    have hsquare_le : t ^ 2 ≤ v * lambda := by
      rw [pow_two]
      exact Nat.mul_le_mul ht_le_v ht_lambda
    have hzero : t ^ 2 - v * lambda = 0 := Nat.sub_eq_zero_of_le hsquare_le
    simp [hzero]

/-- **Divided constant-weight Plotkin bound.**  A positive Plotkin gap gives
the explicit family-cardinality ceiling. -/
theorem constantWeight_plotkin_div
    {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (S : I → Finset U) (t lambda : Nat)
    (hsize : ∀ i, (S i).card = t)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ lambda)
    (hgap : Fintype.card U * lambda < t ^ 2) :
    Fintype.card I ≤
      (Fintype.card U * (t - lambda)) /
        (t ^ 2 - Fintype.card U * lambda) := by
  have hgapPos : 0 < t ^ 2 - Fintype.card U * lambda := by omega
  apply (Nat.le_div_iff_mul_le hgapPos).2
  exact constantWeight_plotkin S t lambda hsize hpair

#print axioms constantWeight_johnson
#print axioms constantWeight_plotkin
#print axioms constantWeight_plotkin_div

end ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound
