/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ManyHeadLocatorMass

/-! # Many-head attacks with unrestricted field size
The second-moment projection preserves a strict 1/Q budget violation as
soon as (Q−1) times the number of available keys reaches the field size.
-/
set_option autoImplicit false
namespace ProximityGap.LinearFieldProjectionBudget
open ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal

/-- A raw count at least q/(Q−1) exceeds the q/Q budget after projection. -/
theorem exceed {M q Q : ℕ} (hq : 0<q) (hQ : 1 < Q) (enough : q≤(Q-1)*M) :
    q/Q < AveragedPencilProjection.retained M q := by
  unfold AveragedPencilProjection.retained
  apply lt_of_lt_of_le _ (le_max_right ..)
  by_contra! h
  have raw := (ceilDiv_le_iff_le_mul (by omega : 0<q+1+(M-1))).mp h
  have pos : 0<M := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at enough;omega
  have factor : q+1+(M-1)=q+M := by omega
  rw [factor] at raw
  have hmul := Nat.mul_le_mul_right Q raw
  have div := Nat.div_mul_le_self q Q
  have high := Nat.mul_le_mul_right (q+M) div
  have low := Nat.mul_le_mul_right q enough
  obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le (show 1≤Q by omega)
  have qr : Q-1=s := by omega
  rw [qr] at low
  nlinarith only [hmul, high, low, hs, Nat.mul_pos pos (Nat.zero_lt_of_lt hQ),
    congrArg (fun a : ℕ => M*a*q) hs, congrArg (fun a : ℕ => M*a) hs]

/-- The same finite failure criterion works on every evaluation domain,
in every characteristic, for all field sizes. -/
theorem ceiling {F : Type} [Field F] [Fintype F] {n k e m Q : ℕ} [NeZero n]
    (x : Fin n ↪ F) (hk : 2≤k) (core : k+e+1≤n) (hm : 0 < m) (hQ : 1 < Q)
    (packing : m*(n-k+1-e) ≤ n-k+2) (budget : Fintype.card F≤(Q-1)*(m*(e+1))) :
    MCAThresholdLedger.mcaDeltaStar (F:=F) (ReedSolomon.code x k : Set (Fin n → F))
      (1/(Q:ℝ≥0∞)) ≤ (e:ℝ≥0)/n := by
  have ni : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  have h := ManyHeadLocatorMass.grid_mass (t:=n-e) x ((e:ℝ≥0)/n) hm hk (by omega) (by omega)
    (by rwa [show n-e-k+1=n-k+1-e by omega])
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ ni,←Nat.cast_tsub])
  rw [show n-(n-e)+1=e+1 by omega] at h
  apply MCAThresholdLedger.mcaDeltaStar_le_of_bad
  apply lt_of_lt_of_le _ h
  apply lt_of_not_ge
  rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega : 0<Q)]
  exact Nat.not_le_of_lt (exceed Fintype.card_pos hQ budget)

end ProximityGap.LinearFieldProjectionBudget
#print axioms ProximityGap.LinearFieldProjectionBudget.ceiling
