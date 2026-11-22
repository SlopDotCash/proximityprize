/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TangentHeadWindows

/-! # The second-prime eighth-rate predecessor of five eighths

The factor allocation below allows either four or five rich heads off a single
polynomial line. Its prices use the written tangent-section estimate.
-/
namespace ArkLib.ProximityGap.Frontier.EighthRichHeadSafety
open Finset Polynomial
set_option autoImplicit false

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 134217727
abbrev e : ℕ := 671088639
abbrev t : ℕ := n - e
abbrev c : ℕ := t - 8191
abbrev cutoff : ℕ := 81920

/-- Noncollinear quartets and five-head families have separate caps. Larger
families lie on a line and use the union lower bound for their rich cores. -/
def headBound (j : ℕ) : ℕ :=
  if j ≤ 3 then j * (e + 1)
  else
    let denominator := c + (j - 1) * d
    let covered := (j * c ^ 2 + denominator - 1) / denominator
    let cluster := min (j * (e + 1)) (j * n - (j - 1) * covered)
    max cluster (if j = 4 then 2125114027 else if j = 5 then 2125114028 else 0)

/-- The remaining factors share the weight of the first surface and the total
scalar/value degree of the second after the rich heads have been removed. -/
def price (l j b : ℕ) : ℕ :=
  TangentHeadWindows.factorPrice n d t cutoff (6 * t - 1 - (l - b) * d) (128 - j) b

/-- The strict affine cutoff, the geometric five-head tests, the Johnson
condition, and the identity-site test all hold for the chosen parameters. -/
theorem parameters :
    max (1 + e / 8192) (1 + 335 * 26 + 16 * 128) = cutoff ∧
    d + 128 * n / cutoff + 3 * (128 * n / (cutoff - 128)) < t ∧ n * d < t ^ 2 ∧
    3 * n + 20 * d < 15 * c ∧ 3 * n + 13 * d < 13 * c := by decide

private theorem prices : ∀ (l j b : Fin 17), j.val ≤ l.val →
    335 + headBound j.val ≤ 2147483648 ∧
    (0 < b.val → b.val ≤ l.val - j.val →
      (l.val - j.val) * price l.val j.val b.val ≤
        b.val * (2147483648 - (335 + headBound j.val))) := by
  set_option maxRecDepth 30000 in
  set_option maxHeartbeats 1000000 in
  decide

/-- All degree allocations fit the literal budget if the four-head
exception is absent. Scalar-only factors have a separate allowance of 335. -/
theorem all_allocations {ι : Type*} (S : Finset ι) (deg labels : ι → ℕ) (l j : Fin 17)
    (hj : j.val ≤ l.val) (hpos : ∀ a ∈ S, 0 < deg a)
    (hdeg : ∑ a ∈ S, deg a = l.val - j.val)
    (hcost : ∀ a ∈ S, labels a ≤ price l.val j.val (deg a)) :
    335 + headBound j.val + ∑ a ∈ S, labels a ≤ 2147483648 := by
  have bound := (prices l j 0 hj).1
  by_cases h : l.val - j.val = 0
  · have empty : S = ∅ := by
      by_contra hs
      obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr hs
      have hh := single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) ha
      rw [hdeg, h] at hh
      exact (hpos a ha).not_ge hh
    simpa [empty] using bound
  · apply TangentHeadWindows.sum_prices S deg labels (Nat.pos_of_ne_zero h) bound hdeg
    intro a ha
    have ha' := single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) ha
    rw [hdeg] at ha'
    let b : Fin 17 := ⟨deg a, ha'.trans_lt ((Nat.sub_le _ _).trans_lt l.isLt)⟩
    exact (Nat.mul_le_mul_left _ (hcost a ha)).trans ((prices l j b hj).2 (hpos a ha) ha')

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- Construct both mixed-Hasse interpolants on the actual two received rows. -/
theorem surfaces {F : Type} [Field F] {I : Type*} [Fintype I]
    (dom : I ↪ F) (u v : I → F) (hn : Fintype.card I = n) (second : Bool) :
    let r := if second then 9 else 6
    let b := if second then 26 else 16
    let s := if second then 128 else 335
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h + j ≤ s ∧ x + j * d < r * t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ B : Finset I, t ≤ B.card →
        (∀ x ∈ B, q.eval (dom x) = u x + z * v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  dsimp only
  let r := if second then 9 else 6
  let b := if second then 26 else 16
  let s := if second then 128 else 335
  have hnum : 0 < r ∧ 0 < t ∧ r ≤ s + 1 ∧
      Fintype.card I * Fintype.card (JetRows s r) < Fintype.card (Monomials s b d (r * t)) := by
    rw [hn]
    cases second <;>
      simp only [JetRows, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] <;>
      norm_num [Fin.sum_univ_succ, r, s, b, d, t, n, e] <;> decide +kernel
  obtain ⟨a, ha, _, hf⟩ := exists_surface dom u v hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2
  refine ⟨surface a, surface_ne_zero ha, fun _ _ _ h => surface_support a h, ?_⟩
  intro z q hq B hB hg
  rw [surface_eval]
  exact hf z q hq B hB hg

#print axioms all_allocations
#print axioms surfaces
end ArkLib.ProximityGap.Frontier.EighthRichHeadSafety
