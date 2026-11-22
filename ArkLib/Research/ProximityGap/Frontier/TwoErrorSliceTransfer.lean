/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSlice

/-! # Transporting the two-error penalty between prescribed fields

A nonempty source profile has a representation as one tested ratio times
a pair of ratios. Preserving equalities between these products gives a single
auxiliary parameter bounding every local count in that source profile.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace ProximityGap.TwoErrorSlice
open Finset
variable {I J F K : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Field F] [Field K]

/-- Product comparisons needed in the two-error test. The singled-out site
can also occur in the two-site subset. -/
def PreservesRatioTripleAt (D : I ↪ F) (E : J ↪ K) (e : I ↪ J) (u v : I) : Prop :=
  let U := (univ.erase u).erase v
    ∀ x∈U, ∀ y∈U, ∀ A∈U.powersetCard 2, ∀ B∈U.powersetCard 2,
    ratio D u v x * (∏ i∈A, ratio D u v i) = ratio D u v y * (∏ i∈B, ratio D u v i) →
    ratio E (e u) (e v) (e x) * (∏ i∈A, ratio E (e u) (e v) (e i)) =
      ratio E (e u) (e v) (e y) * (∏ i∈B, ratio E (e u) (e v) (e i))

/-- Triple comparisons on every row required by the full penalty test. -/
def PreservesRatioTriple (D : I ↪ F) (E : J ↪ K) (e : I ↪ J) : Prop :=
  ∀ u v, u≠v → D u ≠ -D v → PreservesRatioTripleAt D E e u v

/-- A single fixed pair of base sites, tested at every nonzero row parameter. -/
def RowPenaltyBound (D : I ↪ F) (u v : I) : Prop :=
  ∀ μ : F, μ≠0 → (∑ x∈(univ.erase u).erase v,
    penalty (alternatives D u v (μ/ratio D u v x)).card) ≤ 12

private theorem penalty_mono : Monotone penalty := by
  intro a b hab
  unfold penalty
  split_ifs <;> omega

/-- Transfer one tested row. The auxiliary field, domain, and site relabeling
can be chosen separately for each source pair. -/
theorem rowPenaltyBound_transfer (D : I ↪ F) (E : J ↪ K) (e : I ↪ J) (u v : I)
    (htr : PreservesRatioTripleAt D E e u v) (hE : RowPenaltyBound E (e u) (e v)) :
    RowPenaltyBound D u v := by
  classical
  intro μ hμ
  let U := (univ.erase u).erase v
  let V := (univ.erase (e u)).erase (e v)
  let r (x : I) := ratio D u v x
  let s (y : J) := ratio E (e u) (e v) y
  let A (x : I) := alternatives D u v (μ/r x)
  have un (x : I) (h : x∈U) : u≠x ∧ v≠x :=
    ⟨(ne_of_mem_erase (mem_of_mem_erase h)).symm,(ne_of_mem_erase h).symm⟩
  have maps (x : I) (h : x∈U) : e x∈V := by
    obtain ⟨hu,hv⟩ := un x h
    exact mem_erase.mpr ⟨e.injective.ne hv.symm,mem_erase.mpr ⟨e.injective.ne hu.symm,mem_univ _⟩⟩
  have rn (x : I) (hx : x∈U) : r x≠0 := ratio_ne_zero _ (un x hx).1 (un x hx).2
  have sn (x : I) (hx : x∈U) : s (e x)≠0 :=
    ratio_ne_zero _ (e.injective.ne (un x hx).1) (e.injective.ne (un x hx).2)
  have repr {x : I} (hx : x∈U) {B : Finset I} (hB : B∈A x) :
      B∈U.powersetCard 2 ∧ r x * ∏ i∈B, r i = μ := by
    obtain ⟨hb,eq⟩ := mem_filter.mp hB
    exact ⟨hb,(mul_comm ..).trans ((eq_div_iff (rn x hx)).mp eq)⟩
  by_cases hex : ∃ x∈U, (A x).Nonempty
  · obtain ⟨x₀,hx₀,B₀,hB₀⟩ := hex
    let ν := s (e x₀) * ∏ i∈B₀, s (e i)
    have tref := repr hx₀ hB₀
    have hν : ν≠0 := mul_ne_zero (sn _ hx₀)
      (prod_ne_zero_iff.mpr fun i hi => sn _ ((mem_powersetCard.mp tref.1).1 hi))
    let A' (y : J) := alternatives E (e u) (e v) (ν/s y)
    have cap (x : I) (hx : x∈U) : (A x).card ≤ (A' (e x)).card := by
      apply card_le_card_of_injOn (fun B => B.map e) _ (Finset.map_injective e).injOn
      intro B hB
      have rep := repr hx hB
      obtain ⟨sub,card⟩ := mem_powersetCard.mp rep.1
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨?_,by simpa using card⟩,?_⟩
      · intro y hy
        obtain ⟨i,hi,rfl⟩ := mem_map.mp hy
        exact maps i (sub hi)
      · rw [Finset.prod_map]
        apply (eq_div_iff (sn _ hx)).mpr
        exact (mul_comm ..).trans (htr x hx x₀ hx₀ B rep.1 B₀ tref.1
          (rep.2.trans tref.2.symm))
    change ∑ x∈U, penalty (A x).card ≤ 12
    calc _ ≤ ∑ x∈U, penalty (A' (e x)).card := sum_le_sum fun x hx => penalty_mono (cap x hx)
         _ = ∑ y∈U.map e, penalty (A' y).card := by rw [sum_map]
         _ ≤ ∑ y∈V, penalty (A' y).card := by
           apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
           intro y hy
           obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
           exact maps x hx
         _ ≤ 12 := hE ν hν
  · have empty (x : I) (hx : x∈U) : A x=∅ :=
      not_nonempty_iff_eq_empty.mp (fun hn => hex ⟨x,hx,hn⟩)
    change ∑ x∈U, penalty (A x).card ≤ 12
    rw [sum_eq_zero (fun x hx => by simp [empty x hx,penalty])]
    decide

/-- An auxiliary penalty certificate transports along any site embedding
preserving nonantipodal tested pairs and equal ratio triples. -/
theorem penaltyBound_transfer (D : I ↪ F) (E : J ↪ K) (e : I ↪ J)
    (hanti : ∀ u v : I, u≠v → D u ≠ -D v → E (e u) ≠ -E (e v))
    (htr : PreservesRatioTriple D E e) (hE : PenaltyBound E) : PenaltyBound D := by
  intro u v huv hantiuv
  exact rowPenaltyBound_transfer D E e u v (htr u v huv hantiuv)
    (hE _ _ (e.injective.ne huv) (hanti _ _ huv hantiuv))

#print axioms rowPenaltyBound_transfer
#print axioms penaltyBound_transfer
end ProximityGap.TwoErrorSlice
