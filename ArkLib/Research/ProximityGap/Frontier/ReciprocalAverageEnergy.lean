/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReciprocalChartMoments

/-! # Averaging additive energy over the pole of a reciprocal chart

At order r a non-diagonal pair of tuples can collide at at most 2r poles.
Keeping the count rather than requiring zero collisions permits fields of size
about n^r to give a factorial moment bound.
-/
set_option autoImplicit false
namespace ProximityGap.ReciprocalAverageEnergy
open Finset ReciprocalTupleEnergy ReciprocalChartMCA
open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq I] [Fintype F] in
/-- Write the energy of an embedded domain as a single count of index pairs. -/
theorem energy_as_pairs (y : I ↪ F) (r : ℕ) :
    rEnergy (univ.map y) r = ((univ : Finset ((Fin r → I) × (Fin r → I))).filter fun ab =>
      (∑ j, y (ab.1 j)) = ∑ j, y (ab.2 j)).card := by
  classical
  let e : (Fin r → I) ↪ (Fin r → F) :=
    ⟨fun a j => y (a j),fun _ _ he => funext fun j => y.injective (congrFun he j)⟩
  have ids : Fintype.piFinset (fun _ : Fin r => univ.map y) = univ.map e := by
    ext v
    constructor
    · intro h
      have each (j : Fin r) : ∃ i, y i = v j := by
        obtain ⟨i,_,eq⟩ := mem_map.mp (Fintype.mem_piFinset.mp h j)
        exact ⟨i,eq⟩
      choose a ha using each
      exact mem_map.mpr ⟨a,mem_univ _,funext ha⟩
    · intro h
      obtain ⟨a,_,rfl⟩ := mem_map.mp h
      exact Fintype.mem_piFinset.mpr fun j => mem_map.mpr ⟨a j,mem_univ _,rfl⟩
  simp only [rEnergy,ids,sum_map,Finset.card_filter,← univ_product_univ,sum_product]
  rfl

private theorem diagonal_bound (r : ℕ) :
    ((univ : Finset ((Fin r → I) × (Fin r → I))).filter fun ab =>
      ∀ i, count ab.1 i = count ab.2 i).card ≤ (Fintype.card I)^r*r.factorial := by
  classical
  let f (u : (Fin r → I) × Equiv.Perm (Fin r)) := (u.1,fun j => u.1 (u.2 j))
  have h : (univ.filter fun ab : (Fin r → I) × (Fin r → I) => ∀ i, count ab.1 i = count ab.2 i)
      ⊆ univ.image f := by
    rintro ⟨a,b⟩ hab
    obtain ⟨σ,hs⟩ := perm_of_count_eq a b (mem_filter.mp hab).2
    exact mem_image.mpr ⟨(a,σ),mem_univ _,Prod.ext rfl (funext hs)⟩
  exact (card_le_card h).trans (card_image_le.trans_eq (by simp [Fintype.card_perm]))

/-- There exists a chart with at most 2r n^(2r)/(p-n) additional ordered
tuple collisions beyond the diagonal upper bound, on every prime-field domain. -/
theorem prime_energy {p : ℕ} [Fact p.Prime] (x : I ↪ ZMod p) (r : ℕ)
    (hr : r<p) (hn : Fintype.card I<p) :
    ∃ t : ZMod p, (∀ i, t≠x i) ∧ rEnergy (univ.map (chart x t)) r ≤
      (Fintype.card I)^r*r.factorial + ((Fintype.card I)^r)^2*(2*r)/(p-Fintype.card I) := by
  classical
  let T : Finset (ZMod p) := (univ.map x)ᶜ
  let B := (univ : Finset ((Fin r → I) × (Fin r → I))).filter fun ab =>
    ¬ ∀ i, count ab.1 i = count ab.2 i
  let R (t : ZMod p) (ab : (Fin r → I) × (Fin r → I)) :=
    (∑ j, (t-x (ab.1 j))⁻¹) = ∑ j, (t-x (ab.2 j))⁻¹
  have free {t : ZMod p} (ht : t ∈ T) (i : I) : t ≠ x i := fun h =>
    (mem_compl.mp ht) (mem_map.mpr ⟨i,mem_univ _,h.symm⟩)
  have sizeT : T.card = p-Fintype.card I := by simp [T,card_compl]
  have pos : 0<T.card := sizeT ▸ Nat.sub_pos_of_lt hn
  have right (ab : (Fin r → I) × (Fin r → I)) (hb : ab ∈ B) :
      (T.bipartiteBelow R ab).card ≤ 2*r := by
    have h := (mem_filter.mp hb).2
    push Not at h
    obtain ⟨i,hi⟩ := h
    have small (a : Fin r → I) : count a i < p :=
      (show count a i ≤ r by simpa [count] using (card_filter_le (s:=univ) (fun j => a j=i))).trans_lt hr
    have ne : (count ab.1 i : ZMod p) ≠ (count ab.2 i : ZMod p) := by
      intro h
      apply hi
      simpa [ZMod.val_natCast_of_lt (small _)] using congrArg ZMod.val h
    apply (card_le_card ?_).trans (weighted_pair x ab.1 ab.2 ⟨i,ne⟩)
    intro t ht
    obtain ⟨ht,eq⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_univ _,free ht,eq⟩
  let deg (t : ZMod p) := (B.bipartiteAbove R t).card
  obtain ⟨t,ht,least⟩ := T.exists_min_image deg (card_pos.mp pos)
  have total : deg t*T.card ≤ ((Fintype.card I)^r)^2*(2*r) := by
    calc deg t*T.card = ∑ _ ∈ T, deg t := by simp [Nat.mul_comm]
         _ ≤ ∑ z ∈ T, (B.bipartiteAbove R z).card := sum_le_sum least
         _ = ∑ ab ∈ B, (T.bipartiteBelow R ab).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ..
         _ ≤ ∑ _ ∈ B, 2*r := sum_le_sum right
         _ ≤ _ := by
           simp only [sum_const,nsmul_eq_mul]
           apply Nat.mul_le_mul_right
           exact (card_le_card (filter_subset ..)).trans_eq (by simp [sq])
  have cap := (Nat.le_div_iff_mul_le pos).mpr total
  rw [sizeT] at cap
  let diag := (univ : Finset ((Fin r → I) × (Fin r → I))).filter fun ab =>
    ∀ i, count ab.1 i = count ab.2 i
  have sub : (univ.filter (R t)) ⊆ diag ∪ B.bipartiteAbove R t := by
    intro ab hab
    by_cases h : ∀ i, count ab.1 i = count ab.2 i
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h⟩,(mem_filter.mp hab).2⟩)
  refine ⟨t,free ht,?_⟩
  rw [energy_as_pairs]
  exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add (diagonal_bound r) cap))

/-- A chart giving the actual Gauss-sum moment bound, simultaneously for
every primitive additive character of the prime field. -/
theorem prime_moment {p : ℕ} [Fact p.Prime] (x : I ↪ ZMod p) (r : ℕ)
    (hr : r<p) (hn : Fintype.card I<p) :
    ∃ t : ZMod p, (∀ i, t≠x i) ∧ ∀ ψ : AddChar (ZMod p) ℂ, ψ.IsPrimitive →
      ∑ b : ZMod p, ‖ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
          (univ.map (chart x t)) b‖^(2*r) ≤
        (p : ℝ)*(((Fintype.card I)^r*r.factorial +
          ((Fintype.card I)^r)^2*(2*r)/(p-Fintype.card I) : ℕ) : ℝ) := by
  obtain ⟨t,ht,h⟩ := prime_energy x r hr hn
  refine ⟨t,ht,fun ψ hp => ?_⟩
  rw [subgroup_gaussSum_moment hp,ZMod.card]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast h

/-- The aggregate moment upper bound includes a field-size factor. In the
collision-free size regime its diagonal term
alone already exceeds the trivial bound n^(2r). -/
theorem diagonal_moment_cost (n p r : ℕ) (big : n^r ≤ p) :
    n^(2*r) ≤ p*(n^r*r.factorial) := by
  calc n^(2*r) = n^r*n^r := by rw [two_mul,pow_add]
       _ ≤ p*(n^r*r.factorial) := Nat.mul_le_mul big
         (Nat.le_mul_of_pos_right _ (Nat.factorial_pos r))

/-- At length 2³⁰ these moment bounds apply to orders five and eight on the
respective field-size ranges. Each counts ordered tuples with repetitions. -/
theorem production_caps (p : ℕ) :
    let n : ℕ := 2^30
    (2^158 ≤ p → n^5 * Nat.factorial 5 + (n^5)^2*10/(p-n) ≤ 121*n^5) ∧
    (2^245 ≤ p → n^8 * Nat.factorial 8 + (n^8)^2*16/(p-n) ≤ 40321*n^8) := by
  dsimp only
  constructor
  · intro hp
    have d : 2^158-2^30 ≤ p-2^30 := Nat.sub_le_sub_right hp _
    have bound := Nat.div_le_div_left d (by decide : 0 < 2^158-2^30) (a:=((2^30)^5)^2*10)
    exact (Nat.add_le_add_left bound _).trans (by decide)
  · intro hp
    have d : 2^245-2^30 ≤ p-2^30 := Nat.sub_le_sub_right hp _
    have bound := Nat.div_le_div_left d (by decide : 0 < 2^245-2^30) (a:=((2^30)^8)^2*16)
    exact (Nat.add_le_add_left bound _).trans (by decide)

end ProximityGap.ReciprocalAverageEnergy
#print axioms ProximityGap.ReciprocalAverageEnergy.prime_energy

#print axioms ProximityGap.ReciprocalAverageEnergy.production_caps

#print axioms ProximityGap.ReciprocalAverageEnergy.prime_moment
