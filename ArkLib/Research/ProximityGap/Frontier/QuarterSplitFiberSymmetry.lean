/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusSubgroupBound
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # Source symmetries of the first-prime quarter-rate split pencil -/

namespace ProximityGap.QuarterSplitFiberSymmetry

open Finset MobiusSeamCoordinateSupply

variable {F : Type*} [Field F]

/-- A scaling preserving a complete fiber has order dividing both its size and the
subgroup order. At the quarter successor the only choices are the identity and negation. -/
theorem scaling {S : Finset F} (size : S.card = 268435454)
    (roots : ∀ x ∈ S, x ^ (2 ^ 30 : ℕ) = 1) {u : F}
    (stable : ∀ x ∈ S, u * x ∈ S) : u = 1 ∨ u = -1 := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < S.card by omega)
  have hun := roots _ (stable x hx)
  rw [mul_pow, roots x hx, mul_one] at hun
  have hu : u ≠ 0 := by intro hz; simp [hz] at hun
  have heq : S.image (u * ·) = S :=
    eq_of_subset_of_card_le (image_subset_iff.mpr stable)
      (by rw [card_image_of_injective _ (mul_right_injective₀ hu)])
  have hprod : (∏ z ∈ S, u * z) = ∏ z ∈ S, z := by
    conv_rhs => rw [← heq]
    rw [prod_image (mul_right_injective₀ hu).injOn]
  have hnz : (∏ z ∈ S, z) ≠ 0 := prod_ne_zero_iff.mpr fun z hz h => by
    simpa [h] using roots z hz
  rw [prod_mul_distrib, prod_const, size] at hprod
  have hud : u ^ 268435454 = 1 := mul_left_cancel₀ hnz (by simpa [mul_comm] using hprod)
  have hord := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hun) (orderOf_dvd_of_pow_eq_one hud)
  change orderOf u ∣ 2 at hord
  exact sq_eq_one_iff.mp (orderOf_dvd_iff_pow_eq_one.mp hord)

/-- Every nonsingular source map preserving one of the three complete fibers acts on
the affine line by the identity, negation, or a scaled reciprocal with coefficient in
the order-`2^30` subgroup. This works over extensions of the named prime field. -/
theorem classify {p : ℕ} [CharP F p] (hp : p.Prime) (large : 2 ^ 40 < p)
    (S : Finset F) (size : S.card = 268435454)
    (roots : ∀ x ∈ S, x ^ (2 ^ 30 : ℕ) = 1)
    (g : Mobius F) (nonsing : g.det ≠ 0) (stable : ∀ x ∈ S, g.value x ∈ S) :
    (∀ x, g.value x = x) ∨ (∀ x, g.value x = -x) ∨
      ∃ u : F, u ^ (2 ^ 30 : ℕ) = 1 ∧ ∀ x, g.value x = u / x := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < S.card by omega)
  have cases : (g.b = 0 ∧ g.c = 0) ∨ (g.a = 0 ∧ g.d = 0) := by
    by_contra! h
    have noDiag : g.b ≠ 0 ∨ g.c ≠ 0 := by tauto
    have noAnti : g.a ≠ 0 ∨ g.d ≠ 0 := by tauto
    have bound := MobiusSubgroupBound.production_graph hp large
      (fun z : S => z.val) (fun z : S => g.value z.val) Subtype.val_injective
      (fun z => roots _ z.property) (fun z => roots _ (stable _ z.property))
      nonsing noDiag noAnti (by
        intro z
        have hd : g.den z.val ≠ 0 := by
          intro zero
          have hy := roots _ (stable _ z.property)
          simp [Mobius.value, zero] at hy
        exact (div_mul_cancel₀ _ hd).symm)
    rw [Fintype.card_coe, size] at bound
    omega
  rcases cases with ⟨hb, hc⟩ | ⟨ha, hd⟩
  · have act (z : F) : g.value z = (g.a / g.d) * z := by
      simp [Mobius.value, Mobius.num, Mobius.den, hb, hc, div_eq_mul_inv, mul_right_comm]
    rcases scaling size roots (fun z hz => act z ▸ stable z hz) with h | h
    · exact Or.inl fun z => by simp [act, h]
    · exact Or.inr (Or.inl fun z => by simp [act, h])
  · have act (z : F) : g.value z = (g.b / g.c) / z := by
      simp [Mobius.value, Mobius.num, Mobius.den, ha, hd, div_eq_mul_inv, mul_comm, mul_left_comm]
    refine Or.inr (Or.inr ⟨_, ?_, act⟩)
    have h := roots _ (stable x hx)
    rwa [act, div_pow, roots x hx, div_one] at h

/-- Squaring halves the size of a negation-stable set of nonzero sites in odd
characteristic. The two preimages over each squared site are opposites. -/
private theorem square_image [DecidableEq F] {S : Finset F} (two : (2 : F) ≠ 0)
    (nonzero : ∀ x ∈ S, x ≠ 0) (neg : ∀ x ∈ S, -x ∈ S) :
    S.card = (S.image (fun x => x ^ 2)).card * 2 := by
  let f (x : F) := x ^ 2
  calc
    S.card = ∑ y ∈ S.image f, (S.filter (fun z => f z = y)).card :=
      card_eq_sum_card_fiberwise (fun z hz => mem_image_of_mem f hz)
    _ = _ := by
      rw [sum_congr rfl (g := fun _ => 2) ?_, sum_const, smul_eq_mul]
      rintro y hy
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
      have hz' : z ≠ -z := fun h => nonzero z hz
        ((mul_eq_zero.mp (show 2 * z = 0 by linear_combination h)).resolve_left two)
      have heq : S.filter (fun w => f w = f z) = {z, -z} := by
        ext w
        simp only [mem_filter, mem_insert, mem_singleton, f, sq_eq_sq_iff_eq_or_eq_neg]
        constructor
        · exact And.right
        · rintro (rfl|rfl)
          · exact ⟨hz, Or.inl rfl⟩
          · exact ⟨neg _ hz, Or.inr rfl⟩
      rw [heq, card_pair hz']

/-- A reciprocal involution preserving an odd set has a fixed point in that set. -/
private theorem reciprocal_fixed (S : Finset F) (odd : ¬2 ∣ S.card) {u : F} (hu : u ≠ 0)
    (stable : ∀ x ∈ S, u / x ∈ S) :
    ∃ x ∈ S, x ^ 2 = u ∨ x = 0 := by
  classical
  let i : Equiv.Perm S :=
    { toFun := fun x => ⟨u / x.val, stable _ x.property⟩
      invFun := fun x => ⟨u / x.val, stable _ x.property⟩
      left_inv := fun x => Subtype.ext (by simp [hu])
      right_inv := fun x => Subtype.ext (by simp [hu]) }
  have hi : i ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two, i, hu]
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
    (by simpa only [Fintype.card_coe] using odd) hi
  have eq : u / x.val = x.val := congrArg Subtype.val hx
  refine ⟨_, x.property, ?_⟩
  by_cases zero : x.val = 0
  · exact Or.inr zero
  · exact Or.inl (by rw [pow_two]; exact ((div_eq_iff zero).mp eq).symm)

/-- Three disjoint complete fibers cannot all be stable under both negation and one
scaled reciprocal. On squaring, the three fibers have odd size, while the induced
reciprocal has at most two nonzero fixed points. -/
theorem no_simultaneous (S : Fin 3 → Finset F)
    (size : ∀ i, (S i).card = 268435454)
    (two : (2 : F) ≠ 0) (nonzero : ∀ i x, x ∈ S i → x ≠ 0)
    (disj : Pairwise fun i j => Disjoint (S i) (S j))
    {u : F} (hu : u ≠ 0) (neg : ∀ i x, x ∈ S i → -x ∈ S i)
    (recip : ∀ i x, x ∈ S i → u / x ∈ S i) : False := by
  classical
  let W (i : Fin 3) := (S i).image (fun x => x ^ 2)
  have fixed (i : Fin 3) : ∃ w ∈ W i, w = u ∨ w = -u := by
    have count := square_image two (nonzero i) (neg i)
    rw [size] at count
    have odd : ¬ 2 ∣ (W i).card := by dsimp [W]; omega
    obtain ⟨w, hw, h⟩ := reciprocal_fixed (W i) odd (pow_ne_zero 2 hu) (by
      rintro _ hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      rw [← div_pow]
      exact mem_image_of_mem _ (recip _ _ hx))
    refine ⟨w, hw, ?_⟩
    rcases h with h | h
    · exact sq_eq_sq_iff_eq_or_eq_neg.mp h
    · obtain ⟨x, hx, hxw⟩ := mem_image.mp hw
      exact (pow_ne_zero 2 (nonzero _ _ hx) (hxw.trans h)).elim
  choose w member signs using fixed
  have inj : Function.Injective w := by
    intro i j hij
    by_contra different
    obtain ⟨x, hx, hxi⟩ := mem_image.mp (member i)
    obtain ⟨y, hy, hyj⟩ := mem_image.mp (member j)
    have h := sq_eq_sq_iff_eq_or_eq_neg.mp (hxi.trans (hij.trans hyj.symm))
    rcases h with rfl | rfl
    · exact disjoint_left.mp (disj different) hx hy
    · exact disjoint_left.mp (disj different) hx (neg _ _ hy)
  have sub : univ.image w ⊆ {u, -u} := by
    rintro _ hz
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    simpa only [mem_insert, mem_singleton] using signs i
  have count := (card_le_card sub).trans (card_insert_le u {-u})
  rw [card_image_of_injective _ inj, card_univ, Fintype.card_fin, card_singleton] at count
  omega

/-- The common setwise stabilizer of the three production fibers has at most one
nonidentity source map. In particular a Galois pullback with more than two deck
transformations cannot produce the required triple of fibers. -/
theorem unique_nonidentity {p : ℕ} [CharP F p] (hp : p.Prime) (large : 2 ^ 40 < p)
    (S : Fin 3 → Finset F) (size : ∀ i, (S i).card = 268435454)
    (roots : ∀ i x, x ∈ S i → x ^ (2 ^ 30 : ℕ) = 1)
    (disj : Pairwise fun i j => Disjoint (S i) (S j))
    (g h : Mobius F) (gd : g.det ≠ 0) (hd : h.det ≠ 0)
    (gs : ∀ i x, x ∈ S i → g.value x ∈ S i) (hs : ∀ i x, x ∈ S i → h.value x ∈ S i)
    (gn : ¬ ∀ x, g.value x = x) (hn : ¬ ∀ x, h.value x = x) :
    ∀ x, g.value x = h.value x := by
  have two : (2 : F) ≠ 0 := by
    change (↑(2 : ℕ) : F) ≠ 0
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) ((CharP.cast_eq_zero_iff F p 2).mp h)
    omega
  have nz (i x) (hx : x ∈ S i) : x ≠ 0 := by intro z; simpa [z] using roots i x hx
  have excl {u : F} (up : u ^ (2 ^ 30 : ℕ) = 1)
      (neg : ∀ i x, x ∈ S i → -x ∈ S i) (recip : ∀ i x, x ∈ S i → u / x ∈ S i) :
      False := no_simultaneous S size two nz disj (fun z => by simp [z] at up) neg recip
  have hclass := (classify hp large _ (size 0) (roots 0) h hd (hs 0)).resolve_left hn
  rcases (classify hp large _ (size 0) (roots 0) g gd (gs 0)).resolve_left gn with
    gneg | ⟨u, up, gu⟩
  · rcases hclass with hneg | ⟨v, vp, hv⟩
    · exact fun x => (gneg x).trans (hneg x).symm
    · exact (excl vp (fun i x hx => gneg x ▸ gs i x hx)
        (fun i x hx => hv x ▸ hs i x hx)).elim
  · have su (i x) (hx : x ∈ S i) : u / x ∈ S i := gu x ▸ gs i x hx
    rcases hclass with hneg | ⟨v, vp, hv⟩
    · exact (excl up (fun i x hx => hneg x ▸ hs i x hx) su).elim
    · have sv (i x) (hx : x ∈ S i) : v / x ∈ S i := hv x ▸ hs i x hx
      have vn : v ≠ 0 := fun z => by simp [z] at vp
      have sc (i x) (hx : x ∈ S i) : (u / v) * x ∈ S i := by
        have := su i _ (sv i x hx)
        rwa [div_div_eq_mul_div, mul_div_right_comm] at this
      rcases scaling (size 0) (roots 0) (sc 0) with eq | eq
      · have uv := (div_eq_one_iff_eq vn).mp eq
        exact fun x => by rw [gu, hv, uv]
      · exact (excl up (fun i x hx => by simpa [eq] using sc i x hx) su).elim

/-- The production collision lower bound exceeds the nontoric curve bound plus
one full scaling or reciprocal graph throughout this range of inner degrees. -/
theorem collision_cutoff (t : ℤ) (lo : 3 ≤ t) (hi : t ≤ 4194300) :
    108 * 1073741824 ^ 2 * (t - 1) ^ 4 <
      (3 * 268435454 * (t - 1) - 1073741824) ^ 3 := by
  let z := t - 1
  change 108 * 1073741824 ^ 2 * z ^ 4 < (805306362 * z - 1073741824) ^ 3
  by_cases low : z < 5
  · have h : t ≤ 5 := by dsimp [z] at low; omega
    dsimp [z]
    interval_cases t <;> decide
  have lower : 0 ≤ z - 5 := by omega
  have upper : 0 ≤ 4194299 - z := by dsimp [z]; omega
  have aux : 3 * 805306362 ^ 2 * 1073741824 <
      z * (805306362 ^ 3 - 108 * 1073741824 ^ 2 * z) := by
    nlinarith only [mul_nonneg lower upper, upper]
  have square : 0 < z ^ 2 := pow_pos (by omega) 2
  nlinarith only [mul_lt_mul_of_pos_right aux square, lower]

/-- Among divisors of the production pencil degree above the excluded interval,
the only possible proper inner degrees have outer degree fourteen, seven or two. -/
theorem large_divisor (t : ℕ) (divides : t ∣ 268435454) (large : 4194300 < t) :
    t = 19173961 ∨ t = 38347922 ∨ t = 134217727 ∨ t = 268435454 := by
  obtain ⟨m, hm⟩ := divides
  have bound : m ≤ 64 := by
    by_contra! h
    have := Nat.mul_le_mul large h
    omega
  have dm : m ∣ 268435454 := ⟨t, by rw [hm, mul_comm]⟩
  have types : m = 1 ∨ m = 2 ∨ m = 7 ∨ m = 14 := by
    interval_cases m <;> first | decide | norm_num at dm
  rcases types with rfl | rfl | rfl | rfl <;> omega

end ProximityGap.QuarterSplitFiberSymmetry
