/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CubicOrchardIdentity

/-!
# The cyclotomic core of the exact smooth-domain list size (#389)

The number-theoretic ingredients of the EXACT sub-Johnson list-size closed form on
quadratic-residue domains — proven WITHOUT character theory, via the conic `y² = 1 + x²`:

* **`card_units_squares`** — the squaring map is 2-to-1 on `Fˣ`: `2·#QR* + 1 = q`.
* **`conic_card`** — `(y−x)(y+x) = 1` puts the conic `{y² = 1 + x²}` in bijection with
  `Fˣ`: exactly `q − 1` points.
* **`qr_shift_count`** — splitting the conic into `x = 0` (2 points), `y = 0` (2 points,
  needs `−1` a square) and the rest (projected 4-to-1 by `u = x²` onto the consecutive
  nonzero-square pairs): **`4·#{u : u, u+1 ∈ QR*} + 5 = q`** — the order-2 cyclotomic
  number `N = (q−5)/4`, the heart of the smooth-domain list-size formula.

Downstream (derived on paper, probe-verified 13/13 at `q = 29..149`; formalizing the
`G³`-scaling assembly is the next step): the cubic word's exact list size on the QR domain
is `n(q−5)/24` for `q ≡ 5 (8)` and `n(q−17)/24` for `q ≡ 1 (8)`, where the `mod 8` split is
exactly whether `−2 ∈ QR` (the `3·n·[−2∈G]` diagonal correction in
`6·#triples = n·M − 3n·[−2∈G]`, `M = N` here).  Combined with `cubic_list_eq_zeroSum` this
is an exact, character-sum-free smooth-domain sub-Johnson list size.  Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The squaring map is 2-to-1 on `Fˣ`: `2·#QR* + 1 = q` (odd characteristic). -/
theorem card_units_squares (h2 : (2 : F) ≠ 0) :
    2 * ((Finset.univ : Finset F).filter (fun x => x ≠ 0 ∧ IsSquare x)).card + 1
      = Fintype.card F := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ : Finset F).filter (fun x => x ≠ 0),
      x * x ∈ (Finset.univ : Finset F).filter (fun x => x ≠ 0 ∧ IsSquare x) := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mul_ne_zero hx0 hx0, ⟨x, rfl⟩⟩
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib4 : ∀ u ∈ (Finset.univ : Finset F).filter (fun x => x ≠ 0 ∧ IsSquare x),
      (((Finset.univ : Finset F).filter (fun x => x ≠ 0)).filter
        (fun x => x * x = u)).card = 2 := by
    intro u hu
    obtain ⟨-, hu0, r, hr⟩ := Finset.mem_filter.mp hu
    have hr0 : r ≠ 0 := fun h => hu0 (by rw [hr, h, mul_zero])
    have hrr : r ≠ -r := fun h => hr0 (by
      have hh : (2 : F) * r = 0 := by linear_combination h
      rcases mul_eq_zero.mp hh with h2' | h2'
      · exact absurd h2' h2
      · exact h2')
    have hset : ((Finset.univ : Finset F).filter (fun x => x ≠ 0)).filter
        (fun x => x * x = u) = {r, -r} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩
        have hfac : (x - r) * (x + r) = 0 := by linear_combination hx + hr
        rcases mul_eq_zero.mp hfac with h | h
        · exact Or.inl (by linear_combination h)
        · exact Or.inr (by linear_combination h)
      · rintro (rfl | rfl)
        · exact ⟨hr0, hr.symm⟩
        · exact ⟨neg_ne_zero.mpr hr0, by linear_combination -hr⟩
    rw [hset, Finset.card_insert_of_notMem (by simpa using hrr), Finset.card_singleton]
  have hsum : ∑ u ∈ (Finset.univ : Finset F).filter (fun x => x ≠ 0 ∧ IsSquare x),
      (((Finset.univ : Finset F).filter (fun x => x ≠ 0)).filter
        (fun x => x * x = u)).card = 2 *
      ((Finset.univ : Finset F).filter (fun x => x ≠ 0 ∧ IsSquare x)).card := by
    rw [Finset.sum_congr rfl hfib4, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsum] at hfib
  have hc : ((Finset.univ : Finset F).filter (fun x : F => x ≠ 0)).card
      = Fintype.card F - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
      Finset.card_univ]
  rw [hc] at hfib
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  omega

/-- **The conic count**: `{(x,y) : y² = 1 + x²}` is in bijection with `Fˣ` (via
`(x,y) ↦ y − x`, inverse `s ↦ ((s⁻¹−s)/2, (s+s⁻¹)/2)`), so it has exactly `q − 1` points. -/
theorem conic_card (h2 : (2 : F) ≠ 0) :
    ((Finset.univ : Finset (F × F)).filter (fun p => p.2 ^ 2 = 1 + p.1 ^ 2)).card
      = Fintype.card F - 1 := by
  classical
  have hT : ((Finset.univ : Finset F).filter (fun x : F => x ≠ 0)).card
      = Fintype.card F - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
      Finset.card_univ]
  rw [← hT]
  refine Finset.card_bij'
    (fun p _ => p.2 - p.1)
    (fun s _ => ((s⁻¹ - s) / 2, (s + s⁻¹) / 2))
    ?_ ?_ ?_ ?_
  · -- maps the conic into Fˣ
    intro p hp
    obtain ⟨x, y⟩ := p
    have hmem : y ^ 2 = 1 + x ^ 2 := (Finset.mem_filter.mp hp).2
    have key : (y - x) * (y + x) = 1 := by linear_combination hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hzero
    replace hzero : y - x = 0 := hzero
    rw [hzero, zero_mul] at key
    exact one_ne_zero key.symm
  · -- maps Fˣ into the conic
    intro s hs
    have hs0 : s ≠ 0 := (Finset.mem_filter.mp hs).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show ((s + s⁻¹) / 2) ^ 2 = 1 + ((s⁻¹ - s) / 2) ^ 2
    field_simp
    ring
  · -- left inverse
    intro p hp
    obtain ⟨x, y⟩ := p
    have hmem : y ^ 2 = 1 + x ^ 2 := (Finset.mem_filter.mp hp).2
    have key : (y - x) * (y + x) = 1 := by linear_combination hmem
    have hne : y - x ≠ 0 := fun h => by rw [h, zero_mul] at key; exact one_ne_zero key.symm
    have hinv : (y - x)⁻¹ = y + x := by
      rw [inv_eq_one_div, div_eq_iff hne]; linear_combination -key
    show (((y - x)⁻¹ - (y - x)) / 2, ((y - x) + (y - x)⁻¹) / 2) = (x, y)
    rw [hinv, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · field_simp; ring
    · field_simp; ring
  · -- right inverse
    intro s hs
    have hs0 : s ≠ 0 := (Finset.mem_filter.mp hs).2
    show ((s + s⁻¹) / 2) - ((s⁻¹ - s) / 2) = s
    field_simp; ring

open Classical in
/-- **THE CONSECUTIVE-QR PAIR COUNT** (order-2 cyclotomic number): when `−1` is a square
and `2 ≠ 0`, `4·#{u : u ∈ QR*, u+1 ∈ QR*} + 5 = q`, i.e. `N = (q−5)/4`. -/
theorem qr_shift_count (h2 : (2 : F) ≠ 0) (hneg1 : IsSquare (-1 : F)) :
    4 * ((Finset.univ : Finset F).filter
        (fun u => u ≠ 0 ∧ IsSquare u ∧ u + 1 ≠ 0 ∧ IsSquare (u + 1))).card + 5
      = Fintype.card F := by
  classical
  obtain ⟨i, hi⟩ := hneg1
  have hi2 : i * i = -1 := hi.symm
  have hi0 : i ≠ 0 := by
    intro h
    apply h2
    have h01 : (0 : F) = -1 := by rw [← hi2, h, mul_zero]
    linear_combination 2 * h01
  have hii : i ≠ -i := fun h => hi0 (by
    have hh : (2 : F) * i = 0 := by linear_combination h
    rcases mul_eq_zero.mp hh with h' | h'
    · exact absurd h' h2
    · exact h')
  have hone : (1 : F) ≠ -1 := fun h => h2 (by linear_combination h)
  set C := (Finset.univ : Finset (F × F)).filter (fun p => p.2 ^ 2 = 1 + p.1 ^ 2) with hC
  set N := (Finset.univ : Finset F).filter
    (fun u => u ≠ 0 ∧ IsSquare u ∧ u + 1 ≠ 0 ∧ IsSquare (u + 1)) with hN
  -- the four axis points form the "degenerate" part of the conic
  have hB : C.filter (fun p => ¬ (p.1 ≠ 0 ∧ p.2 ≠ 0))
      = {((0 : F), (1 : F)), (0, -1), (i, 0), (-i, 0)} := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, not_and_or, not_not]
    constructor
    · rintro ⟨hcon, hxy⟩
      rcases hxy with hx0 | hy0
      · subst hx0
        have hy : (y - 1) * (y + 1) = 0 := by linear_combination hcon
        rcases mul_eq_zero.mp hy with h | h
        · exact Or.inl ⟨rfl, by linear_combination h⟩
        · exact Or.inr (Or.inl ⟨rfl, by linear_combination h⟩)
      · subst hy0
        have hx : (x - i) * (x + i) = 0 := by linear_combination -hcon - hi2
        rcases mul_eq_zero.mp hx with h | h
        · exact Or.inr (Or.inr (Or.inl ⟨by linear_combination h, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by linear_combination h, rfl⟩))
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨by ring, Or.inl rfl⟩
      · exact ⟨by ring, Or.inl rfl⟩
      · exact ⟨by linear_combination -hi2, Or.inr rfl⟩
      · exact ⟨by linear_combination -hi2, Or.inr rfl⟩
  have hBcard : (C.filter (fun p => ¬ (p.1 ≠ 0 ∧ p.2 ≠ 0))).card = 4 := by
    rw [hB,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact hone h
        · exact hi0 h.symm
        · exact (neg_ne_zero.mpr hi0) h.symm),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hi0 h.symm
        · exact (neg_ne_zero.mpr hi0) h.symm),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton, Prod.mk.injEq]
        rintro ⟨h, _⟩
        exact hii h),
      Finset.card_singleton]
  -- the nondegenerate conic part projects 4-to-1 onto N via u = x²
  have hAmaps : ∀ p ∈ C.filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0), p.1 ^ 2 ∈ N := by
    intro p hp
    rw [Finset.mem_filter, hC, Finset.mem_filter] at hp
    obtain ⟨⟨-, hconn⟩, hx0, hy0⟩ := hp
    rw [hN, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, pow_ne_zero 2 hx0, ⟨p.1, by ring⟩, ?_, ?_⟩
    · rw [show p.1 ^ 2 + 1 = p.2 ^ 2 from by linear_combination -hconn]
      exact pow_ne_zero 2 hy0
    · exact ⟨p.2, by rw [show p.1 ^ 2 + 1 = p.2 ^ 2 from by linear_combination -hconn]; ring⟩
  have hAfib : ∀ u ∈ N, ((C.filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0)).filter
      (fun p => p.1 ^ 2 = u)).card = 4 := by
    intro u hu
    rw [hN, Finset.mem_filter] at hu
    obtain ⟨-, hu0, ⟨x, hx⟩, hu1, ⟨y, hy⟩⟩ := hu
    have hx0 : x ≠ 0 := fun h => hu0 (by rw [hx, h, mul_zero])
    have hy0 : y ≠ 0 := fun h => hu1 (by rw [hy, h, mul_zero])
    have hxx : x ≠ -x := fun h => hx0 (by
      have hh : (2 : F) * x = 0 := by linear_combination h
      rcases mul_eq_zero.mp hh with h' | h'
      · exact absurd h' h2
      · exact h')
    have hyy : y ≠ -y := fun h => hy0 (by
      have hh : (2 : F) * y = 0 := by linear_combination h
      rcases mul_eq_zero.mp hh with h' | h'
      · exact absurd h' h2
      · exact h')
    have hset : (C.filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0)).filter (fun p => p.1 ^ 2 = u)
        = {(x, y), (x, -y), (-x, y), (-x, -y)} := by
      ext p
      obtain ⟨a, b⟩ := p
      simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hcon, _, _⟩, hau⟩
        have ha : (a - x) * (a + x) = 0 := by
          have hax2 : a ^ 2 = x ^ 2 := by rw [hau, hx]; ring
          linear_combination hax2
        have hb : (b - y) * (b + y) = 0 := by
          have hbeq : b ^ 2 = y ^ 2 := by
            rw [show b ^ 2 = 1 + a ^ 2 from hcon, hau,
              show y ^ 2 = u + 1 from by rw [hy]; ring]
            ring
          linear_combination hbeq
        rcases mul_eq_zero.mp ha with hax | hax
        · rcases mul_eq_zero.mp hb with hby | hby
          · exact Or.inl ⟨by linear_combination hax, by linear_combination hby⟩
          · exact Or.inr (Or.inl ⟨by linear_combination hax, by linear_combination hby⟩)
        · rcases mul_eq_zero.mp hb with hby | hby
          · exact Or.inr (Or.inr (Or.inl
              ⟨by linear_combination hax, by linear_combination hby⟩))
          · exact Or.inr (Or.inr (Or.inr
              ⟨by linear_combination hax, by linear_combination hby⟩))
      · have hxy : y ^ 2 = 1 + x ^ 2 := by
          rw [show y ^ 2 = u + 1 from by rw [hy]; ring, show x ^ 2 = u from by rw [hx]; ring]
          ring
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨hxy, hx0, hy0⟩, by rw [hx]; ring⟩
        · exact ⟨⟨by linear_combination hxy, hx0, neg_ne_zero.mpr hy0⟩, by rw [hx]; ring⟩
        · exact ⟨⟨by linear_combination hxy, neg_ne_zero.mpr hx0, hy0⟩, by rw [hx]; ring⟩
        · exact ⟨⟨by linear_combination hxy, neg_ne_zero.mpr hx0, neg_ne_zero.mpr hy0⟩,
            by rw [hx]; ring⟩
    rw [hset,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact hyy h
        · exact hxx h
        · exact hxx h),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hxx h
        · exact hxx h),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton, Prod.mk.injEq]
        rintro ⟨_, h⟩
        exact hyy h),
      Finset.card_singleton]
  have hAcard : (C.filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0)).card = 4 * N.card := by
    rw [Finset.card_eq_sum_card_fiberwise hAmaps, Finset.sum_congr rfl hAfib,
      Finset.sum_const, smul_eq_mul, mul_comm]
  -- assemble
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := C) (p := fun p : F × F => p.1 ≠ 0 ∧ p.2 ≠ 0)
  rw [hAcard, hBcard] at hsplit
  have hCcard : C.card = Fintype.card F - 1 := by rw [hC]; exact conic_card h2
  rw [hCcard] at hsplit
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  omega

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.card_units_squares
#print axioms ProximityGap.PairRank.conic_card
#print axioms ProximityGap.PairRank.qr_shift_count
