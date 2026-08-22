/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

/-!
# The chord-family count: `n(n−4)` / `n(n−8)` parametrized solutions per class

Campaign #357, the per-class counting corollary of the two-plus-antipodal chord law. The
probe-pinned targets: each odd difference class carries exactly `n(n−4)/4` unordered
family triples, each even class `n(n−8)/4`, summing over the `n/4` odd and `n/4 − 1`
even non-antipodal classes to the family closed form `n(n−4)²/8`.

This file proves the odd-class count in its parametrized (ordered) form. The chord law
says `{i, i+d}, {j, j+d}, {k, k+2^(m−1)}` is collinear iff `2k = i + j + d`, so a family
triple is parametrized by `(i, k)` (then `j := 2k − i − d`), and:

* the disjointness of the antipodal completion from the two chord pairs is **exactly**
  `k ∉ {i, i+h, i+d, i+d+h}` (`h = 2^(m−1)`) — the `j`-side disjointness conditions
  coincide with these four (`2k ≡ 2i ⟺ j ≡ i−d`, `2k ≡ 2i+2d ⟺ j ≡ i+d`);
* the degeneracy conditions (`j = i`, the pair collision, and `j = i+h`, the horizontal
  line) are `2k = 2i + d` and `2k = 2i + d + h` — **unsolvable for odd `d`**
  (`oddCast_ne_double`: project to `ZMod 2`).

Hence the parametrized solution set is, per odd class, a per-`i` exclusion of four
distinct points: `chord_param_count_odd` — **exactly `n(n−4)` ordered `(i, k)` pairs**.
On even classes the degeneracies are *solvable* (`double_eq_zero_iff`: the doubling
kernel is `{0, 2^(m−1)}`), each contributing one antipodal pair of excluded completions:
`chord_param_count_even` — **exactly `n(n−8)` pairs**. The unordered family counts are
the 4-fold quotients `n(n−4)/4` and `n(n−8)/4` (the `i ↔ j` swap and `k ↔ k+h`),
matching the probe at n = 8, 16, 32; the cross-class summation
`(n/4)·n(n−4)/4 + (n/4−1)·n(n−8)/4 = n(n−4)²/8` is the remaining assembly step.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (the census closed-forms comment; per-class targets pinned by probe);
  `TwoPlusAntipodalChordLaw.lean` (the law + `completion_count`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.ChordFamilyCount

variable {m : ℕ}

/-- `2^(m−1)` is nonzero in `ZMod (2^m)`. -/
theorem half_ne_zero (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hpos : 0 < 2 ^ (m - 1) := Nat.two_pow_pos _
  exact absurd (Nat.le_of_dvd hpos h0) (not_le.mpr hlt)

/-- `2^(m−1)` is self-negative in `ZMod (2^m)`: `h + h = 0`. -/
theorem half_add_half (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  have h : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  rw [h]

/-- An odd natural is nonzero in `ZMod (2^m)` for `m ≥ 1`. -/
theorem oddCast_ne_zero (hm : 1 ≤ m) {d : ℕ} (hd : d % 2 = 1) :
    ((d : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have h2 : 2 ∣ d := dvd_trans (dvd_pow_self 2 (by omega : m ≠ 0)) h0
  omega

/-- The `ZMod 2` projection of `ZMod (2^m)`. -/
noncomputable def proj (m : ℕ) (hm : m ≠ 0) : ZMod (2 ^ m) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 hm) (ZMod 2)

/-- **Odd unsolvability**: `2x = 2y + d` has no solutions in `ZMod (2^m)` for odd `d` —
the pair-collision degeneracy of the chord parametrization is vacuous on odd classes. -/
theorem oddCast_ne_double (hm : 1 ≤ m) {d : ℕ} (hd : d % 2 = 1)
    (x y : ZMod (2 ^ m)) : 2 * x ≠ 2 * y + (d : ZMod (2 ^ m)) := by
  intro heq
  have h := congrArg (proj m (by omega)) heq
  simp only [map_add, map_mul, map_ofNat, map_natCast] at h
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul, zero_mul, zero_add] at h
  have hd2 : ((d : ℕ) : ZMod 2) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega
  exact hd2 h.symm

/-- **Odd-shift unsolvability**: `2x = 2y + d + 2^(m−1)` has no solutions for odd `d`,
`m ≥ 2` — the horizontal degeneracy is vacuous on odd classes. -/
theorem oddCast_ne_double_half (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1)
    (x y : ZMod (2 ^ m)) :
    2 * x ≠ 2 * y + (d : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  intro heq
  have h := congrArg (proj m (by omega)) heq
  simp only [map_add, map_mul, map_ofNat, map_natCast] at h
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hh2 : ((2 ^ (m - 1) : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact dvd_pow_self 2 (by omega : m - 1 ≠ 0)
  rw [h2, zero_mul, zero_mul, zero_add, hh2, add_zero] at h
  have hd2 : ((d : ℕ) : ZMod 2) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega
  exact hd2 h.symm

/-- An odd natural differs from `2^(m−1)` in `ZMod (2^m)` for `m ≥ 2`. -/
theorem oddCast_ne_half (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1) :
    ((d : ℕ) : ZMod (2 ^ m)) ≠ ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  intro heq
  have h := congrArg (proj m (by omega)) heq
  simp only [map_natCast] at h
  have hd2 : ((d : ℕ) : ZMod 2) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    omega
  have hh2 : ((2 ^ (m - 1) : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact dvd_pow_self 2 (by omega : m - 1 ≠ 0)
  rw [hh2] at h
  exact hd2 h

/-- The four excluded completion points of a chord base `i`. -/
def exclusions (m : ℕ) (d : ℕ) (i : ZMod (2 ^ m)) : Finset (ZMod (2 ^ m)) :=
  {i, i + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), i + (d : ZMod (2 ^ m)),
    i + ((d : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))}

/-- For odd `d` and `m ≥ 2` the four excluded points are pairwise distinct. -/
theorem card_exclusions (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1) (i : ZMod (2 ^ m)) :
    (exclusions m d i).card = 4 := by
  have h1 : 1 ≤ m := by omega
  have hh0 := half_ne_zero h1
  have hd0 := oddCast_ne_zero h1 hd
  have hdh := oddCast_ne_half hm hd
  have hhh := half_add_half h1
  have hdh0 : (d : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
    intro h0
    apply hdh
    have h := congrArg (· + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) h0
    simp only [zero_add] at h
    rw [add_assoc, hhh, add_zero] at h
    exact h
  unfold exclusions
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
    card_singleton]
  · -- i + d ∉ {i + (d + h)}
    simp only [mem_singleton]
    intro h
    rw [← add_assoc] at h
    exact hh0 (left_eq_add.mp h)
  · -- i + h ∉ {i + d, i + (d + h)}
    simp only [mem_insert, mem_singleton]
    push Not
    constructor
    · intro h
      exact hdh (add_left_cancel h).symm
    · intro h
      have h' := add_left_cancel h
      -- h = d + h forces d = 0
      apply hd0
      have h2 := congrArg (· + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) h'
      simp only at h2
      rw [hhh, add_assoc, hhh, add_zero] at h2
      exact h2.symm
  · -- i ∉ {i + h, i + d, i + (d + h)}
    simp only [mem_insert, mem_singleton]
    push Not
    refine ⟨fun h => hh0 (left_eq_add.mp h),
      fun h => hd0 (left_eq_add.mp h),
      fun h => hdh0 (left_eq_add.mp h)⟩

/-- **THE ODD-CLASS CHORD COUNT.** For every odd class `d` at scale `n = 2^m`, `m ≥ 2`:
the parametrized chord-law solution set — pairs `(i, k)` of chord base point and
antipodal completion with the completion disjoint from the chord pairs and the
degeneracies excluded — has **exactly `n(n−4)` elements**. The unordered family count
per odd class is the 4-fold quotient `n(n−4)/4`, the probe-pinned target. -/
theorem chord_param_count_odd (hm : 2 ≤ m) {d : ℕ} (hd : d % 2 = 1) :
    ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).card
      = 2 ^ m * (2 ^ m - 4) := by
  haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have h1 : 1 ≤ m := by omega
  -- the degeneracy conjuncts are vacuous for odd d
  have hvac : ∀ p : ZMod (2 ^ m) × ZMod (2 ^ m),
      (p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
      ↔ p.2 ∉ exclusions m d p.1 :=
    fun p => ⟨fun h => h.1, fun h =>
      ⟨h, oddCast_ne_double h1 hd p.2 p.1, oddCast_ne_double_half hm hd p.2 p.1⟩⟩
  have hfc : ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))))
      = (univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter
          (fun p => p.2 ∉ exclusions m d p.1) :=
    Finset.filter_congr fun p _ => hvac p
  rw [hfc]
  -- fiber over the first coordinate
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := (univ : Finset (ZMod (2 ^ m)))) (fun x _ => mem_univ _)]
  have hfiber : ∀ i0 : ZMod (2 ^ m),
      (((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter
          (fun p => p.2 ∉ exclusions m d p.1)).filter (fun p => p.1 = i0)).card
        = ((univ : Finset (ZMod (2 ^ m))).filter
            (fun k => k ∉ exclusions m d i0)).card := by
    intro i0
    apply Finset.card_nbij (fun p => p.2)
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ,
        true_and] at hp ⊢
      rw [← hp.2]
      exact hp.1
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ,
        true_and] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) hpq
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ,
        true_and] at hk
      exact ⟨(i0, k), by simp [hk], rfl⟩
  rw [Finset.sum_congr rfl fun i0 _ => hfiber i0]
  have hcount : ∀ i0 : ZMod (2 ^ m),
      ((univ : Finset (ZMod (2 ^ m))).filter (fun k => k ∉ exclusions m d i0)).card
        = 2 ^ m - 4 := by
    intro i0
    have hsd : (univ : Finset (ZMod (2 ^ m))).filter (fun k => k ∉ exclusions m d i0)
        = univ \ exclusions m d i0 := by
      ext k
      simp [mem_sdiff]
    rw [hsd, card_sdiff, Finset.inter_univ, card_univ, ZMod.card,
      card_exclusions hm hd i0]
  rw [Finset.sum_congr rfl fun i0 _ => hcount i0, Finset.sum_const, card_univ,
    ZMod.card, smul_eq_mul]

/-! ## The even classes: eight exclusions, `n(n−8)`

For even `d` the two degeneracy conditions are *solvable* — each contributes one
antipodal pair of completions (`2k = 2i+d ⟺ k ∈ i+c+{0,h}`, `c = d/2`;
`2k = 2i+d+h ⟺ k ∈ i+c+q+{0,h}`, `q = 2^(m−2)`) — so the per-base exclusion set grows
to eight points and the count drops to `n(n−8)`, the probe-pinned even-class target. -/

section Even

/-- Cast is injective below `2^m`. -/
theorem natCast_inj_lt {a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : ((a : ℕ) : ZMod (2 ^ m)) = b) : a = b := by
  haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this

/-- **The doubling kernel of `ZMod (2^m)` is `{0, 2^(m−1)}`.** -/
theorem double_eq_zero_iff (hm : 1 ≤ m) (x : ZMod (2 ^ m)) :
    2 * x = 0 ↔ x = 0 ∨ x = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have hx : ((x.val : ℕ) : ZMod (2 ^ m)) = x := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  constructor
  · intro h0
    have h2x : ((2 * x.val : ℕ) : ZMod (2 ^ m)) = 0 := by
      push_cast
      rw [hx]
      exact h0
    rw [ZMod.natCast_eq_zero_iff] at h2x
    have hvlt : x.val < 2 ^ m := ZMod.val_lt x
    obtain ⟨t, ht⟩ := h2x
    rcases t with _ | _ | t
    · left
      have hv : x.val = 0 := by omega
      rw [← hx, hv, Nat.cast_zero]
    · right
      have hv : x.val = 2 ^ (m - 1) := by omega
      rw [← hx, hv]
    · exfalso
      have hge2 : 2 ^ m * 2 ≤ 2 * x.val := by
        calc 2 ^ m * 2 ≤ 2 ^ m * (t + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * x.val := ht.symm
      omega
  · rintro (rfl | rfl)
    · rw [mul_zero]
    · rw [two_mul, ← Nat.cast_add, hsplit, ZMod.natCast_self]

/-- The eight excluded completion points of an even-class chord base
(`c = d/2`, `e = d/2 + 2^(m−2)`): the four chord exclusions plus the two degeneracy
solution pairs. -/
def exclusionsEven (m d : ℕ) (i : ZMod (2 ^ m)) : Finset (ZMod (2 ^ m)) :=
  {i, i + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), i + ((d : ℕ) : ZMod (2 ^ m)),
    i + (((d : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))),
    i + ((d / 2 : ℕ) : ZMod (2 ^ m)),
    i + (((d / 2 : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))),
    i + ((d / 2 + 2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)),
    i + (((d / 2 + 2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
      + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))}

variable (hm : 2 ≤ m) {d : ℕ} (hd2 : d % 2 = 0) (hd0 : 0 < d) (hdn : d < 2 ^ m)
  (hdh : d ≠ 2 ^ (m - 1))

include hm hd2 hd0 hdn hdh in
/-- For even non-antipodal `d` the eight excluded points are pairwise distinct. -/
theorem card_exclusionsEven (i : ZMod (2 ^ m)) :
    (exclusionsEven m d i).card = 8 := by
  have h1 : 1 ≤ m := by omega
  have hhh := half_add_half h1
  have hsplitN : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel h1] at h
    omega
  have hhlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hqlt : 2 ^ (m - 2) < 2 ^ (m - 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hq0 : 0 < 2 ^ (m - 2) := Nat.two_pow_pos _
  have hq2 : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 2)
    rw [show m - 2 + 1 = m - 1 from by omega] at h
    omega
  have hne : ∀ {a b : ℕ}, a < 2 ^ m → b < 2 ^ m → a ≠ b →
      ((a : ℕ) : ZMod (2 ^ m)) ≠ ((b : ℕ) : ZMod (2 ^ m)) :=
    fun ha hb hab h => hab (natCast_inj_lt ha hb h)
  have hzero : (0 : ZMod (2 ^ m)) = ((0 : ℕ) : ZMod (2 ^ m)) := by norm_cast
  set H : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with hH
  set D : ZMod (2 ^ m) := ((d : ℕ) : ZMod (2 ^ m)) with hD
  set C : ZMod (2 ^ m) := ((d / 2 : ℕ) : ZMod (2 ^ m)) with hC
  set E : ZMod (2 ^ m) := ((d / 2 + 2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) with hE
  -- shift converter (H self-negative)
  have hshift : ∀ a b : ZMod (2 ^ m), a + H = b → a = b + H := by
    intro a b h
    rw [← h, add_assoc, hhh, add_zero]
  -- ℕ-size distinctness pool
  have hH0 : H ≠ 0 := half_ne_zero h1
  have hD0 : D ≠ 0 := by rw [hzero]; exact hne (by omega) (by omega) (by omega)
  have hDH : D ≠ H := hne (by omega) (by omega) (by omega)
  have hC0 : C ≠ 0 := by rw [hzero]; exact hne (by omega) (by omega) (by omega)
  have hCH : C ≠ H := hne (by omega) (by omega) (by omega)
  have hCD : C ≠ D := hne (by omega) (by omega) (by omega)
  have hE0 : E ≠ 0 := by rw [hzero]; exact hne (by omega) (by omega) (by omega)
  have hEH : E ≠ H := hne (by omega) (by omega) (by omega)
  have hED : E ≠ D := hne (by omega) (by omega) (by omega)
  have hEC : E ≠ C := hne (by omega) (by omega) (by omega)
  -- D + H, with wraparound-safe reduced representative
  have hDHred : ∃ r : ℕ, r < 2 ^ m ∧ D + H = ((r : ℕ) : ZMod (2 ^ m))
      ∧ r ≠ 0 ∧ r ≠ 2 ^ (m - 1) ∧ r ≠ d ∧ r ≠ d / 2 ∧ r ≠ d / 2 + 2 ^ (m - 2) := by
    haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
    rcases Nat.lt_or_ge (d + 2 ^ (m - 1)) (2 ^ m) with hlt | hge
    · refine ⟨d + 2 ^ (m - 1), hlt, ?_, by omega, by omega, by omega, by omega, by omega⟩
      rw [hD, hH, Nat.cast_add]
    · refine ⟨d + 2 ^ (m - 1) - 2 ^ m, by omega, ?_, by omega, by omega, by omega,
        by omega, by omega⟩
      have hr : ((d + 2 ^ (m - 1) - 2 ^ m : ℕ) : ZMod (2 ^ m))
          = ((d + 2 ^ (m - 1) - 2 ^ m + 2 ^ m : ℕ) : ZMod (2 ^ m)) := by
        rw [Nat.cast_add, ZMod.natCast_self, add_zero]
      rw [hD, hH, ← Nat.cast_add, hr]
      congr 1
      omega
  obtain ⟨r, hrlt, hrEq, hr0, hrH, hrD, hrC, hrE⟩ := hDHred
  have hDH0 : D + H ≠ 0 := by rw [hrEq, hzero]; exact hne hrlt (by omega) hr0
  have hDHH : D + H ≠ H := by rw [hrEq]; exact hne hrlt (by omega) hrH
  have hDHD : D + H ≠ D := by rw [hrEq]; exact hne hrlt (by omega) hrD
  have hDHC : D + H ≠ C := by rw [hrEq]; exact hne hrlt (by omega) hrC
  have hDHE : D + H ≠ E := by rw [hrEq]; exact hne hrlt (by omega) hrE
  -- C + H and E + H pools (both < 2^m as naturals: c < h, e < h)
  have hCHcast : C + H = ((d / 2 + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [hC, hH, Nat.cast_add]
  have hCH0 : C + H ≠ 0 := by
    rw [hCHcast, hzero]; exact hne (by omega) (by omega) (by omega)
  have hCHH : C + H ≠ H := by rw [hCHcast]; exact hne (by omega) (by omega) (by omega)
  have hCHD : C + H ≠ D := by rw [hCHcast]; exact hne (by omega) (by omega) (by omega)
  have hCHC : C + H ≠ C := by rw [hCHcast]; exact hne (by omega) (by omega) (by omega)
  -- E + H, with wraparound-safe reduced representative (wraps when d > 2^(m−1))
  have hEHred : ∃ r' : ℕ, r' < 2 ^ m ∧ E + H = ((r' : ℕ) : ZMod (2 ^ m))
      ∧ r' ≠ 0 ∧ r' ≠ 2 ^ (m - 1) ∧ r' ≠ d ∧ r' ≠ d / 2
      ∧ r' ≠ d / 2 + 2 ^ (m - 2) := by
    haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
    rcases Nat.lt_or_ge (d / 2 + 2 ^ (m - 2) + 2 ^ (m - 1)) (2 ^ m) with hlt | hge
    · refine ⟨d / 2 + 2 ^ (m - 2) + 2 ^ (m - 1), hlt, ?_, by omega, by omega, by omega,
        by omega, by omega⟩
      rw [hE, hH, ← Nat.cast_add]
    · refine ⟨d / 2 + 2 ^ (m - 2) + 2 ^ (m - 1) - 2 ^ m, by omega, ?_, by omega,
        by omega, by omega, by omega, by omega⟩
      have hr : ((d / 2 + 2 ^ (m - 2) + 2 ^ (m - 1) - 2 ^ m : ℕ) : ZMod (2 ^ m))
          = ((d / 2 + 2 ^ (m - 2) + 2 ^ (m - 1) - 2 ^ m + 2 ^ m : ℕ) : ZMod (2 ^ m)) := by
        rw [Nat.cast_add, ZMod.natCast_self, add_zero]
      rw [hE, hH, ← Nat.cast_add, hr]
      congr 1
      omega
  obtain ⟨r', hrlt', hrEq', hr0', hrH', hrD', hrC', hrE'⟩ := hEHred
  have hEH0 : E + H ≠ 0 := by rw [hrEq', hzero]; exact hne hrlt' (by omega) hr0'
  have hEHH : E + H ≠ H := by rw [hrEq']; exact hne hrlt' (by omega) hrH'
  have hEHD : E + H ≠ D := by rw [hrEq']; exact hne hrlt' (by omega) hrD'
  have hEHC : E + H ≠ C := by rw [hrEq']; exact hne hrlt' (by omega) hrC'
  have hEHE : E + H ≠ E := by rw [hrEq', hE]; exact hne hrlt' (by omega) hrE'
  have hEHCH : E + H ≠ C + H := fun h => hEC (add_right_cancel h)
  have hECH : E ≠ C + H := by rw [hCHcast, hE]; exact hne (by omega) (by omega) (by omega)
  have hCHDH : C + H ≠ D + H := fun h => hCD (add_right_cancel h)
  have hEHDH : E + H ≠ D + H := fun h => hED (add_right_cancel h)
  have hCDH : C ≠ D + H := fun h => hDHC h.symm
  have hEDH : E ≠ D + H := fun h => hDHE h.symm
  have hCHE : C + H ≠ E := fun h => hECH h.symm
  -- translate inequality
  have haddne : ∀ t1 t2 : ZMod (2 ^ m), t1 ≠ t2 → i + t1 ≠ i + t2 :=
    fun t1 t2 h hh => h (add_right_injective i hh)
  -- the chain
  unfold exclusionsEven
  rw [← hH, ← hD, ← hC, ← hE]
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
    card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
    card_insert_of_notMem, card_singleton]
  · -- i + E ∉ {i + (E + H)}
    simp only [mem_singleton]
    exact haddne E (E + H) (fun h => hEHE h.symm)
  · -- i + (C + H) ∉ {i + E, i + (E + H)}
    simp only [mem_insert, mem_singleton]
    push Not
    exact ⟨haddne (C + H) E hCHE, haddne (C + H) (E + H) (fun h => hEHCH h.symm)⟩
  · -- i + C ∉ {i + (C + H), i + E, i + (E + H)}
    simp only [mem_insert, mem_singleton]
    push Not
    exact ⟨haddne C (C + H) (fun h => hCHC h.symm), haddne C E (fun h => hEC h.symm),
      haddne C (E + H) (fun h => hEHC h.symm)⟩
  · -- i + (D + H) ∉ {i + C, i + (C + H), i + E, i + (E + H)}
    simp only [mem_insert, mem_singleton]
    push Not
    exact ⟨haddne (D + H) C hDHC, haddne (D + H) (C + H) (fun h => hCHDH h.symm),
      haddne (D + H) E hDHE, haddne (D + H) (E + H) (fun h => hEHDH h.symm)⟩
  · -- i + D ∉ {i + (D + H), i + C, i + (C + H), i + E, i + (E + H)}
    simp only [mem_insert, mem_singleton]
    push Not
    exact ⟨haddne D (D + H) (fun h => hDHD h.symm), haddne D C (fun h => hCD h.symm),
      haddne D (C + H) (fun h => hCHD h.symm), haddne D E (fun h => hED h.symm),
      haddne D (E + H) (fun h => hEHD h.symm)⟩
  · -- i + H ∉ {i + D, i + (D + H), i + C, i + (C + H), i + E, i + (E + H)}
    simp only [mem_insert, mem_singleton]
    push Not
    exact ⟨haddne H D (fun h => hDH h.symm), haddne H (D + H) (fun h => hDHH h.symm),
      haddne H C (fun h => hCH h.symm), haddne H (C + H) (fun h => hCHH h.symm),
      haddne H E (fun h => hEH h.symm), haddne H (E + H) (fun h => hEHH h.symm)⟩
  · -- i ∉ the seven translates
    simp only [mem_insert, mem_singleton]
    push Not
    exact ⟨fun h => hH0 (left_eq_add.mp h), fun h => hD0 (left_eq_add.mp h),
      fun h => hDH0 (left_eq_add.mp h), fun h => hC0 (left_eq_add.mp h),
      fun h => hCH0 (left_eq_add.mp h), fun h => hE0 (left_eq_add.mp h),
      fun h => hEH0 (left_eq_add.mp h)⟩

include hm hd2 hd0 hdn hdh in
/-- **THE EVEN-CLASS CHORD COUNT.** For every even non-antipodal class `d` at scale
`n = 2^m`: the parametrized chord-law solution set has **exactly `n(n−8)` elements** —
the degeneracy conditions are solvable on even classes, each contributing one antipodal
pair of excluded completions. The unordered family count per even class is `n(n−8)/4`,
the probe-pinned target. -/
theorem chord_param_count_even :
    ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).card
      = 2 ^ m * (2 ^ m - 8) := by
  haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  have h1 : 1 ≤ m := by omega
  have hhh := half_add_half h1
  have hsplitN : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel h1] at h
    omega
  have hq2 : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 2)
    rw [show m - 2 + 1 = m - 1 from by omega] at h
    omega
  set H : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with hH
  set D : ZMod (2 ^ m) := ((d : ℕ) : ZMod (2 ^ m)) with hD
  set C : ZMod (2 ^ m) := ((d / 2 : ℕ) : ZMod (2 ^ m)) with hC
  set E : ZMod (2 ^ m) := ((d / 2 + 2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) with hE
  have hDC : D = C + C := by
    rw [hD, hC, ← Nat.cast_add]
    congr 1
    omega
  have hDHE : D + H = E + E := by
    rw [hD, hH, hE, ← Nat.cast_add, ← Nat.cast_add]
    congr 1
    omega
  -- degeneracy 1 ⟺ the C-pair
  have hdeg1 : ∀ i k : ZMod (2 ^ m),
      2 * k = 2 * i + D ↔ (k = i + C ∨ k = i + (C + H)) := by
    intro i k
    constructor
    · intro h
      have h0 : 2 * (k - (i + C)) = 0 := by
        rw [hDC] at h
        ring_nf
        linear_combination h
      rcases (double_eq_zero_iff h1 _).mp h0 with h2 | h2
      · left
        have := sub_eq_zero.mp h2
        exact this
      · right
        rw [← hH] at h2
        have : k = H + (i + C) := eq_add_of_sub_eq h2
        rw [this]
        ring
    · rintro (rfl | rfl)
      · rw [hDC]
        ring
      · rw [hDC]
        linear_combination hhh
  -- degeneracy 2 ⟺ the E-pair
  have hdeg2 : ∀ i k : ZMod (2 ^ m),
      2 * k = 2 * i + D + H ↔ (k = i + E ∨ k = i + (E + H)) := by
    intro i k
    constructor
    · intro h
      have h0 : 2 * (k - (i + E)) = 0 := by
        have hh : 2 * k = 2 * i + (E + E) := by
          rw [← hDHE]
          linear_combination h
        ring_nf
        linear_combination hh
      rcases (double_eq_zero_iff h1 _).mp h0 with h2 | h2
      · left
        exact sub_eq_zero.mp h2
      · right
        rw [← hH] at h2
        have : k = H + (i + E) := eq_add_of_sub_eq h2
        rw [this]
        ring
    · rintro (rfl | rfl)
      · rw [show 2 * i + D + H = 2 * i + (D + H) from by ring, hDHE]
        ring
      · rw [show 2 * i + D + H = 2 * i + (D + H) from by ring, hDHE]
        linear_combination hhh
  -- the full condition ⟺ the eight-point exclusion
  have hcond : ∀ p : ZMod (2 ^ m) × ZMod (2 ^ m),
      (p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + D ∧ 2 * p.2 ≠ 2 * p.1 + D + H)
      ↔ p.2 ∉ exclusionsEven m d p.1 := by
    intro p
    unfold exclusionsEven exclusions
    rw [← hH, ← hD, ← hC, ← hE]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨hA, h2, h3⟩
      push Not at hA ⊢
      have hnc := (hdeg1 p.1 p.2).not.mp h2
      have hne' := (hdeg2 p.1 p.2).not.mp h3
      push Not at hnc hne'
      exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, hnc.1, hnc.2, hne'.1, hne'.2⟩
    · intro hAll
      push Not at hAll
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hAll
      refine ⟨?_, ?_, ?_⟩
      · push Not
        exact ⟨g1, g2, g3, g4⟩
      · intro h
        rcases (hdeg1 p.1 p.2).mp h with h' | h'
        · exact g5 h'
        · exact g6 h'
      · intro h
        rcases (hdeg2 p.1 p.2).mp h with h' | h'
        · exact g7 h'
        · exact g8 h'
  have hfc : ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + D ∧ 2 * p.2 ≠ 2 * p.1 + D + H))
      = (univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter
          (fun p => p.2 ∉ exclusionsEven m d p.1) :=
    Finset.filter_congr fun p _ => hcond p
  rw [hfc]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := (univ : Finset (ZMod (2 ^ m)))) (fun x _ => mem_univ _)]
  have hfiber : ∀ i0 : ZMod (2 ^ m),
      (((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter
          (fun p => p.2 ∉ exclusionsEven m d p.1)).filter (fun p => p.1 = i0)).card
        = ((univ : Finset (ZMod (2 ^ m))).filter
            (fun k => k ∉ exclusionsEven m d i0)).card := by
    intro i0
    apply Finset.card_nbij (fun p => p.2)
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ,
        true_and] at hp ⊢
      rw [← hp.2]
      exact hp.1
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ,
        true_and] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) hpq
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hk
      exact ⟨(i0, k), by simp [hk], rfl⟩
  rw [Finset.sum_congr rfl fun i0 _ => hfiber i0]
  have hcount : ∀ i0 : ZMod (2 ^ m),
      ((univ : Finset (ZMod (2 ^ m))).filter (fun k => k ∉ exclusionsEven m d i0)).card
        = 2 ^ m - 8 := by
    intro i0
    have hsd : (univ : Finset (ZMod (2 ^ m))).filter (fun k => k ∉ exclusionsEven m d i0)
        = univ \ exclusionsEven m d i0 := by
      ext k
      simp [mem_sdiff]
    rw [hsd, card_sdiff, Finset.inter_univ, card_univ, ZMod.card,
      card_exclusionsEven hm hd2 hd0 hdn hdh i0]
  rw [Finset.sum_congr rfl fun i0 _ => hcount i0, Finset.sum_const, card_univ,
    ZMod.card, smul_eq_mul]

end Even

/-! ## The grand total: the family count over all classes -/

section Total

/-- Odd numbers in `[1, 2h')` number exactly `h'`. -/
theorem card_odd_Ico (h' : ℕ) :
    ((Finset.Ico 1 (2 * h')).filter (fun d => d % 2 = 1)).card = h' := by
  have himg : (Finset.Ico 1 (2 * h')).filter (fun d => d % 2 = 1)
      = (Finset.range h').image (fun k => 2 * k + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨x / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega),
    Finset.card_range]

/-- Even numbers in `[1, 2h')` number exactly `h' − 1`. -/
theorem card_even_Ico (h' : ℕ) :
    ((Finset.Ico 1 (2 * h')).filter (fun d => ¬ d % 2 = 1)).card = h' - 1 := by
  have himg : (Finset.Ico 1 (2 * h')).filter (fun d => ¬ d % 2 = 1)
      = (Finset.range (h' - 1)).image (fun k => 2 * k + 2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨x / 2 - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega),
    Finset.card_range]

/-- **THE FAMILY GRAND TOTAL.** Summing the parametrized chord-law counts over all
non-antipodal classes `d ∈ [1, 2^(m−1))`: exactly `2^(m−1)·(2^m − 4)²` ordered
solutions — i.e. **`n(n−4)²/2` ordered, `n(n−4)²/8` unordered family triples**, the
probe-exact closed form of the slanted family layer, now a theorem at every scale. -/
theorem chord_family_grand_total (hm : 2 ≤ m) :
    ∑ d ∈ Finset.Ico 1 (2 ^ (m - 1)),
      ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).card
      = 2 ^ (m - 1) * (2 ^ m - 4) ^ 2 := by
  have h1 : 1 ≤ m := by omega
  have hsplitN : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel h1] at h
    omega
  have hq2 : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 2)
    rw [show m - 2 + 1 = m - 1 from by omega] at h
    omega
  have hq0 : 0 < 2 ^ (m - 2) := Nat.two_pow_pos _
  -- per-class evaluation
  have hsum : ∀ d ∈ Finset.Ico 1 (2 ^ (m - 1)),
      ((univ : Finset (ZMod (2 ^ m) × ZMod (2 ^ m))).filter (fun p =>
        p.2 ∉ exclusions m d p.1
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
        ∧ 2 * p.2 ≠ 2 * p.1 + (d : ZMod (2 ^ m))
            + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).card
      = if d % 2 = 1 then 2 ^ m * (2 ^ m - 4) else 2 ^ m * (2 ^ m - 8) := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    by_cases hpar : d % 2 = 1
    · rw [if_pos hpar]
      exact chord_param_count_odd hm hpar
    · rw [if_neg hpar]
      exact chord_param_count_even hm (by omega) (by omega) (by omega) (by omega)
  rw [Finset.sum_congr rfl hsum, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul]
  have hIco : (2 ^ (m - 1) : ℕ) = 2 * 2 ^ (m - 2) := by omega
  rw [hIco, card_odd_Ico, card_even_Ico]
  -- the closing arithmetic, exact through truncated subtraction
  rcases (show m = 2 ∨ 3 ≤ m from by omega) with rfl | hm3
  · decide
  · have h8 : 8 ≤ 2 ^ m := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    have h2k : 2 ≤ 2 ^ (m - 2) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    zify [h8, by omega, h2k, show (4 : ℕ) ≤ 2 ^ m from by omega,
      show (1 : ℕ) ≤ 2 ^ (m - 2) from by omega]
    have hn4 : (2 ^ m : ℤ) = 4 * 2 ^ (m - 2) := by
      have : ((2 ^ m : ℕ) : ℤ) = ((4 * 2 ^ (m - 2) : ℕ) : ℤ) := by
        congr 1
        omega
      push_cast at this
      exact_mod_cast this
    rw [hn4]
    ring

end Total

/-! ## Source audit -/

#print axioms oddCast_ne_double
#print axioms card_exclusions
#print axioms chord_param_count_odd
#print axioms double_eq_zero_iff
#print axioms card_exclusionsEven
#print axioms chord_param_count_even
#print axioms chord_family_grand_total

end ArkLib.ProximityGap.ChordFamilyCount
