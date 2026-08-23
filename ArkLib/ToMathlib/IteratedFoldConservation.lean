/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Iterated fold-mass conservation down the 2-adic tower (issue #232)

The depth-`ℓ` iteration of the O57 fold-mass conservation law. For a valued error
`(S, v)` on a field of characteristic `≠ 2` with `0 ∉ S`, the squaring map folds the
error two ways — the even fold `foldVal` and the odd fold `foldValOdd` — and iterating
`ℓ` times produces `2^ℓ` *branch values* `branchVal S v b`, one per branch word
`b : List Bool` of length `ℓ`, each a function on the `ℓ`-times-squared support
`iterSq S ℓ`.

Main results:

* `fold_mass_conservation` (the 1-level law, re-proved self-contained here): if both
  folds vanish at a squared point `y`, then `v` vanishes on the whole fiber
  `{x ∈ S : x² = y}` — the `2×2` system `(v(x) + v(−x), (v(x) − v(−x))·x)` is
  nonsingular when `2 ≠ 0` and `0 ∉ S`.
* `iterated_fold_conservation`: if ALL `2^ℓ` depth-`ℓ` branch values vanish at a point
  `y`, then `v` vanishes on the entire iterated fiber `{x ∈ S : x^(2^ℓ) = y}` (a set of
  at most `2^ℓ` elements, `iterFiber_card_le`). Induction on `ℓ` over the 1-level law.
* `exists_alive_branch`: if `v` is not identically zero on `S`, then at every depth `ℓ`
  some branch is *alive* — it has a nonzero value at some point of `iterSq S ℓ`.
* `all_branches_dead_iff`: the iff packaging — all depth-`ℓ` branch values vanish on
  `iterSq S ℓ` exactly when `v` vanishes on `S`.

This is the branch-accounting engine for the all-words descent down the tower
(DISPROOF_LOG O57, C19/descent lane): window-vanishing mass cannot silently cancel in
*every* branch — a genuine error keeps at least one live branch at every depth.

Everything is elementary field algebra over an abstract `[Field F]` with
`(2 : F) ≠ 0` — no `CharZero`, no roots of unity.
-/

namespace ArkLib.IteratedFold

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The even folded error values: sums of `v` over squaring fibers. -/
def foldVal (S : Finset F) (v : F → F) (y : F) : F :=
  ∑ x ∈ S.filter (fun x => x ^ 2 = y), v x

/-- The odd folded error values: sums of `v x · x` over squaring fibers. -/
def foldValOdd (S : Finset F) (v : F → F) (y : F) : F :=
  ∑ x ∈ S.filter (fun x => x ^ 2 = y), v x * x

/-- The `ℓ`-times-squared support: `iterSq S ℓ = S^(2^ℓ)` pointwise. -/
def iterSq (S : Finset F) : ℕ → Finset F
  | 0 => S
  | n + 1 => (iterSq S n).image (· ^ 2)

/-- The depth-`|b|` branch value indexed by a branch word `b : List Bool`:
`branchVal S v [] = v`, and prepending `false`/`true` applies the even/odd fold at the
current level. A word of length `ℓ` is a function supported on `iterSq S ℓ`. -/
def branchVal (S : Finset F) (v : F → F) : List Bool → F → F
  | [] => v
  | false :: bs => foldVal (iterSq S bs.length) (branchVal S v bs)
  | true :: bs => foldValOdd (iterSq S bs.length) (branchVal S v bs)

@[simp] theorem branchVal_nil (S : Finset F) (v : F → F) : branchVal S v [] = v := rfl

theorem branchVal_false (S : Finset F) (v : F → F) (bs : List Bool) :
    branchVal S v (false :: bs) = foldVal (iterSq S bs.length) (branchVal S v bs) := rfl

theorem branchVal_true (S : Finset F) (v : F → F) (bs : List Bool) :
    branchVal S v (true :: bs) = foldValOdd (iterSq S bs.length) (branchVal S v bs) := rfl

/-- Membership descends the tower: `x ∈ S` puts `x^(2^ℓ)` in `iterSq S ℓ`. -/
theorem pow_mem_iterSq {S : Finset F} {x : F} (hx : x ∈ S) (ℓ : ℕ) :
    x ^ 2 ^ ℓ ∈ iterSq S ℓ := by
  induction ℓ with
  | zero => simpa using hx
  | succ n ih =>
    show x ^ 2 ^ (n + 1) ∈ (iterSq S n).image (· ^ 2)
    rw [pow_succ, pow_mul]
    exact Finset.mem_image_of_mem _ ih

/-- `0 ∉ S` persists down the tower (fields have no zero divisors). -/
theorem zero_not_mem_iterSq {S : Finset F} (h0 : (0 : F) ∉ S) (ℓ : ℕ) :
    (0 : F) ∉ iterSq S ℓ := by
  induction ℓ with
  | zero => exact h0
  | succ n ih =>
    intro h
    rw [show iterSq S (n + 1) = (iterSq S n).image (· ^ 2) from rfl,
      Finset.mem_image] at h
    obtain ⟨x, hx, hx2⟩ := h
    exact ih (sq_eq_zero_iff.mp hx2 ▸ hx)

/-- **Fold-mass conservation at a fiber** (the 1-level law, self-contained): both folds
vanishing at `y` forces the error to vanish on the entire fiber (characteristic `≠ 2`,
`0 ∉ S`). The single identity `foldValOdd + x·foldVal = 2·x·v(x)` on the fiber of `x²`
replaces the explicit `2×2` system. -/
theorem fold_mass_conservation {S : Finset F} {v : F → F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ S) {y : F}
    (heven : foldVal S v y = 0) (hodd : foldValOdd S v y = 0) :
    ∀ x ∈ S.filter (fun x => x ^ 2 = y), v x = 0 := by
  intro x hx
  obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxS)
  -- every fiber element z ≠ x has z = −x, killing the factor (z + x)
  have hkey : ∑ z ∈ S.filter (fun z => z ^ 2 = y), v z * (z + x) = v x * (x + x) := by
    refine Finset.sum_eq_single_of_mem x hx ?_
    intro b hb hbx
    have hby : b ^ 2 = y := (Finset.mem_filter.mp hb).2
    have hfac : (b - x) * (b + x) = 0 := by linear_combination hby - hxy
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h) hbx
    · rw [show b + x = 0 from by linear_combination h, mul_zero]
  have hexpand : ∑ z ∈ S.filter (fun z => z ^ 2 = y), v z * (z + x)
      = foldValOdd S v y + x * foldVal S v y := by
    rw [foldVal, foldValOdd, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hexpand, heven, hodd, mul_zero, add_zero] at hkey
  -- hkey : 0 = v x * (x + x), i.e. 2·x·v(x) = 0 with 2 ≠ 0, x ≠ 0
  have hvx : v x * ((2 : F) * x) = 0 := by linear_combination -hkey
  rcases mul_eq_zero.mp hvx with h | h
  · exact h
  · exact absurd h (mul_ne_zero h2 hx0)

/-- **Iterated fold-mass conservation**: if all `2^ℓ` depth-`ℓ` branch values vanish at
`y`, then `v` vanishes on the entire iterated fiber `{x ∈ S : x^(2^ℓ) = y}`. -/
theorem iterated_fold_conservation {S : Finset F} {v : F → F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ S) :
    ∀ (ℓ : ℕ) (y : F),
      (∀ b : List Bool, b.length = ℓ → branchVal S v b y = 0) →
      ∀ x ∈ S.filter (fun x => x ^ 2 ^ ℓ = y), v x = 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro y hb x hx
    obtain ⟨_, hxy⟩ := Finset.mem_filter.mp hx
    have hxy' : x = y := by simpa using hxy
    rw [hxy']
    exact hb [] rfl
  | succ n ih =>
    intro y hb x hx
    obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
    -- the intermediate point one level below y
    have hzS : x ^ 2 ^ n ∈ iterSq S n := pow_mem_iterSq hxS n
    have hz2 : (x ^ 2 ^ n) ^ 2 = y := by rw [← pow_mul, ← pow_succ]; exact hxy
    -- both folds of every depth-n branch vanish at y, so every depth-n branch
    -- vanishes on the fiber of y — in particular at x^(2^n)
    have hbranch : ∀ bs : List Bool, bs.length = n →
        branchVal S v bs (x ^ 2 ^ n) = 0 := by
      intro bs hbs
      have heven : foldVal (iterSq S n) (branchVal S v bs) y = 0 := by
        have h := hb (false :: bs) (by rw [List.length_cons, hbs])
        rwa [branchVal_false, hbs] at h
      have hodd : foldValOdd (iterSq S n) (branchVal S v bs) y = 0 := by
        have h := hb (true :: bs) (by rw [List.length_cons, hbs])
        rwa [branchVal_true, hbs] at h
      exact fold_mass_conservation h2 (zero_not_mem_iterSq h0 n) heven hodd _
        (Finset.mem_filter.mpr ⟨hzS, hz2⟩)
    exact ih (x ^ 2 ^ n) hbranch x (Finset.mem_filter.mpr ⟨hxS, rfl⟩)

/-- Converse direction: an error vanishing on `S` has all branch values vanishing on the
iterated supports (the depth-`0` branch is `v` itself, so the support restriction is
needed only there; deeper branches vanish everywhere). -/
theorem branchVal_eq_zero_of_vanish {S : Finset F} {v : F → F}
    (hv : ∀ x ∈ S, v x = 0) :
    ∀ b : List Bool, ∀ y ∈ iterSq S b.length, branchVal S v b y = 0 := by
  intro b
  induction b with
  | nil => exact fun y hy => hv y hy
  | cons c bs ih =>
    intro y _
    cases c with
    | false =>
      rw [branchVal_false, foldVal]
      exact Finset.sum_eq_zero fun z hz => ih z (Finset.mem_filter.mp hz).1
    | true =>
      rw [branchVal_true, foldValOdd]
      exact Finset.sum_eq_zero fun z hz => by
        rw [ih z (Finset.mem_filter.mp hz).1, zero_mul]

/-- **All branches dead ⟺ no error**: the depth-`ℓ` branch values all vanish on the
`ℓ`-times-squared support exactly when `v` vanishes on `S`. -/
theorem all_branches_dead_iff {S : Finset F} {v : F → F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ S) (ℓ : ℕ) :
    (∀ b : List Bool, b.length = ℓ → ∀ y ∈ iterSq S ℓ, branchVal S v b y = 0) ↔
      ∀ x ∈ S, v x = 0 := by
  constructor
  · intro hdead x hxS
    exact iterated_fold_conservation h2 h0 ℓ (x ^ 2 ^ ℓ)
      (fun b hb => hdead b hb _ (pow_mem_iterSq hxS ℓ)) x
      (Finset.mem_filter.mpr ⟨hxS, rfl⟩)
  · intro hv b hb y hy
    exact branchVal_eq_zero_of_vanish hv b y (hb ▸ hy)

/-- **At every depth, some branch is alive**: a not-identically-zero error keeps, at
every depth `ℓ`, at least one branch word whose value is nonzero somewhere on the
`ℓ`-times-squared support. -/
theorem exists_alive_branch {S : Finset F} {v : F → F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ S) (hv : ∃ x ∈ S, v x ≠ 0) (ℓ : ℕ) :
    ∃ b : List Bool, b.length = ℓ ∧ ∃ y ∈ iterSq S ℓ, branchVal S v b y ≠ 0 := by
  obtain ⟨x, hxS, hvx⟩ := hv
  by_contra hcon
  push Not at hcon
  exact hvx ((all_branches_dead_iff h2 h0 ℓ).mp hcon x hxS)

/-- The iterated fiber over `y` has at most `2^ℓ` elements (roots of `X^(2^ℓ) − y`). -/
theorem iterFiber_card_le (S : Finset F) (y : F) (ℓ : ℕ) :
    (S.filter (fun x => x ^ 2 ^ ℓ = y)).card ≤ 2 ^ ℓ := by
  have hsub : S.filter (fun x => x ^ 2 ^ ℓ = y)
      ⊆ (Polynomial.nthRoots (2 ^ ℓ) y).toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset,
      Polynomial.mem_nthRoots (pow_pos (by norm_num) ℓ)]
    exact (Finset.mem_filter.mp hx).2
  calc (S.filter (fun x => x ^ 2 ^ ℓ = y)).card
      ≤ (Polynomial.nthRoots (2 ^ ℓ) y).toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (Polynomial.nthRoots (2 ^ ℓ) y) := Multiset.toFinset_card_le _
    _ ≤ 2 ^ ℓ := Polynomial.card_nthRoots _ _

end ArkLib.IteratedFold

