/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ChordConverseCore
import ArkLib.Data.CodingTheory.ProximityGap.SecondLayerConverseCore
import ArkLib.Data.CodingTheory.ProximityGap.WideCircuitTrichotomy
import ArkLib.Data.CodingTheory.ProximityGap.ChordFamilyCount

/-!
# The chord converse, wrapped: from `Balanced` to the chord form over `ZMod (2^m)`

Campaign #357, exactness-converse lane, increment 2b. This file welds the abstract
antipodal-branch classification (`ChordConverseCore.chord_of_antipodal_partner`) to the
matching frame's ℕ-side data:

* `cast_signedExp` — the frame's shifted exponent family `signedExp` casts to the core's
  `chordStack` over `ZMod (2^m)`;
* `closure_of_balanced` — `Balanced` supplies the antipodal-partner closure of the cast
  stack (the fiber-count argument, both halves of the residue range);
* `natCast_zmod_ne` / kernel / half-period bridges — `Distinct6`, multiplicity-freeness
  and the doubling-kernel hypotheses in `ZMod` form;
* **`chord_form_of_balanced_antipodal₂`** — the assembled ℕ-side theorem: a balanced
  multiplicity-free `Distinct6` triple, generic (pairwise-distinct products, pairs 1 and
  3 not antipodal) with pair 2 antipodal, satisfies the chord-law form in `ZMod (2^m)`;
* `stack_swap₁₂` / `stack_swap₂₃` — odd relabelings act on the stack as an explicit
  index involution composed with the global `+h` translation, so injectivity and
  closure transport to the other two antipodal labelings;
* **`chord_form_of_balanced_antipodal₁` / `₃`** — the relabeled wrappers.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357; `CollinearityMatchingFrame.lean` (the `Balanced` frame),
  `ChordConverseCore.lean` (the case tree), `TwoPlusAntipodalChordLaw.lean` (supply).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.ChordConverseWrapper

open ArkLib.ProximityGap.CollinearityMatchingFrame
open ArkLib.ProximityGap.CollinearityCensusTransfer
open ArkLib.ProximityGap.ChordConverseCore
open ArkLib.ProximityGap.WideCircuitTrichotomy (Distinct6)
open ArkLib.ProximityGap.ChordFamilyCount

variable {m : ℕ}

/-! ## Cast bridges -/

/-- Distinct naturals below the modulus have distinct casts. -/
theorem natCast_zmod_ne {a b n : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (a : ZMod n) ≠ (b : ZMod n) := by
  intro h
  exact hab (by
    have := (ZMod.natCast_eq_natCast_iff a b n).mp h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)

/-- The half-period is nonzero in `ZMod (2^m)`. -/
theorem half_ne_zero (hm : 1 ≤ m) : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
  intro h
  have hdvd : 2 ^ m ∣ 2 ^ (m - 1) := (ZMod.natCast_eq_zero_iff _ _).mp h
  have hlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hpos : 0 < 2 ^ (m - 1) := by positivity
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- The half-period doubles to zero. -/
theorem half_add_half (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  rw [← Nat.cast_add, hsplit, ZMod.natCast_self]

/-- The doubling kernel of `ZMod (2^m)` is `{0, 2^(m−1)}` (the core's `hker` input). -/
theorem kernel_of_double (hm : 1 ≤ m) (u : ZMod (2 ^ m)) (hu : u + u = 0) :
    u = 0 ∨ u = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) :=
  (double_eq_zero_iff hm u).mp (by linear_combination hu)

/-- The frame's shifted exponent family casts to the core's `chordStack`. -/
theorem cast_signedExp (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) (x : Fin 12) :
    ((signedExp m a₁ b₁ a₂ b₂ a₃ b₃ x : ℕ) : ZMod (2 ^ m))
      = chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
          (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) x := by
  fin_cases x <;>
    simp only [signedExp, censusExp, censusWt, chordStack, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ] <;>
    norm_num <;> push_cast <;> ring

/-- **Closure from balance**: every element of the cast stack has an antipodal partner. -/
theorem closure_of_balanced (hm : 1 ≤ m) {E : Fin 12 → ℕ}
    (hbal : Balanced m E) (x : Fin 12) :
    ∃ y : Fin 12, ((E y : ℕ) : ZMod (2 ^ m))
      = ((E x : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  have h2 : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have hnpos : 0 < 2 ^ m := by positivity
  have hhpos : 0 < 2 ^ (m - 1) := by positivity
  set t := E x % 2 ^ m with ht
  have htlt : t < 2 ^ m := Nat.mod_lt _ hnpos
  by_cases hcase : t < 2 ^ (m - 1)
  · -- the fiber at `t + h` matches the fiber at `t`, which contains `x`
    have hcard := hbal t hcase
    have hxmem : x ∈ (univ : Finset (Fin 12)).filter (fun z => E z % 2 ^ m = t) := by
      simp [ht]
    have hpos : 0 < ((univ : Finset (Fin 12)).filter
        (fun z => E z % 2 ^ m = t + 2 ^ (m - 1))).card := by
      rw [← hcard]
      exact card_pos.mpr ⟨x, hxmem⟩
    obtain ⟨y, hy⟩ := card_pos.mp hpos
    refine ⟨y, ?_⟩
    have hyr : E y % 2 ^ m = t + 2 ^ (m - 1) := by
      simpa using (mem_filter.mp hy).2
    have key : E y % 2 ^ m = (E x + 2 ^ (m - 1)) % 2 ^ m := by
      rw [Nat.add_mod, ← ht, Nat.mod_eq_of_lt (show 2 ^ (m - 1) < 2 ^ m by omega),
        Nat.mod_eq_of_lt (show t + 2 ^ (m - 1) < 2 ^ m by omega)]
      exact hyr
    calc ((E y : ℕ) : ZMod (2 ^ m))
        = ((E x + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr key
    _ = ((E x : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
          push_cast; ring
  · -- `t = t' + h`; the fiber at `t'` matches the fiber at `t`, which contains `x`
    set t' := t - 2 ^ (m - 1) with ht'
    have ht'lt : t' < 2 ^ (m - 1) := by omega
    have htt' : t = t' + 2 ^ (m - 1) := by omega
    have hcard := hbal t' ht'lt
    have hxmem : x ∈ (univ : Finset (Fin 12)).filter
        (fun z => E z % 2 ^ m = t' + 2 ^ (m - 1)) := by
      simp [← htt', ht]
    have hpos : 0 < ((univ : Finset (Fin 12)).filter
        (fun z => E z % 2 ^ m = t')).card := by
      rw [hcard]
      exact card_pos.mpr ⟨x, hxmem⟩
    obtain ⟨y, hy⟩ := card_pos.mp hpos
    refine ⟨y, ?_⟩
    have hyr : E y % 2 ^ m = t' := by simpa using (mem_filter.mp hy).2
    have key : E y % 2 ^ m = (E x + 2 ^ (m - 1)) % 2 ^ m := by
      rw [Nat.add_mod, ← ht, Nat.mod_eq_of_lt (show 2 ^ (m - 1) < 2 ^ m by omega),
        htt', show t' + 2 ^ (m - 1) + 2 ^ (m - 1) = t' + 2 ^ m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (show t' < 2 ^ m by omega)]
      exact hyr
    calc ((E y : ℕ) : ZMod (2 ^ m))
        = ((E x + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr key
    _ = ((E x : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
          push_cast; ring

/-! ## The assembled wrapper, pair-2 labeling -/

/-- Multiplicity-freeness of the shifted family, in residue form: the canonical formal
statement of "the 12 shifted exponents are pairwise distinct mod `2^m`". -/
def MultFree (m : ℕ) (E : Fin 12 → ℕ) : Prop :=
  ∀ x y : Fin 12, E x % 2 ^ m = E y % 2 ^ m → x = y

/-- `MultFree` gives injectivity of the cast stack. -/
theorem cast_injective_of_multFree {E : Fin 12 → ℕ} (hmf : MultFree m E) :
    Function.Injective (fun x => ((E x : ℕ) : ZMod (2 ^ m))) := by
  intro x y hxy
  exact hmf x y (by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mp hxy
    exact this)

/-- **The chord converse over `ZMod (2^m)`, pair-2 antipodal labeling.** A balanced,
multiplicity-free, `Distinct6` exponent-triple with all six exponents below `2^m`,
pairwise-distinct products, pair `2` antipodal and pairs `1`, `3` not antipodal,
satisfies the two-plus-antipodal chord-law form. -/
theorem chord_form_of_balanced_antipodal₂ (hm : 2 ≤ m)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ}
    (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m)
    (hD6 : Distinct6 a₁ b₁ a₂ b₂ a₃ b₃)
    (hbal : Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hmf : MultFree m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hg12 : (a₁ + b₁) % 2 ^ m ≠ (a₂ + b₂) % 2 ^ m)
    (hg23 : (a₂ + b₂) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m)
    (hant₂ : b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₁ : b₁ ≠ (a₁ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₃ : b₃ ≠ (a₃ + 2 ^ (m - 1)) % 2 ^ m) :
    ((a₁ : ZMod (2 ^ m)) - b₁ = (a₃ : ZMod (2 ^ m)) - b₃
        ∧ 2 * (a₂ : ZMod (2 ^ m)) = a₁ + b₃)
      ∨ ((a₁ : ZMod (2 ^ m)) - b₁ = (b₃ : ZMod (2 ^ m)) - a₃
        ∧ 2 * (a₂ : ZMod (2 ^ m)) = a₁ + a₃) := by
  obtain ⟨⟨h11, h22, h33⟩, ⟨h12, h1b2, hb12, hb1b2⟩, ⟨h13, h1b3, hb13, hb1b3⟩,
    ⟨h23, h2b3, hb23, hb2b3⟩⟩ := hD6
  have hm1 : 1 ≤ m := by omega
  have hnpos : (0 : ℕ) < 2 ^ m := by positivity
  -- the ZMod-side antipodal/non-antipodal facts
  have hmod_iff : ∀ a b : ℕ, b < 2 ^ m →
      (b = (a + 2 ^ (m - 1)) % 2 ^ m
        ↔ (b : ZMod (2 ^ m)) = (a : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro a b hb
    constructor
    · intro h
      rw [h, ZMod.natCast_mod]
      push_cast
      ring
    · intro h
      have : (b : ZMod (2 ^ m)) = ((a + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        rw [h]; push_cast; ring
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp this
      rw [Nat.ModEq, Nat.mod_eq_of_lt hb] at hmod
      exact hmod
  have hant₂' : (b₂ : ZMod (2 ^ m)) = (a₂ : ZMod (2 ^ m)) + _ :=
    (hmod_iff a₂ b₂ hb₂).mp hant₂
  have hna₁' : (b₁ : ZMod (2 ^ m)) ≠ (a₁ : ZMod (2 ^ m)) + _ :=
    fun h => hna₁ ((hmod_iff a₁ b₁ hb₁).mpr h)
  have hna₃' : (b₃ : ZMod (2 ^ m)) ≠ (a₃ : ZMod (2 ^ m)) + _ :=
    fun h => hna₃ ((hmod_iff a₃ b₃ hb₃).mpr h)
  -- the products in cast form
  have hg12' : (a₁ : ZMod (2 ^ m)) + b₁ ≠ (a₂ : ZMod (2 ^ m)) + b₂ := by
    intro h
    apply hg12
    have : ((a₁ + b₁ : ℕ) : ZMod (2 ^ m)) = ((a₂ + b₂ : ℕ) : ZMod (2 ^ m)) := by
      push_cast; linear_combination h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hg23' : (a₂ : ZMod (2 ^ m)) + b₂ ≠ (a₃ : ZMod (2 ^ m)) + b₃ := by
    intro h
    apply hg23
    have : ((a₂ + b₂ : ℕ) : ZMod (2 ^ m)) = ((a₃ + b₃ : ℕ) : ZMod (2 ^ m)) := by
      push_cast; linear_combination h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  -- injectivity and closure of the cast stack, transported through `cast_signedExp`
  have hinj : Function.Injective
      (chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
        (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro x y hxy
    refine cast_injective_of_multFree hmf ?_
    simpa only [cast_signedExp] using hxy
  have hclosed : ∀ x : Fin 12, ∃ y : Fin 12,
      chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
          (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) y
        = chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
            (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
            ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) x
          + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    intro x
    obtain ⟨y, hy⟩ := closure_of_balanced hm1 hbal x
    exact ⟨y, by simpa only [cast_signedExp] using hy⟩
  -- the core
  exact chord_of_antipodal_partner (half_add_half hm1) (half_ne_zero hm1)
    (kernel_of_double hm1)
    (natCast_zmod_ne ha₁ hb₁ h11)
    (natCast_zmod_ne ha₁ ha₂ h12) (natCast_zmod_ne ha₁ hb₂ h1b2)
    (natCast_zmod_ne hb₁ ha₂ hb12) (natCast_zmod_ne hb₁ hb₂ hb1b2)
    (natCast_zmod_ne ha₁ ha₃ h13) (natCast_zmod_ne ha₁ hb₃ h1b3)
    (natCast_zmod_ne hb₁ ha₃ hb13) (natCast_zmod_ne hb₁ hb₃ hb1b3)
    hg12' hg23' hant₂' hna₁' hna₃' hinj hclosed

/-! ## Relabeling transports

Odd point-relabelings act on the shifted stack as an explicit index involution composed
with the global `+h` translation, so injectivity and closure transport directly. -/

section Transport

variable {R : Type*} [CommRing R]

/-- The index involution of the `(1↔2)` point swap. -/
def swapPerm₁₂ : Fin 12 → Fin 12 := fun x =>
  match x with
  | 0 => 4 | 1 => 5 | 2 => 8 | 3 => 9 | 4 => 0 | 5 => 1
  | 6 => 10 | 7 => 11 | 8 => 2 | 9 => 3 | 10 => 6 | 11 => 7

/-- The index involution of the `(2↔3)` point swap. -/
def swapPerm₂₃ : Fin 12 → Fin 12 := fun x =>
  match x with
  | 0 => 6 | 1 => 7 | 2 => 10 | 3 => 11 | 4 => 8 | 5 => 9
  | 6 => 0 | 7 => 1 | 8 => 4 | 9 => 5 | 10 => 2 | 11 => 3

theorem swapPerm₁₂_involutive : ∀ x, swapPerm₁₂ (swapPerm₁₂ x) = x := by decide

theorem swapPerm₂₃_involutive : ∀ x, swapPerm₂₃ (swapPerm₂₃ x) = x := by decide

/-- The `(1↔2)` swap = `swapPerm₁₂` + global `h`-translation. -/
theorem stack_swap₁₂ {A₁ B₁ A₂ B₂ A₃ B₃ h : R} (hh2 : h + h = 0) (x : Fin 12) :
    chordStack A₂ B₂ A₁ B₁ A₃ B₃ h x
      = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h (swapPerm₁₂ x) + h := by
  fin_cases x <;>
    simp only [swapPerm₁₂, chordStack] <;>
    first | linear_combination -hh2 | linear_combination (0 : R) * hh2

/-- The `(2↔3)` swap = `swapPerm₂₃` + global `h`-translation. -/
theorem stack_swap₂₃ {A₁ B₁ A₂ B₂ A₃ B₃ h : R} (hh2 : h + h = 0) (x : Fin 12) :
    chordStack A₁ B₁ A₃ B₃ A₂ B₂ h x
      = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h (swapPerm₂₃ x) + h := by
  fin_cases x <;>
    simp only [swapPerm₂₃, chordStack] <;>
    first | linear_combination -hh2 | linear_combination (0 : R) * hh2

/-- The orientation swap `a₁ ↔ b₁` is the pure index swap `(4 5)(8 9)` — no
translation. With `stack_swap₁₂`/`stack_swap₂₃` and the analogous `a₂ ↔ b₂`
(`(0 1)(2 3)`), `a₃ ↔ b₃` (`(6 7)(10 11)`) swaps, the full 48-element relabeling
group acts on the shifted stack by index permutations and `+h`-translations — the
canonicalization kit for the collision-branch emission. -/
theorem stack_bswap₁ {A₁ B₁ A₂ B₂ A₃ B₃ h : R} (x : Fin 12) :
    chordStack B₁ A₁ A₂ B₂ A₃ B₃ h x
      = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h
          ((fun y => match y with
            | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | z => z) x : Fin 12) := by
  fin_cases x <;> simp only [chordStack] <;> ring

/-- The orientation swap `a₂ ↔ b₂` is the pure index swap `(0 1)(2 3)`. -/
theorem stack_bswap₂ {A₁ B₁ A₂ B₂ A₃ B₃ h : R} (x : Fin 12) :
    chordStack A₁ B₁ B₂ A₂ A₃ B₃ h x
      = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h
          ((fun y => match y with
            | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | z => z) x : Fin 12) := by
  fin_cases x <;> simp only [chordStack] <;> ring

/-- The orientation swap `a₃ ↔ b₃` is the pure index swap `(6 7)(10 11)`. -/
theorem stack_bswap₃ {A₁ B₁ A₂ B₂ A₃ B₃ h : R} (x : Fin 12) :
    chordStack A₁ B₁ A₂ B₂ B₃ A₃ h x
      = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h
          ((fun y => match y with
            | 6 => 7 | 7 => 6 | 10 => 11 | 11 => 10 | z => z) x : Fin 12) := by
  fin_cases x <;> simp only [chordStack] <;> ring

/-- Injectivity transports along a stack-swap law. -/
theorem inj_of_swap {f g : Fin 12 → R} {h : R} {π : Fin 12 → Fin 12}
    (hπ : ∀ x, π (π x) = x) (hlaw : ∀ x, g x = f (π x) + h)
    (hinj : Function.Injective f) : Function.Injective g := by
  intro x y hxy
  rw [hlaw, hlaw] at hxy
  have hp := hinj (add_right_cancel hxy)
  have := congrArg π hp
  rwa [hπ, hπ] at this

/-- Closure transports along a stack-swap law. -/
theorem closed_of_swap {f g : Fin 12 → R} {h : R} {π : Fin 12 → Fin 12}
    (hπ : ∀ x, π (π x) = x) (hlaw : ∀ x, g x = f (π x) + h)
    (hclosed : ∀ x, ∃ y, f y = f x + h) : ∀ x, ∃ y, g y = g x + h := by
  intro x
  obtain ⟨y₀, hy₀⟩ := hclosed (π x)
  refine ⟨π y₀, ?_⟩
  rw [hlaw, hlaw, hπ, hy₀]

end Transport

/-! ## The relabeled chord wrappers -/

/-- **Pair-1-antipodal labeling**: pairs 2 and 3 share a difference class with the chord
congruence at `A₁`. -/
theorem chord_form_of_balanced_antipodal₁ (hm : 2 ≤ m)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ}
    (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m)
    (hD6 : Distinct6 a₁ b₁ a₂ b₂ a₃ b₃)
    (hbal : Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hmf : MultFree m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hg12 : (a₁ + b₁) % 2 ^ m ≠ (a₂ + b₂) % 2 ^ m)
    (hg13 : (a₁ + b₁) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m)
    (hant₁ : b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₂ : b₂ ≠ (a₂ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₃ : b₃ ≠ (a₃ + 2 ^ (m - 1)) % 2 ^ m) :
    ((a₂ : ZMod (2 ^ m)) - b₂ = (a₃ : ZMod (2 ^ m)) - b₃
        ∧ 2 * (a₁ : ZMod (2 ^ m)) = a₂ + b₃)
      ∨ ((a₂ : ZMod (2 ^ m)) - b₂ = (b₃ : ZMod (2 ^ m)) - a₃
        ∧ 2 * (a₁ : ZMod (2 ^ m)) = a₂ + a₃) := by
  obtain ⟨⟨h11, h22, h33⟩, ⟨h12, h1b2, hb12, hb1b2⟩, ⟨h13, h1b3, hb13, hb1b3⟩,
    ⟨h23, h2b3, hb23, hb2b3⟩⟩ := hD6
  have hm1 : 1 ≤ m := by omega
  have hmod_iff : ∀ a b : ℕ, b < 2 ^ m →
      (b = (a + 2 ^ (m - 1)) % 2 ^ m
        ↔ (b : ZMod (2 ^ m)) = (a : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro a b hb
    constructor
    · intro h
      rw [h, ZMod.natCast_mod]
      push_cast
      ring
    · intro h
      have hcast : (b : ZMod (2 ^ m)) = ((a + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        rw [h]; push_cast; ring
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hb] at hmod
  have hgcast : ∀ a b c d : ℕ, (a + b) % 2 ^ m ≠ (c + d) % 2 ^ m →
      (a : ZMod (2 ^ m)) + b ≠ (c : ZMod (2 ^ m)) + d := by
    intro a b c d hne h
    apply hne
    have : ((a + b : ℕ) : ZMod (2 ^ m)) = ((c + d : ℕ) : ZMod (2 ^ m)) := by
      push_cast; linear_combination h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  -- transport injectivity and closure through the (1↔2) swap law
  have hinj₀ : Function.Injective
      (chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
        (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro x y hxy
    refine cast_injective_of_multFree hmf ?_
    simpa only [cast_signedExp] using hxy
  have hclosed₀ : ∀ x : Fin 12, ∃ y : Fin 12,
      chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
          (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) y
        = chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
            (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
            ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) x
          + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    intro x
    obtain ⟨y, hy⟩ := closure_of_balanced hm1 hbal x
    exact ⟨y, by simpa only [cast_signedExp] using hy⟩
  exact chord_of_antipodal_partner (half_add_half hm1) (half_ne_zero hm1)
    (kernel_of_double hm1)
    (natCast_zmod_ne ha₂ hb₂ h22)
    (natCast_zmod_ne ha₂ ha₁ (Ne.symm h12)) (natCast_zmod_ne ha₂ hb₁ (Ne.symm hb12))
    (natCast_zmod_ne hb₂ ha₁ (Ne.symm h1b2)) (natCast_zmod_ne hb₂ hb₁ (Ne.symm hb1b2))
    (natCast_zmod_ne ha₂ ha₃ h23) (natCast_zmod_ne ha₂ hb₃ h2b3)
    (natCast_zmod_ne hb₂ ha₃ hb23) (natCast_zmod_ne hb₂ hb₃ hb2b3)
    (fun h => hgcast a₂ b₂ a₁ b₁ (fun h' => hg12 h'.symm) h)
    (hgcast a₁ b₁ a₃ b₃ hg13)
    ((hmod_iff a₁ b₁ hb₁).mp hant₁)
    (fun h => hna₂ ((hmod_iff a₂ b₂ hb₂).mpr h))
    (fun h => hna₃ ((hmod_iff a₃ b₃ hb₃).mpr h))
    (inj_of_swap swapPerm₁₂_involutive (stack_swap₁₂ (half_add_half hm1)) hinj₀)
    (closed_of_swap swapPerm₁₂_involutive (stack_swap₁₂ (half_add_half hm1)) hclosed₀)

/-- **Pair-3-antipodal labeling**: pairs 1 and 2 share a difference class with the chord
congruence at `A₃`. -/
theorem chord_form_of_balanced_antipodal₃ (hm : 2 ≤ m)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ}
    (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m)
    (hD6 : Distinct6 a₁ b₁ a₂ b₂ a₃ b₃)
    (hbal : Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hmf : MultFree m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hg13 : (a₁ + b₁) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m)
    (hg23 : (a₂ + b₂) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m)
    (hant₃ : b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₁ : b₁ ≠ (a₁ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₂ : b₂ ≠ (a₂ + 2 ^ (m - 1)) % 2 ^ m) :
    ((a₁ : ZMod (2 ^ m)) - b₁ = (a₂ : ZMod (2 ^ m)) - b₂
        ∧ 2 * (a₃ : ZMod (2 ^ m)) = a₁ + b₂)
      ∨ ((a₁ : ZMod (2 ^ m)) - b₁ = (b₂ : ZMod (2 ^ m)) - a₂
        ∧ 2 * (a₃ : ZMod (2 ^ m)) = a₁ + a₂) := by
  obtain ⟨⟨h11, h22, h33⟩, ⟨h12, h1b2, hb12, hb1b2⟩, ⟨h13, h1b3, hb13, hb1b3⟩,
    ⟨h23, h2b3, hb23, hb2b3⟩⟩ := hD6
  have hm1 : 1 ≤ m := by omega
  have hmod_iff : ∀ a b : ℕ, b < 2 ^ m →
      (b = (a + 2 ^ (m - 1)) % 2 ^ m
        ↔ (b : ZMod (2 ^ m)) = (a : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro a b hb
    constructor
    · intro h
      rw [h, ZMod.natCast_mod]
      push_cast
      ring
    · intro h
      have hcast : (b : ZMod (2 ^ m)) = ((a + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        rw [h]; push_cast; ring
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hb] at hmod
  have hgcast : ∀ a b c d : ℕ, (a + b) % 2 ^ m ≠ (c + d) % 2 ^ m →
      (a : ZMod (2 ^ m)) + b ≠ (c : ZMod (2 ^ m)) + d := by
    intro a b c d hne h
    apply hne
    have : ((a + b : ℕ) : ZMod (2 ^ m)) = ((c + d : ℕ) : ZMod (2 ^ m)) := by
      push_cast; linear_combination h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hinj₀ : Function.Injective
      (chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
        (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro x y hxy
    refine cast_injective_of_multFree hmf ?_
    simpa only [cast_signedExp] using hxy
  have hclosed₀ : ∀ x : Fin 12, ∃ y : Fin 12,
      chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
          (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) y
        = chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
            (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
            ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) x
          + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    intro x
    obtain ⟨y, hy⟩ := closure_of_balanced hm1 hbal x
    exact ⟨y, by simpa only [cast_signedExp] using hy⟩
  exact chord_of_antipodal_partner (half_add_half hm1) (half_ne_zero hm1)
    (kernel_of_double hm1)
    (natCast_zmod_ne ha₁ hb₁ h11)
    (natCast_zmod_ne ha₁ ha₃ h13) (natCast_zmod_ne ha₁ hb₃ h1b3)
    (natCast_zmod_ne hb₁ ha₃ hb13) (natCast_zmod_ne hb₁ hb₃ hb1b3)
    (natCast_zmod_ne ha₁ ha₂ h12) (natCast_zmod_ne ha₁ hb₂ h1b2)
    (natCast_zmod_ne hb₁ ha₂ hb12) (natCast_zmod_ne hb₁ hb₂ hb1b2)
    (hgcast a₁ b₁ a₃ b₃ hg13)
    (fun h => hgcast a₂ b₂ a₃ b₃ hg23 (by linear_combination -h))
    ((hmod_iff a₃ b₃ hb₃).mp hant₃)
    (fun h => hna₁ ((hmod_iff a₁ b₁ hb₁).mpr h))
    (fun h => hna₂ ((hmod_iff a₂ b₂ hb₂).mpr h))
    (inj_of_swap swapPerm₂₃_involutive (stack_swap₂₃ (half_add_half hm1)) hinj₀)
    (closed_of_swap swapPerm₂₃_involutive (stack_swap₂₃ (half_add_half hm1)) hclosed₀)

/-! ## The no-antipodal wrapper and the assembly -/

open ArkLib.ProximityGap.SecondLayerConverseCore in
/-- **The second-layer converse over `ZMod (2^m)`**: a balanced multiplicity-free
`Distinct6` triple, generic, with NO antipodal pair satisfies one of the eight
second-layer seed systems. -/
theorem secondLayer_form_of_balanced_no_antipodal (hm : 2 ≤ m)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ}
    (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m)
    (hD6 : Distinct6 a₁ b₁ a₂ b₂ a₃ b₃)
    (hbal : Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hmf : MultFree m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hg12 : (a₁ + b₁) % 2 ^ m ≠ (a₂ + b₂) % 2 ^ m)
    (hg13 : (a₁ + b₁) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m)
    (hg23 : (a₂ + b₂) % 2 ^ m ≠ (a₃ + b₃) % 2 ^ m)
    (hna₁ : b₁ ≠ (a₁ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₂ : b₂ ≠ (a₂ + 2 ^ (m - 1)) % 2 ^ m)
    (hna₃ : b₃ ≠ (a₃ + 2 ^ (m - 1)) % 2 ^ m) :
    (((b₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((b₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((b₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((b₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))) := by
  obtain ⟨⟨h11, h22, h33⟩, ⟨h12, h1b2, hb12, hb1b2⟩, ⟨h13, h1b3, hb13, hb1b3⟩,
    ⟨h23, h2b3, hb23, hb2b3⟩⟩ := hD6
  have hm1 : 1 ≤ m := by omega
  have hmod_iff : ∀ a b : ℕ, b < 2 ^ m →
      (b = (a + 2 ^ (m - 1)) % 2 ^ m
        ↔ (b : ZMod (2 ^ m)) = (a : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro a b hb
    constructor
    · intro h
      rw [h, ZMod.natCast_mod]
      push_cast
      ring
    · intro h
      have hcast : (b : ZMod (2 ^ m)) = ((a + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        rw [h]; push_cast; ring
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hb] at hmod
  have hgcast : ∀ a b c d : ℕ, (a + b) % 2 ^ m ≠ (c + d) % 2 ^ m →
      (a : ZMod (2 ^ m)) + b ≠ (c : ZMod (2 ^ m)) + d := by
    intro a b c d hne h
    apply hne
    have : ((a + b : ℕ) : ZMod (2 ^ m)) = ((c + d : ℕ) : ZMod (2 ^ m)) := by
      push_cast; linear_combination h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hinj₀ : Function.Injective
      (chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
        (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
        ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) := by
    intro x y hxy
    refine cast_injective_of_multFree hmf ?_
    simpa only [cast_signedExp] using hxy
  have hclosed₀ : ∀ x : Fin 12, ∃ y : Fin 12,
      chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
          (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
          ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) y
        = chordStack (a₁ : ZMod (2 ^ m)) (b₁ : ZMod (2 ^ m)) (a₂ : ZMod (2 ^ m))
            (b₂ : ZMod (2 ^ m)) (a₃ : ZMod (2 ^ m)) (b₃ : ZMod (2 ^ m))
            ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) x
          + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    intro x
    obtain ⟨y, hy⟩ := closure_of_balanced hm1 hbal x
    exact ⟨y, by simpa only [cast_signedExp] using hy⟩
  exact secondLayer_of_no_antipodal (half_add_half hm1) (half_ne_zero hm1)
    (kernel_of_double hm1)
    (natCast_zmod_ne ha₁ hb₁ h11) (natCast_zmod_ne ha₂ hb₂ h22)
    (natCast_zmod_ne ha₃ hb₃ h33)
    (natCast_zmod_ne ha₁ ha₂ h12) (natCast_zmod_ne ha₁ hb₂ h1b2)
    (natCast_zmod_ne hb₁ ha₂ hb12) (natCast_zmod_ne hb₁ hb₂ hb1b2)
    (natCast_zmod_ne ha₁ ha₃ h13) (natCast_zmod_ne ha₁ hb₃ h1b3)
    (natCast_zmod_ne hb₁ ha₃ hb13) (natCast_zmod_ne hb₁ hb₃ hb1b3)
    (natCast_zmod_ne ha₂ ha₃ h23) (natCast_zmod_ne ha₂ hb₃ h2b3)
    (natCast_zmod_ne hb₂ ha₃ hb23) (natCast_zmod_ne hb₂ hb₃ hb2b3)
    (hgcast a₁ b₁ a₂ b₂ hg12) (hgcast a₁ b₁ a₃ b₃ hg13) (hgcast a₂ b₂ a₃ b₃ hg23)
    (fun h => hna₁ ((hmod_iff a₁ b₁ hb₁).mpr h))
    (fun h => hna₂ ((hmod_iff a₂ b₂ hb₂).mpr h))
    (fun h => hna₃ ((hmod_iff a₃ b₃ hb₃).mpr h))
    hinj₀ hclosed₀

/-- **THE SIMPLE-STRATUM CLASSIFICATION** (the exactness converse on the
multiplicity-free stratum): every balanced multiplicity-free `Distinct6` exponent
triple is horizontal, vertical, a two-plus-antipodal chord-law triple (in one of the
three labelings), or satisfies one of the eight second-layer seed systems. -/
theorem simple_wideCircuit_classification (hm : 2 ≤ m)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ}
    (ha₁ : a₁ < 2 ^ m) (hb₁ : b₁ < 2 ^ m) (ha₂ : a₂ < 2 ^ m) (hb₂ : b₂ < 2 ^ m)
    (ha₃ : a₃ < 2 ^ m) (hb₃ : b₃ < 2 ^ m)
    (hD6 : Distinct6 a₁ b₁ a₂ b₂ a₃ b₃)
    (hbal : Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))
    (hmf : MultFree m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃)) :
    -- horizontal
    ((a₁ + b₁) % 2 ^ m = (a₂ + b₂) % 2 ^ m ∧ (a₂ + b₂) % 2 ^ m = (a₃ + b₃) % 2 ^ m)
    -- vertical
    ∨ (b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m ∧ b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
        ∧ b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m)
    -- chord, antipodal pair 1
    ∨ (b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m
        ∧ (((a₂ : ZMod (2 ^ m)) - b₂ = (a₃ : ZMod (2 ^ m)) - b₃
              ∧ 2 * (a₁ : ZMod (2 ^ m)) = a₂ + b₃)
          ∨ ((a₂ : ZMod (2 ^ m)) - b₂ = (b₃ : ZMod (2 ^ m)) - a₃
              ∧ 2 * (a₁ : ZMod (2 ^ m)) = a₂ + a₃)))
    -- chord, antipodal pair 2
    ∨ (b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
        ∧ (((a₁ : ZMod (2 ^ m)) - b₁ = (a₃ : ZMod (2 ^ m)) - b₃
              ∧ 2 * (a₂ : ZMod (2 ^ m)) = a₁ + b₃)
          ∨ ((a₁ : ZMod (2 ^ m)) - b₁ = (b₃ : ZMod (2 ^ m)) - a₃
              ∧ 2 * (a₂ : ZMod (2 ^ m)) = a₁ + a₃)))
    -- chord, antipodal pair 3
    ∨ (b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m
        ∧ (((a₁ : ZMod (2 ^ m)) - b₁ = (a₂ : ZMod (2 ^ m)) - b₂
              ∧ 2 * (a₃ : ZMod (2 ^ m)) = a₁ + b₂)
          ∨ ((a₁ : ZMod (2 ^ m)) - b₁ = (b₂ : ZMod (2 ^ m)) - a₂
              ∧ 2 * (a₃ : ZMod (2 ^ m)) = a₁ + a₂)))
    -- second layer
    ∨ (((b₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((b₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((b₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((b₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + b₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + b₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + b₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = a₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = a₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))
    ∨ ((a₂ : ZMod (2 ^ m)) + a₃ = a₁ + b₁ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₃ : ZMod (2 ^ m)) + b₃ = b₁ + a₂ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∧ (a₂ : ZMod (2 ^ m)) + b₂ = b₁ + a₃ + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))) := by
  have hm1 : 1 ≤ m := by omega
  rcases ArkLib.ProximityGap.WideCircuitTrichotomy.balanced_trichotomy hm1 ha₁ hb₁ ha₂
    hb₂ ha₃ hb₃ hD6 hbal with hH | hV | ⟨⟨hM12, hM13, hM23⟩, hno12, hno13, hno23⟩
  · exact Or.inl hH
  · exact Or.inr (Or.inl hV)
  · by_cases h1 : b₁ = (a₁ + 2 ^ (m - 1)) % 2 ^ m
    · have hna₂ : b₂ ≠ (a₂ + 2 ^ (m - 1)) % 2 ^ m := fun h => hno12 ⟨h1, h⟩
      have hna₃ : b₃ ≠ (a₃ + 2 ^ (m - 1)) % 2 ^ m := fun h => hno13 ⟨h1, h⟩
      exact Or.inr (Or.inr (Or.inl ⟨h1, chord_form_of_balanced_antipodal₁ hm ha₁ hb₁
        ha₂ hb₂ ha₃ hb₃ hD6 hbal hmf hM12 hM13 h1 hna₂ hna₃⟩))
    by_cases h2 : b₂ = (a₂ + 2 ^ (m - 1)) % 2 ^ m
    · have hna₃ : b₃ ≠ (a₃ + 2 ^ (m - 1)) % 2 ^ m := fun h => hno23 ⟨h2, h⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, chord_form_of_balanced_antipodal₂ hm
        ha₁ hb₁ ha₂ hb₂ ha₃ hb₃ hD6 hbal hmf hM12 hM23 h2 h1 hna₃⟩)))
    by_cases h3 : b₃ = (a₃ + 2 ^ (m - 1)) % 2 ^ m
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3,
        chord_form_of_balanced_antipodal₃ hm ha₁ hb₁ ha₂ hb₂ ha₃ hb₃ hD6 hbal hmf hM13
          hM23 h3 h1 h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (secondLayer_form_of_balanced_no_antipodal hm ha₁ hb₁ ha₂ hb₂ ha₃ hb₃ hD6 hbal
          hmf hM12 hM13 hM23 h1 h2 h3)))))

/-! ## Source audit -/

#print axioms cast_signedExp
#print axioms closure_of_balanced
#print axioms chord_form_of_balanced_antipodal₂
#print axioms chord_form_of_balanced_antipodal₁
#print axioms chord_form_of_balanced_antipodal₃
#print axioms secondLayer_form_of_balanced_no_antipodal
#print axioms simple_wideCircuit_classification

end ArkLib.ProximityGap.ChordConverseWrapper
