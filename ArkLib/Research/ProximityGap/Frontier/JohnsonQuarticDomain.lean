/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarLiteralEps
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar

/-! # The smooth order-sixteen domain with 128-bit MCA budget 111 -/

namespace ProximityGap.JohnsonQuarticMca

open Code

/-- A field size with an integer 128-bit budget of 111. -/
abbrev p : ℕ := 37771342728224169444434581424926271471617

theorem prime_p : p.Prime := by
  have hm : (10 : ZMod p) ^ (p - 1) = 1 := by reduce_mod_char
  apply lucas_primality p 10 hm
  intro v hv hd
  rw [show p - 1 = 2 ^ 128 * (3 * 37) by decide] at hd
  rcases hv.dvd_mul.mp hd with h | h
  · have e := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow h)
    subst v
    reduce_mod_char
    decide
  · rcases hv.dvd_mul.mp h with h | h
    · have e := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 3)).mp h
      subst v
      reduce_mod_char
      decide
    · have e := (Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 37)).mp h
      subst v
      reduce_mod_char
      decide

instance : Fact p.Prime := ⟨prime_p⟩

abbrev K := ZMod p

def generator : Kˣ := Units.mk0 33819743976114766565336136445278419449068 (by decide)

theorem generator_order : orderOf generator = 2 ^ 4 := by
  rw [← orderOf_units]
  apply orderOf_eq_prime_pow (p := 2) (n := 3) <;> decide

def domain : Fin 16 ↪ K := MCADeltaStarLiteralEps.smoothDom p generator generator_order

noncomputable instance smooth : ReedSolomon.Smooth domain where
  H := Subgroup.zpowers generator
  a := 1
  h_card_pow2 := ⟨4, Fintype.card_fin _⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨generator ^ i.val, Subgroup.npow_mem_zpowers _ _, one_mul _⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hu)
      have his := Finset.mem_range.mp hi
      rw [generator_order] at his
      exact Finset.mem_image.mpr ⟨⟨i, his⟩, Finset.mem_univ _, (one_mul _).symm⟩

private theorem modulus_budget : p / 2 ^ 128 = 111 := by decide

private theorem card_K : Fintype.card K = p := ZMod.card p

theorem budget : Fintype.card K / 2 ^ 128 = 111 :=
  (congrArg (fun q : ℕ => q / 2 ^ 128) card_K).trans modulus_budget

end ProximityGap.JohnsonQuarticMca
