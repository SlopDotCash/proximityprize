/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RatioProductNorm
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryRatioSlotFacts

/-! # A split 127-bit prime with a nonlifting three-ratio comparison -/

namespace ProximityGap.Mu128ExceptionalTriple
open ArkLib.ProximityGap.BinaryPower (binaryPow binaryPow_eq_pow)
open RatioProductNorm

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem lucas_of_list (p g : ℕ) (L : List ℕ) (nonzero : p-1≠0)
    (factors : L.prod=p-1) (primes : ∀ q∈L,Nat.Prime q)
    (full : binaryPow (g:ZMod p) (p-1)=1)
    (proper : L.all (fun q => decide (binaryPow (g:ZMod p) ((p-1)/q) ≠ 1))=true) :
    p.Prime := by
  apply lucas_primality p g (by rwa [←binaryPow_eq_pow])
  intro q prime divides
  have mem := (Nat.mem_primeFactorsList_iff_dvd nonzero prime).mpr divides
  have inList := (Nat.primeFactorsList_unique factors primes).mem_iff.mpr mem
  rw [←binaryPow_eq_pow]
  exact of_decide_eq_true ((List.all_eq_true.mp proper) q inList)

private theorem prime₁ : Nat.Prime 4018782934171 := by
  apply lucas_of_list _ 2 [2,3,3,5,23,313,6202687] (by decide) (by decide) _ (by decide) (by decide)
  intro q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

private theorem prime₂ : Nat.Prime 9824580508551939943 := by
  apply lucas_of_list _ 5 [2,3,7,19,23,7211,42467,1747979] (by decide) (by decide) _ (by decide) (by decide)
  intro q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

/-- Largest candidate surviving the full comparison sieve above 2^126. -/
abbrev p : ℕ := 105018080988161859083316683155074219521

theorem prime : Nat.Prime p := by
  apply lucas_of_list _ 3 [2,2,2,2,2,2,2,2,2,5,1039,4018782934171,9824580508551939943]
    (by decide) (by decide) _ (by decide) (by decide)
  intro q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact prime₁ | exact prime₂ | norm_num

instance : Fact p.Prime := ⟨prime⟩

abbrev root : ZMod p := 34402880081108728517061612743246827085

theorem primitive : IsPrimitiveRoot root 128 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  exact orderOf_eq_prime_pow (p:=2) (n:=6) (by decide) (by decide)

abbrev left : Fin 3 → ℕ := ![64,64,102]
abbrev right : Fin 3 → ℕ := ![37,65,65]

/-- The repeated entry is the selected site; each record has two distinct
entries available for its unordered pair. -/
theorem comparison_fails_to_transfer :
    profile root 1 left = profile root 1 right ∧
    profile (AuxiliaryRatioSlotData.root : AuxiliaryRatioSlotFacts.F) 1 left ≠
      profile (AuxiliaryRatioSlotData.root : AuxiliaryRatioSlotFacts.F) 1 right := by
  simp only [profile,Fin.prod_univ_three,left,right,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  constructor
  · field_simp (disch := decide)
    decide
  · intro equal
    field_simp (disch := decide) at equal
    exact (by decide : ¬ _) equal

end ProximityGap.Mu128ExceptionalTriple

#print axioms ProximityGap.Mu128ExceptionalTriple.prime
#print axioms ProximityGap.Mu128ExceptionalTriple.comparison_fails_to_transfer
