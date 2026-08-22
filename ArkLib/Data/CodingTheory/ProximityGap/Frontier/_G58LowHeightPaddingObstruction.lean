/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G56AllDepthPatternDecomposition
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# G58: low-height wraparound persists under antipodal padding

G56 counts nonzero folded patterns that vanish at a primitive `2m`-th root.  This file records the
exact obstruction that such shallow patterns cannot disappear at larger moment depth: append any
`k` antipodal exponent pairs `(a, a + m)`.  The appended pairs contribute
`X^a - X^a = 0` to the folded pattern, so nonzero-ness and evaluation vanishing are unchanged.

The main theorem is the finite-cardinality injection

`wraparoundExcessR ζ m s * (2*m)^k ≤ wraparoundExcessR ζ m (s+k)`.

The concrete section pins the famous thin prime `21523361`: in `ZMod 21523361`, `3` has order
`32`, and the depth-`2` folded relation `X - 3` vanishes at `3`.  Padding then gives a positive
depth-`17` lower bound.
-/

set_option autoImplicit false
set_option linter.style.openClassical false

open Finset Polynomial
open scoped Classical

namespace ArkLib.ProximityGap.Frontier.G58LowHeightPaddingObstruction

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition (monomF)
open ArkLib.ProximityGap.Frontier.G56AllDepthPatternDecomposition

variable {F : Type*} [Field F]

def antipodeExp (m : ℕ) (a : Fin (2 * m)) : Fin (2 * m) :=
  if ha : a.val < m then
    ⟨a.val + m, by omega⟩
  else
    ⟨a.val - m, by omega⟩

/-- One antipodal padding pair contributes zero to the folded pattern. -/
theorem monomF_add_antipodeExp (m : ℕ) (a : Fin (2 * m)) :
    monomF m a.val + monomF m (antipodeExp m a).val = 0 := by
  unfold monomF
  unfold antipodeExp
  by_cases ha : a.val < m
  · rw [dif_pos ha]
    simp only
    rw [if_pos ha, if_neg (by omega : ¬ a.val + m < m)]
    have hsub : a.val + m - m = a.val := by omega
    rw [hsub]
    abel
  · rw [dif_neg ha]
    simp only
    rw [if_neg ha, if_pos (by omega : a.val - m < m)]
    abel

/-- Append `k` antipodal exponent pairs `(a, a+m)` after a shallow tuple. -/
noncomputable def padTuple (m s k : ℕ)
    (t : Fin (2 * s) → Fin (2 * m)) (a : Fin k → Fin (2 * m)) :
    Fin (2 * (s + k)) → Fin (2 * m) :=
  (Fin.append t (Fin.append a (fun j => antipodeExp m (a j)))) ∘
    Fin.cast (by omega : 2 * (s + k) = 2 * s + (k + k))

theorem padTuple_base (m s k : ℕ)
    (t : Fin (2 * s) → Fin (2 * m)) (a : Fin k → Fin (2 * m)) (i : Fin (2 * s)) :
    padTuple m s k t a ⟨i.val, by omega⟩ = t i := by
  change Fin.append t (Fin.append a (fun j => antipodeExp m (a j)))
      (Fin.cast (by omega : 2 * (s + k) = 2 * s + (k + k)) ⟨i.val, by omega⟩) = t i
  rw [show Fin.cast (by omega : 2 * (s + k) = 2 * s + (k + k)) ⟨i.val, by omega⟩ =
      Fin.castAdd (k + k) i by ext; simp]
  simp

theorem padTuple_left (m s k : ℕ)
    (t : Fin (2 * s) → Fin (2 * m)) (a : Fin k → Fin (2 * m)) (j : Fin k) :
    padTuple m s k t a ⟨2 * s + j.val, by omega⟩ = a j := by
  change Fin.append t (Fin.append a (fun j => antipodeExp m (a j)))
      (Fin.cast (by omega : 2 * (s + k) = 2 * s + (k + k)) ⟨2 * s + j.val, by omega⟩) = a j
  rw [show Fin.cast (by omega : 2 * (s + k) = 2 * s + (k + k))
        ⟨2 * s + j.val, by omega⟩ = Fin.natAdd (2 * s) (Fin.castAdd k j) by
      ext
      simp]
  simp

theorem padTuple_right (m s k : ℕ)
    (t : Fin (2 * s) → Fin (2 * m)) (a : Fin k → Fin (2 * m)) (j : Fin k) :
    padTuple m s k t a ⟨2 * s + k + j.val, by omega⟩ = antipodeExp m (a j) := by
  change Fin.append t (Fin.append a (fun j => antipodeExp m (a j)))
      (Fin.cast (by omega : 2 * (s + k) = 2 * s + (k + k))
        ⟨2 * s + k + j.val, by omega⟩) = antipodeExp m (a j)
  rw [show Fin.cast (by omega : 2 * (s + k) = 2 * s + (k + k))
        ⟨2 * s + k + j.val, by omega⟩ = Fin.natAdd (2 * s) (Fin.natAdd k j) by
      ext
      simp
      omega]
  rw [Fin.append_right, Fin.append_right]

private theorem sum_fin_append {α : Type*} [AddCommMonoid α] (m n : ℕ)
    (f : Fin (m + n) → α) :
    ∑ i : Fin (m + n), f i =
      (∑ i : Fin m, f (Fin.castAdd n i)) + (∑ j : Fin n, f (Fin.natAdd m j)) := by
  calc
    ∑ i : Fin (m + n), f i = ∑ x : Fin m ⊕ Fin n, f (finSumFinEquiv x) := by
      exact (Equiv.sum_comp finSumFinEquiv f).symm
    _ = (∑ i : Fin m, f (Fin.castAdd n i)) + (∑ j : Fin n, f (Fin.natAdd m j)) := by
      simp

private theorem sum_fin_two_blocks {α : Type*} [AddCommMonoid α] (s k : ℕ)
    (f : Fin (2 * (s + k)) → α) :
    ∑ i : Fin (2 * (s + k)), f i =
      (∑ i : Fin (2 * s), f ⟨i.val, by omega⟩)
        + (∑ j : Fin k, f ⟨2 * s + j.val, by omega⟩)
        + (∑ j : Fin k, f ⟨2 * s + k + j.val, by omega⟩) := by
  calc
    ∑ i : Fin (2 * (s + k)), f i
        = ∑ i : Fin (2 * s + (k + k)),
            f (Fin.cast (by omega : 2 * s + (k + k) = 2 * (s + k)) i) := by
          exact (Equiv.sum_comp (finCongr (by omega : 2 * s + (k + k) = 2 * (s + k))) f).symm
    _ = (∑ i : Fin (2 * s), f ⟨i.val, by omega⟩)
        + (∑ j : Fin k, f ⟨2 * s + j.val, by omega⟩)
        + (∑ j : Fin k, f ⟨2 * s + k + j.val, by omega⟩) := by
          rw [sum_fin_append (2 * s) (k + k)]
          rw [sum_fin_append k k]
          have hA :
              (∑ i : Fin (2 * s),
                f (Fin.cast (by omega : 2 * s + (k + k) = 2 * (s + k))
                  (Fin.castAdd (k + k) i))) =
              ∑ i : Fin (2 * s), f ⟨i.val, by omega⟩ := by
            apply sum_congr rfl
            intro i _
            apply congrArg f
            ext
            simp
          have hB :
              (∑ j : Fin k,
                f (Fin.cast (by omega : 2 * s + (k + k) = 2 * (s + k))
                  (Fin.natAdd (2 * s) (Fin.castAdd k j)))) =
              ∑ j : Fin k, f ⟨2 * s + j.val, by omega⟩ := by
            apply sum_congr rfl
            intro j _
            apply congrArg f
            ext
            simp
          have hC :
              (∑ j : Fin k,
                f (Fin.cast (by omega : 2 * s + (k + k) = 2 * (s + k))
                  (Fin.natAdd (2 * s) (Fin.natAdd k j)))) =
              ∑ j : Fin k, f ⟨2 * s + k + j.val, by omega⟩ := by
            apply sum_congr rfl
            intro j _
            apply congrArg f
            ext
            simp
            omega
          rw [hA, hB, hC]
          rw [add_assoc]

/-- Antipodal padding leaves the folded pattern unchanged. -/
theorem foldedPattern_padTuple (m s k : ℕ)
    (t : Fin (2 * s) → Fin (2 * m)) (a : Fin k → Fin (2 * m)) :
    foldedPattern m (2 * (s + k)) (padTuple m s k t a) = foldedPattern m (2 * s) t := by
  unfold foldedPattern
  rw [sum_fin_two_blocks s k]
  simp only [padTuple_base, padTuple_left, padTuple_right]
  have hpairs :
      (∑ j : Fin k, monomF m (a j).val)
        + (∑ j : Fin k, monomF m (antipodeExp m (a j)).val) = 0 := by
    rw [← sum_add_distrib]
    exact sum_eq_zero (fun j _ => monomF_add_antipodeExp m (a j))
  rw [add_assoc, hpairs, add_zero]

private theorem padTuple_injective_on_source {m s k : ℕ}
    {x y : (Fin (2 * s) → Fin (2 * m)) × (Fin k → Fin (2 * m))}
    (hxy : padTuple m s k x.1 x.2 = padTuple m s k y.1 y.2) :
    x = y := by
  rcases x with ⟨t, a⟩
  rcases y with ⟨u, b⟩
  have ht : t = u := by
    funext i
    have := congrFun hxy ⟨i.val, by omega⟩
    simpa [padTuple_base] using this
  have ha : a = b := by
    funext j
    have := congrFun hxy ⟨2 * s + j.val, by omega⟩
    simpa [padTuple_left] using this
  simp [ht, ha]

/-- The exact injective persistence theorem: each shallow wraparound tuple and each `k`-tuple of
full exponent padding choices gives a distinct depth-`s+k` wraparound tuple. -/
theorem wraparoundExcessR_mul_two_mul_m_pow_le_pad {ζ : F} {m s k : ℕ} :
    wraparoundExcessR ζ m s * (2 * m) ^ k ≤ wraparoundExcessR ζ m (s + k) := by
  classical
  let Wold :=
    (expTupleSet m (2 * s)).filter
      (fun t => foldedPattern m (2 * s) t ≠ 0 ∧
        aeval ζ (foldedPattern m (2 * s) t) = 0)
  let Wnew :=
    (expTupleSet m (2 * (s + k))).filter
      (fun t => foldedPattern m (2 * (s + k)) t ≠ 0 ∧
        aeval ζ (foldedPattern m (2 * (s + k)) t) = 0)
  have hcardOld : Wold.card = wraparoundExcessR ζ m s := by rfl
  have hcardNew : Wnew.card = wraparoundExcessR ζ m (s + k) := by rfl
  have hcardChoices : (expTupleSet m k).card = (2 * m) ^ k := by
    unfold expTupleSet
    rw [Fintype.card_piFinset]
    simp [Finset.card_univ]
  have hle :
      (Wold.product (expTupleSet m k)).card ≤ Wnew.card := by
    refine Finset.card_le_card_of_injOn
      (fun p : (Fin (2 * s) → Fin (2 * m)) × (Fin k → Fin (2 * m)) =>
        padTuple m s k p.1 p.2) ?map ?inj
    · intro p hp
      change p ∈ Wold ×ˢ expTupleSet m k at hp
      rw [Finset.mem_product] at hp
      obtain ⟨ht, ha⟩ := hp
      change p.1 ∈
        ((expTupleSet m (2 * s)).filter
          (fun t => foldedPattern m (2 * s) t ≠ 0 ∧
            aeval ζ (foldedPattern m (2 * s) t) = 0)) at ht
      rw [Finset.mem_filter] at ht
      change padTuple m s k p.1 p.2 ∈
        ((expTupleSet m (2 * (s + k))).filter
          (fun t => foldedPattern m (2 * (s + k)) t ≠ 0 ∧
            aeval ζ (foldedPattern m (2 * (s + k)) t) = 0))
      rw [Finset.mem_filter]
      have hfold := foldedPattern_padTuple m s k p.1 p.2
      constructor
      · unfold expTupleSet
        rw [Fintype.mem_piFinset]
        intro i
        simp
      · simpa [hfold] using ht.2
    · intro x hx y hy hxy
      exact padTuple_injective_on_source hxy
  simpa [hcardOld, hcardChoices, hcardNew, Finset.card_product] using hle

section Concrete21523361

local instance fact_prime_21523361 : Fact (Nat.Prime 21523361) := ⟨by norm_num⟩

/-- In the thin field `F_21523361`, `3` has exact order `32`. -/
theorem orderOf_3_zmod21523361 : orderOf (3 : ZMod 21523361) = 32 := by
  have h16 : ¬ (3 : ZMod 21523361) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (3 : ZMod 21523361) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (3 : ZMod 21523361)) h16 h32
  norm_num at h
  exact h

/-- `3` is a primitive 32nd root in `F_21523361`. -/
theorem isPrimitiveRoot_3_32_zmod21523361 :
    IsPrimitiveRoot (3 : ZMod 21523361) 32 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_3_zmod21523361

/-- The depth-2 low-height folded relation `X - 3`, represented as four exponents
`1, 16, 16, 16`, is a nonzero folded pattern that vanishes at `ζ = 3`. -/
theorem lowHeight_depth2_relation_zmod21523361 :
    ∃ t : Fin 4 → Fin 32,
      foldedPattern 16 4 t = X - C (3 : ℤ) ∧
      foldedPattern 16 4 t ≠ 0 ∧
      aeval (3 : ZMod 21523361) (foldedPattern 16 4 t) = 0 := by
  let t : Fin 4 → Fin 32 := fun i =>
    match i.val with
    | 0 => ⟨1, by norm_num⟩
    | 1 => ⟨16, by norm_num⟩
    | 2 => ⟨16, by norm_num⟩
    | _ => ⟨16, by norm_num⟩
  have hpoly : foldedPattern 16 4 t = X - C (3 : ℤ) := by
    rw [foldedPattern, Fin.sum_univ_four]
    norm_num [t, monomF]
    ring_nf
  refine ⟨t, hpoly, ?_, ?_⟩
  · intro h
    rw [hpoly] at h
    have hcoeff := congrArg (fun P : ℤ[X] => P.coeff 1) h
    norm_num at hcoeff
  · rw [hpoly]
    simp only [map_sub, aeval_X, aeval_C]
    norm_num

/-- The depth-2 wraparound excess for the thin `n = 32`, `p = 21523361` instance is positive. -/
theorem wraparoundExcessR_3_16_2_pos :
    0 < wraparoundExcessR (3 : ZMod 21523361) 16 2 := by
  classical
  letI : DecidableEq (ZMod 21523361) := Classical.decEq _
  rcases lowHeight_depth2_relation_zmod21523361 with ⟨t, _hpoly, htne, hteval⟩
  unfold wraparoundExcessR
  rw [Finset.card_pos]
  refine ⟨t, ?_⟩
  rw [Finset.mem_filter]
  constructor
  · unfold expTupleSet
    rw [Fintype.mem_piFinset]
    intro i
    simp
  · exact ⟨htne, hteval⟩

/-- Padding the concrete depth-2 relation by fifteen antipodal pairs gives positive depth `17`
wraparound mass. -/
theorem wraparoundExcessR_3_16_17_pos :
    0 < wraparoundExcessR (3 : ZMod 21523361) 16 17 := by
  have hle := wraparoundExcessR_mul_two_mul_m_pow_le_pad
    (F := ZMod 21523361) (ζ := (3 : ZMod 21523361)) (m := 16) (s := 2) (k := 15)
  have hpos : 0 < wraparoundExcessR (3 : ZMod 21523361) 16 2 * (2 * 16) ^ 15 :=
    Nat.mul_pos wraparoundExcessR_3_16_2_pos (by norm_num)
  exact lt_of_lt_of_le hpos hle

/-- A concrete lower bound at the log-scale depth `r = 17`. -/
theorem wraparoundExcessR_3_16_17_lower :
    32 ^ 15 ≤ wraparoundExcessR (3 : ZMod 21523361) 16 17 := by
  have hle := wraparoundExcessR_mul_two_mul_m_pow_le_pad
    (F := ZMod 21523361) (ζ := (3 : ZMod 21523361)) (m := 16) (s := 2) (k := 15)
  have hone : 1 ≤ wraparoundExcessR (3 : ZMod 21523361) 16 2 :=
    Nat.succ_le_of_lt wraparoundExcessR_3_16_2_pos
  simpa using le_trans (Nat.mul_le_mul_right ((2 * 16) ^ 15) hone) hle

end Concrete21523361

#print axioms monomF_add_antipodeExp
#print axioms foldedPattern_padTuple
#print axioms wraparoundExcessR_mul_two_mul_m_pow_le_pad
#print axioms orderOf_3_zmod21523361
#print axioms lowHeight_depth2_relation_zmod21523361
#print axioms wraparoundExcessR_3_16_17_lower

end ArkLib.ProximityGap.Frontier.G58LowHeightPaddingObstruction
