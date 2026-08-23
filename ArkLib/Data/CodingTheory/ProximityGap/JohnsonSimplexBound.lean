/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The second-moment (Johnson) list-size bound, via the simplex embedding (verified, self-contained)

This proves the **Johnson list-size bound** from first principles, `sorry`-free and axiom-clean. It
is independent of the `ArkLib.JohnsonList`/`ArkLib.Coverage` chain, which now also has a clean named
denominator form (`ArkLib.Coverage.card_mul_sub_le_of_agreement`). It is the genuine, honest version
of the second row of the ABF26 table (Issue #232 §3, the Johnson-radius regime).

**Statement (`johnson_simplex_bound`).** Let `L` be a finite set of words `ι → F`, each agreeing with
a fixed word `w` on `≥ a` of the `n = |ι|` coordinates, and pairwise agreeing on `≤ b` coordinates.
Then `|L| · (a² − n·b) ≤ n²`. When `n·b < a²` this caps the list size by `n²/(a² − n·b)`.

**Proof.** The q-ary *simplex embedding* `φ(x)(i,c) = [x i = c]` into `ℝ^(ι×F)` has
`⟨φ x, φ y⟩ = agree(x,y)`. With `A = Σ_{c∈L} φ c`: Cauchy–Schwarz gives `⟨A,φ w⟩² ≤ ⟨A,A⟩·⟨φ w,φ w⟩
= ⟨A,A⟩·n`; the target sum `⟨A,φ w⟩ = Σ agree(c,w) ≥ |L|·a`; the Gram sum `⟨A,A⟩ = Σ_{c,c'} agree(c,c')
≤ |L|·n + |L|(|L|−1)·b`. Combining and cancelling one `|L|` gives `|L|(a²−nb) ≤ n²`.
-/

namespace ArkLib.CodingTheory.JohnsonSimplex

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- Number of coordinates on which `x` and `y` agree. -/
def agree (x y : ι → F) : ℕ := (Finset.univ.filter (fun i => x i = y i)).card

/-- A word agrees with itself everywhere. -/
lemma agree_self (x : ι → F) : agree x x = Fintype.card ι := by
  rw [agree, Finset.filter_true_of_mem (fun i _ => rfl), Finset.card_univ]

/-- The q-ary simplex embedding: `φ(x)(i,c) = 1` if `x i = c`, else `0`. -/
noncomputable def phi (x : ι → F) : ι × F → ℝ := fun p => if x p.1 = p.2 then 1 else 0

/-- **Inner product of two embeddings = agreement count.** `⟨φ x, φ y⟩ = agree(x,y)`. -/
lemma sum_phi_mul (x y : ι → F) :
    ∑ p : ι × F, phi x p * phi y p = (agree x y : ℝ) := by
  rw [Fintype.sum_prod_type]
  have inner : ∀ i : ι, (∑ c : F, phi x (i, c) * phi y (i, c)) = if x i = y i then (1 : ℝ) else 0 := by
    intro i
    simp only [phi]
    rw [Finset.sum_eq_single (x i)]
    · rw [if_pos rfl, one_mul]
      by_cases h : x i = y i
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    · intro c _ hc
      rw [if_neg (fun hh => hc hh.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun i _ => inner i), agree, Finset.sum_boole]

/-- `⟨φ x, φ x⟩ = n`. -/
lemma sum_phi_self (x : ι → F) :
    ∑ p : ι × F, phi x p * phi x p = (Fintype.card ι : ℝ) := by
  rw [sum_phi_mul, agree_self]

/-- **The Johnson second-moment list-size bound.** A finite set `L` of words, each agreeing with `w`
on `≥ a` coordinates and pairwise agreeing on `≤ b`, satisfies `|L| · (a² − n·b) ≤ n²` (`n = |ι|`). -/
theorem johnson_simplex_bound (L : Finset (ι → F)) (w : ι → F) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hclose : ∀ c ∈ L, a ≤ (agree c w : ℝ))
    (hpair : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → (agree c c' : ℝ) ≤ b) :
    (L.card : ℝ) * (a ^ 2 - (Fintype.card ι : ℝ) * b) ≤ (Fintype.card ι : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ (L.card : ℝ) := by positivity
  set A : ι × F → ℝ := fun p => ∑ c ∈ L, phi c p with hA
  -- Target sum.
  have hAw : (∑ p : ι × F, A p * phi w p) = ∑ c ∈ L, (agree c w : ℝ) := by
    simp only [hA, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => sum_phi_mul c w)
  -- Gram sum.
  have hAA : (∑ p : ι × F, A p * A p) = ∑ c ∈ L, ∑ c' ∈ L, (agree c c' : ℝ) := by
    simp only [hA]
    rw [Finset.sum_congr rfl
      (fun p _ => Finset.sum_mul_sum L L (fun c => phi c p) (fun c' => phi c' p))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c' _ => sum_phi_mul c c')
  have hww : (∑ p : ι × F, phi w p * phi w p) = (Fintype.card ι : ℝ) := sum_phi_self w
  -- Cauchy–Schwarz on `ι × F`.
  have hCS : (∑ p : ι × F, A p * phi w p) ^ 2
      ≤ (∑ p : ι × F, A p ^ 2) * (∑ p : ι × F, phi w p ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ A (phi w)
  have hsqA : (∑ p : ι × F, A p ^ 2) = ∑ p : ι × F, A p * A p := by simp [pow_two]
  have hsqw : (∑ p : ι × F, phi w p ^ 2) = ∑ p : ι × F, phi w p * phi w p := by simp [pow_two]
  rw [hsqA, hsqw, hAA, hww, hAw] at hCS
  -- Lower bound on the target sum: `Σ_c agree(c,w) ≥ |L|·a`.
  have hTarget : (L.card : ℝ) * a ≤ ∑ c ∈ L, (agree c w : ℝ) := by
    calc (L.card : ℝ) * a = ∑ _c ∈ L, a := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ L, (agree c w : ℝ) := Finset.sum_le_sum hclose
  -- Upper bound on the Gram sum: `Σ_{c,c'} agree(c,c') ≤ |L|·n + |L|(|L|−1)·b`.
  have hGram : (∑ c ∈ L, ∑ c' ∈ L, (agree c c' : ℝ))
      ≤ (L.card : ℝ) * (Fintype.card ι : ℝ) + (L.card : ℝ) * ((L.card : ℝ) - 1) * b := by
    have hrow : ∀ c ∈ L, (∑ c' ∈ L, (agree c c' : ℝ))
        ≤ (Fintype.card ι : ℝ) + ((L.card : ℝ) - 1) * b := by
      intro c hc
      have hub : ∀ c' ∈ L, (agree c c' : ℝ) ≤ (if c' = c then (Fintype.card ι : ℝ) else b) := by
        intro c' hc'
        by_cases h : c' = c
        · rw [if_pos h, h, agree_self]
        · rw [if_neg h]; exact hpair c hc c' hc' (fun hh => h hh.symm)
      calc (∑ c' ∈ L, (agree c c' : ℝ))
          ≤ ∑ c' ∈ L, (if c' = c then (Fintype.card ι : ℝ) else b) := Finset.sum_le_sum hub
        _ = (Fintype.card ι : ℝ) + ((L.card : ℝ) - 1) * b := by
            have hsplit : ∀ c' : ι → F,
                (if c' = c then (Fintype.card ι : ℝ) else b)
                  = b + (if c' = c then (Fintype.card ι : ℝ) - b else 0) := by
              intro c'; by_cases h : c' = c <;> simp [h]
            rw [Finset.sum_congr rfl (fun c' _ => hsplit c'), Finset.sum_add_distrib,
              Finset.sum_const, nsmul_eq_mul,
              Finset.sum_ite_eq' L c (fun _ => (Fintype.card ι : ℝ) - b), if_pos hc]
            ring
    calc (∑ c ∈ L, ∑ c' ∈ L, (agree c c' : ℝ))
        ≤ ∑ _c ∈ L, ((Fintype.card ι : ℝ) + ((L.card : ℝ) - 1) * b) := Finset.sum_le_sum hrow
      _ = (L.card : ℝ) * (Fintype.card ι : ℝ) + (L.card : ℝ) * ((L.card : ℝ) - 1) * b := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- Combine and cancel one factor of `|L|`.
  have hne0 : (0 : ℝ) ≤ (L.card : ℝ) * a := by positivity
  have hMain : ((L.card : ℝ) * a) ^ 2
      ≤ ((L.card : ℝ) * (Fintype.card ι : ℝ)
          + (L.card : ℝ) * ((L.card : ℝ) - 1) * b) * (Fintype.card ι : ℝ) := by
    calc ((L.card : ℝ) * a) ^ 2 ≤ (∑ c ∈ L, (agree c w : ℝ)) ^ 2 := by
          rw [pow_two, pow_two]; exact mul_self_le_mul_self hne0 hTarget
      _ ≤ (∑ c ∈ L, ∑ c' ∈ L, (agree c c' : ℝ)) * (Fintype.card ι : ℝ) := hCS
      _ ≤ _ := mul_le_mul_of_nonneg_right hGram hN0
  rcases Nat.eq_zero_or_pos L.card with h0 | hpos
  · rw [h0]; simp
  · have hposR : (0 : ℝ) < (L.card : ℝ) := by exact_mod_cast hpos
    have hcancel : (L.card : ℝ) * ((L.card : ℝ) * (a ^ 2 - (Fintype.card ι : ℝ) * b))
        ≤ (L.card : ℝ) * ((Fintype.card ι : ℝ) ^ 2) := by
      nlinarith [hMain, mul_nonneg (mul_nonneg hm0 hb) hN0]
    exact le_of_mul_le_mul_left hcancel hposR

end ArkLib.CodingTheory.JohnsonSimplex
