/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Data.Complex.Basic

/-!
  Round 12 — UNCONDITIONAL Lam–Leung antipodal tightness for GENERAL N = 2^{m-1}.

  Context (Ethereum Proximity Prize, ABF26 / ArkLib #232).  Prior rounds proved
  the Lam–Leung "vanishing sums of roots of unity" tightness at t = 1 only for
  N = 2 (over ℚ(i)), discharging the cyclotomic-independence hypothesis there.
  The general-N discharge — proving that for a primitive 2^m-th root of unity ζ
  the first N = 2^{m-1} powers {ζ^0,…,ζ^{N-1}} are ℚ-linearly independent — was
  scoped OUT because it required the cyclotomic-degree computation.

  This round CLOSES that step for every m ≥ 1.  The chain is:

      minpoly ℚ ζ = cyclotomic(2^m) ℚ         (ζ primitive 2^m-th root, char 0)
      deg(cyclotomic(2^m)) = φ(2^m) = 2^{m-1} = N
   ⟹ {ζ^j : j < N} is ℚ-linearly independent  (PowerBasis.linearIndependent_pow)

  Combined with ζ^N = -1 (ζ^N is a primitive 2nd root of unity), the antipodal
  pairing root(j,true) = -ζ^j = ζ^{j+N} is genuine, and any subset of the 2^m
  roots of unity summing to 0 is negation-symmetric — UNCONDITIONALLY, general N.

  CONCRETE WITNESS:  ζ = Complex.exp(2πI/2^m) in ℂ over ℚ, an explicit primitive
  2^m-th root of unity (Mathlib's `Complex.isPrimitiveRoot_exp`).  We instantiate
  m = 3 (2^m = 8, N = 4) as a numeric example, and exhibit non-vacuity witnesses.

  Self-contained; imports only Mathlib.  Closes with `#print axioms`.
-/

/-!
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

open Polynomial Finset

namespace R12

/-! ## Part 0.  The unconditional linear-independence input (re-stated helper).

`PowerBasis.linearIndependent_pow` (Mathlib) gives, over a field `K`, linear
independence of `{ζ^i : i < (minpoly K ζ).natDegree}`.  We package the first `N`
powers given a degree lower bound `N ≤ (minpoly K ζ).natDegree`. -/

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

/-- UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are
`K`-linearly independent whenever `N ≤ deg(minpoly K ζ)`. -/
theorem linearIndependent_pow_le (ζ : S) {N : ℕ}
    (hN : N ≤ (minpoly K ζ).natDegree) :
    LinearIndependent K (fun j : Fin N => ζ ^ (j : ℕ)) := by
  have hfull : LinearIndependent K (fun i : Fin (minpoly K ζ).natDegree => ζ ^ (i : ℕ)) :=
    _root_.linearIndependent_pow ζ
  have hcomp := hfull.comp (Fin.castLE hN) (Fin.castLE_injective hN)
  simpa [Function.comp, Fin.val_castLE] using hcomp

/-! ## Part 1.  The general antipodal theorem (re-stated helper).

`ζ` is a `2N`-th root of unity with `ζ^N = -1`; the `j`-th and `(j+N)`-th roots
are antipodal, `ζ^(j+N) = -ζ^j`.  Index the `2N` roots by pairs
`(j, b) : Fin N × Bool`, the root at `(j,b)` being `(-1)^b · ζ^j`. -/

variable {N : ℕ}

/-- The value of the root indexed by `(j,b)`:
`root(j,false) = ζ^j`, `root(j,true) = -ζ^j`. -/
def root (ζ : S) (jb : Fin N × Bool) : S :=
  if jb.2 then - ζ ^ (jb.1 : ℕ) else ζ ^ (jb.1 : ℕ)

/-- For a 2N-th root of unity with `ζ^N = -1`, the `(j,true)` root is the genuine
`(j+N)`-th power of `ζ`.  This certifies that our pairing is the true antipodal
pairing of the `2N` roots of unity, not an artificial relabelling. -/
theorem root_true_eq (ζ : S) {N : ℕ} (hpow : ζ ^ N = -1) (j : Fin N) :
    root ζ (j, true) = ζ ^ ((j : ℕ) + N) := by
  simp [root, pow_add, hpow]

/-- **General antipodal tightness.**
If the first `N` powers of `ζ` are `K`-linearly independent (UNCONDITIONAL
whenever `N ≤ deg(minpoly K ζ)`), then any subset `A` of the `2N` antipodal-paired
roots whose values sum to zero is antipodal: it contains `(j,false)` iff it
contains `(j,true)`, for every `j`. -/
theorem antipodal_of_sum_zero {N : ℕ} (ζ : S)
    (hLI : LinearIndependent K (fun j : Fin N => ζ ^ (j : ℕ)))
    (A : Finset (Fin N × Bool))
    (hsum : ∑ a ∈ A, root ζ a = 0) :
    ∀ j : Fin N, ((j, false) ∈ A ↔ (j, true) ∈ A) := by
  classical
  set cF : Fin N → K := fun j => if (j, false) ∈ A then (1 : K) else 0 with hcF
  set cT : Fin N → K := fun j => if (j, true) ∈ A then (1 : K) else 0 with hcT
  set c : Fin N → K := fun j => cF j - cT j with hc
  have hcombo : ∑ j : Fin N, c j • ζ ^ (j : ℕ) = 0 := by
    have hsplit :
        ∑ a ∈ A, root ζ a
          = ∑ j : Fin N, (cF j • ζ ^ (j : ℕ) + cT j • (- ζ ^ (j : ℕ))) := by
      have : ∑ a ∈ A, root ζ a
          = ∑ jb : Fin N × Bool, (if jb ∈ A then root ζ jb else 0) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [this, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_bool]
      simp only [root, hcF, hcT, Bool.false_eq_true, if_false, if_true]
      by_cases hF : (j, false) ∈ A <;> by_cases hT : (j, true) ∈ A <;>
        simp [hF, hT]
    rw [hsplit] at hsum
    have hpt : ∀ j : Fin N,
        cF j • ζ ^ (j : ℕ) + cT j • (- ζ ^ (j : ℕ)) = c j • ζ ^ (j : ℕ) := by
      intro j; rw [hc]; simp only [sub_smul, smul_neg]; ring
    simp_rw [hpt] at hsum
    exact hsum
  have hzero : ∀ j : Fin N, c j = 0 :=
    fun j => (Fintype.linearIndependent_iff.1 hLI) c hcombo j
  intro j
  have := hzero j
  simp only [hc, sub_eq_zero, hcF, hcT] at this
  by_cases hF : (j, false) ∈ A <;> by_cases hT : (j, true) ∈ A <;>
    simp_all

/-! ## Part 2.  THE NEW STEP: discharging independence for general N = 2^{m-1}.

For a primitive `2^m`-th root of unity `ζ` in a characteristic-0 field, the
minimal polynomial over `ℚ` is `cyclotomic(2^m)`, of degree `φ(2^m) = 2^{m-1}`.
Hence the degree bound `N = 2^{m-1} ≤ deg(minpoly ℚ ζ)` holds with EQUALITY, and
`linearIndependent_pow_le` discharges the conditional hypothesis. -/

/-- `φ(2^m) = 2^{m-1}` for `m ≥ 1`. -/
theorem totient_two_pow {m : ℕ} (hm : 1 ≤ m) : Nat.totient (2 ^ m) = 2 ^ (m - 1) := by
  rw [Nat.totient_prime_pow Nat.prime_two hm]
  simp

/-- The degree of the minimal polynomial over `ℚ` of a primitive `2^m`-th root of
unity equals `2^{m-1}`.  KEY cyclotomic-degree fact. -/
theorem natDegree_minpoly_primitiveRoot {L : Type*} [Field L] [CharZero L]
    {ζ : L} {m : ℕ} (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    (minpoly ℚ ζ).natDegree = 2 ^ (m - 1) := by
  have hpos : 0 < 2 ^ m := by positivity
  -- minpoly ℚ ζ = cyclotomic(2^m) ℚ
  have hmin : cyclotomic (2 ^ m) ℚ = minpoly ℚ ζ := cyclotomic_eq_minpoly_rat hζ hpos
  rw [← hmin, natDegree_cyclotomic, totient_two_pow hm]

/-- **Discharged independence, general N.**  For a primitive `2^m`-th root of
unity `ζ` (`m ≥ 1`) in a characteristic-0 field, the first `N = 2^{m-1}` powers
`{ζ^0,…,ζ^{N-1}}` are `ℚ`-linearly independent — UNCONDITIONALLY. -/
theorem linearIndependent_pow_primitiveRoot {L : Type*} [Field L] [CharZero L]
    {ζ : L} {m : ℕ} (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    LinearIndependent ℚ (fun j : Fin (2 ^ (m - 1)) => ζ ^ (j : ℕ)) :=
  linearIndependent_pow_le ζ (by rw [natDegree_minpoly_primitiveRoot hm hζ])

/-- For a primitive `2^m`-th root of unity `ζ` (`m ≥ 1`), `ζ^{2^{m-1}} = -1`:
`ζ^{2^{m-1}}` is a primitive 2nd root of unity, hence equals `-1`.  This makes the
antipodal pairing `root(j,true) = ζ^{j+N}` genuine for the `2^m` roots of unity. -/
theorem pow_half_eq_neg_one {L : Type*} [Field L]
    {ζ : L} {m : ℕ} (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    ζ ^ (2 ^ (m - 1)) = -1 := by
  have hpos : 0 < 2 ^ m := by positivity
  -- 2^m = 2^{m-1} * 2
  have hprod : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [show m = (m - 1) + 1 from (Nat.succ_pred_eq_of_pos hm).symm]
    rw [pow_succ]
  -- ζ^{2^{m-1}} is a primitive 2nd root of unity.
  have h2 : IsPrimitiveRoot (ζ ^ (2 ^ (m - 1))) 2 := hζ.pow hpos hprod
  exact h2.eq_neg_one_of_two_right

/-! ## Part 3.  THE FULLY UNCONDITIONAL GENERAL THEOREM.

Assembling Parts 1 and 2: for a primitive `2^m`-th root of unity `ζ` in a
characteristic-0 field (`m ≥ 1`), any subset of the `2^m` roots of unity (in the
antipodal pairing) summing to 0 is antipodal — NO conditional hypothesis. -/

/-- **General unconditional antipodal tightness for `N = 2^{m-1}`.**
Let `ζ` be a primitive `2^m`-th root of unity (`m ≥ 1`) in a characteristic-0
field.  Any subset `A` of the `2^m` antipodal-paired roots of unity whose values
sum to zero is antipodal: it contains `(j,false)` iff `(j,true)`, for every
`j < 2^{m-1}`.  The cyclotomic-independence input is discharged via the totient
degree of `cyclotomic(2^m)`. -/
theorem antipodal_unconditional {L : Type*} [Field L] [CharZero L]
    {ζ : L} {m : ℕ} (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (A : Finset (Fin (2 ^ (m - 1)) × Bool))
    (hsum : ∑ a ∈ A, root ζ a = 0) :
    ∀ j : Fin (2 ^ (m - 1)), ((j, false) ∈ A ↔ (j, true) ∈ A) :=
  antipodal_of_sum_zero ζ (linearIndependent_pow_primitiveRoot hm hζ) A hsum

end R12

/-! ## Part 4.  A concrete, fully UNCONDITIONAL inhabitant.

We instantiate `L = ℂ`, `ζ = Complex.exp(2πI/2^m)`, an explicit primitive
`2^m`-th root of unity (Mathlib's `Complex.isPrimitiveRoot_exp`).  Everything is
unconditional.  We then specialise to `m = 3` (`2^m = 8`, `N = 4`) numerically. -/

namespace Concrete

open Complex

/-- The explicit primitive `2^m`-th root of unity `exp(2πi/2^m)` in `ℂ`. -/
noncomputable def zeta (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ m))

/-- `zeta m` is a primitive `2^m`-th root of unity (`m ≥ 1`). -/
theorem isPrimitiveRoot_zeta {m : ℕ} (hm : 1 ≤ m) :
    IsPrimitiveRoot (zeta m) (2 ^ m) := by
  have hne : (2 : ℕ) ^ m ≠ 0 := by positivity
  -- `Complex.isPrimitiveRoot_exp` with the cast `((2^m : ℕ) : ℂ)`.
  have := Complex.isPrimitiveRoot_exp (2 ^ m) hne
  simpa [zeta] using this

/-- **General concrete unconditional antipodal tightness over ℚ ⊆ ℂ.**
For `m ≥ 1`, a subset `A` of the `2^m`-th roots of unity (presented via the
antipodal pairing on `Fin (2^{m-1}) × Bool`, with explicit root `exp(2πi/2^m)`)
whose values sum to zero is antipodal.  No hypotheses beyond the vanishing sum;
the cyclotomic-independence input is fully discharged for every `m`. -/
theorem antipodal_C {m : ℕ} (hm : 1 ≤ m)
    (A : Finset (Fin (2 ^ (m - 1)) × Bool))
    (hsum : ∑ a ∈ A, R12.root (zeta m) a = 0) :
    ∀ j : Fin (2 ^ (m - 1)), ((j, false) ∈ A ↔ (j, true) ∈ A) :=
  R12.antipodal_unconditional hm (isPrimitiveRoot_zeta hm) A hsum

/-- `zeta m ^ (2^{m-1}) = -1` for `m ≥ 1` (sanity: the antipodal pairing is the
genuine antipodal structure of the `2^m`-th roots of unity). -/
theorem zeta_pow_half {m : ℕ} (hm : 1 ≤ m) : (zeta m) ^ (2 ^ (m - 1)) = -1 :=
  R12.pow_half_eq_neg_one hm (isPrimitiveRoot_zeta hm)

/-! ### A concrete numeric instance: m = 3, N = 4, 2^m = 8 roots of unity. -/

/-- `zeta 3` is a primitive 8-th root of unity. -/
theorem isPrimitiveRoot_zeta3 : IsPrimitiveRoot (zeta 3) 8 := by
  have := isPrimitiveRoot_zeta (m := 3) (by norm_num)
  norm_num at this
  exact this

/-- UNCONDITIONAL: `{ζ^0, ζ^1, ζ^2, ζ^3}` is `ℚ`-linearly independent in `ℂ`,
where `ζ = zeta 3` is a primitive 8-th root of unity (`N = 4 = φ(8)`). -/
theorem linearIndependent_pow_zeta3 :
    LinearIndependent ℚ (fun j : Fin 4 => (zeta 3) ^ (j : ℕ)) := by
  have h := R12.linearIndependent_pow_primitiveRoot (m := 3) (by norm_num)
    (isPrimitiveRoot_zeta (m := 3) (by norm_num))
  norm_num at h
  exact h

/-- **Concrete unconditional antipodal tightness, N = 4 (8-th roots of unity).**
A subset `A` of the eight 8-th roots of unity (antipodal pairing on
`Fin 4 × Bool`, root `exp(2πi/8)`) whose values sum to zero is antipodal:
it contains `(j,false)` iff `(j,true)` for `j ∈ {0,1,2,3}`.  This is the
GENERAL-`N` Lam–Leung t=1 tightness at `m = 3`, fully unconditional. -/
theorem antipodal_zeta3 (A : Finset (Fin 4 × Bool))
    (hsum : ∑ a ∈ A, R12.root (zeta 3) a = 0) :
    ∀ j : Fin 4, ((j, false) ∈ A ↔ (j, true) ∈ A) := by
  have h := antipodal_C (m := 3) (by norm_num)
  norm_num at h
  exact h A hsum

/-! ### Non-vacuity witnesses for the N = 4 instance. -/

/-- The full set of all eight roots sums to `0` (geometric sum of all 8th roots
of unity vanishes), so the hypothesis of `antipodal_zeta3` is satisfiable. -/
theorem sum_univ_zeta3_zero :
    ∑ a ∈ (Finset.univ : Finset (Fin 4 × Bool)), R12.root (zeta 3) a = 0 := by
  -- Group the eight terms into the four antipodal pairs `ζ^j + (-ζ^j) = 0`.
  rw [Fintype.sum_prod_type]
  have hpair : ∀ j : Fin 4,
      ∑ b : Bool, R12.root (zeta 3) (j, b) = 0 := by
    intro j
    rw [Fintype.sum_bool]
    simp only [R12.root, Bool.false_eq_true, if_false, if_true]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hpair j)]
  simp

/-- An antipodal 2-element witness `{ζ^0, -ζ^0} = {1, -1}` sums to `0`. -/
theorem sum_pair_zeta3_zero :
    ∑ a ∈ ({(0, false), (0, true)} : Finset (Fin 4 × Bool)),
        R12.root (zeta 3) a = 0 := by
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [R12.root, Bool.false_eq_true, if_false, if_true, Fin.val_zero, pow_zero]
  ring

/-- A non-antipodal singleton `{ζ^1}` has NONZERO sum, so the antipodal
conclusion of `antipodal_zeta3` is a genuine restriction (the theorem is
non-vacuous: not every `A` satisfies the vanishing-sum hypothesis). -/
theorem sum_singleton_zeta3_ne_zero :
    ∑ a ∈ ({(1, false)} : Finset (Fin 4 × Bool)), R12.root (zeta 3) a ≠ 0 := by
  rw [Finset.sum_singleton]
  simp only [R12.root, Bool.false_eq_true, if_false, Fin.val_one, pow_one]
  -- `zeta 3 ≠ 0`: it is a root of unity, hence a unit.
  have hprim : IsPrimitiveRoot (zeta 3) 8 := isPrimitiveRoot_zeta3
  intro hz
  have hpow : (zeta 3) ^ 8 = 1 := hprim.pow_eq_one
  rw [hz] at hpow
  norm_num at hpow

/-- Sanity: the full-set witness is antipodal (consistent with `antipodal_zeta3`). -/
theorem antipodal_zeta3_on_univ :
    ∀ j : Fin 4, ((j, false) ∈ (Finset.univ : Finset (Fin 4 × Bool)) ↔
      (j, true) ∈ (Finset.univ : Finset (Fin 4 × Bool))) :=
  antipodal_zeta3 _ sum_univ_zeta3_zero

end Concrete

-- Axiom audit: must report only [propext, Classical.choice, Quot.sound].
#print axioms R12.linearIndependent_pow_primitiveRoot
#print axioms R12.pow_half_eq_neg_one
#print axioms R12.antipodal_unconditional
#print axioms Concrete.antipodal_C
#print axioms Concrete.zeta_pow_half
#print axioms Concrete.antipodal_zeta3
#print axioms Concrete.sum_univ_zeta3_zero
#print axioms Concrete.sum_pair_zeta3_zero
#print axioms Concrete.sum_singleton_zeta3_ne_zero
#print axioms Concrete.antipodal_zeta3_on_univ
