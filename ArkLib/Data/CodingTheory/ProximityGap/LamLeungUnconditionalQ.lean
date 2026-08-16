/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
  Round 11 — UNCONDITIONAL Lam–Leung t=1 antipodal tightness.

  Context (Ethereum Proximity Prize, ABF26 / ArkLib #232).  In prior rounds the
  Lam–Leung "vanishing sums of roots of unity" tightness at t = 1 was proven only
  CONDITIONALLY on a cyclotomic-independence hypothesis:

      IF  {ζ^j : j < N}  is K-linearly independent
      THEN  ∑_{a ∈ A} ζ^a = 0  ⟹  A is antipodal (A = A + N, i.e. S = -S).

  Here we DISCHARGE that hypothesis from Mathlib's power-basis machinery and
  assemble a fully UNCONDITIONAL antipodal-tightness theorem, together with a
  concrete non-vacuous inhabitant.

  The engine is `PowerBasis.linearIndependent_pow`:  over a field `K`, for any
  element `ζ` of a `K`-algebra `S`, the powers  `{ζ^i : i < (minpoly K ζ).natDegree}`
  are K-linearly independent — UNCONDITIONALLY.  Whenever the minimal polynomial
  of `ζ` has degree `≥ N`, the first `N` powers are independent, and the
  conditional hypothesis is met automatically.

  CONCRETE WITNESS:  K = ℚ, S = ℂ, ζ = Complex.I, N = 2 (so 2N = 4).  Then
  ζ^2 = -1 and `minpoly ℚ I` has degree ≥ 2 (since I ∉ ℚ), so a subset of the
  4-th roots of unity {1, I, -1, -I} whose sum vanishes is antipodal.  This is
  the t = 1, m = 2 case of the prize-relevant ω-concentration tightness, now
  with NO conditional hypothesis.

  Self-contained; imports only Mathlib.  Closes with `#print axioms`.
-/
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.Complex.Basic

open Polynomial Finset

namespace R11

/-! ## Part 0.  The unconditional linear-independence input.

`PowerBasis.linearIndependent_pow` (Mathlib) already gives, over a field `K`,
linear independence of `{ζ^i : i < (minpoly K ζ).natDegree}`.  We package the
first `N` powers, given a degree lower bound `N ≤ (minpoly K ζ).natDegree`. -/

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

/-- UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are
`K`-linearly independent whenever `N ≤ deg(minpoly K ζ)`.  No hypothesis on
`ζ` beyond living in a `K`-algebra. -/
theorem linearIndependent_pow_le (ζ : S) {N : ℕ}
    (hN : N ≤ (minpoly K ζ).natDegree) :
    LinearIndependent K (fun j : Fin N => ζ ^ (j : ℕ)) := by
  have hfull : LinearIndependent K (fun i : Fin (minpoly K ζ).natDegree => ζ ^ (i : ℕ)) :=
    _root_.linearIndependent_pow ζ
  have hcomp := hfull.comp (Fin.castLE hN) (Fin.castLE_injective hN)
  simpa [Function.comp, Fin.val_castLE] using hcomp

/-! ## Part 1.  The general unconditional antipodal theorem.

Setting.  `ζ` is a `2N`-th root of unity with `ζ^N = -1`; thus the `j`-th and
`(j+N)`-th roots are antipodal, `ζ^(j+N) = -ζ^j`.  We index the `2N` roots by
pairs `(j, b) : Fin N × Bool`, the root at `(j,b)` being `(-1)^b · ζ^j`
(`b = false` ↦ `ζ^j`, `b = true` ↦ `ζ^(j+N) = -ζ^j`).  A chosen sub-multiset is
a subset `A : Finset (Fin N × Bool)`.

`A` is *antipodal* when, for every `j`, it contains `(j,false)` iff it contains
`(j,true)` — i.e. the chosen set of roots is closed under negation `S = -S`. -/

variable {N : ℕ}

/-- The complex value of the root indexed by `(j,b)` under the antipodal pairing
`root(j,false) = ζ^j`, `root(j,true) = -ζ^j`. -/
def root (ζ : S) (jb : Fin N × Bool) : S :=
  if jb.2 then - ζ ^ (jb.1 : ℕ) else ζ ^ (jb.1 : ℕ)

/-- For a 2N-th root of unity with `ζ^N = -1`, the `(j,true)` root really is the
`(j+N)`-th genuine power of `ζ`.  (Sanity bridge; not needed for the theorem.) -/
theorem root_true_eq (ζ : S) (hpow : ζ ^ N = -1) (j : Fin N) :
    root ζ (j, true) = ζ ^ ((j : ℕ) + N) := by
  simp [root, pow_add, hpow]

/-- **General unconditional antipodal tightness.**
If the first `N` powers of `ζ` are `K`-linearly independent (an UNCONDITIONAL
fact whenever `N ≤ deg(minpoly K ζ)`, see `linearIndependent_pow_le`), then any
subset `A` of the `2N` antipodal-paired roots whose values sum to zero is
antipodal: it contains `(j,false)` iff it contains `(j,true)`, for every `j`. -/
theorem antipodal_of_sum_zero {N : ℕ} (ζ : S)
    (hLI : LinearIndependent K (fun j : Fin N => ζ ^ (j : ℕ)))
    (A : Finset (Fin N × Bool))
    (hsum : ∑ a ∈ A, root ζ a = 0) :
    ∀ j : Fin N, ((j, false) ∈ A ↔ (j, true) ∈ A) := by
  classical
  -- Coefficient of `ζ^j` in the vanishing sum: #(j,false) - #(j,true) ∈ {-1,0,1}.
  set cF : Fin N → K := fun j => if (j, false) ∈ A then (1 : K) else 0 with hcF
  set cT : Fin N → K := fun j => if (j, true) ∈ A then (1 : K) else 0 with hcT
  set c : Fin N → K := fun j => cF j - cT j with hc
  -- Rewrite the vanishing sum as `∑_j c j • ζ^j = 0`.
  have hcombo : ∑ j : Fin N, c j • ζ ^ (j : ℕ) = 0 := by
    -- Split `A` along the Bool coordinate using the product structure.
    have hsplit :
        ∑ a ∈ A, root ζ a
          = ∑ j : Fin N, (cF j • ζ ^ (j : ℕ) + cT j • (- ζ ^ (j : ℕ))) := by
      -- regroup the sum over A by its `Fin N`-coordinate via the universe pairs
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
    -- `cF • x + cT • (-x) = (cF - cT) • x`
    have hpt : ∀ j : Fin N,
        cF j • ζ ^ (j : ℕ) + cT j • (- ζ ^ (j : ℕ)) = c j • ζ ^ (j : ℕ) := by
      intro j; rw [hc]; simp only [sub_smul, smul_neg]; ring
    simp_rw [hpt] at hsum
    exact hsum
  -- Linear independence forces every coefficient to vanish.
  have hzero : ∀ j : Fin N, c j = 0 :=
    fun j => (Fintype.linearIndependent_iff.1 hLI) c hcombo j
  -- `cF j = cT j` ⟺ membership matches.
  intro j
  have := hzero j
  simp only [hc, sub_eq_zero, hcF, hcT] at this
  by_cases hF : (j, false) ∈ A <;> by_cases hT : (j, true) ∈ A <;>
    simp_all

end R11

/-! ## Part 2.  A concrete, fully UNCONDITIONAL inhabitant: ℚ(i), N = 2.

We instantiate with `K = ℚ`, `S = ℂ`, `ζ = Complex.I`, `N = 2` (so `2N = 4`).
The four roots `{ζ^0,…,ζ^3} = {1, I, -1, -I}` are the primitive 4-th roots
structure; under our antipodal pairing `(j,false) ↦ ζ^j`, `(j,true) ↦ -ζ^j`:

  (0,false)↦ 1,  (1,false)↦ I,  (0,true)↦ -1,  (1,true)↦ -I.

Everything below is unconditional. -/

namespace Concrete

open Complex

/-- `Complex.I` is integral over `ℚ`: it is a root of the monic `X^2 + 1`. -/
theorem isIntegral_I : IsIntegral ℚ Complex.I := by
  refine ⟨X ^ 2 + C 1, ?_, ?_⟩
  · -- monic
    apply Polynomial.monic_X_pow_add
    simp [Polynomial.degree_one]
  · -- aeval I (X^2 + 1) = 0
    simp [Complex.I_sq]

/-- `Complex.I` is NOT in the image of `algebraMap ℚ ℂ` (it is not a real,
hence not a rational, number): its imaginary part is `1 ≠ 0`. -/
theorem I_not_mem_range : Complex.I ∉ (algebraMap ℚ ℂ).range := by
  rintro ⟨q, hq⟩
  -- compare imaginary parts: `(algebraMap ℚ ℂ q).im = 0` but `I.im = 1`.
  have him : Complex.I.im = (algebraMap ℚ ℂ q).im := by rw [hq]
  rw [Complex.I_im] at him
  -- `algebraMap ℚ ℂ q = (q : ℂ)`, whose imaginary part is `0`.
  have : (algebraMap ℚ ℂ q).im = 0 := by
    simp [Complex.ratCast_im]
  rw [this] at him
  exact one_ne_zero him

/-- `minpoly ℚ Complex.I` has degree `≥ 2` — UNCONDITIONALLY, from integrality
plus `I ∉ ℚ`.  (In fact it equals `X^2 + 1`, but we only need `≥ 2`.) -/
theorem two_le_natDegree_minpoly_I : 2 ≤ (minpoly ℚ Complex.I).natDegree :=
  (minpoly.two_le_natDegree_iff isIntegral_I).2 I_not_mem_range

/-- UNCONDITIONAL: `{1, I}` is `ℚ`-linearly independent in `ℂ`. -/
theorem linearIndependent_one_I :
    LinearIndependent ℚ (fun j : Fin 2 => Complex.I ^ (j : ℕ)) :=
  R11.linearIndependent_pow_le Complex.I two_le_natDegree_minpoly_I

/-- **Concrete unconditional antipodal tightness over ℚ(i).**
A subset `A` of the four 4-th roots of unity (presented via the antipodal
pairing on `Fin 2 × Bool`) whose values sum to zero is antipodal:  it contains
`(j,false)` iff it contains `(j,true)` for `j ∈ {0,1}`.  No hypotheses beyond
the vanishing sum; the cyclotomic-independence input is fully discharged. -/
theorem antipodal_Qi (A : Finset (Fin 2 × Bool))
    (hsum : ∑ a ∈ A, R11.root Complex.I a = 0) :
    ∀ j : Fin 2, ((j, false) ∈ A ↔ (j, true) ∈ A) :=
  R11.antipodal_of_sum_zero Complex.I linearIndependent_one_I A hsum

/-! ### Non-vacuity witnesses.

We exhibit two concrete `A`'s to show the theorem's hypothesis is satisfiable
in BOTH a non-trivial-vanishing case and the full-set case, and that the
conclusion is meaningful (it genuinely rules out non-antipodal vanishing). -/

/-- The full set `{1, I, -1, -I}` sums to `0` (every root present). -/
theorem sum_univ_zero :
    ∑ a ∈ (Finset.univ : Finset (Fin 2 × Bool)), R11.root Complex.I a = 0 := by
  -- expand the four-term sum and evaluate the roots explicitly.
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, R11.root]
  simp only [Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one]
  ring

/-- The pair `{1, -1}` (i.e. `(0,false),(0,true)`) sums to `0`: an antipodal
2-element witness. -/
theorem sum_pair_zero :
    ∑ a ∈ ({(0, false), (0, true)} : Finset (Fin 2 × Bool)),
        R11.root Complex.I a = 0 := by
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [R11.root, Bool.false_eq_true, if_false, if_true, Fin.val_zero, pow_zero]
  ring

/-- The non-antipodal singleton `{I}` (i.e. `{(1,false)}`) has NONZERO sum `I`.
This shows the antipodal conclusion of `antipodal_Qi` is a genuine restriction:
a non-antipodal set fails the vanishing-sum hypothesis (here directly), so the
theorem is non-vacuous and has real content (it is not implied for all `A`). -/
theorem sum_singleton_ne_zero :
    ∑ a ∈ ({(1, false)} : Finset (Fin 2 × Bool)), R11.root Complex.I a ≠ 0 := by
  rw [Finset.sum_singleton]
  simp only [R11.root, Bool.false_eq_true, if_false, Fin.val_one, pow_one]
  exact Complex.I_ne_zero

/-- Sanity: the full-set witness is itself antipodal (it contains both halves of
each pair), so it is consistent with the conclusion of `antipodal_Qi`. -/
theorem antipodal_Qi_on_univ :
    ∀ j : Fin 2, ((j, false) ∈ (Finset.univ : Finset (Fin 2 × Bool)) ↔
      (j, true) ∈ (Finset.univ : Finset (Fin 2 × Bool))) :=
  antipodal_Qi _ sum_univ_zero

end Concrete

-- Axiom audit: must report only [propext, Classical.choice, Quot.sound].
#print axioms R11.linearIndependent_pow_le
#print axioms R11.antipodal_of_sum_zero
#print axioms Concrete.antipodal_Qi
#print axioms Concrete.sum_univ_zero
#print axioms Concrete.sum_pair_zero
#print axioms Concrete.sum_singleton_ne_zero
#print axioms Concrete.antipodal_Qi_on_univ
