/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Round 22 (Issue #232) — the CONSTRUCTIVE PTE FAMILY inside the smooth domain: `expand` lifts
# every base subset to an equal-symmetric-window support

The open core's final form (O44): do distinct `w`-subsets of `μ_n` with equal `e₁,…,e_t` exist and
abound (the PTE/cyclic deficiency mechanism of Conjecture 41 = the multi-symmetric concentration of
rounds 4–8)? This file gives the **general constructive answer below the depth threshold**:

For `d > 0` and a base set `A` (`|A| = s`), the **lifted polynomial**

  `P_A := expand_d (∏_{a∈A} (X − a)) = ∏_{a∈A} (X^d − a)`

is monic of degree `d·s`, and — being a polynomial in `X^d` — **every coefficient at an index not
divisible by `d` vanishes** (`liftedPoly_coeff_eq_zero_of_not_dvd`, via `Polynomial.coeff_expand`).
In particular the entire top window below the leading coefficient is identically zero
(`liftedPoly_top_window_zero`): the lifted supports have `e₁ = ⋯ = e_{d−1} = 0`. Distinct bases
give distinct lifts (`liftedPoly_injective`), so **ALL `C(|B|, s)` lifts of `s`-subsets of a base
`B` are pairwise equal-symmetric up to depth `d−1`** — and the root set of `P_A` is exactly the
power-map fiber `{x : x^d ∈ A}` (`liftedPoly_eval_eq_zero_iff`), a genuine subset of the smooth
domain when `B = μ_{n/d} ⊂ μ_n`.

## The threshold arithmetic (what this settles)

* PTE families at depth `t ≤ d−1`, `d ∣ n`: size `C(n/d, s)`, support size `w = d·s` —
  constructive, every field, verified.
* The Conjecture-41 deficiency window (equal `e₁,…,e_{w−c}`) requires `w − c ≤ d − 1`, i.e.
  `d ≥ w−c+1`, forcing `s ≤ w/(w−c+1)`. At **deployment codimension** (`c, w−c = Θ(n)`):
  `d = Θ(n)`, `s = O(1)`, family `C(n/d, s) = O(1)` — matching the conjecture's `M = O(1)`
  prediction. Near **capacity** (`c = O(1)`): `s = Θ(w)`, family exponential — matching the
  proven exponential `c = 2` phase. One construction explains both phases of the 2026/858
  empirical phase diagram; its size IS the rounds-4–8 depth-collapse wall in deficiency language.
* **Honest residue:** whether non-lifted PTE families can beat `C(n/d, s)` in the deep window
  (non-cyclic deficiency at large `p`) is the open core — unchanged, with its constructive floor
  now verified.
-/

open Polynomial Finset

namespace Round22PTE

variable {F : Type*} [Field F]

/-- The base nodal polynomial `∏_{a∈A} (X − a)`. -/
noncomputable def baseNodal (A : Finset F) : F[X] :=
  ∏ a ∈ A, (X - C a)

/-- **The lifted polynomial** `P_A = expand_d (baseNodal A) = ∏_{a∈A} (X^d − a)`. -/
noncomputable def liftedPoly (d : ℕ) (A : Finset F) : F[X] :=
  Polynomial.expand F d (baseNodal A)

/-- `expand` of the nodal product is the product of `(X^d − a)`. -/
theorem liftedPoly_eq_prod (d : ℕ) (A : Finset F) :
    liftedPoly d A = ∏ a ∈ A, (X ^ d - C a) := by
  unfold liftedPoly baseNodal
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a _
  rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]

theorem baseNodal_natDegree (A : Finset F) : (baseNodal A).natDegree = A.card := by
  unfold baseNodal
  rw [Polynomial.natDegree_prod _ _ (fun a _ => X_sub_C_ne_zero a)]
  simp

/-- The lift has degree `|A|·d`. -/
theorem liftedPoly_natDegree (d : ℕ) (A : Finset F) :
    (liftedPoly d A).natDegree = A.card * d := by
  unfold liftedPoly
  rw [Polynomial.natDegree_expand, baseNodal_natDegree]

/-! ## 1. The vanishing window -/

/-- **Lattice vanishing:** `P_A` is a polynomial in `X^d`; every coefficient at an index not
divisible by `d` is zero. -/
theorem liftedPoly_coeff_eq_zero_of_not_dvd {d : ℕ} (hd : 0 < d) (A : Finset F) {i : ℕ}
    (hi : ¬ d ∣ i) :
    (liftedPoly d A).coeff i = 0 := by
  unfold liftedPoly
  rw [Polynomial.coeff_expand hd, if_neg hi]

/-- **The zero top window (the PTE property):** for a nonempty base and `1 ≤ j ≤ d−1`, the
coefficient at `|A|·d − j` vanishes — the symmetric functions `e₁, …, e_{d−1}` of the lifted
support are identically zero, for EVERY base set. -/
theorem liftedPoly_top_window_zero {d : ℕ} (hd : 0 < d) {A : Finset F} (hA : A.Nonempty)
    {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d - 1) :
    (liftedPoly d A).coeff (A.card * d - j) = 0 := by
  apply liftedPoly_coeff_eq_zero_of_not_dvd hd
  have hApos : 0 < A.card := Finset.card_pos.mpr hA
  have hjlt : j < d := by omega
  have hjsd : j < A.card * d := lt_of_lt_of_le hjlt (Nat.le_mul_of_pos_left d hApos)
  rintro ⟨q, hq⟩
  -- j = d·(|A| − q) with 1 ≤ j < d: divisibility forces j ≥ d, contradiction.
  have hqlt : q < A.card := by
    by_contra hge
    push Not at hge
    have hmul : A.card * d ≤ d * q := by
      calc A.card * d = d * A.card := Nat.mul_comm _ _
        _ ≤ d * q := Nat.mul_le_mul_left d hge
    omega
  have hj_eq : j = d * (A.card - q) := by
    have hexp : d * (A.card - q) = d * A.card - d * q := Nat.mul_sub d _ _
    have hcomm : d * A.card = A.card * d := Nat.mul_comm _ _
    omega
  have hdj : d ≤ j := by
    rw [hj_eq]
    calc d = d * 1 := (Nat.mul_one d).symm
      _ ≤ d * (A.card - q) := Nat.mul_le_mul_left d (by omega)
  omega

/-! ## 2. Distinctness: the lift is injective -/

/-- The base nodal recovers its root set: `(baseNodal A).eval x = 0 ↔ x ∈ A`. -/
theorem baseNodal_eval_eq_zero_iff (A : Finset F) (x : F) :
    (baseNodal A).eval x = 0 ↔ x ∈ A := by
  unfold baseNodal
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨a, ha, hax⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hax
    rwa [hax]
  · intro hx
    exact ⟨x, hx, by simp⟩

/-- `baseNodal` is injective on finsets (the root sets are recovered). -/
theorem baseNodal_injective : Function.Injective (baseNodal (F := F)) := by
  intro A A' h
  ext x
  rw [← baseNodal_eval_eq_zero_iff A x, ← baseNodal_eval_eq_zero_iff A' x, h]

/-- **The lift is injective** (for `d > 0`): distinct bases give distinct lifted polynomials —
hence the family `{P_A : A ⊆ B, |A| = s}` has exactly `C(|B|, s)` distinct members. -/
theorem liftedPoly_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (liftedPoly (F := F) d) := by
  intro A A' h
  exact baseNodal_injective (Polynomial.expand_injective hd h)

/-! ## 3. The lifted support is the power-map fiber -/

/-- **Root characterization:** `P_A(x) = 0 ↔ x^d ∈ A` — the lifted support is exactly the fiber
preimage of the base under the `d`-th power map (a `d·s`-subset of `μ_n` when `A ⊆ μ_{n/d}`). -/
theorem liftedPoly_eval_eq_zero_iff (d : ℕ) (A : Finset F) (x : F) :
    (liftedPoly d A).eval x = 0 ↔ x ^ d ∈ A := by
  unfold liftedPoly
  rw [Polynomial.expand_eval, baseNodal_eval_eq_zero_iff]

/-! ## 4. The family count -/

/-- **THE PTE FAMILY (headline).** For any base finset `B`, `s ≥ 1`, `d > 0`: the lifts of the
`s`-subsets of `B` form `C(|B|, s)` pairwise-distinct monic-degree-`sd` polynomials whose
coefficients agree (all zero) on the ENTIRE top window `{sd−1, …, sd−(d−1)}` — i.e. `C(|B|, s)`
distinct supports with equal `e₁, …, e_{d−1}`. Instantiated at `B = μ_{n/d}` inside `μ_n`, these
are genuine smooth-domain PTE families at every depth `t ≤ d−1`. -/
theorem pte_family (d s : ℕ) (hd : 0 < d) (hs : 1 ≤ s) (B : Finset F) :
    ∃ Ps : Finset F[X], Ps.card = B.card.choose s ∧
      (∀ P ∈ Ps, P.natDegree = s * d) ∧
      (∀ P ∈ Ps, ∀ j, 1 ≤ j → j ≤ d - 1 → P.coeff (s * d - j) = 0) := by
  classical
  refine ⟨(B.powersetCard s).image (liftedPoly d), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (Function.Injective.injOn (liftedPoly_injective hd)),
        Finset.card_powersetCard]
  · intro P hP
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
    rw [Finset.mem_powersetCard] at hA
    rw [liftedPoly_natDegree, hA.2]
  · intro P hP j hj1 hjd
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
    rw [Finset.mem_powersetCard] at hA
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    have := liftedPoly_top_window_zero hd hAne hj1 hjd
    rwa [hA.2] at this

end Round22PTE

#print axioms Round22PTE.liftedPoly_coeff_eq_zero_of_not_dvd
#print axioms Round22PTE.liftedPoly_top_window_zero
#print axioms Round22PTE.liftedPoly_injective
#print axioms Round22PTE.liftedPoly_eval_eq_zero_iff
#print axioms Round22PTE.pte_family
