/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-! # Multiplicative rigidity for product-coset codeword families

Upgrades the binomial rigidity of `MultiplicativeRigidityZMod` / `MultiplicativeRigidityFiber`
to the **product-coset family** `{∏_s (X^{m_s} - c_s)}` (issue #51): the products of coset
binomials over a smooth multiplicative domain, the natural multiplicative analogue of the
BKR subspace-polynomial family.

## Main results

* `MultiplicativeRigidityProducts.productCoset` — the family, as monic products of
  binomials `X^{m} - C c` over a list of `(exponent, constant)` data.
* `MultiplicativeRigidityProducts.productCoset_monic`, `productCoset_natDegree` —
  basic structure (monic; degree = sum of the exponents).
* `MultiplicativeRigidityProducts.singleFactor_agreement_iff` — **exact rigidity**: two
  products sharing the cofactor `R` and differing in a single binomial constant agree at
  `x` *iff* `R x = 0`.  Hence their agreement set is exactly the root set of the shared
  part (`singleFactor_agreement_filter`), a union of binomial root-cosets (each empty or
  a coset of size `gcd(m, n)` by the existing `MultiplicativeRigidity` fiber machinery),
  of size at most `deg − m` (`singleFactor_agreement_card_le`).
* `MultiplicativeRigidityProducts.agreement_card_le_natDegree_sub` — generic pairwise
  agreement bound: distinct polynomials agree on at most `natDegree (P − Q) < k` points
  of any evaluation set.
* `MultiplicativeRigidityProducts.cluster_le_one` /
  `MultiplicativeRigidityProducts.productCoset_cluster` — the **cluster theorem** upgraded
  from binomial codewords to the full product-coset family: for `2r + k ≤ n`, no received
  word is within Hamming distance `r` (agreement `≥ n − r`) of two distinct members.

## The exact boundary (why the radius hypothesis is necessary)

The dossier's strongest target — self-cluster `≤ 1` across the *full in-band range*
`δ < 1 − k/n` — is **false**, for two independent reasons, so `2r + k ≤ n` is sharp in
shape:

1. *Domain-independent*: two members differing in one factor have agreement exactly the
   shared root set (above); off that set, a received word may copy `P` on half the
   remaining points and `Q` on the other half, giving a 2-cluster at every `δ ≥ 1/2`
   (in-band whenever the rate is `< 1/2`).
2. *μ_{2^t}-specific*: **scaled** coset binomials participate in dihedral certificates —
   `MuTwoPowDerandRefutation.mu8_list_three` exhibits `(1+ω²)(X²−ω²)`, `X²+1`, `0` and a
   received word with pairwise agreement 4 on `μ_8` (a 3-cluster at `δ = 1/2 < 1 − k/n`),
   saturating the `L = 2` generalized-Singleton boundary.  Anti-clustering far beyond the
   unique-decoding radius is therefore *impossible* for the scaled family on `μ_{2^t}`,
   in contrast to the pairwise-binomial separation of `MultiplicativeRigidityZMod`.

Together with `GrandChallengeLDThreshold*` this records the negative evidence against a
BKR-style multiplicative blowup mechanism *within* the unique-decoding band, while the
dihedral mechanism of `MuTwoPowDerandRefutation` marks where rigidity genuinely stops. -/

namespace MultiplicativeRigidityProducts

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The product-coset family -/

/-- The product-coset polynomial attached to a list of `(exponent, constant)` pairs:
`∏_{(m, c) ∈ l} (X^m - C c)`.  For the smooth-domain family take `m = 2^s`. -/
noncomputable def productCoset (l : List (ℕ × F)) : F[X] :=
  (l.map fun mc => X ^ mc.1 - C mc.2).prod

omit [DecidableEq F] in
@[simp]
theorem productCoset_nil : productCoset ([] : List (ℕ × F)) = 1 := rfl

omit [DecidableEq F] in
@[simp]
theorem productCoset_cons (mc : ℕ × F) (l : List (ℕ × F)) :
    productCoset (mc :: l) = (X ^ mc.1 - C mc.2) * productCoset l := by
  simp [productCoset]

omit [DecidableEq F] in
/-- Product-coset polynomials with nonzero exponents are monic. -/
theorem productCoset_monic (l : List (ℕ × F)) (hl : ∀ mc ∈ l, mc.1 ≠ 0) :
    (productCoset l).Monic := by
  induction l with
  | nil => exact monic_one
  | cons mc l ih =>
    rw [productCoset_cons]
    exact (monic_X_pow_sub_C mc.2 (hl mc (List.mem_cons_self ..))).mul
      (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))

omit [DecidableEq F] in
/-- The degree of a product-coset polynomial is the sum of its exponents. -/
theorem productCoset_natDegree (l : List (ℕ × F)) (hl : ∀ mc ∈ l, mc.1 ≠ 0) :
    (productCoset l).natDegree = (l.map fun mc => mc.1).sum := by
  induction l with
  | nil => simp [productCoset]
  | cons mc l ih =>
    rw [productCoset_cons, List.map_cons, List.sum_cons,
      Polynomial.Monic.natDegree_mul (monic_X_pow_sub_C mc.2 (hl mc (List.mem_cons_self ..)))
        (productCoset_monic l fun x hx => hl x (List.mem_cons_of_mem _ hx)),
      natDegree_X_pow_sub_C, ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]

omit [DecidableEq F] in
theorem productCoset_ne_zero (l : List (ℕ × F)) (hl : ∀ mc ∈ l, mc.1 ≠ 0) :
    productCoset l ≠ 0 :=
  (productCoset_monic l hl).ne_zero

/-! ## Generic pairwise agreement bound -/

/-- Distinct polynomials agree on at most `natDegree (P − Q)` points of any evaluation
set: the agreement set embeds into the roots of the difference. -/
theorem agreement_card_le_natDegree_sub (P Q : F[X]) (hne : P ≠ Q) (S : Finset F) :
    (S.filter fun x => P.eval x = Q.eval x).card ≤ (P - Q).natDegree := by
  classical
  have hsub : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hss : (S.filter fun x => P.eval x = Q.eval x) ⊆ (P - Q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub]
    have hev := (Finset.mem_filter.mp hx).2
    simp [Polynomial.IsRoot, hev]
  calc (S.filter fun x => P.eval x = Q.eval x).card
      ≤ (P - Q).roots.toFinset.card := Finset.card_le_card hss
    _ ≤ Multiset.card (P - Q).roots := Multiset.toFinset_card_le _
    _ ≤ (P - Q).natDegree := Polynomial.card_roots' _

/-! ## Exact single-factor rigidity -/

omit [DecidableEq F] in
/-- **Exact rigidity for single-factor differences.**  Two products sharing the cofactor
`R` and differing in one binomial constant agree at `x` iff the *shared part* vanishes
at `x`.  (No hypothesis on `m` is needed.) -/
theorem singleFactor_agreement_iff (R : F[X]) (m : ℕ) {c c' : F} (hcc : c ≠ c') (x : F) :
    (R * (X ^ m - C c)).eval x = (R * (X ^ m - C c')).eval x ↔ R.eval x = 0 := by
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C]
  constructor
  · intro h
    have h2 : R.eval x * (c' - c) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3).symm hcc
  · intro h; rw [h]; ring

/-- The agreement set of two single-factor-differing products is **exactly** the root
set of the shared part — in particular a union of binomial root-cosets when `R` is
itself a product-coset polynomial (each factor's roots being empty or a coset of size
`gcd(m, n)` on a cyclic subgroup, by `MultiplicativeRigidity`). -/
theorem singleFactor_agreement_filter (R : F[X]) (m : ℕ) {c c' : F} (hcc : c ≠ c')
    (S : Finset F) :
    (S.filter fun x => (R * (X ^ m - C c)).eval x = (R * (X ^ m - C c')).eval x)
      = S.filter fun x => R.eval x = 0 := by
  classical
  exact Finset.filter_congr fun x _ => by
    simpa using singleFactor_agreement_iff R m hcc x

/-- Cardinality form: the agreement count of single-factor-differing products is at most
the degree of the shared part — strictly below the total degree by the missing factor. -/
theorem singleFactor_agreement_card_le (R : F[X]) (hR : R ≠ 0) (m : ℕ) {c c' : F}
    (hcc : c ≠ c') (S : Finset F) :
    (S.filter fun x =>
      (R * (X ^ m - C c)).eval x = (R * (X ^ m - C c')).eval x).card ≤ R.natDegree := by
  classical
  rw [singleFactor_agreement_filter R m hcc S]
  have hss : (S.filter fun x => R.eval x = 0) ⊆ R.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hR]
    exact (Finset.mem_filter.mp hx).2
  calc (S.filter fun x => R.eval x = 0).card
      ≤ R.roots.toFinset.card := Finset.card_le_card hss
    _ ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := Polynomial.card_roots' _

/-! ## The cluster theorem at the unique-decoding-style radius -/

/-- **Cluster theorem (generic core).**  If two distinct polynomials of degree `< k` each
agree with a received word `y` on at least `n − r` points of an `n`-point evaluation set,
and `2r + k ≤ n`, we reach a contradiction: the two agreement sets overlap in at least
`n − 2r ≥ k` points, all of which are agreements of the two polynomials — impossible
below degree `k`.  I.e. **every radius-`r` ball contains at most one such codeword**. -/
theorem cluster_le_one {n k r : ℕ} (S : Finset F) (hS : S.card = n)
    (P Q : F[X]) (hne : P ≠ Q) (hP : P.natDegree < k) (hQ : Q.natDegree < k)
    (y : F → F) (hr : 2 * r + k ≤ n)
    (hPy : n - r ≤ (S.filter fun x => P.eval x = y x).card)
    (hQy : n - r ≤ (S.filter fun x => Q.eval x = y x).card) : False := by
  classical
  set A := S.filter fun x => P.eval x = y x with hA
  set B := S.filter fun x => Q.eval x = y x with hB
  have hAB : A ∩ B ⊆ S.filter fun x => P.eval x = Q.eval x := by
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hxA, hxB⟩ := hx
    have h1 := Finset.mem_filter.mp hxA
    have h2 := Finset.mem_filter.mp hxB
    exact Finset.mem_filter.mpr ⟨h1.1, h1.2.trans h2.2.symm⟩
  have hABk : (A ∩ B).card < k := by
    have h1 : (A ∩ B).card ≤ (P - Q).natDegree :=
      le_trans (Finset.card_le_card hAB) (agreement_card_le_natDegree_sub P Q hne S)
    have h2 : (P - Q).natDegree < k :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le P Q) (max_lt hP hQ)
    omega
  have hU : (A ∪ B).card ≤ n := by
    rw [← hS]
    exact Finset.card_le_card
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hsum : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  omega

/-- **The product-coset cluster theorem** (the issue-#51 upgrade): no received word lies
within Hamming distance `r` of two *distinct* product-coset codewords of degree `< k`
on an `n`-point evaluation set, provided `2r + k ≤ n`.  The radius hypothesis is sharp
in shape: see the module docstring for the two boundary counterexamples (the `δ ≥ 1/2`
split word, and the scaled-binomial dihedral 3-cluster of
`MuTwoPowDerandRefutation.mu8_list_three` on `μ_8`). -/
theorem productCoset_cluster {n k r : ℕ} (S : Finset F) (hS : S.card = n)
    (l₁ l₂ : List (ℕ × F)) (hne : productCoset l₁ ≠ productCoset l₂)
    (h₁ : ∀ mc ∈ l₁, mc.1 ≠ 0) (h₂ : ∀ mc ∈ l₂, mc.1 ≠ 0)
    (hd₁ : ((l₁.map fun mc => mc.1).sum) < k) (hd₂ : ((l₂.map fun mc => mc.1).sum) < k)
    (y : F → F) (hr : 2 * r + k ≤ n)
    (hPy : n - r ≤ (S.filter fun x => (productCoset l₁).eval x = y x).card)
    (hQy : n - r ≤ (S.filter fun x => (productCoset l₂).eval x = y x).card) : False :=
  cluster_le_one S hS (productCoset l₁) (productCoset l₂) hne
    (by rw [productCoset_natDegree l₁ h₁]; exact hd₁)
    (by rw [productCoset_natDegree l₂ h₂]; exact hd₂) y hr hPy hQy

end MultiplicativeRigidityProducts
