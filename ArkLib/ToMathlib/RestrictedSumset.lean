/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Polynomial Infrastructure for the Erdős–Heilbronn Restricted Sumset Bound

This module establishes the polynomial and coefficient-theoretic foundations necessary to prove
the $h = 2$ case of the Erdős–Heilbronn conjecture via Alon's Combinatorial Nullstellensatz
(`MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`).

## Mathematical Context

For a field $\mathbb{F}$ of prime characteristic $p$ and a finite subset $A \subseteq \mathbb{F}$
with $n := |A| \ge 2$, the restricted sumset of distinct-pair sums is defined as:
$$\Sigma_2(A) := \{ a + b : a, b ∈ A, a \neq b \}$$

If $2(n - 2) < p$, the Erdős–Heilbronn theorem asserts that:
$$|\Sigma_2(A)| \ge 2n - 3$$

## Proof Strategy (Alon–Nathanson–Ruzsa, $h = 2$)

We proceed by contradiction. Suppose $|\Sigma_2(A)| \le 2(n - 2)$. Since
$|\mathbb{F}| \ge p > 2(n - 2)$, we can pad $\Sigma_2(A)$ to a subset $C'$ of cardinality
exactly $m := 2(n - 2)$.
We then define the bivariate polynomial:
$$Q(X_0, X_1) := (X_1 - X_0) \prod_{c \in C'} (X_0 + X_1 - c) \in \mathbb{F}[X_0, X_1]$$

This polynomial $Q$ vanishes on the entire Cartesian product $A \times A$:
- If $x_0 = x_1$, the factor $(X_1 - X_0)$ vanishes.
- If $x_0 \neq x_1$, then $x_0 + x_1 \in \Sigma_2(A) \subseteq C'$, so one of the factors of
  the product vanishes.

The total degree of $Q$ is $1 + m = 2n - 3$. We target the monomial $t = X_0^{n-1} X_1^{n-2}$,
which has degree $2n - 3$. The coefficient of $t$ in $Q$ equals its coefficient in the
leading homogeneous part of $Q$, which is $(X_1 - X_0)(X_0 + X_1)^m$. This coefficient is
given by:
$$\binom{m}{n-1} - \binom{m}{n-2}$$

By combinatorial and modular arithmetic arguments, this coefficient is shown to be nonzero
modulo $p$ under the condition $m < p$. By Alon's Combinatorial Nullstellensatz, there must
exist some point
$(x_0, x_1) \in A \times A$ such that $Q(x_0, x_1) \neq 0$, yielding a contradiction.

This formalization focuses on the $h=2$ case; for general $h$, the bound is given by the
Dias da Silva–Hamidoune theorem, which requires analyzing ballot-number coefficient
structures.

## References

- Alon, N. *Combinatorial Nullstellensatz*. Combinatorics, Probability and Computing, 1999.
-/

namespace MvPolynomial

open scoped BigOperators

section ErdosHeilbronn

variable {F : Type*} [Field F]

/-- The target monomial `X₀^{a} X₁^{b}` as an element of `Fin 2 →₀ ℕ`. -/
private noncomputable def ehMon (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

private lemma ehMon_apply_zero (a b : ℕ) : ehMon a b 0 = a := by
  simp [ehMon]

private lemma ehMon_apply_one (a b : ℕ) : ehMon a b 1 = b := by
  simp [ehMon]

/-- The coefficient of `X₀^{a} X₁^{b}` in `(X 0 + X 1)^N` (over a field). -/
private lemma coeff_ehMon_add_pow (a b N : ℕ) (hab : a + b = N) :
    coeff (ehMon a b) ((X 0 + X 1 : MvPolynomial (Fin 2) F) ^ N) = (N.choose a : F) := by
  rw [coeff_add_pow]
  rw [ehMon_apply_zero, ehMon_apply_one]
  rw [if_pos]
  · rw [Finset.mem_antidiagonal]; exact hab

/-- **Leading coefficient computation.** The coefficient of `X₀^{n-1} X₁^{n-2}` in
`(X 1 - X 0)(X 0 + X 1)^m` with `m = 2(n-2)` is `C(m, n-1) - C(m, n-2)` (as an element of `F`).
We prove it for `m = a' + b'` with the relevant exponent bookkeeping. -/
private lemma coeff_leading
    {n : ℕ} (hn : 3 ≤ n) :
    coeff (ehMon (n - 1) (n - 2))
        ((X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ (2 * (n - 2)))
      = ((2 * (n - 2)).choose (n - 1) : F) - ((2 * (n - 2)).choose (n - 2) : F) := by
  classical
  set m := 2 * (n - 2) with hm
  rw [sub_mul, coeff_sub]
  have hX1 : coeff (ehMon (n - 1) (n - 2)) (X 1 * (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ m)
      = (m.choose (n - 1) : F) := by
    have hsplit : ehMon (n - 1) (n - 2) = Finsupp.single 1 1 + ehMon (n - 1) (n - 3) := by
      rw [ehMon, ehMon]
      have : (n - 2) = 1 + (n - 3) := by omega
      rw [this]
      rw [show Finsupp.single (1 : Fin 2) (1 + (n - 3))
          = Finsupp.single 1 1 + Finsupp.single 1 (n - 3) from (Finsupp.single_add _ _ _)]
      abel
    rw [hsplit, coeff_X_mul]
    rw [coeff_ehMon_add_pow (n - 1) (n - 3) m (by omega)]
  have hX0 : coeff (ehMon (n - 1) (n - 2)) (X 0 * (X 0 + X 1 : MvPolynomial (Fin 2) F) ^ m)
      = (m.choose (n - 2) : F) := by
    have hsplit : ehMon (n - 1) (n - 2) = Finsupp.single 0 1 + ehMon (n - 2) (n - 2) := by
      rw [ehMon, ehMon]
      have : (n - 1) = 1 + (n - 2) := by omega
      rw [this]
      rw [show Finsupp.single (0 : Fin 2) (1 + (n - 2))
          = Finsupp.single 0 1 + Finsupp.single 0 (n - 2) from (Finsupp.single_add _ _ _)]
      abel
    rw [hsplit, coeff_X_mul]
    rw [coeff_ehMon_add_pow (n - 2) (n - 2) m (by omega)]
  rw [hX1, hX0]

/-- **Nonvanishing of the leading coefficient mod `p`.** With `m := 2(n-2)`, the integer
`C(m, n-2) - C(m, n-1)` (a Catalan number) is nonzero in `F` provided `m < ringChar F` and
`ringChar F` is prime. Equivalently the leading coefficient `C(m,n-1) - C(m,n-2)` is nonzero. -/
private lemma leading_coeff_ne_zero {p : ℕ} (hp : p.Prime) (hchar : ringChar F = p)
    {n : ℕ} (hn : 3 ≤ n) (hmp : 2 * (n - 2) < p) :
    (((2 * (n - 2)).choose (n - 1) : F) - ((2 * (n - 2)).choose (n - 2) : F)) ≠ 0 := by
  set m := 2 * (n - 2) with hm
  set A : ℕ := m.choose (n - 2) with hA
  set B : ℕ := m.choose (n - 1) with hB
  have hrec : B * (n - 1) = A * (n - 2) := by
    have h := Nat.choose_succ_right_eq m (n - 2)
    rw [show (n - 2) + 1 = n - 1 from by omega] at h
    rw [show m - (n - 2) = n - 2 from by omega] at h
    rw [hA, hB]; exact h
  have hApos : 0 < A := Nat.choose_pos (by omega)
  have hle : B ≤ A := by
    by_contra hgt
    push Not at hgt
    have h1 : A * (n - 2) < B * (n - 1) := by
      calc A * (n - 2) < A * (n - 1) := by
            have : n - 2 < n - 1 := by omega
            exact (Nat.mul_lt_mul_left hApos).mpr this
        _ ≤ B * (n - 1) := Nat.mul_le_mul_right _ (le_of_lt hgt)
    omega
  set D : ℕ := A - B with hD
  have hDmul : (n - 1) * D = A := by
    have hstep : (n - 1) * D = (n - 1) * A - (n - 1) * B := by rw [hD, Nat.mul_sub]
    have hnb : (n - 1) * B = (n - 2) * A := by rw [mul_comm, hrec, mul_comm]
    rw [hstep, hnb]
    have : (n - 1) * A - (n - 2) * A = ((n - 1) - (n - 2)) * A := (Nat.sub_mul _ _ _).symm
    rw [this, show (n - 1) - (n - 2) = 1 from by omega, one_mul]
  have hcop : p.Coprime A := hp.coprime_choose_of_lt hmp (by omega)
  have hpD : ¬ (p ∣ D) := by
    intro hpd
    have hpA : p ∣ A := hDmul ▸ hpd.mul_left _
    exact (hp.dvd_iff_not_coprime.mp hpA) hcop
  haveI : CharP F p := hchar ▸ ringChar.charP F
  have hDF : (D : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p D]; exact hpD
  have hval : ((B : F) - (A : F)) = -(D : F) := by
    have : ((D : ℕ) : F) = (A : F) - (B : F) := by
      rw [hD]; push_cast [hle]; ring
    rw [this]; ring
  rw [hval]
  simpa using hDF

/-- Abbreviation for the "diagonal" variable `y = X₀ + X₁`. -/
private noncomputable def ehY : MvPolynomial (Fin 2) F := X 0 + X 1

private lemma totalDegree_ehY_pow_le (j : ℕ) :
    (ehY (F := F) ^ j).totalDegree ≤ j := by
  calc (ehY (F := F) ^ j).totalDegree ≤ j * (ehY (F := F)).totalDegree := totalDegree_pow _ _
    _ ≤ j * 1 := by
        gcongr
        calc (ehY (F := F)).totalDegree ≤ max (X 0 : MvPolynomial (Fin 2) F).totalDegree
              (X 1 : MvPolynomial (Fin 2) F).totalDegree := totalDegree_add _ _
          _ ≤ 1 := by simp [totalDegree_X]
    _ = j := by ring

/-- **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{|s|}`
by a polynomial of total degree at most `|s| - 1`. -/
private lemma totalDegree_prod_sub_pow_le (s : Finset F) :
    ((∏ c ∈ s, (ehY (F := F) - C c)) - ehY ^ s.card).totalDegree ≤ s.card - 1 := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has hind =>
    rw [Finset.prod_cons, Finset.card_cons]
    have hdecomp :
        (ehY (F := F) - C a) * (∏ c ∈ s, (ehY - C c)) - ehY ^ (s.card + 1)
          = (ehY - C a) * ((∏ c ∈ s, (ehY - C c)) - ehY ^ s.card) - C a * ehY ^ s.card := by
      ring
    rw [hdecomp]
    refine (totalDegree_sub _ _).trans ?_
    apply max_le
    · rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · refine (totalDegree_mul _ _).trans ?_
        have h1 : (ehY (F := F) - C a).totalDegree ≤ 1 := by
          refine (totalDegree_sub _ _).trans ?_
          apply max_le
          · calc (ehY (F := F)).totalDegree
                  ≤ max (X 0 : MvPolynomial (Fin 2) F).totalDegree
                      (X 1 : MvPolynomial (Fin 2) F).totalDegree := totalDegree_add _ _
              _ ≤ 1 := by simp [totalDegree_X]
          · simp [totalDegree_C]
        have hscard : 1 ≤ s.card := hne.card_pos
        calc (ehY (F := F) - C a).totalDegree
              + ((∏ c ∈ s, (ehY - C c)) - ehY ^ s.card).totalDegree
            ≤ 1 + (s.card - 1) := by gcongr
          _ = s.card := by omega
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact totalDegree_ehY_pow_le _

/-- **The Erdős–Heilbronn polynomial** for a padded sumset `C'`. -/
private noncomputable def ehQ (Cset : Finset F) : MvPolynomial (Fin 2) F :=
  (X 1 - X 0) * ∏ c ∈ Cset, (X 0 + X 1 - C c)

/-- The coefficient of the top monomial `X₀^{n-1} X₁^{n-2}` in `ehQ C'` (with `|C'| = 2(n-2)`)
equals its coefficient in the leading part `(X₁ - X₀)(X₀ + X₁)^{2(n-2)}`. -/
private lemma coeff_ehQ_eq_leading {Cset : Finset F} {n : ℕ} (hn : 3 ≤ n)
    (hCcard : Cset.card = 2 * (n - 2)) :
    coeff (ehMon (n - 1) (n - 2)) (ehQ Cset)
      = coeff (ehMon (n - 1) (n - 2))
          ((X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ (2 * (n - 2))) := by
  classical
  set m := 2 * (n - 2) with hm
  set P' : MvPolynomial (Fin 2) F := ∏ c ∈ Cset, (X 0 + X 1 - C c) with hP'
  have hP'eq : P' = ∏ c ∈ Cset, (ehY - C c) := by rw [hP', ehY]
  have hQdiff : ehQ Cset - (X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ m
      = (X 1 - X 0) * (P' - ehY ^ m) := by
    rw [ehQ, ehY, ← hP']
    ring
  have htd : (ehQ Cset - (X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ m).totalDegree
      < m + 1 := by
    rw [hQdiff]
    refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
    have h1 : (X 1 - X 0 : MvPolynomial (Fin 2) F).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans ?_
      apply max_le <;> simp [totalDegree_X]
    have h2 : (P' - ehY ^ m).totalDegree ≤ m - 1 := by
      rw [hP'eq, ← hCcard]
      exact totalDegree_prod_sub_pow_le Cset
    have hmpos : 1 ≤ m := by omega
    calc (X 1 - X 0 : MvPolynomial (Fin 2) F).totalDegree + (P' - ehY ^ m).totalDegree
        ≤ 1 + (m - 1) := by gcongr
      _ = m := by omega
      _ < m + 1 := by omega
  have htdeg : ∑ i ∈ (ehMon (n - 1) (n - 2)).support, (ehMon (n - 1) (n - 2)) i = m + 1 := by
    have hsub : (ehMon (n - 1) (n - 2)).support ⊆ (Finset.univ : Finset (Fin 2)) :=
      Finset.subset_univ _
    rw [Finset.sum_subset hsub (fun i _ hi => Finsupp.notMem_support_iff.mp hi)]
    rw [Fin.sum_univ_two, ehMon_apply_zero, ehMon_apply_one]
    omega
  have hcoeff0 : coeff (ehMon (n - 1) (n - 2))
      (ehQ Cset - (X 1 - X 0 : MvPolynomial (Fin 2) F) * (X 0 + X 1) ^ m) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    rw [htdeg]; exact htd
  rw [coeff_sub, sub_eq_zero] at hcoeff0
  rw [hcoeff0]

/-- `ehQ Cset` has total degree at most `|Cset| + 1`. -/
private lemma totalDegree_ehQ_le (Cset : Finset F) :
    (ehQ Cset).totalDegree ≤ Cset.card + 1 := by
  rw [ehQ]
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (X 1 - X 0 : MvPolynomial (Fin 2) F).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans ?_
    apply max_le <;> simp [totalDegree_X]
  have h2 : (∏ c ∈ Cset, (X 0 + X 1 - C c : MvPolynomial (Fin 2) F)).totalDegree ≤ Cset.card := by
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ c ∈ Cset, (X 0 + X 1 - C c : MvPolynomial (Fin 2) F).totalDegree
        ≤ ∑ _c ∈ Cset, 1 := by
          apply Finset.sum_le_sum
          intro c _
          refine (totalDegree_sub _ _).trans ?_
          apply max_le
          · calc (X 0 + X 1 : MvPolynomial (Fin 2) F).totalDegree
                  ≤ max (X 0 : MvPolynomial (Fin 2) F).totalDegree
                      (X 1 : MvPolynomial (Fin 2) F).totalDegree := totalDegree_add _ _
              _ ≤ 1 := by simp [totalDegree_X]
          · simp [totalDegree_C]
      _ = Cset.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  calc (X 1 - X 0 : MvPolynomial (Fin 2) F).totalDegree
        + (∏ c ∈ Cset, (X 0 + X 1 - C c : MvPolynomial (Fin 2) F)).totalDegree
      ≤ 1 + Cset.card := by gcongr
    _ = Cset.card + 1 := by ring

/-- `ehQ Cset` vanishes at every point `s : Fin 2 → F` whose two coordinates either coincide,
or sum to an element of `Cset`. In particular it vanishes on `A × A` once every distinct-pair
sum from `A` lies in `Cset`. -/
private lemma eval_ehQ_eq_zero {Cset : Finset F} (s : Fin 2 → F)
    (h : s 0 = s 1 ∨ (s 0 + s 1) ∈ Cset) :
    eval s (ehQ Cset) = 0 := by
  rw [ehQ, eval_mul]
  rcases h with heq | hmem
  · have : eval s (X 1 - X 0 : MvPolynomial (Fin 2) F) = 0 := by
      simp [eval_sub, eval_X, heq]
    rw [this, zero_mul]
  · have : eval s (∏ c ∈ Cset, (X 0 + X 1 - C c : MvPolynomial (Fin 2) F)) = 0 := by
      rw [eval_prod]
      apply Finset.prod_eq_zero hmem
      simp [eval_sub, eval_add, eval_X, eval_C]
    rw [this, mul_zero]

end ErdosHeilbronn

section Main

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The restricted sumset `Σ₂(A) = { a + b : a, b ∈ A, a ≠ b }`, as the set of all `2`-subset
sums of `A`. -/
def restrictedSumset2 (A : Finset F) : Finset F :=
  (A.powersetCard 2).image (fun S => ∑ a ∈ S, a)

omit [Fintype F] in
/-- If `a, b ∈ A` are distinct, then `a + b ∈ Σ₂(A)`. -/
lemma add_mem_restrictedSumset2 {A : Finset F} {a b : F}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    a + b ∈ restrictedSumset2 A := by
  rw [restrictedSumset2, Finset.mem_image]
  refine ⟨{a, b}, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ ha
      · exact (Finset.mem_singleton.mp h) ▸ hb
    · rw [Finset.card_pair hab]
  · rw [Finset.sum_pair hab]

/-- **Erdős–Heilbronn theorem (`h = 2`).** Let `F` be a finite field whose characteristic
`p := ringChar F` is prime, and let `A : Finset F` with `n := |A| ≥ 2` and `2(n - 2) < p`.
Then the restricted sumset `Σ₂(A) = { a + b : a, b ∈ A, a ≠ b }` satisfies

  `|Σ₂(A)| ≥ 2(n - 2) + 1 = 2n - 3`. -/
theorem erdos_heilbronn_two {p : ℕ} (hp : p.Prime) (hchar : ringChar F = p)
    (A : Finset F) (hn : 2 ≤ A.card) (hsmall : 2 * (A.card - 2) < p) :
    2 * (A.card - 2) + 1 ≤ (restrictedSumset2 A).card := by
  classical
  set n := A.card with hncard
  /- For the base case $n = 2$, the bound reduces to $1 \le |\Sigma_2(A)|$, which holds
     since $A$ has cardinality 2, implying there exists at least one pair of distinct
     elements whose sum is in $\Sigma_2(A)$. -/
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · -- Case $n = 2$.
    have hn2 : n = 2 := by omega
    rw [hn2]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.mp (hncard ▸ hn2)
    have hmem : a + b ∈ restrictedSumset2 A :=
      add_mem_restrictedSumset2 (hAeq ▸ Finset.mem_insert_self _ _)
        (hAeq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hab
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  · -- Case $n \ge 3$. We apply Alon's Combinatorial Nullstellensatz.
    have hn3 : 3 ≤ n := hge
    by_contra hcon
    push Not at hcon
    have hle : (restrictedSumset2 A).card ≤ 2 * (n - 2) := by omega
    set m := 2 * (n - 2) with hm
    /- Since $p \le |F|$ and $m < p$, we have $m < |F|$, allowing us to pad the restricted
       sumset to a set of size $m$. -/
    have hp_le_card : p ≤ Fintype.card F := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hdvd : p ∣ Fintype.card F := by
        rw [← prime_dvd_char_iff_dvd_card (R := F) p, hchar]
      exact Nat.le_of_dvd Fintype.card_pos hdvd
    have hm_le_card : m ≤ Fintype.card F := le_trans (le_of_lt hsmall) hp_le_card
    obtain ⟨C', hC'sub, -, hC'card⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (restrictedSumset2 A)) hle (by rw [Finset.card_univ]; exact hm_le_card)
    set f := MvPolynomial.ehQ C' with hf
    set t := MvPolynomial.ehMon (n - 1) (n - 2) with ht
    -- Verify that the coefficient of the target monomial $t$ in the polynomial $f$ is nonzero.
    have hcoeff : MvPolynomial.coeff t f ≠ 0 := by
      rw [hf, ht, MvPolynomial.coeff_ehQ_eq_leading hn3 hC'card,
        MvPolynomial.coeff_leading hn3]
      exact MvPolynomial.leading_coeff_ne_zero hp hchar hn3 (hm ▸ hsmall)
    -- Compute the degree of the monomial $t$, which is exactly $m + 1$.
    have htdeg : t.degree = m + 1 := by
      rw [ht, Finsupp.degree_eq_sum, Fin.sum_univ_two,
        MvPolynomial.ehMon_apply_zero, MvPolynomial.ehMon_apply_one]
      omega
    -- Establish that the total degree of $f$ is exactly equal to the degree of $t$.
    have htotalDeg : f.totalDegree = t.degree := by
      refine le_antisymm ?_ ?_
      · rw [htdeg, hf, ← hC'card]
        exact MvPolynomial.totalDegree_ehQ_le C'
      · have hmem : t ∈ f.support := MvPolynomial.mem_support_iff.mpr hcoeff
        rw [Finsupp.degree_eq_sum]
        rw [← Finset.sum_subset (Finset.subset_univ t.support)
          (fun i _ hi => Finsupp.notMem_support_iff.mp hi)]
        exact MvPolynomial.le_totalDegree (p := f) hmem
    -- Confirm that the degree of the monomial $t$ in each variable $X_i$ is strictly less
    -- than $|A| = n$.
    set S : Fin 2 → Finset F := fun _ => A with hS
    have htS : ∀ i, t i < (S i).card := by
      intro i
      rw [hS]
      fin_cases i
      · simp [ht, MvPolynomial.ehMon_apply_zero, ← hncard]; omega
      · simp [ht, MvPolynomial.ehMon_apply_one, ← hncard]; omega
    -- Apply Alon's Combinatorial Nullstellensatz to obtain a point of non-vanishing.
    obtain ⟨s, hsA, hsne⟩ := MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
      f t hcoeff htotalDeg S htS
    -- Show that this contradicts the fact that $f$ vanishes identically on the grid $A \times A$.
    apply hsne
    apply MvPolynomial.eval_ehQ_eq_zero
    by_cases heq : s 0 = s 1
    · exact Or.inl heq
    · refine Or.inr (hC'sub ?_)
      exact add_mem_restrictedSumset2 (hsA 0) (hsA 1) heq

end Main

end MvPolynomial
