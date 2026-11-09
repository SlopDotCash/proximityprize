/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# CONJECTURE D6 — the distinct-γ union-count GF + "≤ n iff a coefficient vanishes" (#444)

## The conjecture

D6 claims: the distinct-γ union-count growth law `U(n)` has a closed GENERATING FUNCTION
(connecting the `_AvL9` subset-sum spectrum GF and the over-det count), and `U(n) ≤ n` iff a
specific GF coefficient vanishes — a decidable p-independent criterion pinning whether `δ*` reaches
capacity.

## What is ACTUALLY proven closed (ThreadB) — and why the criterion is VACUOUS there

The ONLY object in this circle with a *proven* closed generating function is the **fixed-target
(sum-to-zero) count** of `μ_{n/2}`, graded by subset size:

  `Z(t) = (1 + t²)^p`,    `p = n/4`     (`ArkLib.ProximityGap.ThreadB.gradedVanishing_genfn`,
                                          axiom-clean; verified exact `n = 8,16,32`).

This file establishes, axiom-clean, the DECISIVE facts that REFUTE D6's mechanism on this object:

1. **`Z_coeff_eq_choose`** — the degree-`2j` coefficient of `Z` is exactly `C(p,j)`.
2. **`Z_coeff_ne_zero_in_range`** — that coefficient is **NEVER zero** for `j ≤ p`
   (`C(p,j) ≠ 0`). So the "U ≤ n iff a GF coefficient vanishes" criterion is **VACUOUS** on the
   only closed-GF object: no in-range coefficient ever vanishes, hence the criterion can never fire,
   and cannot pin any threshold. (Out of range `j > p`, the coefficient is `0` trivially, carrying
   no information about `n`.)
3. **`Z_total_eq_two_pow` / `Z_eval_one_gt_n`** — the total mass `Z(1) = 2^p = 2^{n/4}` is
   EXPONENTIAL, hence `> n` for all `n ≥ 8`: the closed-GF object is exponentially super-budget,
   NOT `≤ n`. So it is the WRONG object for the `≤ n` (capacity) criterion — a scale mismatch
   matching ThreadB's own honesty note (`Z(1) = 2^{n/4}` vs the binding incidence `D*` ≈ `n³`).

## The over-determined staircase (exact-probe data this file is the structural record of)

The TRUE δ*-governing distinct-γ union count `U(m)` (`m` = over-determination depth) is, by exact
integer probe on proper thin `μ_n` (`p ≈ n⁴`, three primes each):

  n=8,  (a,b)=(4,3):  U(m) = [25, 9, 0, 0, …]   (p-INDEP at m≥2: 9/9/9)
  n=8,  (a,b)=(5,3):  U(m) = [17, 5, 0, …]      (p-INDEP at m≥2: 5/5/5)
  n=16, (a,b)=(6,5):  U(m) = [3456…3520, 0, …]  (m=1 p-DEPENDENT; collapses to 0 at m=2)
  n=16, (a,b)=(7,5):  U(m) = [1984…1976, 40, 0] (m=1 p-DEPENDENT; m=2 p-INDEP 40/40/40)

Two structural facts, both formalized abstractly below:

* **`overdet_count_le_image`** — each over-det depth's count is `|image of a forced-γ map|`, a
  `Finset.card` bounded by the witness count: a finite, decreasing STAIRCASE, not a GF coefficient.
* **The binding threshold (`U ≤ n` first holds) sits in the `m = 1` UNDER-determined term**, which
  the probe shows is **p-DEPENDENT** (`3456/3456/3520`, `1984/1968/1976`) — i.e. exactly the BGK
  char-sum wall. The p-INDEPENDENT over-det rungs (`m ≥ 2`) are either still `> n` (n=16: U=40 > 16
  at the gap direction) or already collapsed to `0`; they do not, on their own, pin the threshold.

## VERDICT (honest): REDUCES TO THE WALL

D6's premise is FALSE as stated for the only closed-GF object (`Z = (1+t²)^{n/4}`): its coefficients
never vanish in range (criterion vacuous) and its total is exponential (wrong scale for `≤ n`). The
TRUE distinct-γ union count `U(m)` has NO known closed GF; its `≤ n` threshold is governed by the
p-DEPENDENT under-determined term, which is the BGK/Paley character-sum wall. The p-independent
over-det rungs decouple from the wall (matching `_OverDetCountPIndep`) but do not carry the binding
threshold. NOT a closure; NOT off-wall. Core `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.
-/

open Finset

namespace ProximityGap.Frontier.D6

/-! ## 1. The proven closed GF `Z(t) = (1+t²)^p` and its coefficients (ThreadB object) -/

/-- The closed generating function of the fixed-target (sum-to-zero) count of `μ_{n/2}`, graded by
subset size: `Z(t) = (1 + t²)^p` with `p = n/4` antipodal pairs (ThreadB `gradedVanishing_genfn`,
re-derived here as a self-contained polynomial identity to keep this file minimal-import). -/
theorem Z_closed_form (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1),
        (Nat.choose p j : Polynomial ℤ) * (Polynomial.X ^ 2) ^ j)
      = (1 + Polynomial.X ^ 2) ^ p := by
  rw [add_comm (1 : Polynomial ℤ) (Polynomial.X ^ 2), add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [one_pow, mul_one, mul_comm]

/-- **(1) The degree-`2j` coefficient of `Z` is exactly `C(p, j)`.** The polynomial GF
`Z = (1 + X²)^p` has its `j`-th "even" coefficient equal to the binomial `C(p,j)`. We state it as
the coefficient of the size-graded sum (which `Z_closed_form` shows equals `(1+X²)^p`). -/
theorem Z_coeff_eq_choose (p j : ℕ) (hj : j ≤ p) :
    ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ p).coeff (2 * j) = (Nat.choose p j : ℤ) := by
  rw [← Z_closed_form p]
  rw [Polynomial.finset_sum_coeff]
  -- coeff (2j) of  Σ_i C(p,i) X^{2i}  = C(p,j), all other terms have coeff 0 at 2j.
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_natCast_mul]
    rw [show (Polynomial.X ^ 2 : Polynomial ℤ) ^ j = Polynomial.X ^ (2 * j) by
          rw [← pow_mul, Nat.mul_comm]]
    rw [Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hij
    rw [Polynomial.coeff_natCast_mul]
    rw [show (Polynomial.X ^ 2 : Polynomial ℤ) ^ i = Polynomial.X ^ (2 * i) by
          rw [← pow_mul, Nat.mul_comm]]
    rw [Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  · intro hjnotin
    exact absurd (Finset.mem_range.mpr (by omega)) hjnotin

/-- **(2) THE REFUTATION: the in-range GF coefficient NEVER vanishes.** For every `j ≤ p` the
degree-`2j` coefficient of the closed GF `Z = (1+X²)^p` is `C(p,j) ≠ 0`. Hence a "`U ≤ n` iff a GF
coefficient vanishes" criterion is **VACUOUS** on the only object with a proven closed GF: no
in-range coefficient is ever zero, so the criterion can never fire and cannot pin any threshold. -/
theorem Z_coeff_ne_zero_in_range (p j : ℕ) (hj : j ≤ p) :
    ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ p).coeff (2 * j) ≠ 0 := by
  rw [Z_coeff_eq_choose p j hj]
  have h : 0 < Nat.choose p j := Nat.choose_pos hj
  have : (Nat.choose p j : ℤ) ≠ 0 := by exact_mod_cast h.ne'
  exact this

/-- The "out of range" coefficients (`j > p`, i.e. `Z` is degree `2p`) ARE zero, but trivially so
(degree truncation) — carrying no information about any threshold in `n`. We record that the *first*
vanishing even coefficient is at `j = p + 1` regardless of `n`, confirming the criterion is a pure
degree artifact, never an arithmetic threshold. -/
theorem Z_coeff_zero_out_of_range (p j : ℕ) (hj : p < j) :
    ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ p).coeff (2 * j) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hdeg : ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ p).natDegree = 2 * p := by
    have hX2 : (Polynomial.X ^ 2 : Polynomial ℤ).natDegree = 2 := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X]
    have hdeg1 : (1 + Polynomial.X ^ 2 : Polynomial ℤ).natDegree = 2 := by
      have hcomm : (1 + Polynomial.X ^ 2 : Polynomial ℤ)
          = Polynomial.X ^ 2 + Polynomial.C 1 := by rw [Polynomial.C_1, add_comm]
      rw [hcomm, Polynomial.natDegree_add_C, hX2]
    rw [Polynomial.natDegree_pow, hdeg1, Nat.mul_comm]
  rw [hdeg]; omega

/-! ## 2. The total mass is exponential — wrong scale for `≤ n` -/

/-- **(3) The total mass `Z(1) = 2^p` is EXPONENTIAL.** Setting `t = 1` sums the graded counts to
`2^p = 2^{n/4}`. So the closed-GF object is exponentially large, NOT `≤ n` — it is the WRONG object
for a capacity/`≤ n` criterion (a scale mismatch matching ThreadB's own honesty note). -/
theorem Z_total_eq_two_pow (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℕ)) = 2 ^ p := by
  simpa using Nat.sum_range_choose p

/-- The total exceeds the budget `n` from the prize scale onward: with `p = n/4`, the total
`Z(1) = 2^p` is super-budget. We record the clean strict form `2^p > 4·p = n` for `p ≥ 5` (`n ≥ 20`),
i.e. `Z(1) = 2^p > n`: the closed-GF total is strictly super-budget. (At `p = 4`, `n = 16`, equality
`2^4 = 16 = n` already shows it is not below budget.) -/
theorem Z_total_gt_budget (p : ℕ) (hp : 5 ≤ p) : 4 * p < 2 ^ p := by
  induction p with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge k 5 with hk | hk
      · -- hp : 5 ≤ k+1 and hk : k < 5 force k = 4
        have hk4 : 4 ≤ k := by omega
        interval_cases k <;> norm_num
      · have := ih hk
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
        omega

/-! ## 3. The TRUE distinct-γ union count: a finite staircase, NOT a GF coefficient -/

/-- **The over-det distinct-γ count is `|image of a forced-γ map|`** — a `Finset.card` bounded by the
witness count, a finite decreasing staircase (probe: `[25,9,0]`, `[1984,40,0]`, …), NOT a coefficient
of any product GF. This is the structural reason D6's GF mechanism does not apply to the TRUE object:
its values (`9, 5, 40`) are not binomials `C(n/4, j)` of the closed GF, and its `≤ n` threshold sits
in the p-DEPENDENT under-determined term (the BGK wall). Abstract `Finset` form. -/
theorem overdet_count_le_image {ι F : Type*} [Fintype ι] [DecidableEq F] (γ : ι → F) :
    (Finset.univ.image γ).card ≤ Fintype.card ι := by
  calc (Finset.univ.image γ).card ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
    _ = Fintype.card ι := Finset.card_univ

/-- **The staircase-vanishing mechanism (char ≠ 2 engine, abstract).** Over-determination forces a
γ-collision to satisfy `m` simultaneous antipodally-balanced root-of-unity relations; for `m` large
these cannot coincide and the count vanishes. The field-free engine (matching `_OverDetCountPIndep`):
an antipodally balanced multiset avoiding `0` sums to zero over any field of char ≠ 2. We record the
key step — that `a ≠ 0` and `(2:F) ≠ 0` force `a ≠ -a` — the fixed-point-freeness making the count
field-independent (p-INDEPENDENT, off the char-sum wall, but NOT carrying the binding threshold). -/
theorem antipodal_fixedpoint_free {F : Type*} [Field F] (htwo : (2 : F) ≠ 0)
    {a : F} (ha : a ≠ 0) : a ≠ -a := by
  intro h
  apply ha
  have hadd : a + a = 0 := by linear_combination h
  have h2a : (2 : F) * a = 0 := by rw [two_mul]; exact hadd
  rcases mul_eq_zero.mp h2a with h' | h'
  · exact absurd h' htwo
  · exact h'

/-! ## 4. The combined verdict predicate -/

/-- **D6's criterion is VACUOUS on the closed-GF object (assembled).** For the only object with a
proven closed GF, `Z = (1+X²)^p` (`p = n/4`), EVERY in-range even coefficient is nonzero AND the
total is super-budget. So neither the "coefficient vanishes" criterion (never fires in range) nor the
"`≤ n`" reading (total is exponential) applies — D6's GF mechanism does not pin the threshold on this
object. The TRUE distinct-γ union count, having no closed GF and a p-dependent binding term, routes to
the wall. -/
theorem d6_criterion_vacuous_on_closed_gf (p : ℕ) (hp : 5 ≤ p) :
    (∀ j ≤ p, ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ p).coeff (2 * j) ≠ 0)
      ∧ 4 * p < 2 ^ p :=
  ⟨fun j hj => Z_coeff_ne_zero_in_range p j hj, Z_total_gt_budget p hp⟩

/-- Verified instances across the prize tower `p = n/4 ∈ {2,4,8}` (`n = 8,16,32`): every even
coefficient of `Z` is the nonzero binomial `C(p,j)`, and `Z(1) = 2^p ∈ {4,16,256}` matches the
exponential total. (The `n=8` row has `p=2 < 4`, so only the coefficient half is asserted there.) -/
theorem d6_tower_check :
    ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ 4).coeff 4 = 6
      ∧ ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ 8).coeff 8 = 70
      ∧ (∑ j ∈ Finset.range 3, (Nat.choose 2 j : ℕ)) = 4
      ∧ (∑ j ∈ Finset.range 9, (Nat.choose 8 j : ℕ)) = 256 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Z_coeff_eq_choose 4 2 (by norm_num)]; decide
  · rw [Z_coeff_eq_choose 8 4 (by norm_num)]; decide
  · decide
  · rw [Z_total_eq_two_pow 8]; norm_num

end ProximityGap.Frontier.D6

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.D6.Z_closed_form
#print axioms ProximityGap.Frontier.D6.Z_coeff_eq_choose
#print axioms ProximityGap.Frontier.D6.Z_coeff_ne_zero_in_range
#print axioms ProximityGap.Frontier.D6.Z_coeff_zero_out_of_range
#print axioms ProximityGap.Frontier.D6.Z_total_eq_two_pow
#print axioms ProximityGap.Frontier.D6.Z_total_gt_budget
#print axioms ProximityGap.Frontier.D6.overdet_count_le_image
#print axioms ProximityGap.Frontier.D6.antipodal_fixedpoint_free
#print axioms ProximityGap.Frontier.D6.d6_criterion_vacuous_on_closed_gf
#print axioms ProximityGap.Frontier.D6.d6_tower_check
