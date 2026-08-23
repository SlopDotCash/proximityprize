/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# LogUp Protocol 2 — the soundness converse (issue #13)

The completeness direction of LogUp is the grand-sum logarithmic-derivative identity
`grandSum_identity` (`LogupGrandSumIdentity.lean`): a **valid** lookup makes the table-side and
column-side sums-of-reciprocals coincide for every challenge `x`. Soundness needs the **converse**:
an **invalid** lookup must make a *nonzero* check polynomial, so that Schwartz–Zippel
(`logup_SZ_soundness`, which takes the nonvanishing as a premise `hQ_ne`) actually fires.

This file supplies that previously-missing converse, fully proven against the in-tree count algebra.

## The mathematics

Write `c a := lookupMultiplicityCount oStmt a` (number of lookup-column entries equal to `a`) and
`tableMultiplicityCount oStmt a` (number of table rows equal to `a`). The proven count-form lemmas
in `Common.lean` give, as rational functions of the challenge `x`,

* table side  `∑_u m(u)/(x + t(u))  =  ∑_{a : tableMultiplicityCount a > 0} c a /(x + a)`, and
* column side `∑_i ∑_u 1/(x + f_i(u)) =  ∑_{a : F} c a /(x + a)`.

Their difference is therefore `∑_{a : tableMultiplicityCount a = 0} c a /(x + a)`, supported exactly
on the values `a` that occur in some **column** but **not** in the table. Clearing the common
denominator `∏_{b : F}(x + b)` turns this into the polynomial

    grandSumCheckPoly  =  ∑_{a : F}  C (coeff a) * ∏_{b ≠ a} (X + C b),
    coeff a = if tableMultiplicityCount a = 0 then (c a : F) else 0.

**Key fact (`grandSumCheckPoly_ne_zero_of_bad_lookup`).** If the lookup is invalid there is a value
`a₀` occurring in a column but not in the table (`bad_lookup_exists_column_only_value`). Evaluating
`grandSumCheckPoly` at `-a₀` kills every summand except the `a₀` one (each other product contains the
factor `X + C a₀`, which vanishes), leaving `(c a₀ : F) * ∏_{b ≠ a₀}(b - a₀)`. The product is a
product of differences of *distinct* field elements, hence nonzero; and `(c a₀ : F) ≠ 0` because
`c a₀ ≤ M·2ⁿ < char F` — the paper's `charLarge` hypothesis is *exactly* what prevents the residue
from vanishing modulo the characteristic. So the evaluation is nonzero and the polynomial is nonzero.

This is the genuine soundness obstruction: a residue at an uncancelled pole. It is the converse
companion of `grandSum_identity`, and the nonvanishing premise that `logup_SZ_soundness` consumes.
-/

open scoped NNReal
open Polynomial

namespace Logup

section SoundnessConverse

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}

/-! ### Combinatorial pillar: an invalid lookup exposes a column-only value -/

/-- **An invalid lookup exposes a column-only value.** If the input is *not* in `inputRelation`
(some lookup-column entry is not in the table range) then there is a field value `a₀` occurring in a
column (`0 < lookupMultiplicityCount`) but in no table row (`tableMultiplicityCount = 0`). This is
the value at whose pole the grand-sum identity fails. -/
theorem bad_lookup_exists_column_only_value
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    ∃ a₀ : F, 0 < lookupMultiplicityCount oStmt a₀ ∧ tableMultiplicityCount oStmt a₀ = 0 := by
  rw [mem_inputRelation_iff] at hBad
  push Not at hBad
  obtain ⟨i, x, hx⟩ := hBad
  -- `hx : ∀ y, evalOnHypercube (columnOracle oStmt i) x ≠ evalOnHypercube (tableOracle oStmt) y`
  refine ⟨evalOnHypercube (columnOracle oStmt i) x, ?_, ?_⟩
  · -- the pair `(i, x)` is counted, so the column count is positive
    have hmem : (i, x) ∈ (Finset.univ : Finset (Fin M × Hypercube n)).filter
        (fun ix => evalOnHypercube (columnOracle oStmt ix.1) ix.2 =
          evalOnHypercube (columnOracle oStmt i) x) := by simp
    exact Finset.card_pos.mpr ⟨(i, x), hmem⟩
  · -- no table row hits this value
    apply tableMultiplicityCount_eq_zero_of_not_exists_eval
    rintro ⟨y, hy⟩
    exact hx y hy.symm

/-! ### Arithmetic pillar: the residue is nonzero modulo the characteristic -/

/-- The total number of lookup-column entries with a given value is at most `M · 2ⁿ`. -/
theorem lookupMultiplicityCount_le (oStmt : ∀ i, OStmtIn F n M i) (a : F) :
    lookupMultiplicityCount oStmt a ≤ M * 2 ^ n := by
  unfold lookupMultiplicityCount
  calc ((Finset.univ : Finset (Fin M × Hypercube n)).filter fun ix =>
          evalOnHypercube (columnOracle oStmt ix.1) ix.2 = a).card
      ≤ (Finset.univ : Finset (Fin M × Hypercube n)).card := Finset.card_filter_le _ _
    _ = Fintype.card (Fin M × Hypercube n) := Finset.card_univ
    _ = M * 2 ^ n := by rw [Fintype.card_prod, Fintype.card_fin, card_hypercube]

/-- **The column count is nonzero in `F`.** By the paper's `charLarge` hypothesis
`M · 2ⁿ < char F`, a positive lookup-column count stays nonzero when cast into the field — the
characteristic is too large to annihilate the residue. -/
theorem lookupMultiplicityCount_natCast_ne_zero
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) (a : F)
    (hpos : 0 < lookupMultiplicityCount oStmt a) :
    (lookupMultiplicityCount oStmt a : F) ≠ 0 := by
  apply natCast_ne_zero_of_pos_lt_ringChar hpos
  exact lt_of_le_of_lt (lookupMultiplicityCount_le oStmt a) stmt.charLarge

/-! ### The cleared grand-sum check polynomial and its nonvanishing -/

/-- The cleared-denominator grand-sum **check polynomial** in the challenge variable `X`.

Its coefficient at value `a` is the column count `c a` on values *absent* from the table and `0`
on values present in the table — i.e. the numerator of `column side − table side` after clearing the
common denominator `∏_{b}(X + b)`. A valid lookup has all column values in the table, so every
coefficient vanishes and the polynomial is `0` (completeness); the converse below shows an invalid
lookup forces it nonzero. -/
noncomputable def grandSumCheckPoly (oStmt : ∀ i, OStmtIn F n M i) : Polynomial F :=
  ∑ a : F,
    Polynomial.C (if tableMultiplicityCount oStmt a = 0
        then (lookupMultiplicityCount oStmt a : F) else 0) *
      ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b)

/-- Evaluation of `grandSumCheckPoly` at a point `v`, pushed through the sum/product. -/
theorem eval_grandSumCheckPoly (oStmt : ∀ i, OStmtIn F n M i) (v : F) :
    (grandSumCheckPoly oStmt).eval v =
      ∑ a : F,
        (if tableMultiplicityCount oStmt a = 0
            then (lookupMultiplicityCount oStmt a : F) else 0) *
          ∏ b ∈ Finset.univ.erase a, (v + b) := by
  unfold grandSumCheckPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl (fun b _ => ?_)
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- **The soundness converse.** An invalid lookup forces the cleared grand-sum check polynomial to be
nonzero — the residue at the uncancelled column-only pole is nonzero. This is the nonvanishing
premise (`hQ_ne`) that `logup_SZ_soundness` consumes to turn the LogUp algebraic check into a genuine
Schwartz–Zippel soundness bound. -/
theorem grandSumCheckPoly_ne_zero_of_bad_lookup
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    grandSumCheckPoly oStmt ≠ 0 := by
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  intro hzero
  -- Evaluate the (supposedly zero) polynomial at `-a₀`.
  have heval : (grandSumCheckPoly oStmt).eval (-a₀) = 0 := by rw [hzero]; simp
  rw [eval_grandSumCheckPoly] at heval
  -- Every summand with `a ≠ a₀` vanishes: its product contains the factor `(-a₀ + a₀) = 0`.
  have hterms : ∀ a ∈ (Finset.univ : Finset F), a ≠ a₀ →
      (if tableMultiplicityCount oStmt a = 0 then (lookupMultiplicityCount oStmt a : F) else 0) *
        ∏ b ∈ Finset.univ.erase a, (-a₀ + b) = 0 := by
    intro a _ hane
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hane, Finset.mem_univ a₀⟩)
        (neg_add_cancel a₀))
  rw [Finset.sum_eq_single a₀ hterms (fun hni => absurd (Finset.mem_univ a₀) hni)] at heval
  -- The surviving `a₀` term is `(c a₀ : F) * ∏_{b ≠ a₀}(-a₀ + b) = 0`.
  rw [if_pos htab] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook hc
  · -- a product of `(-a₀ + b)` over `b ≠ a₀` cannot vanish: each factor is nonzero
    rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, hb, hb0⟩ := hprod
    rw [Finset.mem_erase] at hb
    exact hb.1 (by linear_combination hb0)

/-- **Completeness sanity check for the check polynomial.** A *valid* lookup makes every coefficient
of `grandSumCheckPoly` vanish (each column value occurs in the table, so the `if` guard never yields
a nonzero numerator), hence the polynomial is identically `0`. This is the converse direction of
`grandSumCheckPoly_ne_zero_of_bad_lookup` and confirms the coefficient encoding is faithful: nonzero
iff the lookup is invalid. -/
theorem grandSumCheckPoly_eq_zero_of_good_lookup
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hGood : (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    grandSumCheckPoly oStmt = 0 := by
  unfold grandSumCheckPoly
  refine Finset.sum_eq_zero (fun a _ => ?_)
  -- the coefficient at every value `a` is zero, so each summand `C 0 * _` is zero
  have hcoeff : (if tableMultiplicityCount oStmt a = 0
      then (lookupMultiplicityCount oStmt a : F) else 0) = 0 := by
    by_cases htab : tableMultiplicityCount oStmt a = 0
    · -- table count `0` ⇒ (valid lookup) column count `0` ⇒ numerator `0`
      rw [if_pos htab]
      have hnot : ¬ ∃ u : Hypercube n, evalOnHypercube (tableOracle oStmt) u = a := by
        rintro ⟨u, hu⟩
        have hpos := tableMultiplicityCount_pos_of_eval oStmt u
        rw [hu] at hpos
        omega
      rw [lookupMultiplicityCount_eq_zero_of_not_exists_table stmt oStmt hGood a hnot,
        Nat.cast_zero]
    · rw [if_neg htab]
  rw [hcoeff, Polynomial.C_0, zero_mul]

end SoundnessConverse



end Logup

/- Axiom audit for the #13 soundness-converse bricks. -/
#print axioms Logup.bad_lookup_exists_column_only_value
#print axioms Logup.lookupMultiplicityCount_natCast_ne_zero
#print axioms Logup.grandSumCheckPoly_ne_zero_of_bad_lookup
#print axioms Logup.grandSumCheckPoly_eq_zero_of_good_lookup
