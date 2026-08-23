/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SoundnessConverse

/-!
# The adversarial-multiplicity cleared grand-sum polynomial (issue #13, obligation 2c)

The soundness anchor of the `hOuter@midLanguage` blueprint, in the form the malicious-prover
analysis actually needs: the prover commits its multiplicity oracle at round 0, **before** the
round-1 challenge — so the relevant cleared polynomial is `clearedGrandSumPoly oStmt mult`
(residue at each value `a` = multiplicity mass on the table fiber of `a` minus the column count).

* `eval_clearedGrandSumPoly` — evaluation pushed through the sum/product;
* `clearedGrandSumPoly_ne_zero_of_bad_lookup` — **for every adversarial `mult`**, a bad lookup
  forces the polynomial nonzero: at a column-only value `a₀`
  (`bad_lookup_exists_column_only_value`) the table fiber is empty, so the residue is
  `−lookupMultiplicityCount a₀ ≠ 0` regardless of the committed multiplicity. The
  multiplicity-independent generalization of `grandSumCheckPoly_ne_zero_of_bad_lookup`, by the
  same residue-at-`−a₀` evaluation.

Hence the round-1 RBR flip of the claim-based state function is a genuine Schwartz–Zippel event
against a polynomial fixed at round 0 and nonzero for bad inputs. Axiom-clean.
-/

open Polynomial
open scoped BigOperators

namespace Logup

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n M : ℕ}

/-- **The adversarial-multiplicity cleared grand-sum polynomial.** The cleared form of the
prover-side rational identity `∑_u mult(u)/(X + t(u)) − ∑ columns 1/(X + c)`: at each value `a`,
the residue is the multiplicity mass on the table fiber of `a` minus the column count of `a`. -/
noncomputable def clearedGrandSumPoly (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) : Polynomial F :=
  ∑ a : F,
    Polynomial.C
      ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
          (fun u => evalOnHypercube (tableOracle oStmt) u = a),
            evalOnHypercube mult u)
        - (lookupMultiplicityCount oStmt a : F)) *
      ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b)

/-- Evaluation of `clearedGrandSumPoly`, pushed through the sum/product. -/
theorem eval_clearedGrandSumPoly (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) (v : F) :
    (clearedGrandSumPoly oStmt mult).eval v =
      ∑ a : F,
        ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
            (fun u => evalOnHypercube (tableOracle oStmt) u = a),
              evalOnHypercube mult u)
          - (lookupMultiplicityCount oStmt a : F)) *
          ∏ b ∈ Finset.univ.erase a, (v + b) := by
  unfold clearedGrandSumPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl (fun b _ => ?_)
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- **Soundness anchor, adversarial-multiplicity form (obligation 2c-ii).** A bad lookup forces
the cleared grand-sum polynomial to be nonzero for EVERY multiplicity oracle the prover may
commit: at a column-only value `a₀` the multiplicity side has no pole (the table fiber is
empty), so the residue is `−lookupMultiplicityCount a₀ ≠ 0` regardless of `mult`. The
multiplicity-independent generalization of `grandSumCheckPoly_ne_zero_of_bad_lookup`. -/
theorem clearedGrandSumPoly_ne_zero_of_bad_lookup
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    clearedGrandSumPoly oStmt mult ≠ 0 := by
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  intro hzero
  have heval : (clearedGrandSumPoly oStmt mult).eval (-a₀) = 0 := by rw [hzero]; simp
  rw [eval_clearedGrandSumPoly] at heval
  -- all `a ≠ a₀` summands vanish: their products contain the factor `(-a₀ + a₀) = 0`
  have hterms : ∀ a ∈ (Finset.univ : Finset F), a ≠ a₀ →
      ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
          (fun u => evalOnHypercube (tableOracle oStmt) u = a),
            evalOnHypercube mult u)
        - (lookupMultiplicityCount oStmt a : F)) *
        ∏ b ∈ Finset.univ.erase a, (-a₀ + b) = 0 := by
    intro a _ hne
    have hzero' : (∏ b ∈ Finset.univ.erase a, (-a₀ + b)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ a₀⟩) ?_
      ring
    rw [hzero', mul_zero]
  rw [Finset.sum_eq_single a₀ hterms (fun habs => absurd (Finset.mem_univ a₀) habs)] at heval
  -- the table fiber of the column-only value is empty, so the mult mass is the empty sum
  have hfiber : (Finset.univ : Finset (Hypercube n)).filter
      (fun u => evalOnHypercube (tableOracle oStmt) u = a₀) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro u _ hu
    have hcard : 0 < tableMultiplicityCount oStmt a₀ := by
      unfold tableMultiplicityCount
      rw [Finset.card_pos]
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
    omega
  rw [hfiber, Finset.sum_empty, zero_sub, neg_mul, neg_eq_zero] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook hc
  · rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, hb, hb0⟩ := hprod
    rw [Finset.mem_erase] at hb
    exact hb.1 (by linear_combination hb0)

/-- The cleared grand-sum polynomial over a finite value set `V` (the actual pole locations):
clearing the prover-side rational identity over `∏_{a∈V}(X+a)` instead of all of `F`. Its degree
is `≤ |V| − 1`, which for `V` = table ∪ column values gives the paper budget `(M+1)·2ⁿ − 1`. -/
noncomputable def clearedGrandSumPolyOn (V : Finset F) (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) : Polynomial F :=
  ∑ a ∈ V,
    Polynomial.C
      ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
          (fun u => evalOnHypercube (tableOracle oStmt) u = a),
            evalOnHypercube mult u)
        - (lookupMultiplicityCount oStmt a : F)) *
      ∏ b ∈ V.erase a, (Polynomial.X + Polynomial.C b)

/-- Degree bound: the `V`-cleared polynomial has degree `≤ |V| − 1` (each summand is a constant
times a product of `|V| − 1` monic linear factors). For `V` = table ∪ column values this is the
paper budget `(M+1)·2ⁿ − 1`. -/
theorem natDegree_clearedGrandSumPolyOn_le (V : Finset F)
    (oStmt : ∀ i, OStmtIn F n M i) (mult : MultilinearOracle F n) :
    (clearedGrandSumPolyOn V oStmt mult).natDegree ≤ V.card - 1 := by
  unfold clearedGrandSumPolyOn
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun a ha => ?_)
  calc (Polynomial.C
        ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
            (fun u => evalOnHypercube (tableOracle oStmt) u = a),
              evalOnHypercube mult u)
          - (lookupMultiplicityCount oStmt a : F)) *
        ∏ b ∈ V.erase a, (Polynomial.X + Polynomial.C b)).natDegree
      ≤ (Polynomial.C _).natDegree
          + (∏ b ∈ V.erase a, (Polynomial.X + Polynomial.C b)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + ∑ b ∈ V.erase a, (Polynomial.X + Polynomial.C b).natDegree :=
        Nat.add_le_add (le_of_eq (Polynomial.natDegree_C _)) (Polynomial.natDegree_prod_le _ _)
    _ = ∑ b ∈ V.erase a, 1 := by
        rw [zero_add]
        exact Finset.sum_congr rfl (fun b _ => Polynomial.natDegree_X_add_C b)
    _ = (V.erase a).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ = V.card - 1 := Finset.card_erase_of_mem ha

/-- **The `V`-cleared soundness anchor.** For a bad lookup with the column-only value inside `V`
and `V` avoiding spurious cancellation (`-a₀` distinct from the other values' negations is
automatic), the `V`-cleared polynomial is nonzero for every adversarial multiplicity — by the
same residue evaluation at `−a₀` as the all-values version. -/
theorem clearedGrandSumPolyOn_ne_zero_of_bad_lookup (V : Finset F)
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hV : ∀ a₀ : F, lookupMultiplicityCount oStmt a₀ ≠ 0 →
      tableMultiplicityCount oStmt a₀ = 0 → a₀ ∈ V) :
    clearedGrandSumPolyOn V oStmt mult ≠ 0 := by
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  have ha₀V : a₀ ∈ V := hV a₀ (by omega) htab
  intro hzero
  have heval : (clearedGrandSumPolyOn V oStmt mult).eval (-a₀) = 0 := by rw [hzero]; simp
  unfold clearedGrandSumPolyOn at heval
  rw [Polynomial.eval_finset_sum] at heval
  have hterms : ∀ a ∈ V, a ≠ a₀ →
      (Polynomial.C
        ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
            (fun u => evalOnHypercube (tableOracle oStmt) u = a),
              evalOnHypercube mult u)
          - (lookupMultiplicityCount oStmt a : F)) *
        ∏ b ∈ V.erase a, (Polynomial.X + Polynomial.C b)).eval (-a₀) = 0 := by
    intro a _ hne
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have hzero' : (∏ b ∈ V.erase a, ((Polynomial.X + Polynomial.C b).eval (-a₀))) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, ha₀V⟩) ?_
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      ring
    rw [hzero', mul_zero]
  rw [Finset.sum_eq_single_of_mem a₀ ha₀V hterms] at heval
  have hfiber : (Finset.univ : Finset (Hypercube n)).filter
      (fun u => evalOnHypercube (tableOracle oStmt) u = a₀) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro u _ hu
    have hcard : 0 < tableMultiplicityCount oStmt a₀ := by
      unfold tableMultiplicityCount
      rw [Finset.card_pos]
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
    omega
  rw [Polynomial.eval_mul, Polynomial.eval_C, hfiber, Finset.sum_empty, zero_sub] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · rw [neg_eq_zero] at hc
    exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook hc
  · rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, hb, hb0⟩ := hprod
    rw [Finset.mem_erase] at hb
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hb0
    exact hb.1 (by linear_combination hb0)

/-- Generic clearing: a finite sum of fractions with nonvanishing denominators vanishes iff its
cleared numerator does. -/
theorem sum_div_eq_zero_iff_cleared (V : Finset F) (r : F → F) (x : F)
    (hden : ∀ a ∈ V, x + a ≠ 0) :
    (∑ a ∈ V, r a / (x + a)) = 0 ↔
      (∑ a ∈ V, r a * ∏ b ∈ V.erase a, (x + b)) = 0 := by
  classical
  have hprod : (∏ a ∈ V, (x + a)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hden
  constructor
  · intro h
    have hmul := congrArg (· * ∏ a ∈ V, (x + a)) h
    simp only [zero_mul] at hmul
    rw [Finset.sum_mul] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [← Finset.mul_prod_erase V _ ha]
    rw [div_mul_eq_mul_div, mul_comm (x + a) (∏ b ∈ V.erase a, (x + b)), ← mul_assoc,
      mul_div_assoc, div_self (hden a ha), mul_one]
  · intro h
    have key : (∑ a ∈ V, r a / (x + a)) * ∏ a ∈ V, (x + a) = 0 := by
      rw [Finset.sum_mul]
      rw [← h]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [← Finset.mul_prod_erase V _ ha]
      rw [div_mul_eq_mul_div, mul_comm (x + a) (∏ b ∈ V.erase a, (x + b)), ← mul_assoc,
        mul_div_assoc, div_self (hden a ha), mul_one]
    exact (mul_eq_zero.mp key).resolve_right hprod

/-- **The eval-clearing bridge.** At a pole-free point `x`, the value-indexed rational residue sum
vanishes iff the `V`-cleared grand-sum polynomial vanishes at `x`. -/
theorem residue_sum_eq_zero_iff_clearedGrandSumPolyOn_eval (V : Finset F)
    (oStmt : ∀ i, OStmtIn F n M i) (mult : MultilinearOracle F n) (x : F)
    (hden : ∀ a ∈ V, x + a ≠ 0) :
    (∑ a ∈ V,
        ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
            (fun u => evalOnHypercube (tableOracle oStmt) u = a),
              evalOnHypercube mult u)
          - (lookupMultiplicityCount oStmt a : F)) / (x + a)) = 0 ↔
      (clearedGrandSumPolyOn V oStmt mult).eval x = 0 := by
  rw [sum_div_eq_zero_iff_cleared V _ x hden]
  unfold clearedGrandSumPolyOn
  rw [Polynomial.eval_finset_sum]
  constructor <;> intro h <;> [skip; skip] <;>
  · rw [← h]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    refine congrArg _ (Finset.prod_congr rfl (fun b _ => ?_))
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

end Logup

#print axioms Logup.clearedGrandSumPoly_ne_zero_of_bad_lookup
#print axioms Logup.natDegree_clearedGrandSumPolyOn_le
#print axioms Logup.clearedGrandSumPolyOn_ne_zero_of_bad_lookup
#print axioms Logup.sum_div_eq_zero_iff_cleared
#print axioms Logup.residue_sum_eq_zero_iff_clearedGrandSumPolyOn_eval
