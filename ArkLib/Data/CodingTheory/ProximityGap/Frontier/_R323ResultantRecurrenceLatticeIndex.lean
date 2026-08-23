/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS2PatternAnnihilatorResultant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# ROUND 323 (#466, Fable session 2026-07-09): THE DETERMINANT IDENTIFICATION —
  recurrence-lattice index = |cyclotomic resultant|, unconditionally

R321 (`_R321DyadicSaturationBridge.lean`) proved the abstract dyadic saturation statement
*conditionally on the standard determinant/resultant identification*: that for a relation
polynomial `f` in `ℤ[x]/(x^m+1)` (`m = 2^k`), the index of the recurrence lattice
`f·ℤ[x]/(x^m+1)` equals `|Res(x^m+1, f)|`.  R315 produced the resultant annihilator but not
the lattice-index reading.  This brick DISCHARGES the identification, axiom-clean:

* **`nat_card_quot_span_singleton`** — for any domain `S` free and finite over `ℤ` and
  `r ≠ 0`, `#(S ⧸ (r)) = |Norm_ℤ(r)|`.  This is Mathlib's `Ideal.absNorm_span_singleton`
  *re-proved without the `IsDedekindDomain` hypothesis* (which `ℤ[x]/(x^m+1)` satisfies but
  which Mathlib cannot see without the cyclotomic-ring-of-integers transfer): we route
  directly through `Submodule.natAbs_det_equiv` and `Ideal.basisSpanSingleton`.
* **`norm_toQ`** — the ℤ-norm on `AdjoinRoot (x^m+1 : ℤ[X])` casts to the ℚ-norm on
  `AdjoinRoot (x^m+1 : ℚ[X])` (matching power bases; `modByMonic` commutes with `map`).
* **`norm_mk_eq_patternResultant`** — the exact identity
  `Norm_ℤ(P mod x^m+1) = Res_{m,deg P}(x^m+1, P)`, on the nose (no sign): both sides equal
  `∏ P(ζ)` over the primitive `2m`-th roots of unity in `AlgebraicClosure ℚ`, via
  `Algebra.norm_eq_prod_embeddings` (embeddings ↔ roots, `PowerBasis.liftEquiv'`) on the
  left and `Polynomial.resultant_eq_prod_eval` on the right.
* **`nat_card_quot_span_mk_eq_patternResultant`** — the target: for `¬ (x^m+1) ∣ P`,
  `#(ℤ[x]/(x^m+1) ⧸ (P)) = |Res(x^m+1, P)|.natAbs`.

**Consequence for the prize route** (weld of R315 × R321): every realized kernel relation
`d` with `p ∣ N(d) = Res(x^m+1, P_d)` now has a *machine-checked lattice meaning*: the
recurrence lattice `P_d·ℤ[x]/(x^m+1)` has index exactly `|N(d)|` in the full ring, so the
R321 census fact `|N(d)|/p ∈ {2,4,8}` says the evaluation kernel sits above the recurrence
lattice with dyadic quotient — no "standard identification" hypothesis left.  The remaining
open input for the R321 dichotomy is only the uniform principal-lattice return-probability
bound (genuinely open, dossier v3 §6).

Issue #466, round r323.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace ArkLib.ProximityGap.Frontier.R323ResultantRecurrenceLatticeIndex

open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant

/-! ## §1  Cardinality of a principal quotient = |norm|, Dedekind-free -/

/-- `Ideal.absNorm_span_singleton` without `IsDedekindDomain`: for a domain `S` free and
finite as a `ℤ`-module and `r ≠ 0`, the quotient `S ⧸ (r)` has cardinality `|Norm_ℤ(r)|`. -/
theorem nat_card_quot_span_singleton {S : Type*} [CommRing S] [IsDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] {r : S} (hr : r ≠ 0) :
    Nat.card (S ⧸ Ideal.span ({r} : Set S)) = (Algebra.norm ℤ r).natAbs := by
  classical
  let b := Module.Free.chooseBasis ℤ S
  have h := Submodule.natAbs_det_equiv ((Ideal.span ({r} : Set S)).restrictScalars ℤ)
    (b.equiv (Ideal.basisSpanSingleton b hr) (Equiv.refl _))
  rw [Algebra.norm_apply]
  refine ((show Nat.card (S ⧸ Ideal.span ({r} : Set S))
      = Nat.card (S ⧸ (Ideal.span ({r} : Set S)).restrictScalars ℤ) from rfl).trans
    h.symm).trans ?_
  congr 1
  congr 1
  refine b.ext fun i => ?_
  show ((b.equiv (Ideal.basisSpanSingleton b hr) (Equiv.refl _)) (b i) : S) = r * b i
  rw [Module.Basis.equiv_apply]
  exact Ideal.basisSpanSingleton_apply b hr i

/-! ## §2  The two power bases and the cast homomorphism -/

/-- The rational pattern polynomial `x^{2^k} + 1` over `ℚ`. -/
noncomputable def fq (k : ℕ) : ℚ[X] := (fpoly (2 ^ k)).map (Int.castRingHom ℚ)

theorem fz_monic (k : ℕ) : (fpoly (2 ^ k)).Monic :=
  fpoly_monic (pow_pos two_pos k)

theorem fq_monic (k : ℕ) : (fq k).Monic :=
  (fz_monic k).map _

theorem fz_natDegree (k : ℕ) : (fpoly (2 ^ k)).natDegree = 2 ^ k :=
  fpoly_natDegree (pow_pos two_pos k)

theorem fq_natDegree (k : ℕ) : (fq k).natDegree = 2 ^ k := by
  rw [fq, natDegree_map_eq_of_injective Int.cast_injective, fz_natDegree]

theorem deg_eq (k : ℕ) : (fq k).natDegree = (fpoly (2 ^ k)).natDegree := by
  rw [fq_natDegree, fz_natDegree]

theorem fq_irreducible (k : ℕ) : Irreducible (fq k) := by
  rw [fq, fpoly_map_rat_eq_cyclotomic k]
  exact cyclotomic.irreducible_rat (by positivity)

theorem fz_irreducible (k : ℕ) : Irreducible (fpoly (2 ^ k)) :=
  Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom ℚ) _
    (fz_monic k) (fq_irreducible k)

theorem fz_prime (k : ℕ) : Prime (fpoly (2 ^ k)) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (fz_irreducible k)

/-- The cast ring homomorphism `ℤ[x]/(x^m+1) →+* ℚ[x]/(x^m+1)` sending `root ↦ root`. -/
noncomputable def toQ (k : ℕ) : AdjoinRoot (fpoly (2 ^ k)) →+* AdjoinRoot (fq k) :=
  AdjoinRoot.lift ((AdjoinRoot.of (fq k)).comp (Int.castRingHom ℚ)) (AdjoinRoot.root (fq k))
    (by rw [← Polynomial.eval₂_map]; exact AdjoinRoot.eval₂_root (fq k))

theorem toQ_mk (k : ℕ) (Q : ℤ[X]) :
    toQ k (AdjoinRoot.mk (fpoly (2 ^ k)) Q)
      = AdjoinRoot.mk (fq k) (Q.map (Int.castRingHom ℚ)) := by
  rw [toQ, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
    ← aeval_def, AdjoinRoot.aeval_eq]

theorem toQ_root (k : ℕ) :
    toQ k (AdjoinRoot.root (fpoly (2 ^ k))) = AdjoinRoot.root (fq k) :=
  AdjoinRoot.lift_root _

/-- Basis coordinates commute with the cast: the `ℚ`-power-basis coordinates of `toQ t` are
the casts of the `ℤ`-power-basis coordinates of `t`. -/
theorem repr_toQ (k : ℕ) (t : AdjoinRoot (fpoly (2 ^ k))) (i : Fin (fq k).natDegree) :
    (AdjoinRoot.powerBasis' (fq_monic k)).basis.repr (toQ k t) i
      = ((AdjoinRoot.powerBasis' (fz_monic k)).basis.repr t (Fin.cast (deg_eq k) i) : ℤ) := by
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective t
  rw [toQ_mk]
  show ((AdjoinRoot.modByMonicHom (fq_monic k))
      (AdjoinRoot.mk (fq k) (Q.map (Int.castRingHom ℚ)))).coeff (i : ℕ)
    = (((AdjoinRoot.modByMonicHom (fz_monic k))
      (AdjoinRoot.mk (fpoly (2 ^ k)) Q)).coeff ((Fin.cast (deg_eq k) i : Fin _) : ℕ) : ℤ)
  rw [AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk]
  have hmod : Q.map (Int.castRingHom ℚ) %ₘ fq k
      = (Q %ₘ fpoly (2 ^ k)).map (Int.castRingHom ℚ) := by
    rw [fq, ← Polynomial.map_modByMonic _ (fz_monic k)]
  rw [hmod, Polynomial.coeff_map]
  simp

/-- The `ℤ`-norm casts to the `ℚ`-norm along `toQ`. -/
theorem norm_toQ (k : ℕ) (t : AdjoinRoot (fpoly (2 ^ k))) :
    ((Algebra.norm ℤ t : ℤ) : ℚ) = Algebra.norm ℚ (toQ k t) := by
  rw [Algebra.norm_eq_matrix_det
      ((AdjoinRoot.powerBasis' (fz_monic k)).basis.reindex (finCongr (deg_eq k)).symm) t,
    Algebra.norm_eq_matrix_det (AdjoinRoot.powerBasis' (fq_monic k)).basis (toQ k t)]
  have hM : Algebra.leftMulMatrix (AdjoinRoot.powerBasis' (fq_monic k)).basis (toQ k t)
      = (Algebra.leftMulMatrix
          ((AdjoinRoot.powerBasis' (fz_monic k)).basis.reindex (finCongr (deg_eq k)).symm)
          t).map (Int.cast : ℤ → ℚ) := by
    ext i j
    rw [Matrix.map_apply,
      Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      Module.Basis.reindex_apply, Module.Basis.repr_reindex]
    have hbj : toQ k ((AdjoinRoot.powerBasis' (fz_monic k)).basis
          ((finCongr (deg_eq k)).symm.symm j))
        = (AdjoinRoot.powerBasis' (fq_monic k)).basis j := by
      rw [(AdjoinRoot.powerBasis' (fz_monic k)).basis_eq_pow,
        (AdjoinRoot.powerBasis' (fq_monic k)).basis_eq_pow, map_pow]
      simp [toQ_root]
    rw [← hbj, ← map_mul, Finsupp.mapDomain_equiv_apply]
    exact repr_toQ k _ i
  rw [hM]
  have hdet := RingHom.map_det (Int.castRingHom ℚ)
    (Algebra.leftMulMatrix
      ((AdjoinRoot.powerBasis' (fz_monic k)).basis.reindex (finCongr (deg_eq k)).symm) t)
  simpa [RingHom.mapMatrix_apply] using hdet

/-! ## §3  Norm over ℚ = product over the roots -/

/-- The `ℚ`-norm of `P(root)` in `ℚ[x]/(x^m+1)` equals the product of `P` over the roots of
`x^m+1` in the algebraic closure. -/
theorem normQ_aeval_eq_prod (k : ℕ) (PQ : ℚ[X]) :
    algebraMap ℚ (AlgebraicClosure ℚ)
        (Algebra.norm ℚ (aeval (AdjoinRoot.root (fq k)) PQ))
      = (((fq k).aroots (AlgebraicClosure ℚ)).map
          (fun y => (PQ.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval y)).prod := by
  classical
  haveI : Fact (Irreducible (fq k)) := ⟨fq_irreducible k⟩
  haveI : FiniteDimensional ℚ (AdjoinRoot (fq k)) := (fq_monic k).finite_adjoinRoot
  set pb := AdjoinRoot.powerBasis' (fq_monic k) with hpb
  have hgen : pb.gen = AdjoinRoot.root (fq k) := rfl
  have hmin : minpoly ℚ pb.gen = fq k :=
    (minpoly.eq_of_irreducible_of_monic (fq_irreducible k)
      (show aeval pb.gen (fq k) = 0 from
        (AdjoinRoot.aeval_eq (fq k)).trans (by rw [AdjoinRoot.mk_self])) (fq_monic k)).symm
  rw [Algebra.norm_eq_prod_embeddings]
  have hsep : (fq k).Separable := (fq_irreducible k).separable
  have hnodup : ((minpoly ℚ pb.gen).aroots (AlgebraicClosure ℚ)).Nodup := by
    rw [hmin, Polynomial.aroots_def]
    exact Polynomial.nodup_roots hsep.map
  have hstep : (∏ σ : AdjoinRoot (fq k) →ₐ[ℚ] AlgebraicClosure ℚ,
        σ (aeval (AdjoinRoot.root (fq k)) PQ))
      = ∏ y : ((minpoly ℚ pb.gen).aroots (AlgebraicClosure ℚ)).toFinset,
          (PQ.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval y.1 := by
    refine Fintype.prod_equiv
      (pb.liftEquiv'.trans (Equiv.subtypeEquivRight fun y =>
        (Multiset.mem_toFinset (a := y)).symm)) _ _ fun σ => ?_
    rw [← hgen, ← Polynomial.aeval_algHom_apply, ← eval_map_algebraMap]
    rfl
  have hval : ((minpoly ℚ pb.gen).aroots (AlgebraicClosure ℚ)).toFinset.val
      = (minpoly ℚ pb.gen).aroots (AlgebraicClosure ℚ) := by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  refine hstep.trans ((Finset.prod_coe_sort _
    (fun a => (PQ.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval a)).trans ?_)
  rw [Finset.prod_eq_multiset_prod, hval, hmin]

/-! ## §4  The resultant as the same product -/

theorem patternResultant_cast_eq_prod (k : ℕ) (P : ℤ[X]) :
    (algebraMap ℚ (AlgebraicClosure ℚ)) ((patternResultant (2 ^ k) P : ℤ) : ℚ)
      = (((fq k).aroots (AlgebraicClosure ℚ)).map
          (fun y => ((P.map (Int.castRingHom ℚ)).map
              (algebraMap ℚ (AlgebraicClosure ℚ))).eval y)).prod := by
  classical
  set E := AlgebraicClosure ℚ
  set castE : ℤ →+* E := (algebraMap ℚ E).comp (Int.castRingHom ℚ) with hcastE
  have hcast : resultant ((fpoly (2 ^ k)).map castE) (P.map castE) (2 ^ k) P.natDegree
      = castE (patternResultant (2 ^ k) P) := by
    simp only [patternResultant]
    exact resultant_map_map (fpoly (2 ^ k)) P (2 ^ k) P.natDegree castE
  have hfE : ((fpoly (2 ^ k)).map castE) = (fq k).map (algebraMap ℚ E) := by
    rw [fq, Polynomial.map_map]
  have hmonE : ((fpoly (2 ^ k)).map castE).Monic := (fz_monic k).map _
  have hdegE : ((fpoly (2 ^ k)).map castE).natDegree = 2 ^ k := by
    rw [(fz_monic k).natDegree_map, fz_natDegree]
  have hdegP : (P.map castE).natDegree ≤ P.natDegree := natDegree_map_le
  have hsplits : ((fpoly (2 ^ k)).map castE).Splits := IsAlgClosed.splits _
  have hprod := resultant_eq_prod_eval ((fpoly (2 ^ k)).map castE) (P.map castE)
    P.natDegree hdegP hsplits
  rw [hdegE] at hprod
  have hLHS : (algebraMap ℚ E) ((patternResultant (2 ^ k) P : ℤ) : ℚ)
      = castE (patternResultant (2 ^ k) P) := rfl
  rw [hLHS, ← hcast, hprod, hmonE.leadingCoeff, one_pow, one_mul]
  have hroots : ((fpoly (2 ^ k)).map castE).roots = (fq k).aroots E := by
    rw [hfE, aroots_def]
  rw [hroots]
  congr 1
  refine Multiset.map_congr rfl fun y _ => ?_
  rw [Polynomial.map_map, ← hcastE]

/-! ## §5  The determinant identification -/

/-- **The exact norm–resultant identity** (no sign):
`Norm_ℤ(P mod x^{2^k}+1) = Res(x^{2^k}+1, P)`. -/
theorem norm_mk_eq_patternResultant (k : ℕ) (P : ℤ[X]) :
    Algebra.norm ℤ (AdjoinRoot.mk (fpoly (2 ^ k)) P) = patternResultant (2 ^ k) P := by
  classical
  have hinj : Function.Injective
      (((algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ)) : ℤ →+* _) :=
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp Int.cast_injective
  apply hinj
  show algebraMap ℚ (AlgebraicClosure ℚ)
      ((Algebra.norm ℤ (AdjoinRoot.mk (fpoly (2 ^ k)) P) : ℤ) : ℚ)
    = algebraMap ℚ (AlgebraicClosure ℚ) ((patternResultant (2 ^ k) P : ℤ) : ℚ)
  rw [norm_toQ, toQ_mk, ← AdjoinRoot.aeval_eq, normQ_aeval_eq_prod,
    patternResultant_cast_eq_prod]

/-- **The determinant identification (R321's named input), discharged.**
For `P` not divisible by `x^{2^k}+1`, the recurrence lattice `P·ℤ[x]/(x^{2^k}+1)` has index
exactly `|Res(x^{2^k}+1, P)|` in `ℤ[x]/(x^{2^k}+1)`. -/
theorem nat_card_quot_span_mk_eq_patternResultant (k : ℕ) (P : ℤ[X])
    (hP : ¬ fpoly (2 ^ k) ∣ P) :
    Nat.card (AdjoinRoot (fpoly (2 ^ k)) ⧸
        Ideal.span ({AdjoinRoot.mk (fpoly (2 ^ k)) P} : Set (AdjoinRoot (fpoly (2 ^ k)))))
      = (patternResultant (2 ^ k) P).natAbs := by
  haveI : IsDomain (AdjoinRoot (fpoly (2 ^ k))) := AdjoinRoot.isDomain_of_prime (fz_prime k)
  haveI : Module.Free ℤ (AdjoinRoot (fpoly (2 ^ k))) := (fz_monic k).free_adjoinRoot
  haveI : Module.Finite ℤ (AdjoinRoot (fpoly (2 ^ k))) := (fz_monic k).finite_adjoinRoot
  have hr : AdjoinRoot.mk (fpoly (2 ^ k)) P ≠ 0 := by
    rw [Ne, AdjoinRoot.mk_eq_zero]
    exact hP
  rw [nat_card_quot_span_singleton hr]
  exact congrArg Int.natAbs (norm_mk_eq_patternResultant k P)

#print axioms nat_card_quot_span_singleton
#print axioms norm_toQ
#print axioms normQ_aeval_eq_prod
#print axioms patternResultant_cast_eq_prod
#print axioms norm_mk_eq_patternResultant
#print axioms nat_card_quot_span_mk_eq_patternResultant

end ArkLib.ProximityGap.Frontier.R323ResultantRecurrenceLatticeIndex
