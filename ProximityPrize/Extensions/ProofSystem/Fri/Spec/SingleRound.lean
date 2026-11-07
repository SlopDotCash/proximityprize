/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Fri.Spec.SingleRound

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.CodingTheory.Basic.RelativeDistance
import ProximityPrize.Extensions.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.Domain.CosetFftDomain.ToList
import ArkLib.Data.Domain.FftDomain.Subdomain
import ProximityPrize.Extensions.OracleReduction.Basic
import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.Append
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Linear
import CompPoly.Univariate.ToPoly.Impl
import CompPoly.Fields.Basic
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ToMathlib.Finset.Basic

/-!
# The FRI protocol

  We describe the FRI oracle reduction as a composition of many single rounds, and a final
  (zero-interaction) query round where the oracle verifier makes all queries to all received oracle
  codewords.

  This formalisation tries to encompass all of the generalisations of the FRI
  low-degree test covered in [FRI1216].

## References

* [Haböck, U., *A summary on the FRI low degree test*][FRI1216]

 -/

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset NNReal

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `i` the index of the current folding round.
-/

open Domain

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (domain_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (i : Fin k)
variable {ω : SmoothCosetFftDomain n F}


@[simp]
lemma finalOracleStatement_range_nonfinal {i : Fin (k + 1)} (q) :
    [FinalOracleStatement s ω]ₒ.Range ⟨⟨i.1, Nat.lt_succ_of_lt i.2⟩, q⟩ = F := by
  unfold OracleSpec.Range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query OracleInterface.Response
  unfold finalOracleStatementInterface
  simp [Nat.ne_of_lt i.2]

@[simp]
lemma finalOracleStatement_range_final (q) :
    [FinalOracleStatement s ω]ₒ.Range ⟨(Fin.last (k + 1)), q⟩ = CompPoly.CPolynomial F := by
  unfold OracleSpec.Range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query OracleInterface.Response
  unfold finalOracleStatementInterface
  simp

@[simp]
lemma finalOracleStatementInterface_query (j) :
    (finalOracleStatementInterface (ω := ω) s j).Query =
      if j = k + 1 then Unit else (ω.subdomain (∑ j' ∈ finRangeTo _ j.1, s j')).toFinset := by
  rfl

-- omit [Finite F] in
-- @[simp]
-- lemma domain_lem₂ :
--   [FinalOracleStatement D x s]ₒ.domain (Fin.last (k + 1)) = Unit := by
--   unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
--   unfold OracleInterface.Query
--   unfold instOracleInterfaceFinalOracleStatement
--   simp

namespace FoldPhase

-- /- Definition of the non-final folding rounds of the FRI protocol. -/

-- /- Folding total round consistency predicate, checking of two subsequent code words will pass
--    the round consistency at all points. -/
-- def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
--   [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : Fin (k + 1) → ℕ+}
--   (cond : (∑ i, (s i).1) ≤ n) {i : Fin (k + 1)} [DecidableEq F] {j : Fin i}
--     (f : OracleStatement D x s i j.castSucc)
--     (f' : OracleStatement D x s i j.succ)
--     (x₀ : F) : Prop :=
--   ∀ s₀ : evalDomain D x (∑ j' ∈ (List.take j.1 (List.finRange (k + 1))).toFinset, s j'),
--       let queries :
--           List (evalDomain D x
--             (∑ j' ∈ (List.take j.1 (List.finRange (k + 1))).toFinset, s j')) :=
--             List.map
--               (
--                 fun r =>
--                   ⟨
--                     _,
--                     CosetDomain.mul_root_of_unity
--                       D
--                       (Nat.le_sub_of_add_le (by nlinarith [cond, j.2, i.2]))
--                       s₀.2
--                       r.2
--                   ⟩
--               )
--               (Domain.rootsOfUnity D n s);
--       let pts := List.map (fun q => (q.1.1, f q)) queries;
--       let β := f' ⟨_, CosetDomain.pow_lift D x s s₀.2⟩;
--         RoundConsistency.roundConsistencyCheck x₀ pts β

-- /- Checks for the total Folding round consistency of all rounds up to the current one. -/
-- def statementConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
--   [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k s : ℕ} {i : Fin (k + 1)} [DecidableEq F]
--       (cond : (k + 1) * s ≤ n)
--       (stmt : Statement F i)
--       (ostmt : ∀ j, OracleStatement D x s i j) : Prop :=
--   ∀ j : Fin i,
--     let f  := ostmt j.castSucc;
--     let f' := ostmt j.succ;
--     let x₀  := stmt j;
--     roundConsistent cond f f' x₀

instance {i : Fin k} : ∀ j, Inhabited ((pSpec s (ω := ω) i).Challenge j) := by
  intro j
  letI : Inhabited F := ⟨0⟩
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 =>
        cases j1 using Fin.cases with
        | zero => simp at hj
        | succ j2 => exact j2.elim0
  subst h_j_eq_0
  simpa [pSpec, Challenge] using (inferInstance : Inhabited F)

end FoldPhase

namespace FinalFoldPhase

/- Definition of the final folding round of the FRI protocol. -/

-- /- Folding total round consistency predicate, for the final round. -/
-- def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
--   [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ}
--   (cond : (k + 1) * s ≤ n) [DecidableEq F]
--     (f : FinalOracleStatement D x s (Fin.last k).castSucc)
--     (f' : FinalOracleStatement D x s (Fin.last (k + 1)))
--     (x₀ : F) : Prop :=
--   let f : evalDomain D x (s * k) → F := by
--     unfold FinalOracleStatement at f
--     simp only [Fin.coe_castSucc, Fin.val_last, Nat.left_eq_add, one_ne_zero, ↓reduceIte] at f
--     exact f
--   let f' : F[X] := by
--     unfold FinalOracleStatement at f'
--     simp only [Fin.val_last, ↓reduceIte] at f'
--     exact f' ()
--   ∀ s₀ : evalDomain D x (s * k),
--       let queries :
--           List (evalDomain D x (s * k)) :=
--             List.map
--               (
--                 fun r =>
--                   ⟨
--                     _,
--                     CosetDomain.mul_root_of_unity
--                       D
--                       (Nat.le_sub_of_add_le
--                         (by
--                           rw [Nat.add_mul, one_mul, mul_comm] at cond
--                           exact cond
--                         )
--                       )
--                       s₀.2
--                       r.2
--                   ⟩
--               )
--               (Domain.rootsOfUnity D n s);
--       let pts := List.map (fun q => (q.1.1, f q)) queries;
--       let β := f'.eval (s₀.1.1 ^ (2 ^ s));
--         RoundConsistency.roundConsistencyCheck x₀ pts β

private theorem finalFold_bindcomp_heq {M1 M2 : Type} (hM : M1 = M2) {β1 β2 : Type}
    {f1 : M1 → ReaderM M1 β1} {f2 : M2 → ReaderM M2 β2} (hβ : β1 = β2) (hf : HEq f1 f2) :
    HEq ((read : ReaderM M1 M1) >>= f1) ((read : ReaderM M2 M2) >>= f2) := by
  subst hM; subst hβ; rw [heq_eq_eq] at hf; subst hf; rfl

private theorem finalFold_pure_heq {M1 M2 α1 α2 : Type} (hM : M1 = M2) (hα : α1 = α2)
    {a1 : α1} {a2 : α2} (ha : HEq a1 a2) :
    HEq (pure a1 : ReaderM M1 α1) (pure a2 : ReaderM M2 α2) := by
  subst hM; subst hα; rw [heq_eq_eq] at ha; subst ha; rfl

private theorem finalFold_oc_mk_heq {Q1 Q2 : Type} {m1 m2 : Type → Type}
    (sp1 : OracleSpec Q1) (im1 : QueryImpl sp1 m1) (sp2 : OracleSpec Q2) (im2 : QueryImpl sp2 m2)
    (hQ : Q1 = Q2) (hm : m1 = m2) (hsp : HEq sp1 sp2) (him : HEq im1 im2) :
    HEq (OracleContext.mk sp1 im1) (OracleContext.mk sp2 im2) := by
  subst hQ; subst hm; rw [heq_eq_eq] at hsp; subst hsp; rw [heq_eq_eq] at him; subst him; rfl

private theorem finalFold_query_cast {A B : Type} (h : A = B) (o : OracleInterface A) :
    HEq (cast (congrArg OracleInterface h) o).Query o.Query := by subst h; rw [cast_eq]

private theorem finalFold_toOC_cast {A B : Type} (h : A = B) (o : OracleInterface A) :
    HEq (cast (congrArg OracleInterface h) o).toOC o.toOC := by subst h; rw [cast_eq]

private theorem hfun_app {A1 A2 B1 B2 : Type} {f1 : A1 → B1} {f2 : A2 → B2} {a1 : A1} {a2 : A2}
    (hA : A1 = A2) (hB : B1 = B2) (hf : HEq f1 f2) (ha : HEq a1 a2) : HEq (f1 a1) (f2 a2) := by
  subst hA; subst hB; rw [heq_eq_eq] at hf ha; subst hf; subst ha; rfl

end FinalFoldPhase

namespace QueryRound

/- Definition of the query round of the FRI protocol. -/

/-  Parameter for the number of round consistency checks to be
    run by the query round. -/
variable (l : ℕ) [NeZero l]

/- Input/Output relations for the query round of the FRI protocol -/
instance : ∀ j, OracleInterface ((pSpec (ω := ω) l).Message j) := fun j ↦
  match j with
  | ⟨0, h⟩ => nomatch h

end QueryRound

end Spec

end Fri
