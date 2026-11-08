/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.OracleInterface

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import CompPoly.Data.MvPolynomial.Notation
import ArkLib.Data.MvPolynomial.Degrees
import ProximityPrize.Extensions.Data.MvPolynomial.SchwartzZippelCounting
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.IntegralDomain
-- import ArkLib.Data.MlPoly.Basic

/-!
  # Definitions and Instances for `OracleInterface`

  We define `OracleInterface`, which is a type class that augments a type with an oracle interface
  for that type. The interface specifies the type of queries, the type of responses, and the
  oracle's behavior for a given underlying element of the type.

  `OracleInterface` is used to restrict the verifier's access to the input oracle statements and the
  prover's messages in an interactive oracle reduction (see `Basic.lean`).

  We define `OracleInterface` instances for common types:

  - Univariate and multivariate polynomials. These instances turn polynomials into oracles for which
    one can query at a point, and the response is the evaluation of the polynomial on that point.

  - Vectors. This instance turns vectors into oracles for which one can query specific positions.
-/

universe u v w

open OracleComp OracleSpec OracleQuery

namespace OracleInterface

instance {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)]
    [h : ∀ i q, DecidableEq ((O i).Response q)] :
    ∀ q, DecidableEq ([v]ₒ q)
  | ⟨i, q⟩ => h i q

instance {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)]
    [h : ∀ i q, Fintype ((O i).Response q)] :
    ∀ q, Fintype ([v]ₒ q)
  | ⟨i, q⟩ => h i q

instance {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)]
    [h : ∀ i q, Inhabited ((O i).Response q)] :
    ∀ q, Inhabited ([v]ₒ q)
  | ⟨i, q⟩ => h i q

section Polynomial

open Polynomial MvPolynomial

variable (R : Type _) [CommSemiring R] (d : ℕ) (σ : Type*)

end Polynomial

section Vector

variable {n : ℕ} {α : Type*}

/- Vectors of the form `Fin n → α` can be accessed via queries on their indices. We no longer have
   this instance separately since it can be inferred from the instance for `Function`. -/
-- instance instOracleInterfaceForallFin :
--     OracleInterface (Fin n → α) := OracleInterface.instFunction

end Vector

end OracleInterface

section PolynomialDistance

-- Note: refactor these theorems and move them into the appropriate `(Mv)Polynomial` files

open Polynomial MvPolynomial OracleInterface Finset

variable {R : Type*} [CommRing R] {d : ℕ} [Fintype R] [DecidableEq R] [IsDomain R]

omit [Fintype R] [DecidableEq R] [IsDomain R] in
private lemma totalDegree_le_card_mul_of_degreeOf_le {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ R} (hp : ∀ i, p.degreeOf i ≤ d) :
    p.totalDegree ≤ Fintype.card σ * d := by
  classical
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le ?_
  intro m hm
  calc
    Finsupp.sum m (fun _ e => e) = ∑ i : σ, m i := by
      simp [Finsupp.sum_fintype]
    _ ≤ ∑ _i : σ, d := by
      exact Finset.sum_le_sum fun i _ =>
        le_trans (MvPolynomial.monomial_le_degreeOf i hm) (hp i)
    _ = Fintype.card σ * d := by
      simp [Finset.sum_const, mul_comm]

-- Note: golf this theorem
end PolynomialDistance
