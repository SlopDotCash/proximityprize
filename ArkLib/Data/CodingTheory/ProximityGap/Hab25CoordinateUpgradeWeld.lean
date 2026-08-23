/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Production
import ArkLib.ToMathlib.CoordinateKillBudget

/-!
# The CoordinateUpgrade weld: Claim 5.10 from witness-rich factor assignments (#302, R2)

`CoordinateUpgrade` — the single named open input of the Step-7 candidate production
(BCIKS20 Claim 5.10's output) — is here PROVEN from per-coordinate **witness-rich factor
assignment** data, with **no Claim A.2 `Λ`-weight recursion anywhere**:

* `foldSectionAt` — the fold curve at a coordinate as a `Z`-polynomial
  `w_t(Z) = ∑ⱼ u_j(t)·Zʲ` of degree `≤ L − 1`, with `w_t(γ) = ∑ⱼ γʲ•u_j(t)`;
* **`coordinateUpgrade_of_assigned_factor_rich`** — if at each chosen coordinate every cell
  scalar's decode value roots in an assigned irreducible fiber factor carrying more than
  `B + deg_Y·(L−1)` witnessed fold agreements, then `CoordinateUpgrade` holds: the
  per-factor kill (`ArkLib.FactorKill.fiber_root_eq_section_of_irreducible_of_many_agreements`)
  forces each assigned factor to be `c·(Y − w_t(Z))`, whose unique fiber root at EVERY scalar
  is the fold value — the witness-set-majority caveat is removed;
* **`global_branch_of_assigned_factor_rich`** — the full composition: the same data plus the
  cell surface and the count `|E| > B_R + deg_Y R·(L−1)` produce the **global branch**
  `(Y − C pHat) ∣ R` outright, through the (landed) `global_branch_of_coordinate_upgrade`.

## Status of the #302 critical path after this file

The open core of #302 moves from `CoordinateUpgrade` (Claim 5.10, previously thought to need
the #138/#139 `Λ`-weight kernel) to the strictly narrower **assignment coherence**: at each
rich coordinate, each cell scalar's decode value at that coordinate roots in a fiber factor
carrying `> B + deg_Y·(L−1)` witnessed agreements.  For the *witnessed* scalars this is
pigeonhole (`ArkLib.FactorKill.exists_witness_rich_factor` supplies a rich factor
unconditionally); the genuine residual is only the `≤ M` *unwitnessed* scalars per
coordinate, for which the paper invokes the global single-branch capture (all decodes are
fibers of ONE branch — the in-tree `GSPerScalarCapture`/section-factor lane), NOT the weight
recursion.  The factor coefficient budgets are supplied by divisor inheritance from the
sloped interpolant (`ArkLib.FactorKill.coeff_budget_of_dvd` + `GSInterpolantSloped`), so no
term of the budget chain escapes into Claim A.2.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, Claims 5.9–5.11, Appendix A.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-! ## The fold section at a coordinate -/

/-- The fold curve at a coordinate, as a `Z`-polynomial: `w_t(Z) = ∑ⱼ u_j(t)·Zʲ`. -/
noncomputable def foldSectionAt {n L : ℕ} (u : WordStack F₀ (Fin L) (Fin n)) (t : Fin n) :
    F₀[X] :=
  ∑ j : Fin L, Polynomial.C (u j t) * Polynomial.X ^ (j : ℕ)

/-- The fold section evaluates to the curve-fold value: `w_t(γ) = ∑ⱼ γʲ•u_j(t)`. -/
lemma foldSectionAt_eval {n L : ℕ} (u : WordStack F₀ (Fin L) (Fin n)) (t : Fin n)
    (γ : F₀) :
    (foldSectionAt u t).eval γ = ∑ j : Fin L, γ ^ (j : ℕ) • u j t := by
  rw [foldSectionAt, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    smul_eq_mul, mul_comm]

/-- The fold section has degree `≤ L − 1`. -/
lemma foldSectionAt_natDegree_le {n L : ℕ} (u : WordStack F₀ (Fin L) (Fin n)) (t : Fin n) :
    (foldSectionAt u t).natDegree ≤ L - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_X_pow_le _) ?_
  have := j.isLt
  omega

/-! ## The weld: CoordinateUpgrade from witness-rich factor assignments -/

/-- **Claim 5.10 from witness-rich factor assignments — no `Λ`-weight recursion.**
If at each chosen coordinate `t ∈ T` every cell scalar `γ`'s decode value
`(P γ).eval (domain t)` roots in an assigned irreducible fiber factor `Hf t (assign t γ)`
with flat coefficient budget `B` carrying more than `B + deg_Y·(L−1)` witnessed fold
agreements, then `CoordinateUpgrade` holds: each assigned factor is forced to be
`c·(Y − w_t(Z))`, so its unique fiber root at EVERY scalar — witnessed or not — is the
fold value. -/
theorem coordinateUpgrade_of_assigned_factor_rich {n L : ℕ}
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (E : Finset F₀) (P : F₀ → F₀[X]) (T : Finset (Fin n))
    {ι : Type} (Hf : Fin n → ι → F₀[X][Y]) {B : ℕ}
    (hirr : ∀ t ∈ T, ∀ i : ι, Irreducible (Hf t i))
    (hB : ∀ t ∈ T, ∀ (i : ι) (k : ℕ), ((Hf t i).coeff k).natDegree ≤ B)
    (assign : Fin n → F₀ → ι) (S : Fin n → ι → Finset F₀)
    (hroot : ∀ t ∈ T, ∀ γ ∈ E,
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom γ)).eval
        ((P γ).eval (domain t)) = 0)
    (hrich : ∀ t ∈ T, ∀ γ ∈ E,
      B + (Hf t (assign t γ)).natDegree * (L - 1) < (S t (assign t γ)).card)
    (hwit : ∀ t ∈ T, ∀ γ ∈ E, ∀ ζ ∈ S t (assign t γ),
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom ζ)).eval
        ((foldSectionAt u t).eval ζ) = 0) :
    CoordinateUpgrade domain u E P T := by
  intro γ hγ t ht
  rw [← foldSectionAt_eval]
  exact ArkLib.FactorKill.fiber_root_eq_section_of_irreducible_of_many_agreements
    (hirr t ht _) (hB t ht _) (foldSectionAt_natDegree_le u t)
    (S t (assign t γ)) (hrich t ht γ hγ) (hwit t ht γ hγ)
    γ ((P γ).eval (domain t)) (hroot t ht γ hγ)

variable [Fintype F₀] [DecidableEq F₀]

/-- **The full composition: the global branch from witness-rich factor assignments.**
The assignment data above, plus the cell surface and the count
`|E| > B_R + deg_Y R·(L−1)`, produce the global branch `(Y − C pHat) ∣ R` outright — the
exact input of `pinning_of_global_branch`, with Claim 5.10 discharged budget-only. -/
theorem global_branch_of_assigned_factor_rich {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {BR : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR)
    (E : Finset F₀) (P : F₀ → F₀[X]) (T : Finset (Fin n)) (hT : T.card = k)
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    {ι : Type} (Hf : Fin n → ι → F₀[X][Y]) {B : ℕ}
    (hirr : ∀ t ∈ T, ∀ i : ι, Irreducible (Hf t i))
    (hB : ∀ t ∈ T, ∀ (i : ι) (k' : ℕ), ((Hf t i).coeff k').natDegree ≤ B)
    (assign : Fin n → F₀ → ι) (S : Fin n → ι → Finset F₀)
    (hroot : ∀ t ∈ T, ∀ γ ∈ E,
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom γ)).eval
        ((P γ).eval (domain t)) = 0)
    (hrich : ∀ t ∈ T, ∀ γ ∈ E,
      B + (Hf t (assign t γ)).natDegree * (L - 1) < (S t (assign t γ)).card)
    (hwit : ∀ t ∈ T, ∀ γ ∈ E, ∀ ζ ∈ S t (assign t γ),
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom ζ)).eval
        ((foldSectionAt u t).eval ζ) = 0)
    (hbig : BR + R.natDegree * (L - 1) < E.card) :
    (Polynomial.X - Polynomial.C
        (branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j))) ∣ R :=
  global_branch_of_coordinate_upgrade hk hL R hRB E P T hT hdeg hdvdP
    (coordinateUpgrade_of_assigned_factor_rich E P T Hf hirr hB assign S
      hroot hrich hwit) hbig

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms foldSectionAt_eval
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms foldSectionAt_natDegree_le
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms coordinateUpgrade_of_assigned_factor_rich
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms global_branch_of_assigned_factor_rich
