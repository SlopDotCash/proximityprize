/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.ToMathlib.MatchingExtractor

/-!
# Discharging the last two genuine §5 math data: `HasOrderAt` (obligation 4) and `hdvd_C`
  (obligation 1) from the in-tree **proven** multiplicity / divisibility structure.

Two bricks of the [BCIKS20] §5 / Appendix-A formalization still consumed a *hypothesis* whose
mathematical content is the Guruswami–Sudan order-`m` multiplicity of the interpolant on the close
codeword graph:

* `ArkLib.MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`
  (`ArkLib/ToMathlib/MatchingExtractor.lean`) consumes, for each agreement index `i`, the predicate
  `GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m` — *obligation 4*.

* `ArkLib.hdvd_top_of_dvd_C` (`ArkLib/ToMathlib/HdvdTop.lean`) consumes the structural divisibility
  `hdvd_C : (C H.leadingCoeff) ∣ R.coeff R.natDegree` in `(F[X])[X]` — *obligation 1*.

Both are here turned into **theorems** built on the in-tree *proven* facts, so they are no longer
hypotheses:

1. **`HasOrderAt` ⟸ root multiplicity (obligation 4).**  `GuruswamiSudan.HasOrderAt` unfolds to
   "every shifted coefficient of total degree `< m` vanishes".  This is exactly the **easy**
   direction of the multiplicity criterion, and it follows from the *proven* root-multiplicity lower
   bound `m ≤ rootMultiplicity Qz (ωs i) (Pz.eval (ωs i))` — the field-side datum produced
   in tree by `GuruswamiSudan.gsQ_multiplicity` / the `gapB_transport_mult` transport behind
   `Q_vanishes_on_close_codeword_graph`.  The conversion is the public, kernel-checked
   `GuruswamiSudan.rootMultiplicity_le_of_coeff_ne_zero` (its contrapositive), re-derived here
   standalone (the same inline step performed inside `GuruswamiSudan.dvd_property`).  No Johnson /
   `δ ≤ δ₀` side condition is needed for this datum.

2. **`hdvd_C` ⟸ the un-specialized GS-factor divisibility (obligation 1).**  The full
   `(C W) ∣ R.coeff R.natDegree` in `(F[X])[X]` (the strong "every Hasse–Taylor order at once" save,
   strictly stronger than the `i₁ = 0` line fact) is the leading-coefficient shadow of the
   un-specialized factorization `H_lift ∣ R`, where `H_lift = H.map (C)` is `H : F[X][Y]` embedded
   into `F[X][X][Y]` with leading coefficient `C H.leadingCoeff`.  Over the domain `(F[X])[X]`
   `leadingCoeff` is multiplicative, so a divisor's leading coefficient divides the dividend's
   (`leadingCoeff_dvd_of_dvd_lift`); applied to `H_lift ∣ R` this gives `hdvd_C` (the leading
   `Y`-coefficient of `H_lift` is `C H.leadingCoeff`).  This converts the bare `hdvd_C` *hypothesis*
   into a consequence of the cleaner un-specialized GS-factor relation — the genuine §5/App-A
   multiplicity structure.

   Separately, the **value projection** `W ∣ (R.coeff R.natDegree).eval (C x₀)` (the `i₁ = 0` line
   fact / `hdvd_top_zero` input) is discharged **with no residual at all** from the *proven*
   `Hypotheses x₀ R H` multiplicity/separability structure
   (`leadingCoeff_dvd_evalX_coeff_natDegree`) — see `hdvd_C_value_of_hypotheses`.

The Johnson-radius regime condition `δ ≤ δ₀` is *not* introduced by this file: it is the genuine
side condition under which the in-tree producers (`gsQ_multiplicity`, `Q_vanishes_*`,
`gs_dvd_property`) establish the root multiplicity in the first place, and it stays attached to
*those* facts (their `h_dist`/`hcount` arguments), not to the conversions proven here.  The data
exported here take the *already-established* multiplicity / factorization as input.

All results rest only on `[propext, Classical.choice, Quot.sound]`.

## References

* [BCIKS20] — Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain) and Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace MultiplicityDatum

/-! ## Obligation 4 datum: `HasOrderAt` from the proven root multiplicity

`GuruswamiSudan.HasOrderAt Q x y m` is, by definition,
`∀ s t, s + t < m → Bivariate.coeff (shift Q x y) s t = 0`.  Each such shifted coefficient must
vanish whenever the root multiplicity of `Q` at `(x, y)` is `≥ m`, by the contrapositive of
`GuruswamiSudan.rootMultiplicity_le_of_coeff_ne_zero`.  This is the standalone re-derivation of the
inline `multiplicity ⟹ HasOrderAt` step inside `GuruswamiSudan.dvd_property`. -/

variable {F : Type} [Field F]

/-- **The multiplicity ⟹ `HasOrderAt` conversion (single point).**  From the *proven* root
multiplicity lower bound `m ≤ rootMultiplicity Q x y`, the GS order-`m` vanishing predicate
`GuruswamiSudan.HasOrderAt Q x y m` holds.  This is the easy direction of the multiplicity
criterion, derived from the public `GuruswamiSudan.rootMultiplicity_le_of_coeff_ne_zero`. -/
theorem hasOrderAt_of_rootMultiplicity_ge [DecidableEq F] {Q : F[X][Y]} {x y : F} {m : ℕ}
    (hmult : (m : Option ℕ) ≤ Bivariate.rootMultiplicity Q x y) :
    GuruswamiSudan.HasOrderAt Q x y m := by
  intro s t hst
  by_contra hc
  -- a non-zero shifted coefficient of total degree `s + t` caps the multiplicity at `s + t`
  have hle : Bivariate.rootMultiplicity Q x y ≤ ((s + t : ℕ) : WithTop ℕ) :=
    GuruswamiSudan.rootMultiplicity_le_of_coeff_ne_zero hc
  -- but `m ≤ rootMultiplicity ≤ s + t < m`, contradiction.  Case on the multiplicity value;
  -- `none` is impossible by `hmult`, and on `some v` everything reduces to `ℕ`.
  rcases hrm : Bivariate.rootMultiplicity Q x y with _ | v
  · rw [hrm] at hmult; simp at hmult
  · rw [hrm] at hmult hle
    rw [show ((s + t : ℕ) : WithTop ℕ) = ((s + t : ℕ) : Option ℕ) from rfl] at hle
    have hmv : m ≤ v := by exact_mod_cast hmult
    have hvst : v ≤ s + t := by exact_mod_cast hle
    omega

/-- **Obligation-4 datum, packaged over an agreement set.**  From the *proven* per-index root
multiplicity `m ≤ rootMultiplicity Qz (ωs i) (Pz.eval (ωs i))` (the field-side output of
`gsQ_multiplicity` / the `gapB_transport_mult` transport behind
`Q_vanishes_on_close_codeword_graph`) on an agreement set `A`, the exact `hord` hypothesis consumed
by `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` is produced:
`∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m`. -/
theorem hord_of_rootMultiplicity_ge [DecidableEq F] {n : ℕ}
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m : ℕ) (A : Finset (Fin n))
    (hmult : ∀ i ∈ A,
      (m : Option ℕ) ≤ Bivariate.rootMultiplicity Qz (ωs i) (Pz.eval (ωs i))) :
    ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m :=
  fun i hi => hasOrderAt_of_rootMultiplicity_ge (hmult i hi)

/-! ### Matching-factor corollaries from root-multiplicity data

These are the direct single-candidate consumers of the obligation-4 datum above: once the proven
root-multiplicity lower bound holds on a candidate's agreement set, the standalone
`MatchingExtractor` adapters produce the matching factor `Y - P(X)` dividing the interpolant.
-/

/-- **GS matching-factor extraction from bivariate root-multiplicity data.**

If the interpolant has root multiplicity at least `m` on the agreement graph points of `Pz`, and
the specialized degree is below the corresponding root-count budget, then `Y - Pz(X)` divides the
interpolant. -/
theorem matchingFactor_dvd_of_rootMultiplicity_and_count [DecidableEq F] {n : ℕ}
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m : ℕ) (A : Finset (Fin n))
    (hmult : ∀ i ∈ A,
      (m : Option ℕ) ≤ Bivariate.rootMultiplicity Qz (ωs i) (Pz.eval (ωs i)))
    (hcount : (Qz.eval Pz).natDegree < m * A.card) :
    (Polynomial.X - Polynomial.C Pz) ∣ Qz := by
  exact MatchingExtractor.matchingFactor_dvd_of_orderM_and_count ωs Qz Pz m A
    (hord_of_rootMultiplicity_ge ωs Qz Pz m A hmult) hcount

/-- Weighted-degree form of `matchingFactor_dvd_of_rootMultiplicity_and_count`. -/
theorem matchingFactor_dvd_of_rootMultiplicity_and_weightedDegree [DecidableEq F] {n : ℕ}
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m k : ℕ) (A : Finset (Fin n))
    (hPdeg : Pz.natDegree ≤ k)
    (hmult : ∀ i ∈ A,
      (m : Option ℕ) ≤ Bivariate.rootMultiplicity Qz (ωs i) (Pz.eval (ωs i)))
    (hwcount : Bivariate.natWeightedDegree Qz 1 k < m * A.card) :
    (Polynomial.X - Polynomial.C Pz) ∣ Qz := by
  exact MatchingExtractor.matchingFactor_dvd_of_weightedDegree ωs Qz Pz m k A hPdeg
    (hord_of_rootMultiplicity_ge ωs Qz Pz m A hmult) hwcount

/-! ### List-size corollaries from root-multiplicity data

These are the direct finite-family consumers of the obligation-4 datum above: once each candidate
has the proven root-multiplicity lower bound on its agreement set, the standalone
`MatchingExtractor` list-size adapters discharge the GS factor extraction and distinct-factor count.
-/

/-- **Finite-family GS list-size bound from bivariate root-multiplicity data.**

For every candidate `P ∈ Ps`, assume the interpolant has root multiplicity at least `m` on the
agreement graph points indexed by `A P`, and that the specialized degree is below `m * #(A P)`.
Then the candidate family has size at most the `Y`-degree of the nonzero interpolant. -/
theorem list_size_le_of_rootMultiplicity_and_count [DecidableEq F] {n : ℕ}
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (hQz : Qz ≠ 0) (Ps : Finset F[X])
    (m : ℕ) (A : F[X] → Finset (Fin n))
    (hmult : ∀ P ∈ Ps, ∀ i ∈ A P,
      (m : Option ℕ) ≤ Bivariate.rootMultiplicity Qz (ωs i) (P.eval (ωs i)))
    (hcount : ∀ P ∈ Ps, (Qz.eval P).natDegree < m * (A P).card) :
    Ps.card ≤ Qz.natDegree := by
  refine MatchingExtractor.list_size_le_of_orderM_and_count ωs Qz hQz Ps m A ?_ hcount
  intro P hP
  exact hord_of_rootMultiplicity_ge ωs Qz P m (A P) (hmult P hP)

/-- Weighted-degree form of `list_size_le_of_rootMultiplicity_and_count`.  The per-candidate
specialized degree budget is discharged from `P.natDegree ≤ k` and the common `(1,k)` weighted
degree bound on `Qz`. -/
theorem list_size_le_of_rootMultiplicity_and_weightedDegree [DecidableEq F] {n : ℕ}
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (hQz : Qz ≠ 0) (Ps : Finset F[X])
    (m k : ℕ) (A : F[X] → Finset (Fin n))
    (hPdeg : ∀ P ∈ Ps, P.natDegree ≤ k)
    (hmult : ∀ P ∈ Ps, ∀ i ∈ A P,
      (m : Option ℕ) ≤ Bivariate.rootMultiplicity Qz (ωs i) (P.eval (ωs i)))
    (hwcount : ∀ P ∈ Ps, Bivariate.natWeightedDegree Qz 1 k < m * (A P).card) :
    Ps.card ≤ Qz.natDegree := by
  refine MatchingExtractor.list_size_le_of_orderM_and_weightedDegree ωs Qz hQz Ps m k A
    hPdeg ?_ hwcount
  intro P hP
  exact hord_of_rootMultiplicity_ge ωs Qz P m (A P) (hmult P hP)

/-! ## Obligation 1 datum: `hdvd_C` from the un-specialized GS-factor divisibility

`hdvd_C : (C H.leadingCoeff) ∣ R.coeff R.natDegree` lives in `(F[X])[X]`.  Its honest source is the
leading-`Y`-coefficient shadow of an un-specialized factorization `H_lift ∣ R` in `F[X][X][Y]`,
where `H_lift = H.map (C)` embeds `H : F[X][Y]` into `F[X][X][Y]`.  Over the domain `(F[X])[X]`,
`leadingCoeff` is multiplicative, so a divisor's leading coefficient divides the dividend's. -/

/-- Embed `H : F[X][Y]` into `F[X][X][Y]` by lifting each (inner-`X`) coefficient with `C`. -/
noncomputable def Hlift (H : F[X][Y]) : F[X][X][Y] :=
  H.map (Polynomial.C : F[X] →+* (F[X])[X])

/-- The lift `Hlift H` has the same `Y`-natDegree as `H` (`C` is injective, so no leading term is
killed). -/
lemma natDegree_Hlift (H : F[X][Y]) : (Hlift H).natDegree = H.natDegree := by
  rw [Hlift, Polynomial.natDegree_map_eq_of_injective]
  exact Polynomial.C_injective

/-- The leading `Y`-coefficient of `Hlift H` is `C (H.leadingCoeff)`. -/
lemma leadingCoeff_Hlift (H : F[X][Y]) :
    (Hlift H).leadingCoeff = Polynomial.C H.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_Hlift, Hlift, Polynomial.coeff_map]
  rfl

/-- Over the domain `(F[X])[X]`, the leading `Y`-coefficient of a divisor divides that of the
dividend (`leadingCoeff` is multiplicative over a domain). -/
lemma leadingCoeff_dvd_of_dvd {a b : F[X][X][Y]} (hdvd : a ∣ b) :
    a.leadingCoeff ∣ b.leadingCoeff := by
  obtain ⟨q, hq⟩ := hdvd
  exact ⟨q.leadingCoeff, by rw [hq, Polynomial.leadingCoeff_mul]⟩

/-- **Main obligation-1 discharge.**  From the un-specialized GS-factor divisibility
`Hlift H ∣ R` in `F[X][X][Y]` (the genuine §5/App-A factorization structure, whose leading
`Y`-coefficient is `C H.leadingCoeff`), the residual structural hypothesis
`hdvd_C : (C H.leadingCoeff) ∣ R.coeff R.natDegree` consumed by `ArkLib.hdvd_top_of_dvd_C` holds —
**as a theorem**, not a hypothesis. -/
theorem hdvd_C_of_Hlift_dvd {R : F[X][X][Y]} {H : F[X][Y]}
    (hdvd : Hlift H ∣ R) :
    (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree := by
  have h := leadingCoeff_dvd_of_dvd hdvd
  rwa [leadingCoeff_Hlift, Polynomial.leadingCoeff] at h

/-! ### The `i₁ = 0` value projection — discharged outright from the proven `Hypotheses`

The value at `C x₀` of `hdvd_C`, i.e. `W ∣ (R.coeff R.natDegree).eval (C x₀)` (the `i₁ = 0` line
fact that `ArkLib.hdvd_top_zero` consumes), needs **no** un-specialized input: it is exactly
`BCIKS20AppendixA.leadingCoeff_dvd_evalX_coeff_natDegree` applied to the *proven*
`Hypotheses x₀ R H` multiplicity/separability structure (in tree:
`claimA2_hypotheses_graph_clear`). -/

/-- **Value-projection datum, no residual.**  From the proven `Hypotheses x₀ R H` structure
(`H ∣ evalX (C x₀) R` and `evalX (C x₀) R` separable), the value at `C x₀` of `hdvd_C` holds:
`W ∣ (R.coeff R.natDegree).eval (C x₀)`.  This is the `i₁ = 0` line input of `hdvd_top_zero`. -/
theorem hdvd_C_value_of_hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (R.coeff R.natDegree).eval (Polynomial.C x₀) := by
  have h := BCIKS20AppendixA.ClaimA2.leadingCoeff_dvd_evalX_coeff_natDegree hHyp
  -- `(evalX (C x₀) R).coeff R.natDegree = (R.coeff R.natDegree).eval (C x₀)`
  rwa [Bivariate.evalX_eq_map, Polynomial.coeff_map] at h

/-- Consistency: the un-specialized `hdvd_C` (from `Hlift H ∣ R`) implies its value projection,
matching `ArkLib.hdvd_C_implies_zero_case`.  So the obligation-1 theorem is a genuine strengthening
of the `Hypotheses`-backed `i₁ = 0` line fact, not an orthogonal assumption. -/
theorem hdvd_C_of_Hlift_dvd_implies_value {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hdvd : Hlift H ∣ R) :
    H.leadingCoeff ∣ (R.coeff R.natDegree).eval (Polynomial.C x₀) := by
  obtain ⟨c', hc'⟩ := hdvd_C_of_Hlift_dvd hdvd
  rw [hc', Polynomial.eval_mul, Polynomial.eval_C]
  exact Dvd.intro _ rfl

end MultiplicityDatum

end ArkLib
