/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GenuineTruncationFin
import ArkLib.ToMathlib.MatchingExtractor
import ArkLib.ToMathlib.IngredientCBridge

/-!
# Issue #304 — the per-good-`z` rational-root supply

The §5/Appendix-A bundles (`OffcentreKeystoneAssembly`, `BetaIdentify`, `GenuineTruncationFin`)
all consume, at matching places `z`, a `rationalRoot (H_tilde' H) z`
(`= {t_z : F // evalEval z t_z (H_tilde' H) = 0}`) — and ultimately the `S_β`-existential
`∃ r : rationalRoot (H_tilde' H) z, π_z z r β = 0`.  This file is the **existence source**:
it builds rational roots from the honest §5 geometric data — the curve `H` passing through
graph points of decoded words — and packages them into the exact `hvanish` field shape of
`ArkLib.GenuineTruncationFin.SβLargeAtFin_of_graded_disc`.

## The constructors (Part 1)

* `rationalRoot_of_evalEval` — from a root `H(z, y) = 0` of `H` itself, the rational root of
  the monicization `H_tilde' H` at value `lc_H(z)·y` (via the in-tree
  `evalEval_H_tilde'_eq_zero_of_evalEval_eq_zero`).
* `rationalRoot_of_linear_factor_tilde` — from a linear factor `(Y − C v) ∣ (H_tilde' H)(z, ·)`,
  the rational root at value `v` (the trivial eval-roots-from-linear-factors direction).
* `rationalRoot_of_linear_factor` — same, from a linear factor of `H(z, ·)` itself.

## The §5 source: graph points of the matching factor (Part 2)

At an agreement point `z`, the decoded value `P(z)` lies ON the specialized interpolant:
the GS matching factor `(Y − C P) ∣ Q` (`MatchingExtractor.MatchesGraph Q P`, produced
in-tree by `matchingFactor_dvd_of_orderM_and_count` and, at good specializations, by
`GuruswamiSudan.OverRatFunc.scalar_fold_decoded_divides_specialization` via
`matchesGraph_iff_dvd`).  If `H` is the factor of `Q` carrying that branch — `Q = H * G`
with the complementary factor `G` not vanishing at the graph point (`hbranch`) — then the
graph point is a root of `H(z, ·)`:

* `evalEval_eval_eval` — the substitution-composition bridge
  `Q(z, P(z)) = (Q.eval P).eval z`.
* `evalEval_eq_zero_of_matchesGraph` — the curve through the graph: `Q(z, P(z)) = 0`.
* `evalEval_eq_zero_of_factor_branch` — branch separation: `Q(z,v) = 0 ∧ G(z,v) ≠ 0 → H(z,v) = 0`.
* `rationalRoot_of_matchesGraph` / `rationalRoot_of_factor_branch` /
  `rationalRoot_of_matching_branch` — the resulting rational-root constructors, with value
  lemmas (`lc_H(z)·P(z)`, collapsing to `P(z)` for monic `H`).

## The `S_β` / `hvanish` glue (Part 3)

* `pi_z_eq_zero_of_rep` / `exists_root_pi_z_eq_zero_of_rep` / `mem_S_β_of_rep` — from a root
  `r` and the vanishing of any representative `p` of `β` at `(z, r)`, the specialization
  `π_z z r β = 0`, the `S_β`-existential, and `z ∈ S_β β`.
* `hvanish_of_root_supply` / `hvanish_of_representatives` / `hvanish_of_matching_branch`
  (+ `_monic`) — the exact `hvanish` field of `SβLargeAtFin_of_graded_disc`, produced from a
  rational-root section (resp. from the matching-branch factor geometry) plus per-`t`
  vanishing of `βHensel`-representatives at the geometric points.

The honest residual carried by the capstones is exactly the per-place *value* input: the
vanishing of a `βHensel t`-representative at the constructed geometric point (the Hensel-
uniqueness content the in-flight per-place machinery produces); the *existence* of the
rational root itself is fully discharged here from the factor geometry.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (matching factors), Appendix A.3 (`π_z`, `S_β`, Lemma A.1).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate Ideal BCIKS20AppendixA BCIKS20.HenselNumerator

namespace ArkLib

namespace RationalRootSupply

variable {F : Type} [Field F]

/-! ## Part 1 — point constructors for `rationalRoot (H_tilde' H) z` -/

/-- **Rational root from a root of `H` itself.**  If `H(z, y) = 0` then `lc_H(z)·y` is a root
of the monicization `H_tilde' H` at `z` — the basic constructor for
`rationalRoot (H_tilde' H) z`. -/
noncomputable def rationalRoot_of_evalEval {H : F[X][Y]} (hH : 0 < H.natDegree) {z y : F}
    (hroot : Polynomial.evalEval z y H = 0) : rationalRoot (H_tilde' H) z :=
  ⟨(H.coeff H.natDegree).eval z * y,
    evalEval_H_tilde'_eq_zero_of_evalEval_eq_zero H hH hroot⟩

@[simp]
lemma rationalRoot_of_evalEval_val {H : F[X][Y]} (hH : 0 < H.natDegree) {z y : F}
    (hroot : Polynomial.evalEval z y H = 0) :
    (rationalRoot_of_evalEval hH hroot).1 = (H.coeff H.natDegree).eval z * y := rfl

/-- **Rational root from a linear factor of the specialized monicization.**  If
`(Y − C v) ∣ (H_tilde' H)(z, ·)` then `v` itself is a rational root at `z` — the trivial
eval-roots-from-linear-factors direction. -/
noncomputable def rationalRoot_of_linear_factor_tilde {H : F[X][Y]} {z v : F}
    (hdvd : Polynomial.X - Polynomial.C v ∣ Polynomial.Bivariate.evalX z (H_tilde' H)) :
    rationalRoot (H_tilde' H) z :=
  ⟨v, by
    have h : (Polynomial.Bivariate.evalX z (H_tilde' H)).eval v = 0 :=
      Polynomial.dvd_iff_isRoot.mp hdvd
    rwa [eval_evalX_eq_evalEval] at h⟩

@[simp]
lemma rationalRoot_of_linear_factor_tilde_val {H : F[X][Y]} {z v : F}
    (hdvd : Polynomial.X - Polynomial.C v ∣ Polynomial.Bivariate.evalX z (H_tilde' H)) :
    (rationalRoot_of_linear_factor_tilde hdvd).1 = v := rfl

/-- **Rational root from a linear factor of the specialized `H`.**  If
`(Y − C v) ∣ H(z, ·)` then `lc_H(z)·v` is a rational root of `H_tilde' H` at `z`. -/
noncomputable def rationalRoot_of_linear_factor {H : F[X][Y]} (hH : 0 < H.natDegree) {z v : F}
    (hdvd : Polynomial.X - Polynomial.C v ∣ Polynomial.Bivariate.evalX z H) :
    rationalRoot (H_tilde' H) z :=
  rationalRoot_of_evalEval hH (by
    have h : (Polynomial.Bivariate.evalX z H).eval v = 0 :=
      Polynomial.dvd_iff_isRoot.mp hdvd
    rwa [eval_evalX_eq_evalEval] at h)

@[simp]
lemma rationalRoot_of_linear_factor_val {H : F[X][Y]} (hH : 0 < H.natDegree) {z v : F}
    (hdvd : Polynomial.X - Polynomial.C v ∣ Polynomial.Bivariate.evalX z H) :
    (rationalRoot_of_linear_factor hH hdvd).1 = (H.coeff H.natDegree).eval z * v := rfl

/-! ## Part 2 — graph points of the matching factor -/

/-- **The substitution-composition bridge.**  Evaluating the outer variable at the polynomial
`P` and then `X := z` agrees with the two-point evaluation at `(z, P(z))`:
`Q(z, P(z)) = (Q.eval P).eval z`. -/
lemma evalEval_eval_eval (z : F) (Q : F[X][Y]) (P : F[X]) :
    Polynomial.evalEval z (P.eval z) Q = (Q.eval P).eval z := by
  have h := Polynomial.eval₂_at_apply (p := Q) (Polynomial.evalRingHom z) P
  rwa [Polynomial.eval₂_evalRingHom, Polynomial.coe_evalRingHom] at h

/-- **The curve through the decoded graph point.**  If the matching factor `(Y − C P)`
divides `Q` (`MatchesGraph Q P`, i.e. `Q.eval P = 0`), then at every place `z` the decoded
value `P(z)` lies on the specialized curve: `Q(z, P(z)) = 0`. -/
lemma evalEval_eq_zero_of_matchesGraph {Q : F[X][Y]} {P : F[X]}
    (hmatch : MatchingExtractor.MatchesGraph Q P) (z : F) :
    Polynomial.evalEval z (P.eval z) Q = 0 := by
  have h : Q.eval P = 0 := hmatch
  rw [evalEval_eval_eval, h, Polynomial.eval_zero]

/-- **Branch separation.**  If `Q = H * G`, the point `(z, v)` lies on `Q`, and the
complementary factor `G` does not vanish there, then `(z, v)` lies on `H`. -/
lemma evalEval_eq_zero_of_factor_branch {H G Q : F[X][Y]} (hfac : Q = H * G) {z v : F}
    (hQ : Polynomial.evalEval z v Q = 0) (hbranch : Polynomial.evalEval z v G ≠ 0) :
    Polynomial.evalEval z v H = 0 := by
  rw [hfac, Polynomial.evalEval_mul] at hQ
  rcases mul_eq_zero.mp hQ with h | h
  · exact h
  · exact absurd h hbranch

/-- **The whole-family rational-root supply from a matching factor of `H` itself.**  If `H`
matches the graph of `P` (`H.eval P = 0`, the affine-branch case), then *every* place `z`
carries a rational root — the section `(z : F) → rationalRoot (H_tilde' H) z` consumed by
the §5 bundles. -/
noncomputable def rationalRoot_of_matchesGraph {H : F[X][Y]} (hH : 0 < H.natDegree)
    {P : F[X]} (hmatch : MatchingExtractor.MatchesGraph H P) (z : F) :
    rationalRoot (H_tilde' H) z :=
  rationalRoot_of_evalEval hH (evalEval_eq_zero_of_matchesGraph hmatch z)

@[simp]
lemma rationalRoot_of_matchesGraph_val {H : F[X][Y]} (hH : 0 < H.natDegree)
    {P : F[X]} (hmatch : MatchingExtractor.MatchesGraph H P) (z : F) :
    (rationalRoot_of_matchesGraph hH hmatch z).1 =
      (H.coeff H.natDegree).eval z * P.eval z := rfl

/-- **Rational root from a point on `Q` and branch separation.** -/
noncomputable def rationalRoot_of_factor_branch {H G Q : F[X][Y]} (hH : 0 < H.natDegree)
    (hfac : Q = H * G) {z v : F} (hQ : Polynomial.evalEval z v Q = 0)
    (hbranch : Polynomial.evalEval z v G ≠ 0) : rationalRoot (H_tilde' H) z :=
  rationalRoot_of_evalEval hH (evalEval_eq_zero_of_factor_branch hfac hQ hbranch)

/-- **The §5-shaped per-`z` rational-root producer.**  `Q` carries the GS matching factor
`(Y − C P)` (in-tree: `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`, or the S10
converse `scalar_fold_decoded_divides_specialization` through `matchesGraph_iff_dvd`); `H` is
the factor of `Q` carrying that branch at `z` (`hbranch` — the complementary factor misses
the graph point).  Then the decoded value `P(z)` descends to a rational root of `H_tilde' H`
at `z`. -/
noncomputable def rationalRoot_of_matching_branch {H G Q : F[X][Y]} (hH : 0 < H.natDegree)
    (hfac : Q = H * G) {P : F[X]} (hmatch : MatchingExtractor.MatchesGraph Q P) {z : F}
    (hbranch : Polynomial.evalEval z (P.eval z) G ≠ 0) : rationalRoot (H_tilde' H) z :=
  rationalRoot_of_evalEval hH
    (evalEval_eq_zero_of_factor_branch hfac (evalEval_eq_zero_of_matchesGraph hmatch z)
      hbranch)

@[simp]
lemma rationalRoot_of_matching_branch_val {H G Q : F[X][Y]} (hH : 0 < H.natDegree)
    (hfac : Q = H * G) {P : F[X]} (hmatch : MatchingExtractor.MatchesGraph Q P) {z : F}
    (hbranch : Polynomial.evalEval z (P.eval z) G ≠ 0) :
    (rationalRoot_of_matching_branch hH hfac hmatch hbranch).1 =
      (H.coeff H.natDegree).eval z * P.eval z := rfl

/-- For monic `H` the constructed root *is* the decoded value `P(z)`. -/
lemma rationalRoot_of_matching_branch_val_monic {H G Q : F[X][Y]} (hH : 0 < H.natDegree)
    (hfac : Q = H * G) {P : F[X]} (hmatch : MatchingExtractor.MatchesGraph Q P) {z : F}
    (hbranch : Polynomial.evalEval z (P.eval z) G ≠ 0) (hmonic : H.Monic) :
    (rationalRoot_of_matching_branch hH hfac hmatch hbranch).1 = P.eval z := by
  rw [rationalRoot_of_matching_branch_val hH hfac hmatch hbranch,
    hmonic.coeff_natDegree, Polynomial.eval_one, one_mul]

/-! ## Part 3 — the `π_z` / `S_β` glue -/

/-- **Specialization vanishing from any representative.**  If `p` represents `β` in `𝒪 H`
and `p` vanishes at the geometric point `(z, r)`, then `π_z z r β = 0`. -/
lemma pi_z_eq_zero_of_rep {H : F[X][Y]} {β : 𝒪 H} {p : F[X][Y]}
    (hrep : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = β)
    {z : F} (r : rationalRoot (H_tilde' H) z)
    (hvan : Polynomial.evalEval z r.1 p = 0) : (π_z z r) β = 0 := by
  rw [← hrep, π_z_mk]
  exact hvan

/-- The `S_β`-existential form: a rational root with vanishing specialization, from a
representative-level vanishing. -/
lemma exists_root_pi_z_eq_zero_of_rep {H : F[X][Y]} {β : 𝒪 H} {p : F[X][Y]}
    (hrep : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = β)
    {z : F} (r : rationalRoot (H_tilde' H) z)
    (hvan : Polynomial.evalEval z r.1 p = 0) :
    ∃ r' : rationalRoot (H_tilde' H) z, (π_z z r') β = 0 :=
  ⟨r, pi_z_eq_zero_of_rep hrep r hvan⟩

/-- `S_β`-membership from a representative-level vanishing at a rational root. -/
lemma mem_S_β_of_rep {H : F[X][Y]} {β : 𝒪 H} {p : F[X][Y]}
    (hrep : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = β)
    {z : F} (r : rationalRoot (H_tilde' H) z)
    (hvan : Polynomial.evalEval z r.1 p = 0) : z ∈ S_β β :=
  IngredientC.mem_S_β_of_pi_z_eq_zero β r (pi_z_eq_zero_of_rep hrep r hvan)

/-! ## Part 4 — the `hvanish` supply (the exact landing-pad shape of
`ArkLib.GenuineTruncationFin.SβLargeAtFin_of_graded_disc`) -/

section Hvanish

variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`hvanish` from a rational-root section.**  Pure packaging: a per-place root section on
the matching set plus per-`t` specialization vanishing yields the exact `hvanish` field of
`SβLargeAtFin_of_graded_disc` / `gammaGenuine_eq_trunc_of_graded_disc`. -/
theorem hvanish_of_root_supply {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {k T : ℕ} {matchingSet : Finset F}
    (root : (z : F) → z ∈ matchingSet → rationalRoot (H_tilde' H) z)
    (hvan : ∀ t, k ≤ t → t ≤ T → ∀ z, (hz : z ∈ matchingSet) →
      (π_z z (root z hz)) (βHensel H x₀ R hHyp t) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0 :=
  fun t hkt htT z hz => ⟨root z hz, hvan t hkt htT z hz⟩

/-- **`hvanish` from per-`t` representatives.**  The `π_z`-vanishing side is discharged at
the representative level: `p t` represents `βHensel t` and vanishes at each geometric point
`(z, root z)`. -/
theorem hvanish_of_representatives {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) {k T : ℕ} {matchingSet : Finset F}
    (root : (z : F) → z ∈ matchingSet → rationalRoot (H_tilde' H) z)
    (p : ℕ → F[X][Y])
    (hrep : ∀ t, k ≤ t → t ≤ T →
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (p t) : 𝒪 H) = βHensel H x₀ R hHyp t)
    (hvan : ∀ t, k ≤ t → t ≤ T → ∀ z, (hz : z ∈ matchingSet) →
      Polynomial.evalEval z (root z hz).1 (p t) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0 :=
  fun t hkt htT z hz =>
    ⟨root z hz, pi_z_eq_zero_of_rep (hrep t hkt htT) (root z hz) (hvan t hkt htT z hz)⟩

/-- **The capstone: `hvanish` from the matching-branch factor geometry.**  Inputs:
* `hfac`/`hmatch`/`hbranch` — the §5 factor geometry: `Q = H * G` carries the GS matching
  factor `(Y − C P)`, and at every matching place the complementary factor `G` misses the
  graph point (so the decoded value lands on the `H`-branch);
* `hrep`/`hvan` — the honest per-place value residual: a representative of `βHensel t`
  vanishes at the constructed geometric point `(z, lc_H(z)·P(z))`.

Output: the exact `hvanish` field of `SβLargeAtFin_of_graded_disc`. -/
theorem hvanish_of_matching_branch {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {Q G : F[X][Y]} (hfac : Q = H * G) {P : F[X]}
    (hmatch : MatchingExtractor.MatchesGraph Q P)
    {k T : ℕ} {matchingSet : Finset F}
    (hbranch : ∀ z ∈ matchingSet, Polynomial.evalEval z (P.eval z) G ≠ 0)
    (p : ℕ → F[X][Y])
    (hrep : ∀ t, k ≤ t → t ≤ T →
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (p t) : 𝒪 H) = βHensel H x₀ R hHyp t)
    (hvan : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((H.coeff H.natDegree).eval z * P.eval z) (p t) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0 := by
  intro t hkt htT z hz
  refine ⟨rationalRoot_of_matching_branch hH hfac hmatch (hbranch z hz), ?_⟩
  exact pi_z_eq_zero_of_rep (hrep t hkt htT) _ (hvan t hkt htT z hz)

/-- **The monic capstone.**  For monic `H` (the `GenuineTruncationFin` setting) the
geometric point is the decoded value itself: the per-place value residual is the vanishing
of a `βHensel t`-representative at `(z, P(z))`. -/
theorem hvanish_of_matching_branch_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hmonic : H.Monic)
    {Q G : F[X][Y]} (hfac : Q = H * G) {P : F[X]}
    (hmatch : MatchingExtractor.MatchesGraph Q P)
    {k T : ℕ} {matchingSet : Finset F}
    (hbranch : ∀ z ∈ matchingSet, Polynomial.evalEval z (P.eval z) G ≠ 0)
    (p : ℕ → F[X][Y])
    (hrep : ∀ t, k ≤ t → t ≤ T →
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (p t) : 𝒪 H) = βHensel H x₀ R hHyp t)
    (hvan : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      Polynomial.evalEval z (P.eval z) (p t) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0 := by
  refine hvanish_of_matching_branch H hHyp hH hfac hmatch hbranch p hrep ?_
  intro t hkt htT z hz
  rw [hmonic.coeff_natDegree, Polynomial.eval_one, one_mul]
  exact hvan t hkt htT z hz

end Hvanish

end RationalRootSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]` (or a subset); no
`sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_evalEval
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_evalEval_val
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_linear_factor_tilde
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_linear_factor_tilde_val
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_linear_factor
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_linear_factor_val
#print axioms ArkLib.RationalRootSupply.evalEval_eval_eval
#print axioms ArkLib.RationalRootSupply.evalEval_eq_zero_of_matchesGraph
#print axioms ArkLib.RationalRootSupply.evalEval_eq_zero_of_factor_branch
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_matchesGraph
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_matchesGraph_val
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_factor_branch
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_matching_branch
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_matching_branch_val
#print axioms ArkLib.RationalRootSupply.rationalRoot_of_matching_branch_val_monic
#print axioms ArkLib.RationalRootSupply.pi_z_eq_zero_of_rep
#print axioms ArkLib.RationalRootSupply.exists_root_pi_z_eq_zero_of_rep
#print axioms ArkLib.RationalRootSupply.mem_S_β_of_rep
#print axioms ArkLib.RationalRootSupply.hvanish_of_root_supply
#print axioms ArkLib.RationalRootSupply.hvanish_of_representatives
#print axioms ArkLib.RationalRootSupply.hvanish_of_matching_branch
#print axioms ArkLib.RationalRootSupply.hvanish_of_matching_branch_monic
