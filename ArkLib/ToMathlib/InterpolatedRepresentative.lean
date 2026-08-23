/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaToCurveCoeffPolysOffcentre
import ArkLib.ToMathlib.WeightLambdaCalculus
import ArkLib.ToMathlib.SbetaPackaging
import ArkLib.ToMathlib.FiniteSeriesToPoly

/-!
# Issue #304 — Brick C: the interpolated-representative producer (the Claim 5.9 bypass)

## Design (Phase 1 — pinned in-tree shapes)

**Target shape.**  The off-centre per-`P` §5 bundle
(`OffcentreKeystone.Section5StrictDataOffcentreFin`, `OffcentreKeystoneAssembly.lean`) ends in
the per-`P` representative pair

  `Ppoly : F[X][Y]`,
  `hrep  : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff`,
  `hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1`.

[BCIKS20] §6.2 produces this pair **not** from the sharp weight claim `Λ(α_t) = 1` of
Claim 5.9 — machine-refuted in-tree for canonical representatives
(`P1MonicWeightRefutation.lean`) — but by **interpolation**: the local Hensel series
`gammaLocal = mk (αFromBeta …)` is a polynomial of degree `< k` in the series variable (the
`htail` content, produced in-tree by the matching lane), one interpolates the per-`z` decoded
values to get `v₀ v₁ : F[X]` of degree `< k`, sets `Ppoly := (map C v₀) + (C X)·(map C v₁)`
(so `hdegX` holds **by construction**), and proves `hrep` per coefficient by the Lemma-A.1
counting argument at the **loose, proven** weight budget (`betaRec_weight_le_graded`), never
the sharp one.

**In-tree currencies consumed (all pinned before writing):**
* `BCIKS20AppendixA.Lemma_A_1` (`RationalFunctionsCore.lean`): for `β : 𝒪 H`, if
  `ncard (S_β β) > weight_Λ_over_𝒪 hH β D * H.natDegree` then `embeddingOf𝒪Into𝕃 H β = 0`,
  where `S_β β = {z | ∃ root, π_z z root β = 0}`.  Finset packaging:
  `ArkLib.embedding_eq_zero_of_finset_subset_S_β` (`SbetaPackaging.lean`).  Injectivity:
  `embeddingOf𝒪Into𝕃_injective`.
* Weight calculus (`WeightLambdaCalculus.lean`): `weight_Λ_over_𝒪_sub_le` (max form),
  `_mul_le_of_le`, `_pow_le_of_le`, `_C_le`, `weight_Λ_over_𝒪_W_reg_le` (`Λ(W) ≤ D − d_H`).
* `BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t : 𝕃 H` is the **quotient**
  `embedding(betaRec t) / (W^{t+1} · embedding(ξ)^{e_t})` with
  `W = liftToFunctionField H.leadingCoeff` and `e_t = henselDenominatorExponent t`; the
  per-coefficient identity `αFromBeta t = liftToFunctionField c` therefore **clears** to the
  `𝒪 H`-identity `betaRec t = mk (C c) · (W_𝒪^{t+1} · ξ^{e_t})`, which is exactly Lemma-A.1
  currency (`clearedCoeff` below).  Its `π_z`-reading matches the per-place series
  denominator of `PlaceSeriesCanonical.aBetaPlace` — the matching-lane per-`z` currency.
* `polyToPowerSeries𝕃 H Ppoly = mk (fun t => liftToFunctionField (Ppoly.coeff t))`
  (`coeff_polyToPowerSeries𝕃`); `coeff_gammaLocal` reads `αFromBeta`.
* Interpolation: `Lagrange.interpolate s id a` with `eval_interpolate_at_node` and
  `degree_interpolate_lt` (Mathlib), node map `id`, `Set.injOn_id`.
* Linear shape: the eval-shape consumed by `exists_linear_decomposition_of_degreeX_le_one`
  and by the bundle's `hPz` is `(map C v₀) + (C X)·(map C v₁)`; its `Y`-coefficients are
  `C (v₀.coeff t) + X·C (v₁.coeff t)`, hence `degreeX ≤ 1` and tail-coefficient vanishing
  past `max deg v₀ deg v₁` are pure coefficient reading.

**NOT consumed**: `gammaGenuine` (the `hrep`-against-`gammaGenuine` shape is UNSATISFIABLE at
`d_H ≥ 2`, FINDING F6, `GenuinePpolyConverter.not_hrepG_of_two_le_natDegree`); the sharp
Claim 5.9 budget `Λ(α_t) = 1` (refuted); `PowerSeries.subst` of the shift series (invalid
off-centre).  The target is `gammaLocal`, where `hrep` is satisfiable.

## What this file proves (Phase 2 — the bricks)

* **Brick C1 (the counting weld, two-sided Lemma A.1)** —
  `eq_of_pi_z_eq_on_finset`: for `a b : 𝒪 H`, if `Λ(a − b) ≤ B` (a `ℕ`-budget) and the
  `π_z`-readings of `a` and `b` agree on a `Finset` `T` with `B · d_H < #T`, then `a = b`.
  Companions: `weight_Λ_over_𝒪_sub_le_of_le` (the difference budget from componentwise
  `ℕ`-budgets).
* **Brick C2 (the interpolant)** — `interpolatedRep s a₀ a₁ :=
  (map C (interpolate s id a₀)) + (C X)·(map C (interpolate s id a₁))` with
  `degreeX_interpolatedRep_le_one` (**`hdegX` by construction**),
  `natDegree_interpolatedRep_lt` (top degree `< #s`),
  `coeff_interpolatedRep_eq_zero` (tail coefficients vanish from `#s` on, the `htailP` input
  of C3 **by construction**), and `eval_interpolatedRep_at_node` (the per-node eval shape
  `C (a₀ z) + (a₁ z) • X` — the `hPz`-lane currency of `eval_linear_representative`).
* **Brick C3 (the per-coefficient identity skeleton)** —
  `clearedCoeff`/`pi_z_clearedCoeff` (the cleared competitor and its per-place reading),
  `alphaFromBeta_eq_lift_of_betaRec_eq_cleared` (the division-clearing step: the cleared
  `𝒪`-identity yields `αFromBeta t = liftToFunctionField c`, given `embedding ξ ≠ 0`),
  `alphaFromBeta_eq_lift_of_counting` (C1 + clearing: the per-coefficient identity from
  per-`z` vanishing + loose budget), `weight_clearedCoeff_le` /
  `weight_betaRec_sub_clearedCoeff_le` (the loose-budget suppliers for the difference), and
  the capstones `hrep_of_cleared_counting` (any `Ppoly`; head by counting, tail by `htailP` +
  `htailα`) and `interpolatedRep_hrep_hdegX` / `exists_representative_pair` (the bundle's
  `(Ppoly, hrep, hdegX)` pair from the interpolant, with `hdegX` and `htailP` discharged by
  construction).

## Honest residuals (named hypotheses, NOT sorries)

* `hvan` — the per-`(t, z)` vanishing `π_z(betaRec t) = π_z(clearedCoeff (Ppoly.coeff t) t)`
  for `t < k` on the counting set `T`: this is exactly the matching-lane per-`z` currency
  (the §5 geometry: per-place proximate-root reading of the decoded values; compare
  `PlaceSeriesCanonical.aBetaPlace` and `BetaMatchingVanishes.MatchingPoint`).
* `hw`/`hcard` — the loose weight budget for the difference and the field-size largeness;
  the `betaRec` side is the **proven** graded budget (`betaRec_weight_le_graded`, consumed
  through `weight_betaRec_sub_clearedCoeff_le` + a `ℕ`-bound), the counting set is supplied
  by the §6 discriminant lane (`gradedConcreteFin_of_disc`).
* `hξ` — `embedding ξ ≠ 0`: standard in-tree hypothesis currency
  (`GSSurfaceMappedSeparability` takes `ξ ≠ 0` named throughout).
* `htailα` — the tail vanishing `αFromBeta t = 0` for `t ≥ k`: the already-produced in-tree
  `htail` content (`tail_zero_of_betaRec_embedding_zero`,
  `HcardDischarge.tail_zero_of_finite_card_and_degree`).

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, §6.2, Appendix A.1–A.4 (Lemma A.1).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 Ideal

namespace ArkLib

namespace InterpolatedRepresentative

variable {F : Type} [Field F]

/-! ## Part 1 — Brick C1: the two-sided Lemma-A.1 counting weld -/

section CountingWeld

/-- **Difference budget from componentwise `ℕ`-budgets.**  `Λ(a − b) ≤ max ba bb` in the
`ℕ`-cast form consumed by the counting weld. -/
theorem weight_Λ_over_𝒪_sub_le_of_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {a b : 𝒪 H} {ba bb : ℕ}
    (ha : weight_Λ_over_𝒪 hH a D ≤ (WithBot.some ba : WithBot ℕ))
    (hb : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some bb : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (a - b) D ≤ (WithBot.some (max ba bb) : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_sub_le hD hH a b).trans ?_
  rw [show (WithBot.some (max ba bb) : WithBot ℕ) =
        max (WithBot.some ba : WithBot ℕ) (WithBot.some bb) from WithBot.coe_max ba bb]
  exact max_le_max ha hb

/-- **Brick C1 — the counting weld (two-sided Lemma A.1).**  Two regular elements of `𝒪 H`
whose difference carries an `ℕ`-weight budget `B` and whose `π_z`-readings agree at more than
`B · d_H` places are **equal**.  This is the equality-from-counting engine of the §6.2
interpolation argument, in the exact in-tree currency (`π_z` place readings on a `Finset`,
`weight_Λ_over_𝒪` budgets, `Lemma_A_1` via `embedding_eq_zero_of_finset_subset_S_β`). -/
theorem eq_of_pi_z_eq_on_finset {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {a b : 𝒪 H} (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {T : Finset F} (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hvan : ∀ z ∈ T, (π_z z (root z)) a = (π_z z (root z)) b)
    {B : ℕ} (hw : weight_Λ_over_𝒪 hH (a - b) D ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card) :
    a = b := by
  -- the agreement set sits inside `S_β (a − b)`
  have hsub : (↑T : Set F) ⊆ S_β (a - b) := by
    intro z hz
    refine ⟨root z, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact hvan z (Finset.mem_coe.mp hz)
  -- the weight bound, multiplied through by `d_H`
  have hmul : weight_Λ_over_𝒪 hH (a - b) D * (H.natDegree : WithBot ℕ)
      ≤ ((B * H.natDegree : ℕ) : WithBot ℕ) := by
    have hcast : ((B * H.natDegree : ℕ) : WithBot ℕ)
        = (B : WithBot ℕ) * (H.natDegree : WithBot ℕ) := by push_cast; ring
    rw [hcast]
    gcongr
  have hbig : (↑T.card : WithBot ℕ) > weight_Λ_over_𝒪 hH (a - b) D * H.natDegree :=
    lt_of_le_of_lt hmul (by exact_mod_cast hcard)
  -- Lemma A.1 (finset packaging) + injectivity of the embedding
  have hemb : embeddingOf𝒪Into𝕃 H (a - b) = 0 :=
    embedding_eq_zero_of_finset_subset_S_β hH (a - b) D hD hsub hbig
  have hzero : a - b = 0 := by
    refine embeddingOf𝒪Into𝕃_injective hH ?_
    rw [map_zero]
    exact hemb
  exact sub_eq_zero.mp hzero

end CountingWeld

/-! ## Part 2 — Brick C2: the Lagrange interpolant in the bundle's eval shape -/

section LinearShape

/-- The linear (eval-shape) lift of a coefficient pair: the exact bivariate shape consumed by
`exists_linear_decomposition_of_degreeX_le_one` and by the bundle's `hPz` lane. -/
noncomputable def linearShape (v₀ v₁ : F[X]) : F[X][Y] :=
  (Polynomial.map Polynomial.C v₀)
    + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)

/-- The `Y`-coefficients of the linear shape are the `X`-affine polynomials
`C (v₀.coeff t) + X · C (v₁.coeff t)`. -/
theorem coeff_linearShape (v₀ v₁ : F[X]) (t : ℕ) :
    (linearShape v₀ v₁).coeff t
      = Polynomial.C (v₀.coeff t) + Polynomial.X * Polynomial.C (v₁.coeff t) := by
  rw [linearShape, Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]

/-- **`hdegX` by construction**: the linear shape has `X`-degree at most `1`. -/
theorem degreeX_linearShape_le_one (v₀ v₁ : F[X]) :
    Polynomial.Bivariate.degreeX (linearShape v₀ v₁) ≤ 1 := by
  rw [FiniteSeriesToPoly.degreeX_le_one_iff_forall_coeff_natDegree_le_one]
  intro n
  rw [coeff_linearShape]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · simp
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp

/-- The top (`Y`-)degree of the linear shape is bounded by the component degrees. -/
theorem natDegree_linearShape_le (v₀ v₁ : F[X]) :
    (linearShape v₀ v₁).natDegree ≤ max v₀.natDegree v₁.natDegree := by
  rw [linearShape]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans (Polynomial.natDegree_map_le) (le_max_left _ _)
  · refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, zero_add]
    exact le_trans (Polynomial.natDegree_map_le) (le_max_right _ _)

/-- **Tail-coefficient vanishing by construction**: past the component degrees the
`Y`-coefficients of the linear shape are zero (the `htailP` input of Brick C3). -/
theorem coeff_linearShape_eq_zero {v₀ v₁ : F[X]} {N : ℕ}
    (h₀ : v₀.natDegree < N) (h₁ : v₁.natDegree < N) {t : ℕ} (ht : N ≤ t) :
    (linearShape v₀ v₁).coeff t = 0 := by
  rw [coeff_linearShape,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h₀ ht),
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h₁ ht)]
  simp

end LinearShape

section Interpolant

variable [DecidableEq F]

/-- The Lagrange interpolant of the value family `a` at the node set `s` (node map `id`),
with degree `< #s`. -/
noncomputable def interpolant (s : Finset F) (a : F → F) : F[X] :=
  Lagrange.interpolate s id a

/-- The interpolant takes the prescribed value at each node. -/
theorem interpolant_eval_node {s : Finset F} (a : F → F) {z : F} (hz : z ∈ s) :
    (interpolant s a).eval z = a z := by
  simpa using Lagrange.eval_interpolate_at_node a (Set.injOn_id _) hz

/-- The interpolant has degree `< #s` (`natDegree` form; needs a nonempty node set for the
zero-polynomial corner). -/
theorem natDegree_interpolant_lt {s : Finset F} (hs : s.Nonempty) (a : F → F) :
    (interpolant s a).natDegree < s.card := by
  rcases eq_or_ne (interpolant s a) 0 with h0 | hne
  · rw [h0, Polynomial.natDegree_zero]
    exact hs.card_pos
  · have hinj : Set.InjOn id (↑s : Set F) := fun x _ y _ hxy => hxy
    exact (Polynomial.natDegree_lt_iff_degree_lt hne).mpr
      (by simpa using Lagrange.degree_interpolate_lt a hinj)

/-- **Brick C2 — the interpolated representative.**  Interpolate the two per-`z` value
families at the node set `s` and assemble them in the bundle's eval shape. -/
noncomputable def interpolatedRep (s : Finset F) (a₀ a₁ : F → F) : F[X][Y] :=
  linearShape (interpolant s a₀) (interpolant s a₁)

/-- **`hdegX` by construction** for the interpolated representative. -/
theorem degreeX_interpolatedRep_le_one (s : Finset F) (a₀ a₁ : F → F) :
    Polynomial.Bivariate.degreeX (interpolatedRep s a₀ a₁) ≤ 1 :=
  degreeX_linearShape_le_one _ _

/-- The interpolated representative has top degree `< #s` (the truncation index of the §6.2
argument; this is the `T := Ppoly.natDegree` budget of the off-centre assembly). -/
theorem natDegree_interpolatedRep_lt {s : Finset F} (hs : s.Nonempty) (a₀ a₁ : F → F) :
    (interpolatedRep s a₀ a₁).natDegree < s.card :=
  lt_of_le_of_lt (natDegree_linearShape_le _ _)
    (max_lt (natDegree_interpolant_lt hs a₀) (natDegree_interpolant_lt hs a₁))

/-- The tail `Y`-coefficients of the interpolated representative vanish from `#s` on
(the `htailP` input of Brick C3, **by construction**). -/
theorem coeff_interpolatedRep_eq_zero {s : Finset F} (hs : s.Nonempty) (a₀ a₁ : F → F)
    {t : ℕ} (ht : s.card ≤ t) :
    (interpolatedRep s a₀ a₁).coeff t = 0 :=
  coeff_linearShape_eq_zero (natDegree_interpolant_lt hs a₀)
    (natDegree_interpolant_lt hs a₁) ht

/-- **The per-node evaluation fact**: specializing the interpolated representative at a node
`z ∈ s` yields the affine polynomial `C (a₀ z) + (a₁ z) • X` — the exact output shape of the
`hPz` lane (`eval_linear_representative`). -/
theorem eval_interpolatedRep_at_node {s : Finset F} (a₀ a₁ : F → F) {z : F} (hz : z ∈ s) :
    (interpolatedRep s a₀ a₁).eval (Polynomial.C z)
      = Polynomial.C (a₀ z) + (a₁ z) • (Polynomial.X : F[X]) := by
  rw [interpolatedRep, linearShape, BetaToCurveCoeffPolys.eval_linear_representative,
    interpolant_eval_node a₀ hz, interpolant_eval_node a₁ hz]

end Interpolant

/-! ## Part 3 — Brick C3: the per-coefficient identity skeleton -/

section Cleared

variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)

/-- **The cleared per-coefficient competitor.**  The `𝒪 H`-element
`mk (C c) · (W_𝒪^{t+1} · ξ^{e_t})` whose embedding is `lift c` times the `αFromBeta`
denominator: the identity `betaRec t = clearedCoeff c t` in `𝒪 H` is the **cleared** form of
the per-coefficient series identity `αFromBeta t = liftToFunctionField c`, and it lives in
exactly the Lemma-A.1 counting currency. -/
noncomputable def clearedCoeff (c : F[X]) (t : ℕ) : 𝒪 H :=
  (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C c) : 𝒪 H)
    * (W_𝒪 H ^ (t + 1) * ξ x₀ R H hHyp ^ henselDenominatorExponent t)

/-- The `π_z`-reading of the cleared competitor: `c(z)` times the per-place denominator of
the canonical place series (`PlaceSeriesCanonical.aBetaPlace`) — the matching-lane per-`z`
currency. -/
theorem pi_z_clearedCoeff (c : F[X]) (t : ℕ) {z : F}
    (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) (clearedCoeff x₀ R H hHyp c t)
      = c.eval z * ((π_z z root) (W_𝒪 H) ^ (t + 1)
          * (π_z z root) (ξ x₀ R H hHyp) ^ henselDenominatorExponent t) := by
  rw [clearedCoeff, map_mul, map_mul, map_pow, map_pow, π_z_mk, Polynomial.evalEval_C]

/-- **The division-clearing step.**  If `betaRec t` equals the cleared competitor in `𝒪 H`,
then the Hensel-lift coefficient is exactly the lifted ground polynomial:
`αFromBeta t = liftToFunctionField c`.  Needs only `embedding ξ ≠ 0` (the in-tree named
hypothesis currency); the `W`-factor is nonzero unconditionally
(`liftToFunctionField_leadingCoeff_ne_zero`). -/
theorem alphaFromBeta_eq_lift_of_betaRec_eq_cleared
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0) {c : F[X]} {t : ℕ}
    (heq : betaRec x₀ R H hHyp Bcoeff t = clearedCoeff x₀ R H hHyp c t) :
    BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t
      = liftToFunctionField (H := H) c := by
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero
  have hden : (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
      * (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent t ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hξ)
  rw [show BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t
      = embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t)
        / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent t)
    from rfl]
  rw [heq, clearedCoeff, map_mul, map_mul, embeddingOf𝒪Into𝕃_mk, liftBivariate_C,
    embeddingOf𝒪Into𝕃_W_𝒪_pow, map_pow, W_𝕃]
  exact mul_div_cancel_right₀ _ hden

/-- **C1 + clearing: the per-coefficient identity from counting.**  Per-`z` agreement of
`betaRec t` with the cleared competitor at more than `B · d_H` places, at the loose budget
`B` for the difference, pins the Hensel-lift coefficient:
`αFromBeta t = liftToFunctionField c`. -/
theorem alphaFromBeta_eq_lift_of_counting
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0) {c : F[X]} {t : ℕ}
    {T : Finset F} (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hvan : ∀ z ∈ T, (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t)
      = (π_z z (root z)) (clearedCoeff x₀ R H hHyp c t))
    {B : ℕ}
    (hw : weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t - clearedCoeff x₀ R H hHyp c t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card) :
    BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t
      = liftToFunctionField (H := H) c :=
  alphaFromBeta_eq_lift_of_betaRec_eq_cleared x₀ R H hHyp Bcoeff hξ
    (eq_of_pi_z_eq_on_finset hH D hD root hvan hw hcard)

/-- The loose `Λ`-budget of the cleared competitor:
`Λ(clearedCoeff c t) ≤ deg c + ((t+1)(D − d_H) + e_t · bξ)` from any `ξ`-budget `bξ`.
All inequalities are the proven sub-multiplicative calculus — no sharp claim anywhere. -/
theorem weight_clearedCoeff_le {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    {bξ : ℕ} (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (c : F[X]) (t : ℕ) :
    weight_Λ_over_𝒪 hH (clearedCoeff x₀ R H hHyp c t) D
      ≤ (WithBot.some (c.natDegree
          + ((t + 1) * (D - H.natDegree) + henselDenominatorExponent t * bξ)) :
            WithBot ℕ) := by
  have hWreg : W_reg H = W_𝒪 H := rfl
  refine weight_Λ_over_𝒪_mul_le_of_le hD hH (weight_Λ_over_𝒪_C_le hD hH c) ?_
  refine weight_Λ_over_𝒪_mul_le_of_le hD hH ?_
    (weight_Λ_over_𝒪_pow_le_of_le hD hH hξw (henselDenominatorExponent t))
  rw [← hWreg]
  exact weight_Λ_over_𝒪_pow_le_of_le hD hH (weight_Λ_over_𝒪_W_reg_le hD hH) (t + 1)

/-- The loose `Λ`-budget of the **difference** `betaRec t − clearedCoeff c t` from a `betaRec`
budget `bβ` (e.g. the proven graded budget `betaRec_weight_le_graded`) and a `ξ`-budget
`bξ`. -/
theorem weight_betaRec_sub_clearedCoeff_le
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    {bβ bξ : ℕ} {t : ℕ}
    (hβw : weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some bβ : WithBot ℕ))
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (c : F[X]) :
    weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t - clearedCoeff x₀ R H hHyp c t) D
      ≤ (WithBot.some (max bβ (c.natDegree
          + ((t + 1) * (D - H.natDegree) + henselDenominatorExponent t * bξ))) :
            WithBot ℕ) :=
  weight_Λ_over_𝒪_sub_le_of_le hD hH hβw (weight_clearedCoeff_le x₀ R H hHyp hD hH hξw c t)

/-- **Brick C3 — the `hrep` skeleton.**  For ANY candidate representative `Ppoly`, the bundle
field `hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal …` follows from:
* `hvan`/`hw`/`hcard` — head coefficients (`t < k`): per-`z` agreement of `betaRec t` with the
  cleared competitor at the loose budget (Brick C1 + the clearing step);
* `htailP` — tail coefficients of `Ppoly` vanish from `k` on (for the interpolant: by
  construction, `coeff_interpolatedRep_eq_zero`);
* `htailα` — the in-tree `htail` content `αFromBeta t = 0` for `t ≥ k`.

This converts `hrep` into exactly the matching lane's per-`z` currency, at the loose proven
budgets — the Claim 5.9 bypass. -/
theorem hrep_of_cleared_counting
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0)
    {Ppoly : F[X][Y]} {k : ℕ}
    (root : (z : F) → rationalRoot (H_tilde' H) z) {T : Finset F}
    (hvan : ∀ t, t < k → ∀ z ∈ T,
      (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t)
        = (π_z z (root z)) (clearedCoeff x₀ R H hHyp (Ppoly.coeff t) t))
    {B : ℕ}
    (hw : ∀ t, t < k → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t - clearedCoeff x₀ R H hHyp (Ppoly.coeff t) t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card)
    (htailP : ∀ t, k ≤ t → Ppoly.coeff t = 0)
    (htailα : ∀ t, k ≤ t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff := by
  ext t
  rw [coeff_polyToPowerSeries𝕃, BetaToCurveCoeffPolys.coeff_gammaLocal]
  rcases Nat.lt_or_ge t k with htk | htk
  · exact (alphaFromBeta_eq_lift_of_counting x₀ R H hHyp Bcoeff hH D hD hξ root
      (hvan t htk) (hw t htk) hcard).symm
  · rw [htailP t htk, map_zero, htailα t htk]

end Cleared

/-! ## Part 4 — the assembled producer: the bundle's `(Ppoly, hrep, hdegX)` pair -/

section Capstone

variable [DecidableEq F]

/-- **The interpolated-representative producer (Bricks C1+C2+C3 assembled).**  From the
per-`z` counting data at the loose budgets, the interpolant of the value families `a₀ a₁` at
the `k`-element node set `s` satisfies BOTH terminal bundle fields:
`hrep : polyToPowerSeries𝕃 H (interpolatedRep s a₀ a₁) = gammaLocal …` and
`hdegX : degreeX (interpolatedRep s a₀ a₁) ≤ 1` (plus the truncation-index bound
`natDegree < #s`).  The tail-`Ppoly` obligation of the skeleton is discharged **by
construction**; the residual hypotheses are exactly the matching-lane per-`z` currency
(`hvan`), the loose budgets (`hw`, dischargeable through
`weight_betaRec_sub_clearedCoeff_le` + `betaRec_weight_le_graded`), the §6 counting-set
largeness (`hcard`), the `ξ`-nonvanishing (`hξ`), and the in-tree `htail` content
(`htailα`). -/
theorem interpolatedRep_hrep_hdegX
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0)
    {s : Finset F} (hs : s.Nonempty) (a₀ a₁ : F → F)
    (root : (z : F) → rationalRoot (H_tilde' H) z) {T : Finset F}
    (hvan : ∀ t, t < s.card → ∀ z ∈ T,
      (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t)
        = (π_z z (root z))
            (clearedCoeff x₀ R H hHyp ((interpolatedRep s a₀ a₁).coeff t) t))
    {B : ℕ}
    (hw : ∀ t, t < s.card → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t
          - clearedCoeff x₀ R H hHyp ((interpolatedRep s a₀ a₁).coeff t) t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card)
    (htailα : ∀ t, s.card ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    polyToPowerSeries𝕃 H (interpolatedRep s a₀ a₁)
        = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff
      ∧ Polynomial.Bivariate.degreeX (interpolatedRep s a₀ a₁) ≤ 1
      ∧ (interpolatedRep s a₀ a₁).natDegree < s.card :=
  ⟨hrep_of_cleared_counting x₀ R H hHyp Bcoeff hH D hD hξ root hvan hw hcard
      (fun t ht => coeff_interpolatedRep_eq_zero hs a₀ a₁ ht) htailα,
    degreeX_interpolatedRep_le_one s a₀ a₁,
    natDegree_interpolatedRep_lt hs a₀ a₁⟩

/-- **Existential form** — the bundle's terminal per-`P` field pair: a representative with
`hrep` and `hdegX` (and top degree `< #s`) **exists**, produced by interpolation at the loose
budgets.  This is the satisfiable replacement for the refuted sharp-Claim-5.9 lane. -/
theorem exists_representative_pair
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0)
    {s : Finset F} (hs : s.Nonempty) (a₀ a₁ : F → F)
    (root : (z : F) → rationalRoot (H_tilde' H) z) {T : Finset F}
    (hvan : ∀ t, t < s.card → ∀ z ∈ T,
      (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t)
        = (π_z z (root z))
            (clearedCoeff x₀ R H hHyp ((interpolatedRep s a₀ a₁).coeff t) t))
    {B : ℕ}
    (hw : ∀ t, t < s.card → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t
          - clearedCoeff x₀ R H hHyp ((interpolatedRep s a₀ a₁).coeff t) t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card)
    (htailα : ∀ t, s.card ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff
        ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
        ∧ Ppoly.natDegree < s.card :=
  ⟨interpolatedRep s a₀ a₁,
    interpolatedRep_hrep_hdegX x₀ R H hHyp Bcoeff hH D hD hξ hs a₀ a₁ root
      hvan hw hcard htailα⟩

end Capstone

end InterpolatedRepresentative

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.InterpolatedRepresentative.weight_Λ_over_𝒪_sub_le_of_le
#print axioms ArkLib.InterpolatedRepresentative.eq_of_pi_z_eq_on_finset
#print axioms ArkLib.InterpolatedRepresentative.linearShape
#print axioms ArkLib.InterpolatedRepresentative.coeff_linearShape
#print axioms ArkLib.InterpolatedRepresentative.degreeX_linearShape_le_one
#print axioms ArkLib.InterpolatedRepresentative.natDegree_linearShape_le
#print axioms ArkLib.InterpolatedRepresentative.coeff_linearShape_eq_zero
#print axioms ArkLib.InterpolatedRepresentative.interpolant
#print axioms ArkLib.InterpolatedRepresentative.interpolant_eval_node
#print axioms ArkLib.InterpolatedRepresentative.natDegree_interpolant_lt
#print axioms ArkLib.InterpolatedRepresentative.interpolatedRep
#print axioms ArkLib.InterpolatedRepresentative.degreeX_interpolatedRep_le_one
#print axioms ArkLib.InterpolatedRepresentative.natDegree_interpolatedRep_lt
#print axioms ArkLib.InterpolatedRepresentative.coeff_interpolatedRep_eq_zero
#print axioms ArkLib.InterpolatedRepresentative.eval_interpolatedRep_at_node
#print axioms ArkLib.InterpolatedRepresentative.clearedCoeff
#print axioms ArkLib.InterpolatedRepresentative.pi_z_clearedCoeff
#print axioms ArkLib.InterpolatedRepresentative.alphaFromBeta_eq_lift_of_betaRec_eq_cleared
#print axioms ArkLib.InterpolatedRepresentative.alphaFromBeta_eq_lift_of_counting
#print axioms ArkLib.InterpolatedRepresentative.weight_clearedCoeff_le
#print axioms ArkLib.InterpolatedRepresentative.weight_betaRec_sub_clearedCoeff_le
#print axioms ArkLib.InterpolatedRepresentative.hrep_of_cleared_counting
#print axioms ArkLib.InterpolatedRepresentative.interpolatedRep_hrep_hdegX
#print axioms ArkLib.InterpolatedRepresentative.exists_representative_pair
