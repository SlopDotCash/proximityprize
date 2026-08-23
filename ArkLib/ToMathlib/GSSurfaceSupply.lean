/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DecodedCapstonesCorrected
import ArkLib.ToMathlib.GSFactorData
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSIntegerRepresentative

/-!
# Issue #304 — the GLOBAL GS inputs of the decoded capstones (`GSSurfaceSupply`)

The F6-repaired global capstone
`DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected` consumes five global
GS-side inputs about `(x₀, R, H, w, G, k)`:

* `hHyp  : Hypotheses x₀ R H`                       (Claim-A.2 hypotheses)
* `hsplit : Bivariate.evalX (C x₀) R = H * G`       (the GS split)
* `hdvd  : (Y′ − C w) ∣ R`                          (the decoded SURFACE factor, trivariate)
* `hdeg  : w.natDegree < k`                          (RS degree of the surface)
* `hR    : R.Separable`                              (trivariate separability)

This file determines, brick by brick, which of these the in-tree GS existence chain
already produces, builds the producers that are genuinely reachable, isolates what is open
as named `Prop`s, and composes the deepest reachable capstone.

## What the in-tree chain produces (the audit)

* **`hHyp` — PRODUCED for the graph objects.**  `ProximityGap.claimA2_hypotheses_graph`
  (wired into `GSFactorData.Bundle.hHyp` by `GSFactorData.of_section5Inputs`) is exactly
  `Hypotheses x₀ R_graph H_graph`.
* **`hsplit` — DERIVED (trivial choose).**  `Hypotheses.dvd_evalX` is the divisibility
  `H ∣ evalX (C x₀) R`; `hsplit_of_hypotheses` / `cofactor` / `cofactor_spec` extract the
  cofactor `G`.  This eliminates `hsplit` from the capstone's input set.
* **`hdvd` — REFUTED for the graph `R`, PRODUCED for the integer representative `Q₀`.**
  - *F8 finding (`not_surface_dvd_of_irreducible`)*: the graph `R` is **irreducible**
    (`ProximityGap.pg_Rset_irreducible` + `R_graph_mem_pg_Rset`), and a linear `Y`-factor
    of an irreducible trivariate forces `natDegreeY R = 1`
    (`natDegree_eq_one_of_X_sub_C_dvd_of_irreducible`).  Jointly with the capstone's own
    `hd2 : 2 ≤ natDegreeY R` the input `hdvd` is therefore **unsatisfiable for every graph
    `R`** — the surface factor can only live in a *reducible* trivariate, i.e. in the full
    GS interpolant, never in its irreducible factor.
  - *The producible route (`surface_dvd_integerRep`, `exists_surface_of_decoded`)*: at the
    level of the **integer representative `Q₀`** of the `K = F(Z)` GS interpolant
    (`exists_integer_representative`), the K-level decoded factor `(Y − C p) ∣ Q`
    (`gs_divisibility_over_ratfunc`) descends to the genuine trivariate surface factor
    `(Y′ − C w) ∣ Q₀` with `w = affinePairLift a b` the integral affine-pair lift
    (`affine_pair_of_hammingDist` + `integer_representative_eval_eq_zero`).
* **`hdeg` — PRODUCED alongside.**  The GS construction bounds the RS degree of the
  decoded codeword in the **middle (`X`) variable**: `deg_X p ≤ k − 1`
  (`GuruswamiSudan.codewordToPoly_degree_le`), and the affine-pair lift preserves it
  (`affinePairLift_natDegree_lt`), giving exactly the consumer's `w.natDegree < k`.
* **`hR` — OPEN (named `SurfaceSeparabilitySupply`).**  The chain produces only the
  *bivariate* separability `(evalX (C x₀) R).Separable` (inside `Hypotheses`); trivariate
  separability of `Q₀` over the non-field base `F[Z][X]` has no in-tree producer.  The
  only producible case is the linear one (`separable_of_eq_surface`).

## Capstones

* `gammaGenuine_eq_trunc_of_surface` — the consumer with `hsplit` ELIMINATED
  (`G := cofactor hHyp` internally); input set = consumer minus `hsplit`.
* `gammaGenuine_eq_trunc_of_decoded_integerRep` — **the deepest reachable composition**:
  `R := Q₀`, `w := decodedSurface …` produced from the in-tree GS chain, `hsplit`, `hdvd`,
  `hdeg` all INTERNAL.  Residual inputs: `hHyp` for `Q₀` (named open
  `IntegerRepCentreSupply` shape), `hξ`, the numeric degree side conditions, `hrepT` (the
  documented `GenuinePpolyConverter` loop), `hR` (open `SurfaceSeparabilitySupply`), the
  two certificate nonvanishings and the field-size inequality.

## Satisfiability boundary (inherited, documented)

The certificate input `hbr` is unsatisfiable for `d_H ≥ 2` (F7,
`BranchSeparationUnsat.branchCert_eq_zero`), so the composed capstones are non-vacuously
instantiable only at `H.natDegree = 1`; and by F8 (this file) the surface-bearing `R` must
be reducible — which the integer representative `Q₀` is.  Neither fact is hidden inside a
proof; both are kernel-proved refutations of the complementary regimes.

## References
* [BCIKS20] §5, Appendix A; Hab25 §3 Steps S2/S4/S6; the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine
open ProximityGap Finset

attribute [local instance] Classical.propDecidable

namespace ArkLib

namespace GSSurfaceSupply

variable {F : Type} [Field F]

/-! ## §1 — `hsplit` from `Hypotheses` (trivial choose, but needed glue) -/

/-- **`hsplit` from the Claim-A.2 `Hypotheses`.**  The `dvd_evalX` field of `Hypotheses` is
exactly the divisibility `H ∣ evalX (C x₀) R`; destructuring it gives the GS split
`evalX (C x₀) R = H * G` the decoded capstones consume.  This eliminates `hsplit` from the
capstone input set wherever `hHyp` is available (in particular for the graph objects, where
`hHyp = claimA2_hypotheses_graph` via `GSFactorData.Bundle.hHyp`). -/
theorem hsplit_of_hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    ∃ G : F[X][Y], Bivariate.evalX (Polynomial.C x₀) R = H * G := by
  obtain ⟨G, hG⟩ := hHyp.dvd_evalX
  exact ⟨G, hG⟩

/-- The chosen GS cofactor `G` of the split `evalX (C x₀) R = H * G`. -/
noncomputable def cofactor {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) : F[X][Y] :=
  (hsplit_of_hypotheses hHyp).choose

/-- The chosen cofactor witnesses the GS split — the exact `hsplit` shape of
`gammaGenuine_eq_trunc_global_corrected`. -/
theorem cofactor_spec {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    Bivariate.evalX (Polynomial.C x₀) R = H * cofactor hHyp :=
  (hsplit_of_hypotheses hHyp).choose_spec

/-- **`hsplit` for the graph objects.**  The `GSFactorData.Bundle` (whose `hHyp` field is
`claimA2_hypotheses_graph`) already carries everything needed for the GS split. -/
theorem hsplit_of_bundle [DecidableEq F] [Finite F] {x₀ : F}
    (b : GSFactorData.Bundle (F := F) x₀) :
    ∃ G : F[X][Y], Bivariate.evalX (Polynomial.C x₀) b.R = b.H * G :=
  hsplit_of_hypotheses b.hHyp

/-! ## §2 — F8: the surface factor is REFUTED for every irreducible trivariate

The graph `R` produced by the §5 chain is irreducible (`pg_Rset_irreducible`).  A linear
`Y`-factor `(Y′ − C w)` of an irreducible polynomial over the domain `F[Z][X]` forces
`Y`-degree one — jointly unsatisfiable with the capstone's `hd2 : 2 ≤ natDegreeY R`.
The `hdvd` input can therefore NEVER be discharged for the graph objects; the surface
lives one level up, in the reducible full interpolant (§3 below). -/

/-- A linear factor of an irreducible polynomial over a commutative domain forces degree
one (the generic form of `BranchSeparationUnsat.natDegree_eq_one_of_X_sub_C_dvd_irreducible`,
usable at any coefficient ring — here at `F[Z][X]`). -/
theorem natDegree_eq_one_of_X_sub_C_dvd_of_irreducible {A : Type*} [CommRing A] [IsDomain A]
    {p : A[X]} {v : A} (hirr : Irreducible p)
    (hdvd : (Polynomial.X - Polynomial.C v) ∣ p) : p.natDegree = 1 := by
  obtain ⟨c, hc⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hc with hu | hu
  · exact absurd hu (Polynomial.not_isUnit_X_sub_C v)
  · have hc0 : c ≠ 0 := fun h => by
      rw [h, mul_zero] at hc
      exact hirr.ne_zero hc
    have hX0 : (Polynomial.X - Polynomial.C v) ≠ 0 := Polynomial.X_sub_C_ne_zero v
    have hcdeg : c.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hc, Polynomial.natDegree_mul hX0 hc0, Polynomial.natDegree_X_sub_C, hcdeg]

/-- **F8 (degree form).**  A trivariate surface factor `(Y′ − C w) ∣ R` of an irreducible
`R` forces `natDegreeY R = 1`. -/
theorem natDegreeY_eq_one_of_surface_dvd_of_irreducible {R : F[X][X][Y]} {w : F[X][Y]}
    (hirr : Irreducible R) (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    Bivariate.natDegreeY R = 1 :=
  natDegree_eq_one_of_X_sub_C_dvd_of_irreducible hirr hdvd

/-- **F8 (refutation form): the `hdvd` input of
`gammaGenuine_eq_trunc_global_corrected` is unsatisfiable for every irreducible `R` in the
capstone's own regime `hd2 : 2 ≤ natDegreeY R`.**  Since the §5 graph `R` is irreducible,
the surface factor can never be produced for the graph objects. -/
theorem not_surface_dvd_of_irreducible {R : F[X][X][Y]} {w : F[X][Y]}
    (hirr : Irreducible R) (hd2 : 2 ≤ Bivariate.natDegreeY R) :
    ¬ (Polynomial.X - Polynomial.C w) ∣ R := fun hdvd => by
  have h1 := natDegreeY_eq_one_of_surface_dvd_of_irreducible hirr hdvd
  rw [h1] at hd2
  omega

/-- **F8 for the §5 extraction set:** no member of `pg_Rset` (all of which are irreducible
normalized factors of the modified-Guruswami interpolant) of `Y`-degree `≥ 2` carries a
surface factor.  This covers the graph `R` via `R_graph_mem_pg_Rset`. -/
theorem not_surface_dvd_of_mem_pg_Rset [DecidableEq F]
    {n m : ℕ} (k : ℕ) {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {R : F[Z][X][Y]}
    (hR : R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) h_gs)
    (hd2 : 2 ≤ Bivariate.natDegreeY R) (w : F[X][Y]) :
    ¬ (Polynomial.X - Polynomial.C w) ∣ R :=
  not_surface_dvd_of_irreducible (pg_Rset_irreducible k h_gs R hR) hd2

/-! ## §3 — the surface factor IS produced at the integer-representative level

The K = F(Z) GS chain (`gs_existence_over_ratfunc` → `gs_divisibility_over_ratfunc` →
`affine_pair_of_hammingDist` → `exists_integer_representative`) ends one `dvd_iff_isRoot`
short of the trivariate surface: `integer_representative_eval_eq_zero` already gives
`eval w Q₀ = 0` for the integral affine-pair lift `w`.  These bricks close that gap and
package the consumer-shaped `hdvd` + `hdeg` pair. -/

/-- **The trivariate surface factor of the integer representative.**  If the K-level
matching factor `(Y − C p) ∣ Q` holds and `w` is an integral representative of `p`
(`w.map (algebraMap F[X] K) = p`), then the genuine trivariate surface factor divides the
integer representative: `(Y′ − C w) ∣ Q₀`.  This is the consumer's `hdvd` shape with
`R := Q₀`. -/
theorem surface_dvd_integerRep {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    {w : F[X][Y]} {p : (RatFunc F)[X]}
    (hw : w.map (algebraMap F[X] (RatFunc F)) = p)
    (hdvdK : (Polynomial.X - Polynomial.C p) ∣ Q) :
    (Polynomial.X - Polynomial.C w) ∣ Q₀ :=
  Polynomial.dvd_iff_isRoot.mpr
    (GuruswamiSudan.OverRatFunc.integer_representative_eval_eq_zero hrep hw
      (Polynomial.dvd_iff_isRoot.mp hdvdK))

/-- **The consumer's `hdeg` for the affine-pair lift.**  The GS construction bounds the
decoded codeword's RS degree in the middle (`X`) variable; the integral lift
`affinePairLift a b = a + Z·b` preserves it: `deg a, deg b < k ⟹ (a + Z·b).natDegree < k`. -/
theorem affinePairLift_natDegree_lt {a b : F[X]} {k : ℕ} (hk : k ≠ 0)
    (ha : a.degree < (k : WithBot ℕ)) (hb : b.degree < (k : WithBot ℕ)) :
    (GuruswamiSudan.OverRatFunc.affinePairLift a b).natDegree < k := by
  have haN : a.natDegree < k := by
    by_cases h0 : a = 0
    · simp [h0, Nat.pos_of_ne_zero hk]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ha
  have hbN : b.natDegree < k := by
    by_cases h0 : b = 0
    · simp [h0, Nat.pos_of_ne_zero hk]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hb
  have h1 : (a.map (Polynomial.C : F →+* F[X])).natDegree ≤ a.natDegree :=
    Polynomial.natDegree_map_le
  have h2 : (Polynomial.C (Polynomial.X : F[X]) *
      b.map (Polynomial.C : F →+* F[X])).natDegree ≤ b.natDegree :=
    le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_map_le
  have h3 := Polynomial.natDegree_add_le (a.map (Polynomial.C : F →+* F[X]))
    (Polynomial.C (Polynomial.X : F[X]) * b.map (Polynomial.C : F →+* F[X]))
  unfold GuruswamiSudan.OverRatFunc.affinePairLift
  exact lt_of_le_of_lt h3 (max_lt (lt_of_le_of_lt h1 haN) (lt_of_le_of_lt h2 hbN))

/-- **The packaged surface producer (the `hdvd` + `hdeg` pair from the in-tree GS chain).**
From the canonical K = F(Z) decoded-codeword data — the GS `Conditions` interpolant `Q`,
its integer representative `(d, Q₀)`, and a decoded RS codeword `p` within the GS Johnson
radius of the generic fold with agreement margin `k` — there exists a surface `w` with
*both* consumer inputs: `w.natDegree < k` and `(Y′ − C w) ∣ Q₀`. -/
theorem exists_surface_of_decoded {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hk0 : k ≠ 0)
    (p : ReedSolomon.code (GuruswamiSudan.OverRatFunc.liftedDomain ωs) k)
    (h_dist : (hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          ((GuruswamiSudan.OverRatFunc.liftedDomain ωs) i)) : ℝ) / n < gs_johnson k n m)
    (h_close : hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          (GuruswamiSudan.OverRatFunc.liftedDomain ωs i)) + k ≤ n) :
    ∃ w : F[X][Y], w.natDegree < k ∧ (Polynomial.X - Polynomial.C w) ∣ Q₀ := by
  have hdvdK : Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p) ∣ Q :=
    GuruswamiSudan.OverRatFunc.gs_divisibility_over_ratfunc k m ωs f₀ f₁ hkn hm p hQ h_dist
  have hdegp : (ReedSolomon.codewordToPoly p).degree < (k : WithBot ℕ) := by
    by_cases h0 : (ReedSolomon.codewordToPoly p) = 0
    · rw [h0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe k
    · have h1 : (ReedSolomon.codewordToPoly p).natDegree ≤ k - 1 :=
        GuruswamiSudan.codewordToPoly_degree_le hkn p
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (by omega)
  obtain ⟨a, b, ha, hb, haffine⟩ :=
    GuruswamiSudan.OverRatFunc.affine_pair_of_hammingDist ωs f₀ f₁ hdegp h_close
  refine ⟨GuruswamiSudan.OverRatFunc.affinePairLift a b,
    affinePairLift_natDegree_lt hk0 ha hb, ?_⟩
  exact surface_dvd_integerRep hrep
    (by rw [GuruswamiSudan.OverRatFunc.affinePairLift_map, haffine]) hdvdK

/-- The chosen decoded surface of the integer representative (classical choice from
`exists_surface_of_decoded`), so the capstone residuals can be stated about ONE fixed
surface. -/
noncomputable def decodedSurface {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hk0 : k ≠ 0)
    (p : ReedSolomon.code (GuruswamiSudan.OverRatFunc.liftedDomain ωs) k)
    (h_dist : (hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          ((GuruswamiSudan.OverRatFunc.liftedDomain ωs) i)) : ℝ) / n < gs_johnson k n m)
    (h_close : hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          (GuruswamiSudan.OverRatFunc.liftedDomain ωs i)) + k ≤ n) : F[X][Y] :=
  (exists_surface_of_decoded ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).choose

/-- The chosen decoded surface has the consumer's RS degree bound (`hdeg`). -/
theorem decodedSurface_natDegree_lt {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hk0 : k ≠ 0)
    (p : ReedSolomon.code (GuruswamiSudan.OverRatFunc.liftedDomain ωs) k)
    (h_dist : (hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          ((GuruswamiSudan.OverRatFunc.liftedDomain ωs) i)) : ℝ) / n < gs_johnson k n m)
    (h_close : hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          (GuruswamiSudan.OverRatFunc.liftedDomain ωs i)) + k ≤ n) :
    (decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).natDegree < k :=
  (exists_surface_of_decoded ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).choose_spec.1

/-- The chosen decoded surface divides the integer representative (`hdvd`). -/
theorem decodedSurface_dvd {n k m : ℕ}
    (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hk0 : k ≠ 0)
    (p : ReedSolomon.code (GuruswamiSudan.OverRatFunc.liftedDomain ωs) k)
    (h_dist : (hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          ((GuruswamiSudan.OverRatFunc.liftedDomain ωs) i)) : ℝ) / n < gs_johnson k n m)
    (h_close : hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          (GuruswamiSudan.OverRatFunc.liftedDomain ωs i)) + k ≤ n) :
    (Polynomial.X - Polynomial.C
      (decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close)) ∣ Q₀ :=
  (exists_surface_of_decoded ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).choose_spec.2

/-! ## §4 — the genuinely open inputs, isolated as named `Prop`s -/

/-- **OPEN residual (#304): the centre-curve supply for the integer representative.**
The `hHyp : Hypotheses x₀ Q₀ H` input of the composed capstone needs an irreducible,
positive-degree curve `H(Z, Y)` dividing the centre slice `evalX (C x₀) Q₀` *separably*.
The in-tree chain produces this for the GRAPH `R` (`claimA2_hypotheses_graph`, packaged in
`GSFactorData.Bundle` — see `integerRepCentreSupply_of_bundle`), but for the integer
representative `Q₀` (the only trivariate that can carry the surface factor, by F8) it is
open: the obstruction is the separability `(evalX (C x₀) Q₀).Separable` over the non-field
base `F[Z]`, which even the graph route takes as a documented §5 standing input (`hsep`).
This `Prop` is hypothesis-shaped (an input the capstone consumes), never goal-shaped. -/
def IntegerRepCentreSupply (x₀ : F) (Q₀ : F[X][X][Y]) : Prop :=
  ∃ H : F[X][Y], Irreducible H ∧ 0 < H.natDegree ∧ Hypotheses x₀ Q₀ H

/-- The graph route DOES satisfy the centre-supply shape — for its own (irreducible) `R`.
This is the non-vacuity witness for `IntegerRepCentreSupply`; what is open is the same
supply for the reducible `Q₀`. -/
theorem integerRepCentreSupply_of_bundle [DecidableEq F] [Finite F] {x₀ : F}
    (b : GSFactorData.Bundle (F := F) x₀) :
    IntegerRepCentreSupply x₀ b.R :=
  ⟨b.H, b.hIrr.out, b.hH, b.hHyp⟩

/-- **OPEN residual (#304): trivariate separability (`hR : R.Separable`).**
`Polynomial.Separable` over the non-field base `F[Z][X]` demands a Bézout identity
`A·R + B·R′ = 1` *in the trivariate ring*; the §5 chain only ever produces (or assumes)
the bivariate `evalX`-level separability inside `Hypotheses`.  No in-tree producer exists
for the integer representative `Q₀`; the only producible case is the linear one
(`separable_of_eq_surface` below).  Hypothesis-shaped, never goal-shaped. -/
def SurfaceSeparabilitySupply (Q₀ : F[X][X][Y]) : Prop := Q₀.Separable

/-- The linear case of `SurfaceSeparabilitySupply` IS producible: a trivariate that *is* a
surface `Y′ − C w` is separable (its `Y`-derivative is `1`). -/
theorem separable_of_eq_surface {R : F[X][X][Y]} {w : F[X][Y]}
    (h : R = Polynomial.X - Polynomial.C w) : R.Separable :=
  h ▸ Polynomial.separable_X_sub_C

/-! ## §5 — the composed capstones -/

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable [Fintype F] [DecidableEq F]

/-- **The global capstone with `hsplit` ELIMINATED.**  As
`DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected`, but the GS split is
derived internally from `hHyp` (`G := cofactor hHyp`); the two certificate nonvanishings
and the field-size inequality are now stated about the chosen cofactor.  Input set =
consumer minus `hsplit`.  (Satisfiability boundary, inherited and documented: `hbr` forces
`H.natDegree = 1` by F7, and `hdvd` + `hd2` force `R` reducible by F8.) -/
theorem gammaGenuine_eq_trunc_of_surface {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    (hbr : (cofactor hHyp).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + (((cofactor hHyp).eval (w.eval (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval
                (w.eval (Polynomial.C x₀))).natDegree
        < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected hHyp hξ hD hH hmonic
    hd2 hdHD hD_Rx0 hRgrade hrepT (cofactor_spec hHyp) hdeg hdvd hR hbr hxi hbig

/-- **THE DEEPEST REACHABLE COMPOSITION: Claim 5.8′ for the integer representative, with
`hsplit`, `hdvd`, `hdeg` all INTERNAL.**  The trivariate is the integer representative
`Q₀` of the K = F(Z) GS interpolant — the only surface-bearing choice (F8) — and the
surface is `decodedSurface …`, produced end-to-end from the in-tree GS chain
(`gs_divisibility_over_ratfunc` + `affine_pair_of_hammingDist` +
`integer_representative_eval_eq_zero`).  Residual inputs, each named and honest:

* `hHyp` — the open `IntegerRepCentreSupply` content for `Q₀` (centre curve + separable
  centre slice);
* `hξ`, the numeric degree side conditions, `hbig` — finite global data;
* `hrepT` — the corrected representative (the documented `GenuinePpolyConverter` loop;
  producible at monic `d_H ≤ 2` from the truncation itself);
* `hR` — the open `SurfaceSeparabilitySupply Q₀`;
* `hbr`, `hxi` — the certificate nonvanishings (satisfiable only at `H.natDegree = 1`,
  by F7). -/
theorem gammaGenuine_eq_trunc_of_decoded_integerRep
    {n k m : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : F[X][X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m) (hk0 : k ≠ 0)
    (p : ReedSolomon.code (GuruswamiSudan.OverRatFunc.liftedDomain ωs) k)
    (h_dist : (hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          ((GuruswamiSudan.OverRatFunc.liftedDomain ωs) i)) : ℝ) / n < gs_johnson k n m)
    (h_close : hammingDist (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
        (fun i => (ReedSolomon.codewordToPoly p).eval
          (GuruswamiSudan.OverRatFunc.liftedDomain ωs i)) + k ≤ n)
    {x₀ : F} (hHyp : Hypotheses x₀ Q₀ H)
    (hξ : ξ x₀ Q₀ H hHyp ≠ 0)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY Q₀)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) Q₀))
    (hRgrade : ∀ j, Bivariate.degreeX (Q₀.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ Q₀ H hHyp)
    (hR : SurfaceSeparabilitySupply Q₀)
    (hbr : (cofactor hHyp).eval
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ Q₀ H hHyp)).eval
      ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
        (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY Q₀) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + (((cofactor hHyp).eval
              ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
                (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ Q₀ H hHyp)).eval
                ((decodedSurface ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close).eval
                  (Polynomial.C x₀))).natDegree
        < Fintype.card F) :
    gammaGenuine x₀ Q₀ H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ Q₀ H hHyp)) : PowerSeries (𝕃 H)) :=
  gammaGenuine_eq_trunc_of_surface hHyp hξ hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hrepT
    (decodedSurface_natDegree_lt ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close)
    (decodedSurface_dvd ωs f₀ f₁ hrep hQ hkn hm hk0 p h_dist h_close)
    hR hbr hxi hbig

end GSSurfaceSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GSSurfaceSupply.hsplit_of_hypotheses
#print axioms ArkLib.GSSurfaceSupply.cofactor
#print axioms ArkLib.GSSurfaceSupply.cofactor_spec
#print axioms ArkLib.GSSurfaceSupply.hsplit_of_bundle
#print axioms ArkLib.GSSurfaceSupply.natDegree_eq_one_of_X_sub_C_dvd_of_irreducible
#print axioms ArkLib.GSSurfaceSupply.natDegreeY_eq_one_of_surface_dvd_of_irreducible
#print axioms ArkLib.GSSurfaceSupply.not_surface_dvd_of_irreducible
#print axioms ArkLib.GSSurfaceSupply.not_surface_dvd_of_mem_pg_Rset
#print axioms ArkLib.GSSurfaceSupply.surface_dvd_integerRep
#print axioms ArkLib.GSSurfaceSupply.affinePairLift_natDegree_lt
#print axioms ArkLib.GSSurfaceSupply.exists_surface_of_decoded
#print axioms ArkLib.GSSurfaceSupply.decodedSurface
#print axioms ArkLib.GSSurfaceSupply.decodedSurface_natDegree_lt
#print axioms ArkLib.GSSurfaceSupply.decodedSurface_dvd
#print axioms ArkLib.GSSurfaceSupply.IntegerRepCentreSupply
#print axioms ArkLib.GSSurfaceSupply.integerRepCentreSupply_of_bundle
#print axioms ArkLib.GSSurfaceSupply.SurfaceSeparabilitySupply
#print axioms ArkLib.GSSurfaceSupply.separable_of_eq_surface
#print axioms ArkLib.GSSurfaceSupply.gammaGenuine_eq_trunc_of_surface
#print axioms ArkLib.GSSurfaceSupply.gammaGenuine_eq_trunc_of_decoded_integerRep
