/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionGlobalLift
import ArkLib.ToMathlib.RadicalBranch
import ArkLib.ToMathlib.GSSurfaceMappedSeparability
import ArkLib.ToMathlib.FiberSectionCoherence

/-!
# The #304 end-to-end chain theorem over the final minimal surface

**GOAL (this file, Part 4)**: `Chain304.correlatedAgreement_of_minimal_surface` — ONE
theorem whose hypothesis list IS the final minimal external surface of #304 and whose
conclusion is the keystone `δ_ε_correlatedAgreementCurves` ([BCIKS20] Theorem 1.4 /
Claim A.2 conclusion) in the strict list-decoding regime `δ < 1 − √ρ`.

The surface (`Chain304.MinimalSurface304`, per decoding `(u, P)`):
1. the fiberwise GS-decoder outputs — per-centre sections `v : F → F[X]` rooting the
   fibers `evalX (C y) R` on a centre set `S`, their local `(k+1)`-coherence, and the
   global-lift budget `DX + deg_Y R · (k−1) < |S|`;
2. the §6 incidence fact `hOnH` at the (unique) produced global section;
3. the §6 counting budget `hbig` at the RADICAL branch certificate;
4. `MappedSliceSeparability` (the audit's irreducible separability residue — strictly
   weaker than `R.Separable`, see `RadicalAssembler`'s audit);
5. the graded budget side conditions (`hd2`/`hdHD`/`hD_Rx0`/`hRgrade`);
6. the series-level identifications `hsubst`/`hβHensel`/`hHensel`/`hdeg`.

Mechanically the chain is
`RootOn304.correlatedAgreement_listDecoding_strict_finOn` (the keystone front door)
∘ `RootOn304.Section5StrictDataFinOn.ofProducersOn_radical` (the radical bundle producer
underlying `hcoeffPoly_witness_of_producersOn_radical_sep`)
∘ `FiberSectionCoherence.section_dvd_global_of_local_coherence` (the fiberwise → global
section lift, interpolation rigidity + lifting budget).

**Build note (olean gap)**: `ArkLib/ToMathlib/RadicalAssembler.lean` is landed in-tree
but has NO olean in the current build, so it cannot be imported here; Parts 1–3 below
are its content inlined VERBATIM (same fully-qualified names, statements and proofs
unchanged) under its own three imports, which all have oleans
(`SectionGlobalLift`, `RadicalBranch`, `GSSurfaceMappedSeparability`).  When the tree
heals, delete Parts 1–3 and `import ArkLib.ToMathlib.RadicalAssembler` instead.
-/

/-! ## Parts 1–3 — `ArkLib/ToMathlib/RadicalAssembler.lean` inlined VERBATIM (no olean; see build note) -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open UniqueFactorizationMonoid
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace RadicalWire304

/-! ## Part 1 — the canonical radical package at the bundle

`split_canonical_radical` + `hbr_canonical_radical`: the `(hsplit, hbr)` package at
`radical (evalX (C x₀) b.R)`, with NO separability input — squarefreeness is free on the
radical; the only consequence of the bundle-internal `separable_evalX` consumed is
nonzeroness of the fiber. -/

section CanonicalRadical

variable {F : Type} [Field F] [DecidableEq F]

/-- Nonzeroness of the fiber — the ONLY consequence of `separable_evalX` used in the
radical split/branch production (zero squarefreeness content). -/
theorem fiber_ne_zero {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    Bivariate.evalX (Polynomial.C x₀) R ≠ 0 :=
  hHyp.separable_evalX.ne_zero

/-- **`H` divides the radical of the fiber**: irreducibility + `dvd_evalX` +
nonzeroness — no separability. -/
theorem H_dvd_radical_fiber {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hirr : Irreducible H) (hHyp : Hypotheses x₀ R H) :
    H ∣ radical (Bivariate.evalX (Polynomial.C x₀) R) :=
  (dvd_radical_iff_of_irreducible hirr (fiber_ne_zero hHyp)).mpr hHyp.dvd_evalX

/-- Degree budget: the radical of the fiber has no larger degree than the fiber. -/
theorem natDegree_radical_fiber_le {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    (radical (Bivariate.evalX (Polynomial.C x₀) R)).natDegree
      ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree :=
  RadicalBranch.natDegree_radical_le (fiber_ne_zero hHyp)

/-- The radical of the fiber is nonzero (unconditionally: `radical 0 = 1`). -/
theorem radical_fiber_ne_zero (x₀ : F) (R : F[X][X][Y]) :
    radical (Bivariate.evalX (Polynomial.C x₀) R) ≠ 0 :=
  radical_ne_zero

/-- The bivariate eval-degree bound (the fiber-level mirror of
`SectionGlobalLift.eval_section_natDegree_le`): `(Q.eval v).natDegree ≤ DX +
natDegree(Q)·natDegree(v)` whenever every `Y`-coefficient of `Q` has degree `≤ DX`. -/
theorem eval_natDegree_le_of_coeff_le {Q : F[X][Y]} {v : F[X]} {DX : ℕ}
    (hcoeff : ∀ j, (Q.coeff j).natDegree ≤ DX) :
    (Q.eval v).natDegree ≤ DX + Q.natDegree * v.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (v ^ j).natDegree ≤ j * v.natDegree := Polynomial.natDegree_pow_le
  have h2 : j * v.natDegree ≤ Q.natDegree * v.natDegree := Nat.mul_le_mul_right _ hjle
  have h3 := hcoeff j
  omega

variable [Fintype F]

/-- **K4 split (the canonical radical split)**: at the bundle's own monic `H`, the RADICAL
of the fiber splits with the canonical cofactor
`G' := radical (evalX (C x₀) b.R) /ₘ b.H`.  Mirror of
`BranchWire304.split_canonical`, with `dvd_evalX` upgraded through the radical — NO
separability input. -/
theorem split_canonical_radical {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    (hmonic : b.H.Monic) :
    radical (Bivariate.evalX (Polynomial.C x₀) b.R)
      = b.H * (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H) := by
  have hdvd : b.H ∣ radical (Bivariate.evalX (Polynomial.C x₀) b.R) :=
    H_dvd_radical_fiber b.hIrr.out b.hHyp
  have hmod : radical (Bivariate.evalX (Polynomial.C x₀) b.R) %ₘ b.H = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  conv_lhs => rw [← Polynomial.modByMonic_add_div
    (radical (Bivariate.evalX (Polynomial.C x₀) b.R)) b.H]
  rw [hmod, zero_add]

/-- **K4 branch certificate (`hbr` at the radical canonical cofactor)** from the single
§6-incidence fact `hOnH` — squarefreeness of the radical is FREE
(`squarefree_radical`): NO separability input.  Mirror of `BranchWire304.hbr_canonical`
with `branch_ne_zero_of_separable` replaced by
`RadicalBranch.branch_ne_zero_of_squarefree`. -/
theorem hbr_canonical_radical {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    (hmonic : b.H.Monic)
    {w : F[X][Y]} (hOnH : b.H.eval (w.eval (Polynomial.C x₀)) = 0) :
    (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
        (w.eval (Polynomial.C x₀)) ≠ 0 :=
  RadicalBranch.branch_ne_zero_of_squarefree squarefree_radical
    (split_canonical_radical b hmonic) hOnH

/-- **The K4 split-and-branch package at the bundle, existential form**
(`RadicalBranch.exists_radical_split_branch` packaged at the `GSFactorData.Bundle` shape):
from the single §6-incidence fact `hOnH`, SOME cofactor `G'` realizes both `hsplit` and
`hbr` at the radical of the fiber — no monicity needed (contrast the canonical pair above),
no separability input. -/
theorem split_branch_radical {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    {w : F[X][Y]} (hOnH : b.H.eval (w.eval (Polynomial.C x₀)) = 0) :
    ∃ G' : F[X][Y],
      radical (Bivariate.evalX (Polynomial.C x₀) b.R) = b.H * G' ∧
      G'.eval (w.eval (Polynomial.C x₀)) ≠ 0 :=
  RadicalBranch.exists_radical_split_branch (fiber_ne_zero b.hHyp) b.hIrr.out
    b.hHyp.dvd_evalX hOnH

/-! ### The degree-budget transfers
(`natDegree_radical_le` pushed through to the `gradedCardBudget` inequalities) -/

/-- Degree additivity of the canonical radical split (monic case). -/
theorem natDegree_radical_fiber_eq_add {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    (hmonic : b.H.Monic) :
    (radical (Bivariate.evalX (Polynomial.C x₀) b.R)).natDegree
      = b.H.natDegree
        + (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).natDegree := by
  have hsplit := split_canonical_radical b hmonic
  have hH_ne : b.H ≠ 0 := b.hIrr.out.ne_zero
  have hcof_ne : (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsplit
    exact radical_fiber_ne_zero x₀ b.R hsplit
  calc (radical (Bivariate.evalX (Polynomial.C x₀) b.R)).natDegree
      = (b.H * (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H)).natDegree := by
        rw [← hsplit]
    _ = b.H.natDegree
        + (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).natDegree :=
        Polynomial.natDegree_mul hH_ne hcof_ne

/-- **The cofactor degree budget**: the canonical radical cofactor has `Y`-degree at most
`natDegree(fiber) − natDegree(H)` (via `natDegree_radical_le`). -/
theorem natDegree_radical_cofactor_le {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    (hmonic : b.H.Monic) :
    (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).natDegree
      ≤ (Bivariate.evalX (Polynomial.C x₀) b.R).natDegree - b.H.natDegree := by
  have h1 := natDegree_radical_fiber_eq_add b hmonic
  have h2 := natDegree_radical_fiber_le b.hHyp
  omega

/-- **The radical branch-certificate degree budget**: with coefficient bounds `DX` on the
canonical radical cofactor, the §6 discriminant's degree is at most
`DX + (natDegree(fiber) − natDegree(H)) · natDegree(w(x₀))`. -/
theorem cert_radical_natDegree_le {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    (hmonic : b.H.Monic) {w : F[X][Y]} {DX : ℕ}
    (hcoeff : ∀ j, ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).coeff
      j).natDegree ≤ DX) :
    ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
        (w.eval (Polynomial.C x₀))).natDegree
      ≤ DX + ((Bivariate.evalX (Polynomial.C x₀) b.R).natDegree - b.H.natDegree)
          * (w.eval (Polynomial.C x₀)).natDegree := by
  have h1 := eval_natDegree_le_of_coeff_le (v := w.eval (Polynomial.C x₀)) hcoeff
  have h2 := natDegree_radical_cofactor_le b hmonic
  have h3 : (radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).natDegree
        * (w.eval (Polynomial.C x₀)).natDegree
      ≤ ((Bivariate.evalX (Polynomial.C x₀) b.R).natDegree - b.H.natDegree)
        * (w.eval (Polynomial.C x₀)).natDegree := Nat.mul_le_mul_right _ h2
  omega

/-- **The assembler-shaped `hbig` at the RADICAL certificate** — the exact counting field of
`ofProducersOn_radical` below, discharged from the numeric budget
`gradedCardBudget + (DX + (deg fiber − deg H)·deg w(x₀)) < |F|`. -/
theorem hbig_radical_of_coeff_budget {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    (hmonic : b.H.Monic) {w : F[X][Y]} {Ppoly : F[X][Y]} {DX : ℕ}
    (hcoeff : ∀ j, ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).coeff
      j).natDegree ≤ DX)
    (hbudget : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + (DX + ((Bivariate.evalX (Polynomial.C x₀) b.R).natDegree - b.H.natDegree)
            * (w.eval (Polynomial.C x₀)).natDegree)
        < Fintype.card F) :
    gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
            (w.eval (Polynomial.C x₀))).natDegree
        < Fintype.card F := by
  have h := cert_radical_natDegree_le b hmonic (w := w) hcoeff
  omega

/-- **The overlap transfer (divisibility)**: any radical-split cofactor divides any
fiber-split cofactor at the same `H` (cancel `H` against `radical_dvd_self`). -/
theorem radical_cofactor_dvd_cofactor {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    {G' Gf : F[X][Y]}
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) b.R) = b.H * G')
    (hsplitFib : Bivariate.evalX (Polynomial.C x₀) b.R = b.H * Gf) :
    G' ∣ Gf := by
  have hdvd : radical (Bivariate.evalX (Polynomial.C x₀) b.R)
      ∣ Bivariate.evalX (Polynomial.C x₀) b.R := radical_dvd_self
  rw [hsplitRad, hsplitFib] at hdvd
  exact (mul_dvd_mul_iff_left b.hIrr.out.ne_zero).mp hdvd

/-- The radical branch certificate divides the fiber branch certificate. -/
theorem cert_radical_dvd_cert_fiber {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    {G' Gf w : F[X][Y]}
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) b.R) = b.H * G')
    (hsplitFib : Bivariate.evalX (Polynomial.C x₀) b.R = b.H * Gf) :
    G'.eval (w.eval (Polynomial.C x₀)) ∣ Gf.eval (w.eval (Polynomial.C x₀)) :=
  Polynomial.eval_dvd (radical_cofactor_dvd_cofactor b hsplitRad hsplitFib)

/-- **The overlap-regime budget transfer**: wherever the FIBER certificate is nonzero (the
regime in which `ofProducersOn_global`'s own `hbr` holds), the assembler's original `hbig`
already implies the radical-certificate `hbig` — the radical route never worsens the §6
counting. -/
theorem hbig_radical_of_hbig_fiber {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    {G' Gf w : F[X][Y]} {Ppoly : F[X][Y]}
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) b.R) = b.H * G')
    (hsplitFib : Bivariate.evalX (Polynomial.C x₀) b.R = b.H * Gf)
    (hcertNe : Gf.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + (Gf.eval (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F) :
    gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + (G'.eval (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F := by
  have hdvd := cert_radical_dvd_cert_fiber b (w := w) hsplitRad hsplitFib
  have hle := Polynomial.natDegree_le_of_dvd hdvd hcertNe
  omega

end CanonicalRadical

/-! ## Part 2 — the radical decoded-root supply

`DecodedRootSupply.rootDecoded` re-run against the radical: the centre-fold linear factor
`(Y′ − C (w.eval (C x₀)))` is prime, hence divides `radical (evalX (C x₀) R)`; through the
radical split and per-place branch separation at the RADICAL cofactor, every such place
decodes a rational root of `H` — no squarefreeness of the fiber anywhere. -/

section DecodedRadical

variable {F : Type} [Field F] [DecidableEq F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine

/-- The centre-fold linear factor divides the RADICAL of the fiber (monic linear is prime,
hence irreducible; `centreFold_dvd` supplies divisibility into the fiber itself). -/
theorem centreFold_dvd_radical {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀)))
      ∣ radical (Bivariate.evalX (Polynomial.C x₀) R) :=
  (dvd_radical_iff_of_irreducible
      (Polynomial.prime_X_sub_C (w.eval (Polynomial.C x₀))).irreducible hQ0).mpr
    (DecodedRootSupply.centreFold_dvd hdvd)

/-- The centre fold of the surface roots the RADICAL of the fiber at every curve
parameter — mirror of `DecodedRootSupply.evalEval_evalX_eq_zero`. -/
theorem evalEval_radical_eq_zero {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F) :
    Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z)
      (radical (Bivariate.evalX (Polynomial.C x₀) R)) = 0 := by
  obtain ⟨c, hc⟩ := centreFold_dvd_radical (x₀ := x₀) hQ0 hdvd
  rw [hc, Polynomial.evalEval_mul]
  have hlin : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z)
      (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀))) = 0 := by
    rw [Polynomial.evalEval_sub, Polynomial.evalEval_X, Polynomial.evalEval_C, sub_self]
  rw [hlin, zero_mul]

/-- **The radical decoded branch root** — `DecodedRootSupply.rootDecoded` with the GS split
replaced by the RADICAL split `radical (evalX (C x₀) R) = H · G'` and branch separation at
the radical cofactor.  No squarefreeness of the fiber enters. -/
noncomputable def rootDecodedRadical {x₀ : F} {R : F[X][X][Y]} {w G' : F[X][Y]}
    (hH : 0 < H.natDegree)
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G' ≠ 0) :
    rationalRoot (H_tilde' H) z :=
  RationalRootSupply.rationalRoot_of_evalEval hH
    (RationalRootSupply.evalEval_eq_zero_of_factor_branch hsplitRad
      (evalEval_radical_eq_zero hQ0 hdvd z) hbranch)

/-- The radical decoded root's value, in general: `lc_H(z) · w(x₀, z)`. -/
theorem rootDecodedRadical_val {x₀ : F} {R : F[X][X][Y]} {w G' : F[X][Y]}
    (hH : 0 < H.natDegree)
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G' ≠ 0) :
    (rootDecodedRadical hH hQ0 hsplitRad hdvd z hbranch).1
      = (H.coeff H.natDegree).eval z * ((w.eval (Polynomial.C x₀)).eval z) := rfl

/-- The base-point fact at the radical decoded root (monic case): the value is exactly the
surface's centre value `w(x₀, z)` — mirror of
`DecodedRootSupply.rootDecoded_val_monic`. -/
theorem rootDecodedRadical_val_monic {x₀ : F} {R : F[X][X][Y]} {w G' : F[X][Y]}
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G' ≠ 0) :
    ((w.eval (Polynomial.C x₀)).eval z : F)
      = (rootDecodedRadical hH hQ0 hsplitRad hdvd z hbranch).1 := by
  rw [rootDecodedRadical_val]
  have h1 : H.coeff H.natDegree = 1 := hlc
  rw [h1, Polynomial.eval_one, one_mul]

/-- **The centre fold globally roots `H`, through the RADICAL**: mirror of
`XiCertReduction.H_eval_centreFold_eq_zero` with the GS split replaced by the radical split
and the branch certificate at the radical cofactor. -/
theorem H_eval_centreFold_eq_zero_radical {x₀ : F} {R : F[X][X][Y]} {w G' : F[X][Y]}
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G'.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    H.eval (w.eval (Polynomial.C x₀)) = 0 := by
  have hv0 : (radical (Bivariate.evalX (Polynomial.C x₀) R)).eval
      (w.eval (Polynomial.C x₀)) = 0 :=
    Polynomial.dvd_iff_isRoot.mp (centreFold_dvd_radical hQ0 hdvd)
  have h0 : H.eval (w.eval (Polynomial.C x₀)) * G'.eval (w.eval (Polynomial.C x₀)) = 0 := by
    rw [← Polynomial.eval_mul, ← hsplitRad]
    exact hv0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h hbr

/-- **The `ξ`-certificate value identity from the centre-fold root directly** — mirror of
`XiCertReduction.xiCert_eq_derivativeCert` with `H.eval v = 0` taken as input (which the
RADICAL package supplies through `H_eval_centreFold_eq_zero_radical`), so the GS split and
the fiber branch certificate are not consumed. -/
theorem xiCert_eq_derivativeCert_of_centreFold_root {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hHv : H.eval (w.eval (Polynomial.C x₀)) = 0) :
    (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))
      = ((Bivariate.evalX (Polynomial.C x₀) R).derivative).eval
          (w.eval (Polynomial.C x₀)) := by
  have hrep : canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)
      = (Bivariate.evalX (Polynomial.C x₀) R).derivative %ₘ H := by
    have hrfl : ξ x₀ R H hHyp
        = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ξ_pre x₀ R H) := rfl
    rw [hrfl, canonicalRepOf𝒪_mk hH,
      BCIKS20.HenselNumerator.ξ_pre_eq_of_monic H x₀ R hlc,
      evalX_derivative_comm x₀ R,
      BCIKS20.HenselNumerator.H_tilde'_eq_self_of_monic H hlc]
  have hdm := Polynomial.modByMonic_add_div
    ((Bivariate.evalX (Polynomial.C x₀) R).derivative) H
  have hev := congrArg (Polynomial.eval (w.eval (Polynomial.C x₀))) hdm
  rw [Polynomial.eval_add, Polynomial.eval_mul, hHv, zero_mul, add_zero] at hev
  rw [hrep]
  exact hev

/-- **The `ξ`-certificate is a UNIT from the centre-fold root** — mirror of
`XiCertReduction.xiCert_isUnit` on the radical-supplied `H.eval v = 0`.  (The fiber
separability consumed here is `hHyp.separable_evalX`, a `Hypotheses` structure field — see
the audit in the file docstring; the radical deletes the SQUAREFREENESS use, not this
derivative-unit use.) -/
theorem xiCert_isUnit_of_centreFold_root {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hHv : H.eval (w.eval (Polynomial.C x₀)) = 0) :
    IsUnit ((canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))) := by
  rw [xiCert_eq_derivativeCert_of_centreFold_root hHyp hH hlc hHv]
  exact XiCertReduction.derivative_eval_centreFold_isUnit hHyp.separable_evalX hdvd

/-- **The `ξ`-certificate reading at the radical decoded root** (monic case) — mirror of
`BranchCertificates.xiCert_eval_monic` against the radical split. -/
theorem xiCert_eval_monic_radical {x₀ : F} {R : F[X][X][Y]} {w G' : F[X][Y]}
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G' ≠ 0)
    (a : 𝒪 H) :
    (π_z z (rootDecodedRadical hH hQ0 hsplitRad hdvd z hbranch)) a
      = (((canonicalRepOf𝒪 hH a).eval (w.eval (Polynomial.C x₀))).eval z : F) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH a]
  rw [π_z_mk]
  rw [← rootDecodedRadical_val_monic hH hlc hQ0 hsplitRad hdvd z hbranch]
  exact RationalRootSupply.evalEval_eval_eval z _ _

section Family

variable [Fintype F]

/-- **Per-place `ξ`-nonvanishing at the radical decoded roots, GLOBALLY discharged** —
mirror of `RootOn304.hx_of_global_structural` against the radical split: the certificate is
a unit by `xiCert_isUnit_of_centreFold_root` on the radical-supplied centre-fold root. -/
theorem hx_of_global_structural_radical {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {w G' : F[X][Y]} (hmonic : H.Monic)
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G'.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    ∀ z (hz : z ∈ BranchCertificates.nonvanishingLocus
        (G'.eval (w.eval (Polynomial.C x₀)))),
      (π_z z (rootDecodedRadical (Fact.out) hQ0 hsplitRad hdvdR z
        (RootOn304.branch_of_mem_locus hz))) (ξ x₀ R H hHyp) ≠ 0 := by
  intro z hz
  rw [xiCert_eval_monic_radical (Fact.out) hmonic.leadingCoeff hQ0 hsplitRad hdvdR z
    (RootOn304.branch_of_mem_locus hz)]
  have hHv : H.eval (w.eval (Polynomial.C x₀)) = 0 :=
    H_eval_centreFold_eq_zero_radical hQ0 hsplitRad hdvdR hbr
  have hu : IsUnit ((canonicalRepOf𝒪 (Fact.out) (ξ x₀ R H hHyp)).eval
      (w.eval (Polynomial.C x₀))) :=
    xiCert_isUnit_of_centreFold_root hHyp (Fact.out) hmonic.leadingCoeff hdvdR hHv
  have h := ((Polynomial.evalRingHom z).isUnit_map hu).ne_zero
  simpa [Polynomial.coe_evalRingHom] using h

/-- **The `mpFin` family from the RADICAL split, on the consolidated separability
hypothesis** — `DecodedRootSupply.mpFin_of_decoded_roots` with (a) the GS split replaced by
the radical split (roots = `rootDecodedRadical`) and (b) `hR : R.Separable` weakened to
`MappedSliceSeparability` (the audit's irreducible residue; see file docstring). -/
noncomputable def mpFin_of_decoded_roots_radical_mapped {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {w G' : F[X][Y]} {k : ℕ}
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G' ≠ 0)
    (hsepM : MappedSeparability.MappedSliceSeparability hHyp) (T : ℕ)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (rootDecodedRadical (Fact.out) hQ0 hsplitRad hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z, ∀ hz : z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z
        (rootDecodedRadical (Fact.out) hQ0 hsplitRad hdvd z (hbranch z hz)) :=
  fun t hkt _ z hz =>
    MappedSeparability.matchingPoint_of_decoded_mapped hHyp hξ hlc z
      (rootDecodedRadical (Fact.out) hQ0 hsplitRad hdvd z (hbranch z hz)) (hx z hz)
      hdeg hdvd
      (rootDecodedRadical_val_monic (Fact.out) hlc hQ0 hsplitRad hdvd z (hbranch z hz))
      hsepM t hkt

/-- The `hRsep` drop-in form of the radical `mpFin` family (via
`MappedSliceSeparability.of_separable`). -/
noncomputable def mpFin_of_decoded_roots_radical {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {w G' : F[X][Y]} {k : ℕ}
    (hQ0 : Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsplitRad : radical (Bivariate.evalX (Polynomial.C x₀) R) = H * G')
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G' ≠ 0)
    (hR : R.Separable) (T : ℕ)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (rootDecodedRadical (Fact.out) hQ0 hsplitRad hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z, ∀ hz : z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z
        (rootDecodedRadical (Fact.out) hQ0 hsplitRad hdvd z (hbranch z hz)) :=
  mpFin_of_decoded_roots_radical_mapped hHyp hξ hlc hQ0 hsplitRad hdeg hdvd hbranch
    (MappedSeparability.MappedSliceSeparability.of_separable hHyp hR) T hx

end Family

end DecodedRadical

end RadicalWire304

/-! ## Part 3 — the assembler re-run against the radical: the front door -/

namespace RootOn304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge

section ProducersRadical

open BetaRecGenuineBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The satisfiable bundle from the RADICAL of the fiber** (monic case): mirror of
`Section5StrictDataFinOn.ofProducersOn_global` with

* the GS split + branch certificate inputs `{hsplit, hbr}` REPLACED by the single incidence
  fact `hOnH` (as in `hcoeffPoly_witness_of_producersOn_branch`), but produced at the
  RADICAL canonical cofactor `radical (evalX (C x₀) b.R) /ₘ b.H` — NO squarefreeness
  hypothesis is consumed anywhere in the production (`squarefree_radical` is free);
* `hRsep : b.R.Separable` REPLACED by the strictly weaker
  `MappedSliceSeparability b.hHyp` — per the audit, this is the sole genuine consumption of
  the external trivariate separability and is NOT deletable by the radical;
* the matching set CONSTRUCTED as the nonvanishing locus of the radical branch
  certificate, which doubles as the §6 discriminant (`hbig` measured at its degree). -/
noncomputable def Section5StrictDataFinOn.ofProducersOn_radical {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- the global §5 structural data, radical-route shape:
    {w : F[X][Y]}
    (hwdeg : w.natDegree < k)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ b.R)
    (hOnH : b.H.eval (w.eval (Polynomial.C x₀)) = 0)
    (hsepM : MappedSeparability.MappedSliceSeparability b.hHyp)
    -- graded budget side conditions + the sharpened §6 counting at the radical certificate:
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
            (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F)
    -- series-level identifications (items 5-7 of the external surface):
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  Section5StrictDataFinOn.ofProducersOn_gradedSigned b
    (BranchCertificates.nonvanishingLocus
      ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
        (w.eval (Polynomial.C x₀))))
    (fun z hz => RadicalWire304.rootDecodedRadical (Fact.out)
      (RadicalWire304.fiber_ne_zero b.hHyp)
      (RadicalWire304.split_canonical_radical b hmonic) hdvdR z
      (branch_of_mem_locus hz))
    Ppoly hmonic hrep hdegX
    (RadicalWire304.mpFin_of_decoded_roots_radical_mapped b.hHyp
      (XiCertReduction.xi_ne_zero x₀ b.R b.hHyp) hmonic.leadingCoeff
      (RadicalWire304.fiber_ne_zero b.hHyp)
      (RadicalWire304.split_canonical_radical b hmonic) hwdeg hdvdR
      (fun _z hz => branch_of_mem_locus hz) hsepM Ppoly.natDegree
      (RadicalWire304.hx_of_global_structural_radical b.hHyp hmonic
        (RadicalWire304.fiber_ne_zero b.hHyp)
        (RadicalWire304.split_canonical_radical b hmonic) hdvdR
        (RadicalWire304.hbr_canonical_radical b hmonic hOnH)))
    hd2 hdHD hD_Rx0 hRgrade
    (RadicalWire304.hbr_canonical_radical b hmonic hOnH)
    (fun _z hz => BranchCertificates.mem_nonvanishingLocus.mpr hz)
    hbig hsubst hβHensel hHensel hdeg

/-- **THE RADICAL FRONT DOOR**: the root-free `hcoeffPoly` existential from the radical
producers.  Versus the landed `hcoeffPoly_witness_of_producersOn_branch`: the branch
package is produced at the RADICAL canonical cofactor with NO squarefreeness consumed, and
`hRsep : b.R.Separable` is replaced by the strictly weaker `MappedSliceSeparability` (full
deletion is impossible — see the audit in the file docstring). -/
theorem hcoeffPoly_witness_of_producersOn_radical {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    {w : F[X][Y]}
    (hwdeg : w.natDegree < k)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ b.R)
    (hOnH : b.H.eval (w.eval (Polynomial.C x₀)) = 0)
    (hsepM : MappedSeparability.MappedSliceSeparability b.hHyp)
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
            (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  hcoeffPoly_witness_of_section5DataFinOn
    (Section5StrictDataFinOn.ofProducersOn_radical b Ppoly hmonic hrep hdegX hwdeg
      hdvdR hOnH hsepM hd2 hdHD hD_Rx0 hRgrade hbig hsubst hβHensel hHensel hdeg)

/-- The `hRsep` drop-in form of the radical front door (exact hypothesis-list parity with
`hcoeffPoly_witness_of_producersOn_branch` except the branch production runs through the
radical and the `hbig` discriminant degree is measured at the radical cofactor). -/
theorem hcoeffPoly_witness_of_producersOn_radical_sep {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    {w : F[X][Y]}
    (hwdeg : w.natDegree < k)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ b.R)
    (hOnH : b.H.eval (w.eval (Polynomial.C x₀)) = 0)
    (hRsep : b.R.Separable)
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
            (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  hcoeffPoly_witness_of_producersOn_radical b Ppoly hmonic hrep hdegX hwdeg hdvdR hOnH
    (MappedSeparability.MappedSliceSeparability.of_separable b.hHyp hRsep)
    hd2 hdHD hD_Rx0 hRgrade hbig hsubst hβHensel hHensel hdeg

end ProducersRadical

end RootOn304

end ArkLib

/-! ## Part 4 — the #304 END-TO-END CHAIN THEOREM over the final minimal surface -/

namespace ArkLib

namespace Chain304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge
open BetaRecGenuineBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The final minimal external surface of #304**, per decoding `(u, P)`: the exact
hypothesis list of the end-to-end chain theorem `correlatedAgreement_of_minimal_surface`.

Contents (each field is a genuinely-research-level input, named and documented; nothing
here is fabricated, and nothing beyond this list is consumed):

* the centre/bundle/representative data of [BCIKS20] §5 (`x₀`, `b`, `Ppoly`, `hmonic`,
  `hrep`, `hdegX`);
* the **fiberwise GS-decoder outputs**: per-centre sections `v` rooting the fibers on a
  centre set `S` (`hfib`), their local `(k+1)`-coherence (`hcoh`), and the global-lift
  budget (`hcoeffR` + `hbigS`) — `FiberSectionCoherence` turns these into ONE global
  section `w` of `Y`-degree `< k` with `(Y′ − C w) ∣ R`;
* the **§6 incidence fact** `hOnH` and the **§6 counting budget at the RADICAL branch
  certificate** `hbig`, both stated at the produced global section — which is UNIQUE
  given `(S, v)` (`FiberSectionCoherence.section_eq_of_agree`: two `Y`-degree-`< k`
  sections agreeing on the `≥ k+1` centres of `S` coincide), so each of these
  `w`-quantified fields pins exactly one section;
* **`MappedSliceSeparability`** (`hsepM`) — the audit's irreducible residue of the
  external trivariate separability, strictly weaker than `b.R.Separable`
  (`MappedSeparability.MappedSliceSeparability.of_separable` is the drop-in);
* the graded budget side conditions (`hd2`, `hdHD`, `hD_Rx0`, `hRgrade`);
* the series-level identifications (`hsubst`, `hβHensel`, `hHensel`, `hdeg`). -/
structure MinimalSurface304 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- the centre of the §5 curve analysis. -/
  x₀ : F
  /-- the GS factor bundle at the centre (`R`, `H`, `D`, the standing `Hypotheses`). -/
  b : GSFactorData.Bundle (F := F) x₀
  /-- irreducibility of the bundle's `H` (instance form). -/
  hIrr : Fact (Irreducible b.H)
  /-- positivity of `natDegree b.H` (instance form). -/
  hPos : Fact (0 < b.H.natDegree)
  /-- the Prop-5.5 polynomial representative of `γ`. -/
  Ppoly : F[X][Y]
  /-- monicity of the bundle's `H`. -/
  hmonic : b.H.Monic
  /-- `Ppoly` represents `γ`. -/
  hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp
  /-- linearity of the representative in `Z`. -/
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- fiberwise GS-decoder output: the centre set. -/
  S : Finset F
  /-- fiberwise GS-decoder output: the per-centre section values. -/
  v : F → F[X]
  /-- per-centre sections: the decoded value roots the fiber at every centre of `S`. -/
  hfib : ∀ y ∈ S,
    (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) b.R
  /-- the centre set carries at least `k + 1` centres. -/
  hScard : k + 1 ≤ S.card
  /-- local `(k+1)`-coherence of the decoder outputs: every `(k+1)`-subset of the family
  lies on SOME polynomial section of `Y`-degree `< k` (interpolation rigidity then glues
  these to ONE global section). -/
  hcoh : ∀ T ⊆ S, T.card = k + 1 →
    ∃ wT : F[X][Y], wT.natDegree < k ∧ ∀ y ∈ T, v y = wT.eval (Polynomial.C y)
  /-- the uniform coefficient budget of the surface. -/
  DX : ℕ
  /-- every `Y′`-coefficient of `b.R` has centre-degree `≤ DX`. -/
  hcoeffR : ∀ j, (b.R.coeff j).natDegree ≤ DX
  /-- the global-lift budget: the centre set beats `DX + deg_Y R · (k − 1)`. -/
  hbigS : DX + b.R.natDegree * (k - 1) < S.card
  /-- **the §6 incidence fact** at the produced global section: the section lies on the
  bundle's own branch `H`.  (Quantified over the produced section, which is unique.) -/
  hOnH : ∀ w : F[X][Y], w.natDegree < k →
    (∀ y ∈ S, v y = w.eval (Polynomial.C y)) →
    (Polynomial.X - Polynomial.C w) ∣ b.R →
    b.H.eval (w.eval (Polynomial.C x₀)) = 0
  /-- **the consolidated separability residue**: `MappedSliceSeparability`, strictly
  weaker than `b.R.Separable` (the audit's sole genuine consumption of the external
  trivariate separability — not deletable by the radical). -/
  hsepM : MappedSeparability.MappedSliceSeparability b.hHyp
  /-- graded side condition: `Y`-degree of `R` at least `2`. -/
  hd2 : 2 ≤ Bivariate.natDegreeY b.R
  /-- graded side condition: `natDegree b.H ≤ b.D`. -/
  hdHD : b.H.natDegree ≤ b.D
  /-- graded side condition: `b.D` dominates the total degree of the centre fiber. -/
  hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R)
  /-- graded side condition: the graded coefficient bounds on `b.R`. -/
  hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j
  /-- **the §6 counting budget at the RADICAL branch certificate**, at the produced
  global section (quantified over the produced section, which is unique). -/
  hbig : ∀ w : F[X][Y], w.natDegree < k →
    (∀ y ∈ S, v y = w.eval (Polynomial.C y)) →
    (Polynomial.X - Polynomial.C w) ∣ b.R →
    gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
            (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F
  /-- series identification: validity of the BCIKS substitution `X ↦ X − x₀`. -/
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H)
  /-- series identification: the signed numerator coefficients are the genuine Hensel
  coefficients. -/
  hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t
  /-- series identification: every linear decomposition of `γ` yields the per-`z` Hensel
  datum of the §5 specialisation bridge. -/
  hHensel : ∀ v₀ v₁ : F[X],
    γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁
  /-- series identification: degree bounds of any linear decomposition of `γ`. -/
  hdeg : ∀ v₀ v₁ : F[X],
    γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

/-- **THE #304 END-TO-END CHAIN THEOREM**: from the final minimal external surface —
the fiberwise GS-decoder outputs (per-centre sections + local coherence + budgets), the
§6 incidence fact, the §6 counting budget at the radical certificate,
`MappedSliceSeparability`, and the series-level identifications — conclude
`δ_ε_correlatedAgreementCurves` ([BCIKS20] Theorem 1.4 conclusion) in the strict
list-decoding regime `δ < 1 − √ρ`.

Chain: `correlatedAgreement_listDecoding_strict_finOn`
∘ `Section5StrictDataFinOn.ofProducersOn_radical`
∘ `FiberSectionCoherence.section_dvd_global_of_local_coherence`. -/
theorem correlatedAgreement_of_minimal_surface {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hSurface : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        MinimalSurface304 (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine RootOn304.correlatedAgreement_listDecoding_strict_finOn hδ ?_
  intro u hprob hJ P hP
  have s := hSurface u hprob hJ P hP
  haveI := s.hIrr
  haveI := s.hPos
  -- the fiberwise → global lift: ONE section `w`, degree < k, coherent on S, dividing R
  have hex : ∃ w : F[X][Y], w.natDegree < k ∧
      (∀ y ∈ s.S, s.v y = w.eval (Polynomial.C y)) ∧
      (Polynomial.X - Polynomial.C w) ∣ s.b.R :=
    FiberSectionCoherence.section_dvd_global_of_local_coherence
      s.hfib s.hScard s.hcoh s.hcoeffR s.hbigS
  have hwdeg := hex.choose_spec.1
  have hwagree := hex.choose_spec.2.1
  have hdvdR := hex.choose_spec.2.2
  -- the radical bundle producer at the produced section
  exact RootOn304.Section5StrictDataFinOn.ofProducersOn_radical s.b s.Ppoly s.hmonic
    s.hrep s.hdegX hwdeg hdvdR (s.hOnH _ hwdeg hwagree hdvdR) s.hsepM
    s.hd2 s.hdHD s.hD_Rx0 s.hRgrade (s.hbig _ hwdeg hwagree hdvdR)
    s.hsubst s.hβHensel s.hHensel s.hdeg

end Chain304

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_radical
#print axioms ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical
#print axioms ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical_sep
#print axioms ArkLib.Chain304.correlatedAgreement_of_minimal_surface
