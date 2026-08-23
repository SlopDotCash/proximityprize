/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BCIKS20GlobalAssembler

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace SectionGlobalLift

variable {F : Type} [Field F]

/-! ## Part 1 — commutation and the lifting lemma -/

/-- **The fiber/global commutation**: reading the specialized surface at the specialized
section equals specializing the global obstruction `R.eval w ∈ F[X][X]` at the centre. -/
theorem eval_section_evalX (x₀ : F) (R : F[X][X][Y]) (w : F[X][Y]) :
    (Bivariate.evalX (Polynomial.C x₀) R).eval (w.eval (Polynomial.C x₀))
      = (R.eval w).eval (Polynomial.C x₀) := by
  rw [Bivariate.evalX_eq_map, Polynomial.eval_map]
  have h := Polynomial.eval₂_hom (Polynomial.evalRingHom (Polynomial.C x₀)) w (p := R)
  simpa only [Polynomial.coe_evalRingHom] using h

/-- **The global factor specializes to the fiber factor** (task goal c): `(Y′ − C w) ∣ R`
yields the exact `GSSurfaceData.hdvd` shape `(T − C (w.eval (C x₀))) ∣ evalX (C x₀) R` at
every centre. -/
theorem centre_section_dvd (x₀ : F) {R : F[X][X][Y]} {w : F[X][Y]}
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀)))
      ∣ Bivariate.evalX (Polynomial.C x₀) R := by
  rw [Polynomial.dvd_iff_isRoot]
  show (Bivariate.evalX (Polynomial.C x₀) R).eval (w.eval (Polynomial.C x₀)) = 0
  have h0 : R.eval w = 0 := Polynomial.dvd_iff_isRoot.mp hdvdR
  rw [eval_section_evalX x₀ R w, h0, Polynomial.eval_zero]

/-- **THE LIFTING LEMMA** (task goal a): a coherent section through enough fibers lifts to a
global surface factor.  If `(T − C (w.eval (C y))) ∣ evalX (C y) R` at every centre `y` of a
set `S` with `(R.eval w).natDegree < |S|`, then `(Y′ − C w) ∣ R`: the global obstruction
`R.eval w ∈ F[X][X]` vanishes at the `|S|` distinct points `C y`, exceeding its degree. -/
theorem section_dvd_global_of_fibers {R : F[X][X][Y]} {w : F[X][Y]} {S : Finset F}
    (hfib : ∀ y ∈ S, (Polynomial.X - Polynomial.C (w.eval (Polynomial.C y)))
      ∣ Bivariate.evalX (Polynomial.C y) R)
    (hbig : (R.eval w).natDegree < S.card) :
    (Polynomial.X - Polynomial.C w) ∣ R := by
  classical
  rw [Polynomial.dvd_iff_isRoot]
  show R.eval w = 0
  by_contra hEne
  have hroot : ∀ y ∈ S, (Polynomial.C y : F[X]) ∈ (R.eval w).roots.toFinset := by
    intro y hy
    refine Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hEne, ?_⟩)
    show (R.eval w).eval (Polynomial.C y) = 0
    rw [← eval_section_evalX y R w]
    have h := hfib y hy
    rw [Polynomial.dvd_iff_isRoot] at h
    exact h
  have hsub : S.image (fun y : F => (Polynomial.C y : F[X])) ⊆ (R.eval w).roots.toFinset :=
    Finset.image_subset_iff.mpr hroot
  have h1 : S.card = (S.image (fun y : F => (Polynomial.C y : F[X]))).card :=
    (Finset.card_image_of_injOn (fun a _ b _ h => Polynomial.C_injective h)).symm
  have h2 := Finset.card_le_card hsub
  have h3 := Multiset.toFinset_card_le (R.eval w).roots
  have h4 := Polynomial.card_roots' (R.eval w)
  omega

/-- **The obstruction degree budget**: `(R.eval w).natDegree ≤ DX + natDegree(R) · natDegree(w)`
whenever every `Y′`-coefficient of `R` has centre-degree `≤ DX`. -/
theorem eval_section_natDegree_le {R : F[X][X][Y]} {w : F[X][Y]} {DX : ℕ}
    (hcoeff : ∀ j, (R.coeff j).natDegree ≤ DX) :
    (R.eval w).natDegree ≤ DX + R.natDegree * w.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : (w ^ j).natDegree ≤ j * w.natDegree := Polynomial.natDegree_pow_le
  have h2 : j * w.natDegree ≤ R.natDegree * w.natDegree := Nat.mul_le_mul_right _ hjle
  have h3 := hcoeff j
  omega

/-- The lifting lemma with the numeric budget: the count
`DX + natDegree(R) · natDegree(w) < |S|` suffices. -/
theorem section_dvd_global_of_fibers_budget {R : F[X][X][Y]} {w : F[X][Y]} {S : Finset F}
    {DX : ℕ} (hcoeff : ∀ j, (R.coeff j).natDegree ≤ DX)
    (hfib : ∀ y ∈ S, (Polynomial.X - Polynomial.C (w.eval (Polynomial.C y)))
      ∣ Bivariate.evalX (Polynomial.C y) R)
    (hbig : DX + R.natDegree * w.natDegree < S.card) :
    (Polynomial.X - Polynomial.C w) ∣ R :=
  section_dvd_global_of_fibers hfib (lt_of_le_of_lt (eval_section_natDegree_le hcoeff) hbig)

/-! ## Part 2 — `hbr` from separability -/

/-- **Branch separation from separability** (task goal b): if the centre specialization is
separable (squarefree) and the section value roots `H`, then the cofactor `G` CANNOT also
vanish there — a common root would put `(T − C v)²` inside `H · G`. -/
theorem branch_ne_zero_of_separable {x₀ : F} {R : F[X][X][Y]} {H G : F[X][Y]} {v : F[X]}
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hH0 : H.eval v = 0) :
    G.eval v ≠ 0 := by
  intro hG0
  have hdH : (Polynomial.X - Polynomial.C v) ∣ H := Polynomial.dvd_iff_isRoot.mpr hH0
  have hdG : (Polynomial.X - Polynomial.C v) ∣ G := Polynomial.dvd_iff_isRoot.mpr hG0
  have hsq : (Polynomial.X - Polynomial.C v) * (Polynomial.X - Polynomial.C v)
      ∣ Bivariate.evalX (Polynomial.C x₀) R := by
    rw [hsplit]; exact mul_dvd_mul hdH hdG
  exact Polynomial.not_isUnit_X_sub_C v (hsep.squarefree _ hsq)

/-- **The split AND the branch certificate from the factorization** (task goals b+c composed):
from the `PigeonholeFactorSupply` shape `evalX (C x₀) R = ∏ᵢ Hᵢ`, fiber separability, and the
global surface factor, SOME factor carries the section, and at that factor both `hsplit` and
`hbr` hold — the assembler's `(H, G, hsplit, hbr)` package is produced outright. -/
theorem exists_split_branch_of_factorization {ι' : Type*} [DecidableEq ι'] {x₀ : F}
    {R : F[X][X][Y]} {s : Finset ι'} {Hf : ι' → F[X][Y]} {w : F[X][Y]}
    (hQ : Bivariate.evalX (Polynomial.C x₀) R = ∏ i ∈ s, Hf i)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ R) :
    ∃ i ∈ s,
      Bivariate.evalX (Polynomial.C x₀) R = Hf i * ∏ j ∈ s.erase i, Hf j ∧
      (Hf i).eval (w.eval (Polynomial.C x₀)) = 0 ∧
      (∏ j ∈ s.erase i, Hf j).eval (w.eval (Polynomial.C x₀)) ≠ 0 := by
  have hfib := centre_section_dvd x₀ hdvdR
  have hv0 : (Bivariate.evalX (Polynomial.C x₀) R).eval (w.eval (Polynomial.C x₀)) = 0 :=
    Polynomial.dvd_iff_isRoot.mp hfib
  have hprod : ∏ i ∈ s, (Hf i).eval (w.eval (Polynomial.C x₀)) = 0 := by
    rw [← Polynomial.eval_prod, ← hQ]; exact hv0
  obtain ⟨i, hi, hi0⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hsplit : Bivariate.evalX (Polynomial.C x₀) R = Hf i * ∏ j ∈ s.erase i, Hf j := by
    rw [hQ, Finset.mul_prod_erase s Hf hi]
  exact ⟨i, hi, hsplit, hi0, branch_ne_zero_of_separable hsep hsplit hi0⟩

/-- **The full production**: factorization + fiber separability + coherent fiber sections +
the lifting budget produce the global factor `hdvdR` AND the `(hsplit, on-branch, hbr)`
package at some factor of the in-tree factorization. -/
theorem global_facts_of_fiber_sections {ι' : Type*} [DecidableEq ι'] {x₀ : F}
    {R : F[X][X][Y]} {s : Finset ι'} {Hf : ι' → F[X][Y]} {w : F[X][Y]} {S : Finset F}
    (hQ : Bivariate.evalX (Polynomial.C x₀) R = ∏ i ∈ s, Hf i)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hfib : ∀ y ∈ S, (Polynomial.X - Polynomial.C (w.eval (Polynomial.C y)))
      ∣ Bivariate.evalX (Polynomial.C y) R)
    (hbig : (R.eval w).natDegree < S.card) :
    (Polynomial.X - Polynomial.C w) ∣ R ∧
    ∃ i ∈ s,
      Bivariate.evalX (Polynomial.C x₀) R = Hf i * ∏ j ∈ s.erase i, Hf j ∧
      (Hf i).eval (w.eval (Polynomial.C x₀)) = 0 ∧
      (∏ j ∈ s.erase i, Hf j).eval (w.eval (Polynomial.C x₀)) ≠ 0 := by
  have hdvdR := section_dvd_global_of_fibers hfib hbig
  exact ⟨hdvdR, exists_split_branch_of_factorization hQ hsep hdvdR⟩

end SectionGlobalLift

namespace BranchWire304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge

section BundleWire

open BetaRecGenuineBridge

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The canonical GS split**: at the bundle's own `H` (monic), `hsplit` holds with the
CANONICAL cofactor `G := evalX (C x₀) b.R /ₘ b.H` — no choice, no extra input: the divisibility
is the bundle's own `Hypotheses.dvd_evalX`. -/
theorem split_canonical {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀) (hmonic : b.H.Monic) :
    Bivariate.evalX (Polynomial.C x₀) b.R
      = b.H * (Bivariate.evalX (Polynomial.C x₀) b.R /ₘ b.H) := by
  have hmod : Bivariate.evalX (Polynomial.C x₀) b.R %ₘ b.H = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr b.hHyp.dvd_evalX
  conv_lhs => rw [← Polynomial.modByMonic_add_div (Bivariate.evalX (Polynomial.C x₀) b.R) b.H]
  rw [hmod, zero_add]

/-- **`hbr` at the canonical cofactor** from the bundle's own fiber separability plus the
single §6-incidence fact `hOnH : b.H.eval (w.eval (C x₀)) = 0` (the section lies on the
bundle's branch — the exact `F[X]`-level shape `FactorPigeonhole` selects). -/
theorem hbr_canonical {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀) (hmonic : b.H.Monic)
    {w : F[X][Y]} (hOnH : b.H.eval (w.eval (Polynomial.C x₀)) = 0) :
    (Bivariate.evalX (Polynomial.C x₀) b.R /ₘ b.H).eval (w.eval (Polynomial.C x₀)) ≠ 0 :=
  SectionGlobalLift.branch_ne_zero_of_separable b.hHyp.separable_evalX
    (split_canonical b hmonic) hOnH

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **The assembler front door with the external surface shrunk 4 → 3** (task goal b wired):
`hcoeffPoly_witness_of_producersOn_global` with `{hsplit, hbr}` REPLACED by the single
incidence fact `hOnH : b.H.eval (w.eval (C x₀)) = 0`; the split is the canonical monic
division and `hbr` is derived from the bundle's own fiber separability.  Remaining global
facts: `hdvdR` (+ `hwdeg`), `hOnH`, `hRsep`. -/
theorem hcoeffPoly_witness_of_producersOn_branch {k deg : ℕ}
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
        + ((Bivariate.evalX (Polynomial.C x₀) b.R /ₘ b.H).eval
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
  RootOn304.hcoeffPoly_witness_of_producersOn_global b Ppoly hmonic hrep hdegX
    (split_canonical b hmonic) hwdeg hdvdR (hbr_canonical b hmonic hOnH) hRsep
    hd2 hdHD hD_Rx0 hRgrade hbig hsubst hβHensel hHensel hdeg

/-- **The assembler front door from FIBERWISE sections** (task goals a+b wired): additionally
`hdvdR` is replaced by the in-tree fiberwise shape (`GSSurfaceData.hdvd` at every centre of a
set `S`) plus the lifting budget `(b.R.eval w).natDegree < |S|`.  The remaining global facts
are: the fiberwise sections coherent with one global `w` of degree `< k`, the incidence
`hOnH`, and `hRsep`. -/
theorem hcoeffPoly_witness_of_producersOn_fiberwise {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    {w : F[X][Y]}
    (hwdeg : w.natDegree < k)
    {S : Finset F}
    (hfib : ∀ y ∈ S, (Polynomial.X - Polynomial.C (w.eval (Polynomial.C y)))
      ∣ Bivariate.evalX (Polynomial.C y) b.R)
    (hbigS : (b.R.eval w).natDegree < S.card)
    (hOnH : b.H.eval (w.eval (Polynomial.C x₀)) = 0)
    (hRsep : b.R.Separable)
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + ((Bivariate.evalX (Polynomial.C x₀) b.R /ₘ b.H).eval
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
  hcoeffPoly_witness_of_producersOn_branch b Ppoly hmonic hrep hdegX hwdeg
    (SectionGlobalLift.section_dvd_global_of_fibers hfib hbigS) hOnH hRsep
    hd2 hdHD hD_Rx0 hRgrade hbig hsubst hβHensel hHensel hdeg

end BundleWire

end BranchWire304

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionGlobalLift.eval_section_evalX
#print axioms ArkLib.SectionGlobalLift.centre_section_dvd
#print axioms ArkLib.SectionGlobalLift.section_dvd_global_of_fibers
#print axioms ArkLib.SectionGlobalLift.eval_section_natDegree_le
#print axioms ArkLib.SectionGlobalLift.section_dvd_global_of_fibers_budget
#print axioms ArkLib.SectionGlobalLift.branch_ne_zero_of_separable
#print axioms ArkLib.SectionGlobalLift.exists_split_branch_of_factorization
#print axioms ArkLib.SectionGlobalLift.global_facts_of_fiber_sections
#print axioms ArkLib.BranchWire304.split_canonical
#print axioms ArkLib.BranchWire304.hbr_canonical
#print axioms ArkLib.BranchWire304.hcoeffPoly_witness_of_producersOn_branch
#print axioms ArkLib.BranchWire304.hcoeffPoly_witness_of_producersOn_fiberwise
