/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PigeonholeTruncationCapstone
import ArkLib.ToMathlib.XiCertReduction

/-!
# Issue #304 — the `hx` input of the pigeonhole capstone ELIMINATED by a Bezout adjustment

`PigeonholeTruncationCapstone.gammaGenuine_eq_trunc_of_pigeonhole` carries the per-place input

  `hx : ∀ z (hz : z ∈ matchingSet),
     (π_z z (BranchValuePigeonhole.incidenceRootFn (hinc z hz))) (ξ x₀ R H hHyp) ≠ 0`

— `ξ`-nonvanishing at the incidence roots.  This file **eliminates it** in favor of a purely
numeric adjustment, the last per-place input of the capstone after the `CentreVanishingSupply`
lane.

## The mechanism

1. **The `π_z` reading at an incidence root is root-value-only**
   (`pi_z_incidenceRootFn_eq`): by `π_z_eq_evalEval_canonicalRep` + `incidenceRootFn_val_monic`,
   for monic `H` the reading of any `a : 𝒪 H` at the incidence root over the decoded value `y`
   is `evalEval z y (canonicalRepOf𝒪 a)` — a per-place evaluation of ONE fixed bivariate at the
   decoded point.  Hence (`hx_iff_evalEval`) the capstone's `hx` at a place `z` is equivalent
   to `evalEval z ((Pz z).eval x₀) (canonicalRepOf𝒪 ξ) ≠ 0`.

2. **A `ξ`-bad place sits on TWO curves** (`mem_S_β_of_incidence_vanish`): at a bad place the
   decoded point is a common root of `H̃′` (the incidence) and of `canonicalRepOf𝒪 ξ` (the
   vanishing) — i.e. `z ∈ S_β ξ`.  Since `H̃` is irreducible and the representative has smaller
   `Y`-degree, the two curves are coprime over `F(X)`, so the `Y`-resultant
   `xiResultant := Res_Y(canonicalRepOf𝒪 ξ, H̃′)` is a NONZERO element of `F[X]`
   (`xiResultant_ne_zero`, via `resultant_canonicalRep_H_tilde'_ne_zero` and the unconditional
   `XiCertReduction.xi_ne_zero`); every bad place is one of its roots
   (`eval_resultant_eq_zero_of_mem_S_β`).  **Bezout**: at most `natDegree xiResultant` bad
   places (`xiBad_card_le`), so the `ξ`-good filter loses at most that many places
   (`xiGood_card_ge`).

3. **The adjusted capstone** (`gammaGenuine_eq_trunc_of_pigeonhole_xiAdjusted`): run the
   capstone on the `ξ`-good filtered matching set.  `hx` holds there by construction; the
   numeric chain pays `+ natDegree xiResultant` inside the budget.  `hξ` is also dropped
   (`xi_ne_zero` is a theorem).

Note the F8 lesson in reverse: the bad set CANNOT be bounded through a polynomial-in-`z`
incidence (the decoded values `(Pz z).eval x₀` are not the evaluations of any global
polynomial) — but it does not need to be: badness places the decoded point on the intersection
of two fixed coprime curves, and the resultant bound is value-function-agnostic.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claims 5.8/5.8′), Appendix A.3–A.5 (the `π_z` substitutions and the Lemma A.1
  resultant elimination, reused here for the `ξ`-certificate).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace XiAtIncidenceSupply

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## 1. The `π_z` reading at an incidence root is root-value-only -/

omit [Fact (Irreducible H)] in
/-- **The `π_z` reading at an incidence root depends only on the decoded value** (monic):
for any `a : 𝒪 H`, the reading at the incidence root over `(z, y)` is the evaluation of the
fixed canonical representative of `a` at the decoded point `(z, y)`.  This is
`π_z_eq_evalEval_canonicalRep` + `incidenceRootFn_val_monic`. -/
theorem pi_z_incidenceRootFn_eq (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    {y z : F} (hinc : Polynomial.evalEval z y H = 0) (a : 𝒪 H) :
    (π_z z (BranchValuePigeonhole.incidenceRootFn (H := H) hinc)) a
      = Polynomial.evalEval z y (canonicalRepOf𝒪 hH a) := by
  rw [π_z_eq_evalEval_canonicalRep hH a z
      (BranchValuePigeonhole.incidenceRootFn (H := H) hinc),
    ← BranchValuePigeonhole.incidenceRootFn_val_monic hlc hinc]

/-- **The capstone's `hx` at one place, read off the fixed bivariate**: `ξ`-nonvanishing at
the incidence root is equivalent to nonvanishing of the canonical representative of `ξ` at the
decoded point `(z, y)`. -/
theorem hx_iff_evalEval {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    {y z : F} (hinc : Polynomial.evalEval z y H = 0) :
    (π_z z (BranchValuePigeonhole.incidenceRootFn (H := H) hinc)) (ξ x₀ R H hHyp) ≠ 0
      ↔ Polynomial.evalEval z y (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) ≠ 0 := by
  rw [pi_z_incidenceRootFn_eq hH hlc hinc]

/-! ## 2. A `ξ`-bad place is on the intersection of two coprime curves -/

omit [Fact (Irreducible H)] in
/-- **A bad place lies in `S_β`**: if the canonical representative of `a : 𝒪 H` vanishes at a
decoded point `(z, y)` that is also on `H`, then `z ∈ S_β a` (the incidence root witnesses
the vanishing `π_z`-reading). -/
theorem mem_S_β_of_incidence_vanish (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    {y z : F} (hinc : Polynomial.evalEval z y H = 0) {a : 𝒪 H}
    (hvan : Polynomial.evalEval z y (canonicalRepOf𝒪 hH a) = 0) :
    z ∈ S_β a :=
  ⟨BranchValuePigeonhole.incidenceRootFn (H := H) hinc,
    by rw [pi_z_incidenceRootFn_eq hH hlc hinc a]; exact hvan⟩

/-- **The `ξ`-elimination resultant**: the `Y`-resultant of the canonical representative of
`ξ` with the defining relation `H̃′`, an element of `F[X]` whose roots contain every
`ξ`-bad place. -/
noncomputable def xiResultant (hH : 0 < H.natDegree) (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) : F[X] :=
  Polynomial.resultant (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) (H_tilde' H)
    H.natDegree H.natDegree

/-- **The `ξ`-elimination resultant is nonzero**: `ξ ≠ 0` holds unconditionally
(`XiCertReduction.xi_ne_zero`), and the coprimality of the small-degree representative with
the irreducible relation makes the resultant nonzero
(`resultant_canonicalRep_H_tilde'_ne_zero`). -/
theorem xiResultant_ne_zero (hH : 0 < H.natDegree) (x₀ : F) (R : F[X][X][Y])
    (hHyp : Hypotheses x₀ R H) :
    xiResultant hH x₀ R hHyp ≠ 0 :=
  resultant_canonicalRep_H_tilde'_ne_zero hH (XiCertReduction.xi_ne_zero x₀ R hHyp)

/-! ## 3. The Bezout bound on the bad set and the filtered cardinality -/

/-- **THE BEZOUT BOUND**: over any value function `y : F → F` (no polynomial structure in `z`
needed!), the set of incidence places where the `ξ`-representative vanishes at the decoded
point has at most `natDegree xiResultant` elements: each such place carries a common root of
the two coprime curves `canonicalRepOf𝒪 ξ` and `H̃′`, hence roots the nonzero resultant. -/
theorem xiBad_card_le [DecidableEq F] {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {y : F → F}
    (hinc : ∀ z ∈ matchingSet, Polynomial.evalEval z (y z) H = 0) :
    (matchingSet.filter (fun z =>
        Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0)).card
      ≤ (xiResultant hH x₀ R hHyp).natDegree := by
  classical
  have hRne : xiResultant hH x₀ R hHyp ≠ 0 := xiResultant_ne_zero hH x₀ R hHyp
  have hsub : matchingSet.filter (fun z =>
        Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0)
      ⊆ (xiResultant hH x₀ R hHyp).roots.toFinset := by
    intro z hz
    rw [Finset.mem_filter] at hz
    have hmem : z ∈ S_β (ξ x₀ R H hHyp) :=
      mem_S_β_of_incidence_vanish hH hlc (hinc z hz.1) hz.2
    have heval : (xiResultant hH x₀ R hHyp).eval z = 0 :=
      eval_resultant_eq_zero_of_mem_S_β hH (ξ x₀ R H hHyp) hmem
    exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hRne, heval⟩)
  calc (matchingSet.filter (fun z =>
        Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0)).card
      ≤ (xiResultant hH x₀ R hHyp).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (xiResultant hH x₀ R hHyp).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (xiResultant hH x₀ R hHyp).natDegree := Polynomial.card_roots' _

/-- **The filtered matching set keeps almost everything**: restricting to the `ξ`-good places
loses at most `natDegree xiResultant` places. -/
theorem xiGood_card_ge [DecidableEq F] {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {y : F → F}
    (hinc : ∀ z ∈ matchingSet, Polynomial.evalEval z (y z) H = 0) :
    matchingSet.card ≤ (matchingSet.filter (fun z =>
        ¬ Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0)).card
      + (xiResultant hH x₀ R hHyp).natDegree := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := matchingSet)
    (p := fun z =>
      Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0)
  have hbad := xiBad_card_le hHyp hH hlc hinc
  omega

/-! ## 4. THE ADJUSTED CAPSTONE — `hx` and `hξ` both eliminated -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **The pigeonhole truncation capstone with the `hx` input ELIMINATED**: Claim 5.8′ from
the per-place pigeonhole data WITHOUT the `ξ`-nonvanishing input `hx` and WITHOUT `hξ`,
at the price of the Bezout adjustment `+ natDegree xiResultant` inside the numeric chain.
The capstone is run on the `ξ`-good filtered matching set, where `hx` holds by construction
(`hx_iff_evalEval`); the bad places are at most `natDegree xiResultant` many
(`xiBad_card_le`), absorbed by the adjusted budget. -/
theorem gammaGenuine_eq_trunc_of_pigeonhole_xiAdjusted {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁
      = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F} {Pz : F → F[X]}
    (hinc : ∀ z ∈ matchingSet, Polynomial.evalEval z ((Pz z).eval x₀) H = 0)
    (hdvd : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (Pz z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hR : R.Separable)
    {n : ℕ}
    (hbudget : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + (xiResultant hH x₀ R hHyp).natDegree < n)
    (hcard : n ≤ matchingSet.card) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) := by
  -- the per-place data restricted to the `ξ`-good filtered matching set
  have hgoodinc : ∀ z ∈ matchingSet.filter (fun z =>
      ¬ Polynomial.evalEval z ((Pz z).eval x₀)
          (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0),
      Polynomial.evalEval z ((Pz z).eval x₀) H = 0 :=
    fun z hz => hinc z (Finset.filter_subset _ _ hz)
  refine PigeonholeTruncationCapstone.gammaGenuine_eq_trunc_of_pigeonhole H hHyp
    (XiCertReduction.xi_ne_zero x₀ R hHyp) hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hrepT
    hgoodinc
    (fun z hz => hdvd z (Finset.filter_subset _ _ hz))
    (fun z hz => hdeg z (Finset.filter_subset _ _ hz))
    (fun z hz => ?_) hR
    (n := n - (xiResultant hH x₀ R hHyp).natDegree) ?_ ?_
  · -- `hx` on the good set: by the root-value-only reading + the filter membership
    rw [pi_z_incidenceRootFn_eq hH hmonic.leadingCoeff (hgoodinc z hz)]
    exact (Finset.mem_filter.mp hz).2
  · -- the adjusted budget
    omega
  · -- the adjusted cardinality, via the Bezout bound on the bad set
    have hsplit := Finset.card_filter_add_card_filter_not (s := matchingSet)
      (p := fun z => Polynomial.evalEval z ((Pz z).eval x₀)
        (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0)
    have hbad := xiBad_card_le hHyp hH hmonic.leadingCoeff hinc
    omega

end Capstone

end XiAtIncidenceSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.XiAtIncidenceSupply.pi_z_incidenceRootFn_eq
#print axioms ArkLib.XiAtIncidenceSupply.hx_iff_evalEval
#print axioms ArkLib.XiAtIncidenceSupply.mem_S_β_of_incidence_vanish
#print axioms ArkLib.XiAtIncidenceSupply.xiResultant
#print axioms ArkLib.XiAtIncidenceSupply.xiResultant_ne_zero
#print axioms ArkLib.XiAtIncidenceSupply.xiBad_card_le
#print axioms ArkLib.XiAtIncidenceSupply.xiGood_card_ge
#print axioms ArkLib.XiAtIncidenceSupply.gammaGenuine_eq_trunc_of_pigeonhole_xiAdjusted
