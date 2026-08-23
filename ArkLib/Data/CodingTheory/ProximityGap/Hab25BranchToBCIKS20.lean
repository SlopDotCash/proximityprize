/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25RichCoordinateGate

/-!
# Seam A: the counting-lane branch in the Section-5 `hdvdR` shape (#302)

The #304 global assembler (`Section5GlobalAssembler.ofProducersOn_global`) consumes four
global GS facts, one of which is the **global surface factor**

  `hdvdR : (Y′ − C w) ∣ R` with `w.natDegree < k`.

The counting lane's capstone (`Hab25RichCoordinateGate.exists_global_branch_of_proximity`)
produces exactly this shape: its branch `pHat = branchOfCurveTuple (lagrangeCurveTuple …)`
lives in `(F₀[X])[X]` with the SAME variable orientation (outer = the domain/centre
variable, inner = the fold scalar `Z`), divides the trivariate `R` in the outer-`Y` sense,
and carries the degree bound through `branchOfCurveTuple_natDegree_lt` +
`lagrangeCurveTuple_natDegree_lt`.  This file packages the weld:

* **`exists_section5_hdvdR_of_proximity`** — under the rich-coordinate gate's hypotheses
  (per-scalar proximity data, the Claim 5.11 numeric leg, richness-guarded factor data,
  decode degrees/divisibility, and the count leg), there is a `w` with `w.natDegree < k`
  and `(Y′ − C w) ∣ R` — the `hdvdR` input of the Section-5 bundle, produced outright.

The remaining Section-5 inputs (`hsplit`, `hbr`, `hRsep`) are the outputs of the GS
split / branch-separation / squarefreeness lanes and are NOT touched here.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Seam A**: the counting-lane global branch, packaged in the Section-5 `hdvdR` shape
`∃ w, w.natDegree < k ∧ (Y′ − C w) ∣ R`. -/
theorem exists_section5_hdvdR_of_proximity {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
    [NeZero n]
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {BR : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR)
    (E : Finset F₀) (P : F₀ → F₀[X])
    (e M : ℕ) (hkn : k ≤ n)
    (hprox : ∀ γ ∈ E, n - e ≤
      (Finset.univ.filter (fun t => decodeAgreesAt domain u P t γ)).card)
    (hnum : e * E.card < (M + 1) * (n - k + 1))
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (Hp : Fin n → F₀[X][Y]) {B : ℕ}
    (S : Fin n → Finset F₀)
    (hdata : ∀ t : Fin n,
      E.card - M ≤ (E.filter (fun γ => decodeAgreesAt domain u P t γ)).card →
      Irreducible (Hp t) ∧ (∀ k' : ℕ, ((Hp t).coeff k').natDegree ≤ B) ∧
      (B + (Hp t).natDegree * (L - 1) < (S t).card) ∧
      (∀ ζ ∈ S t,
        ((Hp t).map (Polynomial.evalRingHom ζ)).eval ((foldSectionAt u t).eval ζ) = 0))
    (hbig : BR + R.natDegree * (L - 1) + k * M < E.card) :
    ∃ w : (F₀[X])[X], w.natDegree < k ∧
      (Polynomial.X - Polynomial.C w) ∣ R := by
  obtain ⟨T, hTcard, hdvd⟩ := exists_global_branch_of_proximity hk hL R hRB E P e M hkn
    hprox hnum hdeg hdvdP Hp S hdata hbig
  refine ⟨branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j), ?_, hdvd⟩
  exact branchOfCurveTuple_natDegree_lt hk
    (fun j => lagrangeCurveTuple_natDegree_lt hk domain u hTcard j)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_section5_hdvdR_of_proximity
