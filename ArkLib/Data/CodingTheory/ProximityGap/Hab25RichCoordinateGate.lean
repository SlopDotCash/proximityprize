/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25SlackWeld

/-!
# The rich-coordinate gate (#302, R-K5): global branch from per-coordinate rich factors

This file welds the slack weld (`global_branch_of_witnessed_subcell`, R-K3) to a CONCRETE
witness predicate — `γ` is witnessed at `t` iff its decode value at `t` equals the fold
value, `(P γ).eval (x_t) = w_t(γ)` — and discharges the weld's per-scalar factor data from
ONE witness-rich factor per chosen coordinate:

* **`global_branch_of_perCoordinate_rich`** — given, at each chosen coordinate `t ∈ T`, an
  irreducible budgeted factor `Hp t` carrying `> B + deg_Y·(L−1)` witnessed fold agreements
  (`S t`), the full weld data exists: the kill's root (`section_root_of_many_agreements`)
  makes the fold section an identical `Y`-root of `Hp t`, so at every *witnessed* scalar the
  decode value (= the fold value there) roots in `Hp t` — `hroot`, `hrich`, `hwit` all
  discharge with `assign` constant.  The unwitnessed scalars are counted away by R-K3.
* **`exists_global_branch_of_proximity`** — the proximity-fed capstone: from per-scalar
  agreement data (every decode agrees with the fold on all but `e` coordinates), the
  Claim 5.11 numeric leg `e·|E| < (M+1)·(n−k+1)`, and factor data *guarded by richness*
  (demanded only at coordinates where all but `M` cell scalars agree — exactly what
  `exists_rich_coordinates` produces), some `k`-subset `T` of coordinates yields the global
  branch `(Y − C pHat_T) ∣ R`.

## Status of #302 after this file

The witnessed-scalar half of the assignment-coherence residual is CLOSED: `hroot`/`hrich`/
`hwit` are no longer per-scalar obligations — they collapse to "a witness-rich factor exists
at each rich coordinate", which for *witnessed* mass is pigeonhole
(`exists_unique_witnessRich_factor`, R-K2) over the attributed factors of the interpolant
fiber (`factorBudgetSupply`, R-K4).  What remains open, honestly:
1. **the witnessed-mass → rich-factor wiring at the interpolant fiber** (the variable
   bookkeeping between `R`'s `F[Z]`-coefficient specialization and the per-coordinate
   `F[X][Y]` fiber factors — the `hwit` mass must be produced from `hdvdP` + attribution,
   not assumed); and
2. **the Johnson-regime defect problem**: here `M` enters the count leg additively
   (`k·M`), while at Johnson radius the true defect is multiplicative
   (`M ≈ δ/(1−ρ)·|E|`, BCIKS20 Claim 5.11), so this gate's regime is
   `k·δ/(1−ρ) < 1` — below Johnson for `k ≥ 2`.  The Johnson closure is the
   per-coordinate-INDEPENDENT route (global capture + the `𝒪`-level kill of
   `CoordinateKillBudget` Part 1, interpolating in `𝕃` scalar-free), tracked as R-A1.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 Claims 5.9–5.11.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- The concrete witness predicate: `γ` is witnessed at `t` iff its decode value at the
coordinate equals the fold value there. -/
def decodeAgreesAt {n L : ℕ} (domain : Fin n ↪ F₀) (u : WordStack F₀ (Fin L) (Fin n))
    (P : F₀ → F₀[X]) (t : Fin n) (γ : F₀) : Prop :=
  (P γ).eval (domain t) = (foldSectionAt u t).eval γ

/-- **The rich-coordinate gate**: one witness-rich irreducible budgeted factor per chosen
coordinate discharges ALL the weld's per-scalar factor data at witnessed scalars; the
unwitnessed scalars are counted away by the slack weld. -/
theorem global_branch_of_perCoordinate_rich {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {BR : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR)
    (E : Finset F₀) (P : F₀ → F₀[X]) (T : Finset (Fin n)) (hT : T.card = k)
    (M : ℕ)
    (hdefect : ∀ t ∈ T,
      (E.filter (fun γ => ¬ decodeAgreesAt domain u P t γ)).card ≤ M)
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (Hp : Fin n → F₀[X][Y]) {B : ℕ}
    (hirr : ∀ t ∈ T, Irreducible (Hp t))
    (hB : ∀ t ∈ T, ∀ k' : ℕ, ((Hp t).coeff k').natDegree ≤ B)
    (S : Fin n → Finset F₀)
    (hrich : ∀ t ∈ T, B + (Hp t).natDegree * (L - 1) < (S t).card)
    (hwit : ∀ t ∈ T, ∀ ζ ∈ S t,
      ((Hp t).map (Polynomial.evalRingHom ζ)).eval ((foldSectionAt u t).eval ζ) = 0)
    (hbig : BR + R.natDegree * (L - 1) + k * M < E.card) :
    (Polynomial.X - Polynomial.C
        (branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j))) ∣ R := by
  classical
  -- the fold section is an identical `Y`-root of each rich factor
  have hsec : ∀ t ∈ T, Polynomial.eval (foldSectionAt u t) (Hp t) = 0 := fun t ht =>
    ArkLib.FactorKill.section_root_of_many_agreements (hB t ht)
      (foldSectionAt_natDegree_le u t) (S t) (hrich t ht) (hwit t ht)
  refine global_branch_of_witnessed_subcell hk hL R hRB E P T hT
    (decodeAgreesAt domain u P) M hdefect hdeg hdvdP
    (ι := Unit) (fun t _ => Hp t)
    (fun t ht _ => hirr t ht)
    (fun t ht _ k' => hB t ht k')
    (fun _ _ => ()) (fun t _ => S t)
    (fun t ht γ _ hW => ?_)
    (fun t ht γ _ _ => hrich t ht)
    (fun t ht γ _ _ => hwit t ht)
    hbig
  -- `hroot` at a witnessed scalar: the decode value is the fold value, which roots in `Hp t`
  rw [hW, ← ArkLib.FactorKill.eval_section_specializes, hsec t ht, Polynomial.eval_zero]

/-- **The proximity-fed capstone**: per-scalar agreement data (each decode agrees with the
fold on all but `e` coordinates) + the Claim 5.11 numeric leg + richness-GUARDED factor data
(demanded only at coordinates where all but `M` cell scalars agree — what
`exists_rich_coordinates` produces) yield the global branch at SOME `k`-subset of
coordinates. -/
theorem exists_global_branch_of_proximity {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
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
    ∃ T : Finset (Fin n), T.card = k ∧
      (Polynomial.X - Polynomial.C
          (branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j))) ∣ R := by
  classical
  -- Claim 5.11: `k` coordinates on which all but `M` cell scalars agree
  obtain ⟨T, hTcard, hTrich⟩ := exists_rich_coordinates E
    (fun γ => Finset.univ.filter (fun t => decodeAgreesAt domain u P t γ))
    e M k hkn hprox hnum
  -- translate membership in the agreement set
  have hmemA : ∀ (γ : F₀) (t : Fin n),
      (t ∈ Finset.univ.filter (fun t => decodeAgreesAt domain u P t γ)) ↔
        decodeAgreesAt domain u P t γ := by
    intro γ t
    simp
  have hrichT : ∀ t ∈ T,
      E.card - M ≤ (E.filter (fun γ => decodeAgreesAt domain u P t γ)).card := by
    intro t ht
    have h := hTrich t ht
    calc E.card - M
        ≤ (E.filter (fun γ =>
            t ∈ Finset.univ.filter (fun t => decodeAgreesAt domain u P t γ))).card := h
      _ = (E.filter (fun γ => decodeAgreesAt domain u P t γ)).card := by
          apply Finset.card_nbij' id id <;> intro γ hγ <;>
            simp_all [Finset.mem_filter]
  -- the defect bound at each chosen coordinate
  have hdefect : ∀ t ∈ T,
      (E.filter (fun γ => ¬ decodeAgreesAt domain u P t γ)).card ≤ M := by
    intro t ht
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := E) (p := fun γ => decodeAgreesAt domain u P t γ)
    have hge := hrichT t ht
    omega
  refine ⟨T, hTcard, ?_⟩
  exact global_branch_of_perCoordinate_rich hk hL R hRB E P T hTcard M hdefect hdeg hdvdP
    Hp (fun t ht => (hdata t (hrichT t ht)).1) (fun t ht => (hdata t (hrichT t ht)).2.1)
    S (fun t ht => (hdata t (hrichT t ht)).2.2.1) (fun t ht => (hdata t (hrichT t ht)).2.2.2)
    hbig

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms global_branch_of_perCoordinate_rich
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_global_branch_of_proximity
