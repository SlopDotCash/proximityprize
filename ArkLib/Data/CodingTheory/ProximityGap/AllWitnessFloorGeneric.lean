/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalBelowUDR

/-!
# The all-witness ownership floor, generic domain (#371)

`AllWitnessOwnershipFloor.lean` proved the exact per-witness subset-ownership floor —
an unfit `w`-set carries at most `C(w−1, d+2)` fit `(d+2)`-subsets, hence at least
`C(w−1, d+1)` owned ones — over the smooth power domains `x_i = g^i` of `evalCode`.
Its mechanism (the pivot divided-difference recursion) is pure interpolation: nothing
in it needs `ZMod`, primality, or the power structure.  This file ports the floor and
its MCA assembly to **every injective evaluation domain over every finite field**
(`rsCode dom k`, `dom : Fin n ↪ F`), the same generality as the puncture-descent law
(`BelowUDRPuncture.lean`).

  **`allWitnessDom_badScalars_card_mul_le`** : at witness threshold `w₀`
  (radius `δ` with `w₀ < (1−δ)·n`), every stack over every injective domain satisfies
  `#bad · C(w₀, d+1) ≤ C(n, d+2)`.

Consequence for the generic-domain band (`allWitnessDom_band_budget`): at integer
radius `δ ≤ w/n` the threshold `w₀ = n−w−1` applies, giving
`#bad · C(n−w−1, d+1) ≤ C(n, d+2)` — on the whole below-UDR range (and at every radius)
this strictly sharpens the puncture-descent assembly budget `n^{k+1}/(n−2w−k)`; the
descent brick `mcaEvent_puncture` remains the independent transfer mechanism.

The divided-difference convergence is now complete: `fit_insert_iff_divDiffDom`
(fit-subset level, this file) and `mcaEvent_puncture` (whole-event level) are the two
faces of division at a domain point — the structure-preserving descent of this problem.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1 Degree-`d` fits over a generic domain -/

/-- Degree-`d` explainability of the word `y` on the index set `S` over the generic
injective domain `dom`: some polynomial of degree at most `d` matches `y` at every index
of `S`.  The generic-domain form of `polyFitOn`. -/
def polyFitOnDom {n : ℕ} (dom : Fin n ↪ F) (d : ℕ) (S : Finset (Fin n))
    (y : Fin n → F) : Prop :=
  ∃ q : F[X], q.natDegree ≤ d ∧ ∀ i ∈ S, y i = q.eval (dom i)

/-- Evaluations of degree-≤-`d` polynomials belong to the dimension-`(d+1)` code. -/
theorem polyEval_mem_rsCode {n : ℕ} (dom : Fin n ↪ F) {d : ℕ} (q : F[X])
    (hq : q.natDegree ≤ d) :
    (fun i : Fin n => q.eval (dom i))
      ∈ (rsCode dom (d + 1) : Submodule F (Fin n → F)) := by
  refine ⟨q, ?_, rfl⟩
  calc q.degree ≤ (q.natDegree : WithBot ℕ) := degree_le_natDegree
    _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_of_le hq

/-- `polyFitOnDom` restricts to subsets (the same interpolant works). -/
theorem fitDom_mono {n : ℕ} {dom : Fin n ↪ F} {d : ℕ} {T T' : Finset (Fin n)}
    {y : Fin n → F} (h : polyFitOnDom dom d T y) (hsub : T' ⊆ T) :
    polyFitOnDom dom d T' y := by
  obtain ⟨q, hq, hv⟩ := h
  exact ⟨q, hq, fun i hi => hv i (hsub hi)⟩

/-- Uniqueness of degree-`≤ d` interpolation through `d + 1` distinct domain points. -/
theorem fit_unique_dom {n : ℕ} (dom : Fin n ↪ F) {d : ℕ} {T : Finset (Fin n)}
    (hcard : d + 1 ≤ T.card) {q₁ q₂ : F[X]}
    (h₁ : q₁.natDegree ≤ d) (h₂ : q₂.natDegree ≤ d)
    (hagree : ∀ i ∈ T, q₁.eval (dom i) = q₂.eval (dom i)) : q₁ = q₂ := by
  by_contra hne
  refine sub_ne_zero.mpr hne ?_
  refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
    (f := q₁ - q₂) (s := T.image dom) ?_ ?_
  · have hicard : (T.image dom).card = T.card :=
      Finset.card_image_of_injective _ dom.injective
    have hdeg : (q₁ - q₂).natDegree ≤ d :=
      le_trans (Polynomial.natDegree_sub_le _ _) (max_le h₁ h₂)
    calc (q₁ - q₂).degree ≤ ((q₁ - q₂).natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (d : WithBot ℕ) := by exact_mod_cast hdeg
      _ < ((T.image dom).card : WithBot ℕ) := by
          rw [hicard]
          exact_mod_cast by omega
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Polynomial.eval_sub, hagree i hi, sub_self]

/-! ## §2 The divided-difference recursion step -/

/-- The pivot divided difference over a generic domain. -/
def divDiffDom {n : ℕ} (dom : Fin n ↪ F) (u : Fin n → F) (x₀ : Fin n) :
    Fin n → F :=
  fun i => (u i - u x₀) / (dom i - dom x₀)

/-- **The divided-difference fit transport** (generic domain): for `d ≥ 1` and `x₀ ∉ G`,
a degree-`d` fit of `u` on `insert x₀ G` is the same thing as a degree-`(d−1)` fit of the
divided difference `divDiffDom dom u x₀` on `G`. -/
theorem fit_insert_iff_divDiffDom {n : ℕ} {dom : Fin n ↪ F}
    {d : ℕ} (hd : 1 ≤ d) {x₀ : Fin n} {G : Finset (Fin n)} (hxG : x₀ ∉ G)
    {u : Fin n → F} :
    polyFitOnDom dom d (insert x₀ G) u ↔ polyFitOnDom dom (d - 1) G (divDiffDom dom u x₀) := by
  have hne : ∀ i ∈ G, dom i - dom x₀ ≠ 0 := by
    intro i hi
    refine sub_ne_zero.mpr (fun h => hxG ?_)
    rw [← dom.injective h]
    exact hi
  constructor
  · rintro ⟨q, hqdeg, hqval⟩
    have hroot : (q - Polynomial.C (u x₀)).IsRoot (dom x₀) := by
      have := hqval x₀ (Finset.mem_insert_self _ _)
      simp [Polynomial.IsRoot, ← this]
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    refine ⟨R, ?_, fun i hi => ?_⟩
    · by_cases hR0 : R = 0
      · simp [hR0]
      · have h1 : (q - Polynomial.C (u x₀)).natDegree ≤ d :=
          le_trans (Polynomial.natDegree_sub_le _ _)
            (max_le hqdeg (by simp))
        rw [hR, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hR0,
          Polynomial.natDegree_X_sub_C] at h1
        omega
    · have hev : u i - u x₀ = (dom i - dom x₀) * R.eval (dom i) := by
        have hco := congrArg (Polynomial.eval (dom i)) hR
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X] at hco
        rw [← hqval i (Finset.mem_insert_of_mem hi)] at hco
        exact hco
      show (u i - u x₀) / (dom i - dom x₀) = R.eval (dom i)
      rw [hev, mul_div_cancel_left₀ _ (hne i hi)]
  · rintro ⟨R, hRdeg, hRval⟩
    refine ⟨Polynomial.C (u x₀)
      + (Polynomial.X - Polynomial.C (dom x₀)) * R, ?_, fun i hi => ?_⟩
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_X_sub_C]
      omega
    · rcases Finset.mem_insert.mp hi with h | h
      · subst h
        simp
      · have hv := hRval i h
        simp only [divDiffDom] at hv
        rw [div_eq_iff (hne i h)] at hv
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        linear_combination hv

/-! ## §3 The erasure step -/

/-- For `w ≥ d+3`, some erasure of an unfit set stays unfit: otherwise two fitting erasures
glue through their `≥ d+1` common points into a fit of all of `S`. -/
theorem exists_erase_unfit_dom {n : ℕ} {dom : Fin n ↪ F}
    {d : ℕ} {S : Finset (Fin n)} (hcard : d + 3 ≤ S.card)
    {u : Fin n → F} (hunfit : ¬ polyFitOnDom dom d S u) :
    ∃ x ∈ S, ¬ polyFitOnDom dom d (S.erase x) u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) a
  obtain ⟨qa, hqadeg, hqaval⟩ := hcon a ha
  obtain ⟨qb, hqbdeg, hqbval⟩ := hcon b hb
  have hcommon : d + 1 ≤ ((S.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba, hb⟩),
      Finset.card_erase_of_mem ha]
    omega
  have hqq : qa = qb := by
    refine fit_unique_dom dom hcommon hqadeg hqbdeg (fun i hi => ?_)
    have hia : i ∈ S.erase a := Finset.mem_of_mem_erase hi
    have hib : i ∈ S.erase b := by
      have h1 := Finset.mem_erase.mp hi
      have h2 := Finset.mem_erase.mp hia
      exact Finset.mem_erase.mpr ⟨h1.1, h2.2⟩
    rw [← hqaval i hia, ← hqbval i hib]
  refine hunfit ⟨qa, hqadeg, fun i hi => ?_⟩
  by_cases hia : i = a
  · subst hia
    rw [hqq]
    exact hqbval i (Finset.mem_erase.mpr ⟨hba.symm, hi⟩)
  · exact hqaval i (Finset.mem_erase.mpr ⟨hia, hi⟩)

/-! ## §4 The all-witness floor -/

open Classical in
/-- **The all-witness fit-subset bound** (auxiliary, fuel-indexed form): an unfit `w`-set
has at most `C(w−1, d+2)` fit `(d+2)`-subsets.  Divided-difference double recursion on
`(d, w)`, fueled by `N ≥ d + w` — the generic-domain port. -/
private theorem fitDom_subsets_card_le_aux {n : ℕ} (dom : Fin n ↪ F) :
    ∀ N d : ℕ, ∀ S : Finset (Fin n), ∀ u : Fin n → F, d + S.card ≤ N →
      ¬ polyFitOnDom dom d S u →
      ((S.powersetCard (d + 2)).filter (fun T => polyFitOnDom dom d T u)).card
        ≤ (S.card - 1).choose (d + 2) := by
  intro N
  induction N with
  | zero =>
    intro d S u hfuel hunfit
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    refine absurd ⟨0, by simp, fun i hi => ?_⟩ hunfit
    rw [hS0] at hi
    exact absurd hi (Finset.notMem_empty i)
  | succ N ih =>
    intro d S u hfuel hunfit
    by_cases hsmall : S.card ≤ d + 2
    · have hempty : (S.powersetCard (d + 2)).filter (fun T => polyFitOnDom dom d T u) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro T hT
        obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
        have hTS : T = S := Finset.eq_of_subset_of_card_le hTsub (by omega)
        rw [hTS]
        exact hunfit
      simp [hempty]
    · push Not at hsmall
      obtain ⟨x₀, hx₀S, hx₀unfit⟩ := exists_erase_unfit_dom (by omega) hunfit
      have hWcard : (S.erase x₀).card = S.card - 1 := Finset.card_erase_of_mem hx₀S
      set Ffam := (S.powersetCard (d + 2)).filter (fun T => polyFitOnDom dom d T u)
        with hFdef
      have hsplit : (Ffam.filter (fun T => x₀ ∈ T)).card
          + (Ffam.filter (fun T => ¬ x₀ ∈ T)).card = Ffam.card :=
        Finset.filter_card_add_filter_neg_card_eq_card (s := Ffam) (p := fun T => x₀ ∈ T)
      have havoid : Ffam.filter (fun T => ¬ x₀ ∈ T)
          = ((S.erase x₀).powersetCard (d + 2)).filter (fun T => polyFitOnDom dom d T u) := by
        ext T
        simp only [hFdef, Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨⟨hTsub, hTcard⟩, hTfit⟩, hTx⟩
          exact ⟨⟨Finset.subset_erase.mpr ⟨hTsub, hTx⟩, hTcard⟩, hTfit⟩
        · rintro ⟨⟨hTsub, hTcard⟩, hTfit⟩
          obtain ⟨h1, h2⟩ := Finset.subset_erase.mp hTsub
          exact ⟨⟨⟨h1, hTcard⟩, hTfit⟩, h2⟩
      have havoid_le : (Ffam.filter (fun T => ¬ x₀ ∈ T)).card
          ≤ (S.card - 2).choose (d + 2) := by
        rw [havoid]
        have h := ih d (S.erase x₀) u (by omega) hx₀unfit
        rwa [hWcard, show S.card - 1 - 1 = S.card - 2 from by omega] at h
      have hcontain_le : (Ffam.filter (fun T => x₀ ∈ T)).card
          ≤ (S.card - 2).choose (d + 1) := by
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · subst hd0
          obtain ⟨z, hzW, hzne⟩ : ∃ z ∈ S.erase x₀, u z ≠ u x₀ := by
            by_contra hcon
            push Not at hcon
            refine hunfit ⟨Polynomial.C (u x₀), by simp, fun i hi => ?_⟩
            rw [Polynomial.eval_C]
            by_cases hix : i = x₀
            · rw [hix]
            · exact hcon i (Finset.mem_erase.mpr ⟨hix, hi⟩)
          set M := (S.erase x₀).filter (fun y => u y = u x₀) with hMdef
          have hMcard : M.card ≤ S.card - 2 := by
            have hsub : M ⊆ (S.erase x₀).erase z := by
              intro y hy
              obtain ⟨hyW, hyv⟩ := Finset.mem_filter.mp hy
              exact Finset.mem_erase.mpr ⟨fun h => hzne (h ▸ hyv), hyW⟩
            calc M.card ≤ ((S.erase x₀).erase z).card := Finset.card_le_card hsub
            _ = (S.erase x₀).card - 1 := Finset.card_erase_of_mem hzW
            _ = S.card - 2 := by omega
          have hmaps : ∀ T ∈ Ffam.filter (fun T => x₀ ∈ T),
              T.erase x₀ ∈ M.powersetCard 1 := by
            intro T hT
            obtain ⟨hTF, hTx⟩ := Finset.mem_filter.mp hT
            rw [hFdef] at hTF
            obtain ⟨hTmem, hTfit⟩ := Finset.mem_filter.mp hTF
            obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
            refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
            · intro y hy
              obtain ⟨hyx, hyT⟩ := Finset.mem_erase.mp hy
              obtain ⟨q, hqdeg, hqval⟩ := hTfit
              have hq : q = Polynomial.C (q.coeff 0) :=
                Polynomial.eq_C_of_natDegree_le_zero hqdeg
              have hval : u y = u x₀ := by
                rw [hqval y hyT, hqval x₀ hTx, hq]
                simp
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨hyx, hTsub hyT⟩, hval⟩
            · rw [Finset.card_erase_of_mem hTx, hTcard]
          have hinj : Set.InjOn (fun T : Finset (Fin n) => T.erase x₀)
              ↑(Ffam.filter (fun T => x₀ ∈ T)) := by
            intro T1 hT1 T2 hT2 h12
            have hx1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT1)).2
            have hx2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT2)).2
            have h12' : T1.erase x₀ = T2.erase x₀ := h12
            rw [← Finset.insert_erase hx1, ← Finset.insert_erase hx2, h12']
          calc (Ffam.filter (fun T => x₀ ∈ T)).card
              ≤ (M.powersetCard 1).card := Finset.card_le_card_of_injOn _ hmaps hinj
          _ = M.card.choose 1 := Finset.card_powersetCard _ _
          _ = M.card := Nat.choose_one_right _
          _ ≤ (S.card - 2).choose (0 + 1) := by
              rw [Nat.choose_one_right]
              exact hMcard
        · have hvunfit : ¬ polyFitOnDom dom (d - 1) (S.erase x₀) (divDiffDom dom u x₀) := by
            intro hfit
            have h := (fit_insert_iff_divDiffDom (G := S.erase x₀) hdpos
              (Finset.notMem_erase x₀ S)).mpr hfit
            rw [Finset.insert_erase hx₀S] at h
            exact hunfit h
          have hmaps : ∀ T ∈ Ffam.filter (fun T => x₀ ∈ T),
              T.erase x₀ ∈ ((S.erase x₀).powersetCard (d + 1)).filter
                (fun G => polyFitOnDom dom (d - 1) G (divDiffDom dom u x₀)) := by
            intro T hT
            obtain ⟨hTF, hTx⟩ := Finset.mem_filter.mp hT
            rw [hFdef] at hTF
            obtain ⟨hTmem, hTfit⟩ := Finset.mem_filter.mp hTF
            obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
            have hGsub : T.erase x₀ ⊆ S.erase x₀ := fun y hy => by
              obtain ⟨hyx, hyT⟩ := Finset.mem_erase.mp hy
              exact Finset.mem_erase.mpr ⟨hyx, hTsub hyT⟩
            have hGcard : (T.erase x₀).card = d + 1 := by
              rw [Finset.card_erase_of_mem hTx, hTcard]
              omega
            have hGfit : polyFitOnDom dom (d - 1) (T.erase x₀) (divDiffDom dom u x₀) := by
              refine (fit_insert_iff_divDiffDom hdpos
                (Finset.notMem_erase x₀ T)).mp ?_
              rwa [Finset.insert_erase hTx]
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_powersetCard.mpr ⟨hGsub, hGcard⟩, hGfit⟩
          have hinj : Set.InjOn (fun T : Finset (Fin n) => T.erase x₀)
              ↑(Ffam.filter (fun T => x₀ ∈ T)) := by
            intro T1 hT1 T2 hT2 h12
            have hx1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT1)).2
            have hx2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hT2)).2
            have h12' : T1.erase x₀ = T2.erase x₀ := h12
            rw [← Finset.insert_erase hx1, ← Finset.insert_erase hx2, h12']
          have hrec : (((S.erase x₀).powersetCard ((d - 1) + 2)).filter
              (fun G => polyFitOnDom dom (d - 1) G (divDiffDom dom u x₀))).card
                ≤ ((S.erase x₀).card - 1).choose ((d - 1) + 2) :=
            ih (d - 1) (S.erase x₀) (divDiffDom dom u x₀) (by omega) hvunfit
          rw [show (d - 1) + 2 = d + 1 from by omega, hWcard,
            show S.card - 1 - 1 = S.card - 2 from by omega] at hrec
          calc (Ffam.filter (fun T => x₀ ∈ T)).card
              ≤ (((S.erase x₀).powersetCard (d + 1)).filter
                  (fun G => polyFitOnDom dom (d - 1) G (divDiffDom dom u x₀))).card :=
                Finset.card_le_card_of_injOn _ hmaps hinj
          _ ≤ (S.card - 2).choose (d + 1) := hrec
      have hpascal : (S.card - 2).choose (d + 1) + (S.card - 2).choose (d + 2)
          = (S.card - 1).choose (d + 2) := by
        rw [show S.card - 1 = (S.card - 2) + 1 from by omega]
        exact (Nat.choose_succ_succ (S.card - 2) (d + 1)).symm
      omega

open Classical in
/-- **THE ALL-WITNESS FIT-SUBSET BOUND, generic domain.**  If `u` has no degree-`d` fit
on `S` (`|S| = w`), then at most `C(w−1, d+2)` of the `(d+2)`-subsets of `S` are fit. -/
theorem fitDom_subsets_card_le {n : ℕ} (dom : Fin n ↪ F)
    {d : ℕ} {S : Finset (Fin n)} {u : Fin n → F}
    (hunfit : ¬ polyFitOnDom dom d S u) :
    ((S.powersetCard (d + 2)).filter (fun T => polyFitOnDom dom d T u)).card
      ≤ (S.card - 1).choose (d + 2) :=
  fitDom_subsets_card_le_aux dom (d + S.card) d S u le_rfl hunfit

open Classical in
/-- **THE ALL-WITNESS OWNERSHIP FLOOR, generic domain.**  If `u` has no degree-`d` fit on
`S` (`|S| = w`), then at least `C(w−1, d+1)` of the `(d+2)`-subsets of `S` are unfit. -/
theorem unfitDom_subsets_card_ge {n : ℕ} (dom : Fin n ↪ F)
    {d : ℕ} {S : Finset (Fin n)} {u : Fin n → F}
    (hunfit : ¬ polyFitOnDom dom d S u) :
    (S.card - 1).choose (d + 1)
      ≤ ((S.powersetCard (d + 2)).filter (fun T => ¬ polyFitOnDom dom d T u)).card := by
  have hsplit : ((S.powersetCard (d + 2)).filter (fun T => polyFitOnDom dom d T u)).card
      + ((S.powersetCard (d + 2)).filter (fun T => ¬ polyFitOnDom dom d T u)).card
      = (S.powersetCard (d + 2)).card :=
    Finset.filter_card_add_filter_neg_card_eq_card
      (s := S.powersetCard (d + 2)) (p := fun T => polyFitOnDom dom d T u)
  have htotal : (S.powersetCard (d + 2)).card = S.card.choose (d + 2) :=
    Finset.card_powersetCard _ _
  have hfit := fitDom_subsets_card_le dom hunfit
  have hS1 : 1 ≤ S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | h
    · exfalso
      refine hunfit ⟨0, by simp, fun i hi => ?_⟩
      rw [Finset.card_eq_zero.mp h0] at hi
      exact absurd hi (Finset.notMem_empty i)
    · exact h
  have hpascal : S.card.choose (d + 2)
      = (S.card - 1).choose (d + 1) + (S.card - 1).choose (d + 2) := by
    rw [show S.card = (S.card - 1) + 1 from by omega]
    rw [show (S.card - 1) + 1 - 1 = S.card - 1 from by omega]
    exact Nat.choose_succ_succ (S.card - 1) (d + 1)
  omega

/-! ## §5 The assembly: `#bad · C(w₀, d+1) ≤ C(n, d+2)` at every radius, every domain -/

open Classical in
/-- **The all-witness ownership assembly, generic domain.**  At witness threshold `w₀`
(radius `δ` with `w₀ < (1−δ)·n`), every stack over every injective evaluation domain
satisfies `#bad · C(w₀, d+1) ≤ C(n, d+2)` — each bad scalar owns the unfit
`(d+2)`-subsets of its witness, an owned subset determines its scalar, and only
`C(n, d+2)` subsets exist. -/
theorem allWitnessDom_badScalars_card_mul_le {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (d w₀ : ℕ)
    {δ : ℝ≥0} (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    (Finset.filter (fun γ : F =>
        mcaEvent (F := F) (A := F)
          ((rsCode dom (d + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
        Finset.univ).card * w₀.choose (d + 1)
      ≤ n.choose (d + 2) := by
  classical
  set B := Finset.filter (fun γ : F =>
      mcaEvent (F := F) (A := F)
        ((rsCode dom (d + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
      Finset.univ with hBdef
  -- witness extraction: size ≥ w₀+1, line degree-d-fit, u₁ NOT fit
  have hwit : ∀ γ ∈ B, ∃ S : Finset (Fin n), w₀ + 1 ≤ S.card ∧
      (∃ qS : F[X], qS.natDegree ≤ d ∧
        ∀ i ∈ S, u₀ i + γ * u₁ i = qS.eval (dom i)) ∧
      ¬ polyFitOnDom dom d S u₁ := by
    intro γ hγ
    obtain ⟨S, hScard, ⟨w, hwC, hagree⟩, hnojoint⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨qS, hqSdeg, hw⟩ := hwC
    have hqSnat : qS.natDegree ≤ d := by
      by_cases hq0 : qS = 0
      · simp [hq0]
      · have := (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hqSdeg
        omega
    have hlin : ∀ i ∈ S, u₀ i + γ * u₁ i = qS.eval (dom i) := by
      intro i hi
      have h := hagree i hi
      rw [hw, smul_eq_mul] at h
      exact h.symm
    have hSw : w₀ + 1 ≤ S.card := by
      have h2 : ((w₀ : ℕ) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hδ hScard
      have h2' : w₀ < S.card := by exact_mod_cast h2
      omega
    refine ⟨S, hSw, ⟨qS, hqSnat, hlin⟩, ?_⟩
    rintro ⟨q₁, hq₁deg, hq₁⟩
    refine hnojoint ⟨fun i => (qS - Polynomial.C γ * q₁).eval (dom i),
      polyEval_mem_rsCode dom _ (le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le hqSnat (le_trans (Polynomial.natDegree_C_mul_le _ _) hq₁deg))),
      fun i => q₁.eval (dom i), polyEval_mem_rsCode dom _ hq₁deg,
      fun i hi => ⟨?_, ?_⟩⟩
    · show (qS - Polynomial.C γ * q₁).eval (dom i) = u₀ i
      have e := hlin i hi
      have e1 := hq₁ i hi
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      linear_combination γ * e1 - e
    · exact (hq₁ i hi).symm
  choose Sf hSf using hwit
  -- per-scalar owned family: unfit (d+2)-subsets of the witness
  set Pt : {x // x ∈ B} → Finset (Finset (Fin n)) := fun γ =>
    (((Finset.univ : Finset (Fin n)).powersetCard (d + 2)).filter
      (fun R => R ⊆ Sf γ.1 γ.2 ∧ ¬ polyFitOnDom dom d R u₁)) with hPt
  have hPr : ∀ γ : {x // x ∈ B}, w₀.choose (d + 1) ≤ (Pt γ).card := by
    intro γ
    obtain ⟨hcard, _, hunfit⟩ := hSf γ.1 γ.2
    have hfloor := unfitDom_subsets_card_ge dom hunfit
    have hmono : w₀.choose (d + 1) ≤ ((Sf γ.1 γ.2).card - 1).choose (d + 1) :=
      Nat.choose_le_choose _ (by omega)
    have hsub : ((Sf γ.1 γ.2).powersetCard (d + 2)).filter
        (fun T => ¬ polyFitOnDom dom d T u₁) ⊆ Pt γ := by
      intro R hR
      obtain ⟨hRmem, hRnf⟩ := Finset.mem_filter.mp hR
      obtain ⟨hRsub, hRc⟩ := Finset.mem_powersetCard.mp hRmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hRc⟩, hRsub, hRnf⟩
    calc w₀.choose (d + 1) ≤ ((Sf γ.1 γ.2).card - 1).choose (d + 1) := hmono
    _ ≤ (((Sf γ.1 γ.2).powersetCard (d + 2)).filter
          (fun T => ¬ polyFitOnDom dom d T u₁)).card := hfloor
    _ ≤ (Pt γ).card := Finset.card_le_card hsub
  -- disjointness: a common owned subset would fit u₁
  have hPdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ → Disjoint (Pt γ₁) (Pt γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro R hR1 hR2
    obtain ⟨_, hRsub1, hRunfit⟩ := Finset.mem_filter.mp hR1
    obtain ⟨_, hRsub2, _⟩ := Finset.mem_filter.mp hR2
    obtain ⟨q₁, hq₁deg, hl1⟩ := (hSf γ₁.1 γ₁.2).2.1
    obtain ⟨q₂, hq₂deg, hl2⟩ := (hSf γ₂.1 γ₂.2).2.1
    have hγne : γ₁.1 - γ₂.1 ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
    refine hRunfit ⟨Polynomial.C (γ₁.1 - γ₂.1)⁻¹ * (q₁ - q₂),
      le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_trans (Polynomial.natDegree_sub_le _ _) (max_le hq₁deg hq₂deg)),
      fun i hi => ?_⟩
    have e1 := hl1 i (hRsub1 hi)
    have e2 := hl2 i (hRsub2 hi)
    have hdiff : (γ₁.1 - γ₂.1) * u₁ i = (q₁ - q₂).eval (dom i) := by
      rw [Polynomial.eval_sub]
      linear_combination e1 - e2
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← hdiff, ← mul_assoc,
      inv_mul_cancel₀ hγne, one_mul]
  -- assemble
  have hbig : B.attach.card * w₀.choose (d + 1) ≤ (B.attach.biUnion Pt).card := by
    rw [Finset.card_biUnion hPdisj]
    calc B.attach.card * w₀.choose (d + 1)
        = ∑ _γ ∈ B.attach, w₀.choose (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hPr γ)
  have hsubE : (B.attach.biUnion Pt) ⊆ (Finset.univ : Finset (Fin n)).powersetCard (d + 2) := by
    intro R hR
    obtain ⟨γ, _, hRP⟩ := Finset.mem_biUnion.mp hR
    exact (Finset.mem_filter.mp hRP).1
  calc B.card * w₀.choose (d + 1) = B.attach.card * w₀.choose (d + 1) := by
        rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Pt).card := hbig
  _ ≤ (((Finset.univ : Finset (Fin n))).powersetCard (d + 2)).card :=
        Finset.card_le_card hsubE
  _ = n.choose (d + 2) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The generic-domain band budget** (integer-radius form): at every radius `δ ≤ w/n`
with `w + 1 ≤ n`, the witness threshold `w₀ = n − w − 1` applies, giving

  `#bad · C(n−w−1, d+1) ≤ C(n, d+2)`

for every stack over every injective evaluation domain — on the whole below-UDR range
(and at every radius) this strictly sharpens the puncture-descent assembly budget. -/
theorem allWitnessDom_badScalars_card_mul_le_w {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (d : ℕ) {w : ℕ} (hwn : w + 1 ≤ n)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (u₀ u₁ : Fin n → F) :
    (Finset.filter (fun γ : F =>
        mcaEvent (F := F) (A := F)
          ((rsCode dom (d + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
        Finset.univ).card * (n - w - 1).choose (d + 1)
      ≤ n.choose (d + 2) := by
  refine allWitnessDom_badScalars_card_mul_le dom d (n - w - 1) ?_ u₀ u₁
  rw [Fintype.card_fin]
  have hsub : ((n : ℝ≥0) - (w : ℝ≥0)) ≤ ((1 : ℝ≥0) - δ) * (n : ℝ≥0) := by
    rw [tsub_mul, one_mul]
    exact tsub_le_tsub_left (by rwa [Fintype.card_fin] at hδn) _
  calc ((n - w - 1 : ℕ) : ℝ≥0) < ((n - w : ℕ) : ℝ≥0) := by
        have : n - w - 1 < n - w := by omega
        exact_mod_cast this
    _ = (n : ℝ≥0) - (w : ℝ≥0) := Nat.cast_tsub n w
    _ ≤ ((1 : ℝ≥0) - δ) * (n : ℝ≥0) := hsub

open Classical in
omit [DecidableEq F] in
/-- Fixed-stack probability form of `allWitnessDom_badScalars_card_mul_le`: at witness
threshold `w₀ ≥ d+1`, every stack's bad-scalar probability is bounded by the all-witness
floor divided by the field size. -/
theorem allWitnessDom_mcaEvent_prob_le {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (d w₀ : ℕ) (hw₀ : d + 1 ≤ w₀)
    {δ : ℝ≥0} (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (A := F)
        ((rsCode dom (d + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ]
      ≤ ((n.choose (d + 2) / w₀.choose (d + 1) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  have h := allWitnessDom_badScalars_card_mul_le dom d w₀ hδ u₀ u₁
  have hpos : 0 < w₀.choose (d + 1) :=
    Nat.choose_pos (by omega)
  have hdiv : (Finset.filter (fun γ : F =>
      mcaEvent (F := F) (A := F)
        ((rsCode dom (d + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
      Finset.univ).card ≤ n.choose (d + 2) / w₀.choose (d + 1) :=
    Nat.le_div_iff_mul_le hpos |>.mpr h
  exact_mod_cast hdiv

open Classical in
/-- **The all-witness `ε_mca` bound, generic domain**: at witness threshold `w₀ ≥ d+1`,
`ε_mca ≤ (C(n, d+2)/C(w₀, d+1))/|F|`. -/
theorem allWitnessDom_epsMCA_le {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (d w₀ : ℕ) (hw₀ : d + 1 ≤ w₀)
    {δ : ℝ≥0} (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := F) (A := F)
        ((rsCode dom (d + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n.choose (d + 2) / w₀.choose (d + 1) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  exact iSup_le fun u => allWitnessDom_mcaEvent_prob_le dom d w₀ hw₀ hδ (u 0) (u 1)

open Classical in
/-- **The threshold form, generic domain**: `δ* ≥ δ` at the all-witness budget for every
injective evaluation domain over every finite field. -/
theorem le_mcaDeltaStar_allWitnessDom {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (d w₀ : ℕ) (hw₀ : d + 1 ≤ w₀)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {εstar : ℝ≥0∞}
    (hbudget : ((n.choose (d + 2) / w₀.choose (d + 1) : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom (d + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (allWitnessDom_epsMCA_le dom d w₀ hw₀ hδ) hbudget)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.fit_insert_iff_divDiffDom
#print axioms ProximityGap.Ownership.fitDom_subsets_card_le
#print axioms ProximityGap.Ownership.unfitDom_subsets_card_ge
#print axioms ProximityGap.Ownership.allWitnessDom_badScalars_card_mul_le
#print axioms ProximityGap.Ownership.allWitnessDom_badScalars_card_mul_le_w
#print axioms ProximityGap.Ownership.allWitnessDom_mcaEvent_prob_le
#print axioms ProximityGap.Ownership.allWitnessDom_epsMCA_le
#print axioms ProximityGap.Ownership.le_mcaDeltaStar_allWitnessDom
