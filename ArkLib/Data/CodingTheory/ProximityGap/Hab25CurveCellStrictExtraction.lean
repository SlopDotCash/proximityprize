/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CoordinateUpgradeWeld

/-!
# The elementary per-cell strict extraction (#304, SK1)

**The strict Johnson coefficient-polynomial extraction, per section-linked cell, by plain
counting** — no Hensel lifting, no `𝒪`-ring, no `Λ`-weights, no characteristic hypothesis.
At a cell of the (curve) GS production — an irreducible factor `R` of the interpolant with
a uniform decode family `P` and the surface divisibility `(Y − C w) ∣ R` — the §5 Steps
5–7 machinery collapses:

* `decode_eq_surface_map` — **the decode IS the surface's specialization**:
  `P γ = w.map (evalRingHom γ)` (irreducibility makes `R` an associate of the surface
  factor; the fiber strips to a unit times `X − C (w(γ))`; monic-linear divisibility in a
  domain pins the root);
* `foldSection_eq_of_heavy` — at a coordinate carrying `> max(B_w, k)` agreeing cell
  scalars, the surface's coordinate section **is** the degree-`≤ k` fold section
  (one root count);
* `surface_coeff_natDegree_le` — with `> deg w` such coordinates, every coefficient of
  `w` has `Z`-degree `≤ k` (a second root count on the coefficient slices);
* **`strict_coeffPolys_of_cell`** — the capstone: the coefficient polynomials demanded by
  `StrictCoeffPolysResidual` exist on the cell, and they are **literally the coefficients
  of the surface**: `B j := w.coeff j`, `natDegree < k + 1`, and
  `(P γ).coeff j = (B j).eval γ` for every cell scalar (by `coeff_map`).

Char-uniformity (SA5): no `CharZero`/`CharP`/separability hypothesis appears — the
extraction is field-uniform at the cell level, removing BCIKS20 App. C from this layer.

What this does NOT give (honest scope): the GLOBAL single-`B` family across the whole
good set demanded by the literal `StrictCoeffPolysResidual` — the paper's own Prop 5.5
yields a SUBSET (`|S′| ≥ |S|/2D_Y`) on one curve, and the global form is the Step-8 /
uniqueness layer (SK3 audit on the issue).  Composed with
`exists_curve_cell_production_total` + pigeonhole, this brick yields the Prop-5.5-faithful
subset form (SK2).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace BCIKS20.CurveCellStrictExtraction

open Polynomial Polynomial.Bivariate Finset
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-! ## The decode is the surface's specialization -/

/-- **The decode IS the surface's specialization** (the map form of the section link,
arity-generic): cell irreducibility + the surface divisibility pin every cell decode to
`w.map (evalRingHom γ)`. -/
theorem decode_eq_surface_map {R : (F₀[X])[X][Y]}
    (hRirr : Irreducible R) {w : F₀[X][Y]}
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (γ : F₀) (P : F₀[X])
    (hdvdP : (Polynomial.X - Polynomial.C P) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    P = w.map (Polynomial.evalRingHom γ) := by
  classical
  have hXw_nu : ¬ IsUnit (Polynomial.X - Polynomial.C w) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc⟩ := hwdvd
  have hcu : IsUnit c := (hRirr.isUnit_or_isUnit hc).resolve_left hXw_nu
  set φ : (F₀[X])[X] →+* F₀[X] := Polynomial.mapRingHom (Polynomial.evalRingHom γ) with hφ
  set wγ : F₀[X] := w.map (Polynomial.evalRingHom γ) with hwγ
  have hfiber : R.map φ = (Polynomial.X - Polynomial.C wγ) * c.map φ := by
    rw [hc, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hcuγ : IsUnit (c.map φ) := hcu.map (Polynomial.mapRingHom φ)
  have hdvd2 : (Polynomial.X - Polynomial.C P) ∣ (Polynomial.X - Polynomial.C wγ) := by
    have h := hdvdP
    rw [hfiber] at h
    exact (IsUnit.dvd_mul_right hcuγ).mp h
  obtain ⟨q, hq⟩ := hdvd2
  have hXw0 : (Polynomial.X - Polynomial.C wγ : F₀[X][Y]) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero wγ
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact hXw0 hq
  have hdegq : q.natDegree = 0 := by
    have hdegs := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero P) hq0,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C] at hdegs
    omega
  have ha1 : q.leadingCoeff = 1 := by
    have hlc := congrArg Polynomial.leadingCoeff hq
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_sub_C,
      Polynomial.leadingCoeff_X_sub_C, one_mul] at hlc
    exact hlc.symm
  have hq1 : q = 1 := by
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdegq
    rw [hC] at ha1 ⊢
    rw [Polynomial.leadingCoeff_C] at ha1
    rw [ha1, Polynomial.C_1]
  rw [hq1, mul_one] at hq
  exact (Polynomial.C_injective (sub_right_inj.mp hq)).symm

/-! ## The eval swap and the coordinate section -/

/-- Outer-evaluation at a constant commutes with inner specialization:
`(w.eval (C a)).eval z = (w.map (evalRingHom z)).eval a`. -/
theorem eval_C_eval_eq_map_eval (w : F₀[X][Y]) (a z : F₀) :
    (w.eval (Polynomial.C a)).eval z
      = (w.map (Polynomial.evalRingHom z)).eval a := by
  have h := ArkLib.FactorKill.eval_section_specializes w (Polynomial.C a) z
  rw [h, Polynomial.eval_C]

/-- The coordinate section's degree is bounded by the surface's flat coefficient budget. -/
theorem eval_C_natDegree_le (w : F₀[X][Y]) (a : F₀) {Bw : ℕ}
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw) :
    (w.eval (Polynomial.C a)).natDegree ≤ Bw := by
  rw [Polynomial.eval_eq_sum_range]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 := hB i
  have h2 : ((Polynomial.C a : F₀[X]) ^ i).natDegree = 0 := by
    rw [← Polynomial.C_pow, Polynomial.natDegree_C]
  omega

/-- The `m`-th inner coefficient of the coordinate section is the evaluation of the
coefficient slice: `(w.eval (C a)).coeff m = ∑ i, (w.coeff i).coeff m · aⁱ`. -/
theorem eval_C_coeff (w : F₀[X][Y]) (a : F₀) (m : ℕ) :
    (w.eval (Polynomial.C a)).coeff m
      = ∑ i ∈ Finset.range (w.natDegree + 1), (w.coeff i).coeff m * a ^ i := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_pow, Polynomial.coeff_mul_C]

/-- **The fold-section identification (one root count)**: a coordinate section agreeing
with the degree-`≤ k` fold section at more than `max(B_w, k)` scalars IS the fold
section. -/
theorem foldSection_eq_of_heavy {n L : ℕ} {u : WordStack F₀ (Fin L) (Fin n)}
    {w : F₀[X][Y]} {Bw k : ℕ} (hLk : L - 1 ≤ k)
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw)
    (a : F₀) (t : Fin n) (S : Finset F₀)
    (hcard : max Bw k < S.card)
    (hagree : ∀ z ∈ S, (w.eval (Polynomial.C a)).eval z = (foldSectionAt u t).eval z) :
    w.eval (Polynomial.C a) = foldSectionAt u t := by
  classical
  by_contra hne
  have hsub0 : w.eval (Polynomial.C a) - foldSectionAt u t ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (w.eval (Polynomial.C a) - foldSectionAt u t).natDegree ≤ max Bw k := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le_max (eval_C_natDegree_le w a hB) ?_
    exact le_trans (foldSectionAt_natDegree_le u t) hLk
  have hroots : S ⊆ (w.eval (Polynomial.C a) - foldSectionAt u t).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub0]
    show (w.eval (Polynomial.C a) - foldSectionAt u t).eval z = 0
    rw [Polynomial.eval_sub, hagree z hz, sub_self]
  have hle : S.card ≤ max Bw k :=
    le_trans (Finset.card_le_card hroots)
      (le_trans (Multiset.toFinset_card_le _)
        (le_trans (Polynomial.card_roots' _) hdeg))
  omega

/-! ## The coefficient slices vanish above degree `k` -/

/-- **The Z-degree collapse (the second root count)**: with more than `deg w` coordinates
each identifying the section with the fold, every coefficient of the surface has inner
degree `≤ k`. -/
theorem surface_coeff_natDegree_le {n L : ℕ} {domain : Fin n ↪ F₀}
    {u : WordStack F₀ (Fin L) (Fin n)}
    {w : F₀[X][Y]} {Bw k : ℕ} (hLk : L - 1 ≤ k)
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw)
    (T : Finset (Fin n)) (hT : w.natDegree < T.card)
    (S : Fin n → Finset F₀)
    (hcard : ∀ t ∈ T, max Bw k < (S t).card)
    (hagree : ∀ t ∈ T, ∀ z ∈ S t,
      (w.eval (Polynomial.C (domain t))).eval z = (foldSectionAt u t).eval z) :
    ∀ j, (w.coeff j).natDegree ≤ k := by
  classical
  -- each chosen coordinate's section IS the fold section
  have hsec : ∀ t ∈ T, w.eval (Polynomial.C (domain t)) = foldSectionAt u t :=
    fun t ht => foldSection_eq_of_heavy hLk hB (domain t) t (S t) (hcard t ht)
      (hagree t ht)
  -- hence each section has inner degree ≤ k
  have hsecdeg : ∀ t ∈ T, (w.eval (Polynomial.C (domain t))).natDegree ≤ k := by
    intro t ht
    rw [hsec t ht]
    exact le_trans (foldSectionAt_natDegree_le u t) hLk
  -- the coefficient slice at inner index m > k
  intro j
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  -- the slice polynomial: X-coefficients are the m-th inner coefficients of w's coeffs
  set cm : F₀[X] := ∑ i ∈ Finset.range (w.natDegree + 1),
    Polynomial.monomial i ((w.coeff i).coeff m) with hcm
  have hcmdeg : cm.natDegree ≤ w.natDegree := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine le_trans (Polynomial.natDegree_monomial_le _) ?_
    rw [Finset.mem_range] at hi
    omega
  have hcmeval : ∀ a : F₀, cm.eval a = (w.eval (Polynomial.C a)).coeff m := by
    intro a
    rw [eval_C_coeff, hcm, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial]
  -- the slice vanishes at every chosen coordinate point (the section has degree ≤ k < m)
  have hvanish : ∀ t ∈ T, cm.eval (domain t) = 0 := by
    intro t ht
    rw [hcmeval]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hsecdeg t ht) hm)
  -- more roots than the degree: the slice is zero
  have hcm0 : cm = 0 := by
    by_contra hne
    have hroots : T.image (fun t => domain t) ⊆ cm.roots.toFinset := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨t, ht, rfl⟩ := ha
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hvanish t ht
    have hinj : (T.image (fun t => domain t)).card = T.card :=
      Finset.card_image_of_injective T domain.injective
    have hle : T.card ≤ w.natDegree := by
      calc T.card = (T.image (fun t => domain t)).card := hinj.symm
        _ ≤ cm.roots.toFinset.card := Finset.card_le_card hroots
        _ ≤ cm.roots.card := Multiset.toFinset_card_le _
        _ ≤ cm.natDegree := Polynomial.card_roots' _
        _ ≤ w.natDegree := hcmdeg
    omega
  -- extract the coefficient: the slice's j-th X-coefficient is (w.coeff j).coeff m
  have hcoeff : cm.coeff j = (w.coeff j).coeff m := by
    rw [hcm, Polynomial.finset_sum_coeff]
    rcases lt_or_ge j (w.natDegree + 1) with hj | hj
    · rw [Finset.sum_eq_single j
        (fun i _ hij => by rw [Polynomial.coeff_monomial, if_neg hij])
        (fun h => absurd (Finset.mem_range.mpr hj) h)]
      rw [Polynomial.coeff_monomial, if_pos rfl]
    · -- past the degree: both sides vanish
      have hwj : w.coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hwj, Polynomial.coeff_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [Polynomial.coeff_monomial, if_neg (by omega)]
  rw [← hcoeff, hcm0, Polynomial.coeff_zero]

/-! ## The capstone: the strict coefficient polynomials on the cell -/

/-- **THE ELEMENTARY PER-CELL STRICT EXTRACTION (#304, SK1).**  On a section-linked cell
of the curve GS production, the coefficient polynomials demanded by the strict Johnson
extraction exist, with the residual's exact degree bound — and they are **literally the
coefficients of the surface** (`B j := w.coeff j`).  No Hensel lifting, no `𝒪`-ring, no
`Λ`-weights, no characteristic hypothesis. -/
theorem strict_coeffPolys_of_cell {n L : ℕ} {domain : Fin n ↪ F₀}
    {u : WordStack F₀ (Fin L) (Fin n)}
    {R : (F₀[X])[X][Y]} (hRirr : Irreducible R)
    {w : F₀[X][Y]} (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    {Bw k : ℕ} (hLk : L - 1 ≤ k)
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw)
    (E : Finset F₀) (P : F₀ → F₀[X])
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    -- the heavy coordinates: more than `deg w` of them, each with more than
    -- `max(B_w, k)` cell scalars whose decode agrees with the fold there
    (T : Finset (Fin n)) (hT : w.natDegree < T.card)
    (S : Fin n → Finset F₀) (hSE : ∀ t ∈ T, S t ⊆ E)
    (hcard : ∀ t ∈ T, max Bw k < (S t).card)
    (hagree : ∀ t ∈ T, ∀ z ∈ S t,
      (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    ∃ B : ℕ → F₀[X],
      (∀ j, (B j).natDegree < k + 1) ∧
      ∀ γ ∈ E, ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  -- the surface's coordinate sections satisfy the heavy agreement
  have hagree' : ∀ t ∈ T, ∀ z ∈ S t,
      (w.eval (Polynomial.C (domain t))).eval z = (foldSectionAt u t).eval z := by
    intro t ht z hz
    rw [eval_C_eval_eq_map_eval,
      ← decode_eq_surface_map hRirr hwdvd z (P z) (hdvdP z (hSE t ht hz))]
    exact hagree t ht z hz
  -- the Z-degree collapse
  have hdeg := surface_coeff_natDegree_le (domain := domain) (u := u) hLk hB T hT S
    hcard hagree'
  -- the coefficient polynomials are the surface's coefficients
  refine ⟨fun j => w.coeff j, fun j => Nat.lt_succ_of_le (hdeg j), fun γ hγ j => ?_⟩
  rw [decode_eq_surface_map hRirr hwdvd γ (P γ) (hdvdP γ hγ), Polynomial.coeff_map]
  rfl

/-- **Sharper fold-degree form of SK1.**  The cell proof actually bounds the coefficient
polynomials by the fold length: with the heavy-section cardinality measured against
`L - 1`, the witnesses satisfy `deg(B j) < L`.  This is the form needed when the
residual's coefficient-polynomial degree budget is the fold degree rather than the decoded
RS degree. -/
theorem strict_coeffPolys_of_cell_degree_lt_L {n L : ℕ} (hL : 0 < L)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    {R : (F₀[X])[X][Y]} (hRirr : Irreducible R)
    {w : F₀[X][Y]} (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    {Bw : ℕ}
    (hB : ∀ i, (w.coeff i).natDegree ≤ Bw)
    (E : Finset F₀) (P : F₀ → F₀[X])
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (T : Finset (Fin n)) (hT : w.natDegree < T.card)
    (S : Fin n → Finset F₀) (hSE : ∀ t ∈ T, S t ⊆ E)
    (hcard : ∀ t ∈ T, max Bw (L - 1) < (S t).card)
    (hagree : ∀ t ∈ T, ∀ z ∈ S t,
      (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    ∃ B : ℕ → F₀[X],
      (∀ j, (B j).natDegree < L) ∧
      ∀ γ ∈ E, ∀ j, (P γ).coeff j = (B j).eval γ := by
  obtain ⟨B, hBdeg, hBmatch⟩ :=
    strict_coeffPolys_of_cell (domain := domain) (u := u) hRirr hwdvd
      (k := L - 1) le_rfl hB E P hdvdP T hT S hSE hcard hagree
  refine ⟨B, ?_, hBmatch⟩
  intro j
  simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hL)] using hBdeg j

/-! ## SK2: the Prop-5.5-faithful subset form (pigeonhole over the cells) -/

/-- **The heavy factor cell exists (pigeonhole)**: in any cell decomposition of the good
set with the degenerate cell bounded by `T < |G|` and `≤ ℓ` factor cells, some factor
cell carries at least a `1/ℓ` share of the non-degenerate mass. -/
theorem exists_heavy_factor_cell {Idx : Type} [DecidableEq F₀] [DecidableEq Idx]
    (G : Finset F₀) (Index : Finset (Option Idx))
    (Ecell : Option Idx → Finset F₀) {ℓ T : ℕ}
    (hIdx : Index.card ≤ ℓ + 1) (hnone : none ∈ Index)
    (hcover : G ⊆ Index.biUnion Ecell)
    (hnoneCard : (Ecell none).card ≤ T)
    (hbig : T < G.card) :
    ∃ R : Idx, some R ∈ Index ∧ G.card ≤ T + ℓ * (Ecell (some R)).card := by
  classical
  set Fac : Finset (Option Idx) := Index.erase none with hFac
  have hFacCard : Fac.card ≤ ℓ := by
    have h : Fac.card = Index.card - 1 := by
      rw [hFac]
      exact Finset.card_erase_of_mem hnone
    omega
  -- the cover bound
  have hsum : G.card ≤ (Ecell none).card + ∑ ij ∈ Fac, (Ecell ij).card := by
    calc G.card ≤ (Index.biUnion Ecell).card := Finset.card_le_card hcover
      _ ≤ ∑ ij ∈ Index, (Ecell ij).card := Finset.card_biUnion_le
      _ = (Ecell none).card + ∑ ij ∈ Fac, (Ecell ij).card := by
          rw [hFac, ← Finset.add_sum_erase _ _ hnone]
  -- the factor cells are nonempty as a family (else |G| ≤ T)
  have hFacNe : Fac.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hsum
    omega
  -- the maximal factor cell
  obtain ⟨ij₀, hij₀, hmax⟩ := Finset.exists_max_image Fac (fun ij => (Ecell ij).card) hFacNe
  have hsum2 : ∑ ij ∈ Fac, (Ecell ij).card ≤ ℓ * (Ecell ij₀).card := by
    calc ∑ ij ∈ Fac, (Ecell ij).card
        ≤ ∑ _ij ∈ Fac, (Ecell ij₀).card := Finset.sum_le_sum (fun ij hij => hmax ij hij)
      _ = Fac.card * (Ecell ij₀).card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ℓ * (Ecell ij₀).card := Nat.mul_le_mul_right _ hFacCard
  -- ij₀ is a `some`
  obtain ⟨hij₀mem, hij₀ne⟩ := Finset.mem_erase.mp hij₀
  obtain ⟨R, rfl⟩ := Option.ne_none_iff_exists'.mp hij₀mem
  exact ⟨R, hij₀ne, by omega⟩

/-- **THE PROP-5.5-FAITHFUL SUBSET EXTRACTION (#304, SK2)**: composing the cell pigeonhole
with the elementary per-cell extraction — in any section-linked cell decomposition of the
good set, some factor cell of `1/ℓ` mass carries the FULL strict coefficient-polynomial
family.  This is the exact shape of BCIKS20 Proposition 5.5 (a `≥ |S|/2D_Y`-style subset
on one curve), with the curve's coefficient polynomials literally the cell surface's
coefficients. -/
theorem strict_coeffPolys_of_heavy_cell {n L : ℕ} [DecidableEq F₀] {domain : Fin n ↪ F₀}
    {u : WordStack F₀ (Fin L) (Fin n)}
    (G : Finset F₀)
    {Idx : Type} [DecidableEq Idx]
    (Index : Finset (Option Idx)) (Ecell : Option Idx → Finset F₀) (P : F₀ → F₀[X])
    {ℓ T : ℕ}
    (hIdx : Index.card ≤ ℓ + 1) (hnone : none ∈ Index)
    (hcover : G ⊆ Index.biUnion Ecell)
    (hnoneCard : (Ecell none).card ≤ T)
    (hbig : T < G.card)
    -- the per-factor-cell data: the factor, the surface, and the heavy coordinates
    (Rof : Idx → (F₀[X])[X][Y])
    (hRirr : ∀ R, some R ∈ Index → Irreducible (Rof R))
    (hdvdP : ∀ R, some R ∈ Index → ∀ γ ∈ Ecell (some R),
      (Polynomial.X - Polynomial.C (P γ)) ∣
        (Rof R).map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (wof : Idx → F₀[X][Y]) {Bw k : ℕ} (hLk : L - 1 ≤ k)
    (hwdvd : ∀ R, some R ∈ Index →
      (Polynomial.X - Polynomial.C (wof R)) ∣ Rof R)
    (hB : ∀ R, some R ∈ Index → ∀ i, ((wof R).coeff i).natDegree ≤ Bw)
    (Tset : Idx → Finset (Fin n))
    (hT : ∀ R, some R ∈ Index → (wof R).natDegree < (Tset R).card)
    (Sset : Idx → Fin n → Finset F₀)
    (hSE : ∀ R, some R ∈ Index → ∀ t ∈ Tset R, Sset R t ⊆ Ecell (some R))
    (hScard : ∀ R, some R ∈ Index → ∀ t ∈ Tset R, max Bw k < (Sset R t).card)
    (hagree : ∀ R, some R ∈ Index → ∀ t ∈ Tset R, ∀ z ∈ Sset R t,
      (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    ∃ G' : Finset F₀, G.card ≤ T + ℓ * G'.card ∧ G' ⊆ Index.biUnion Ecell ∧
      ∃ B : ℕ → F₀[X],
        (∀ j, (B j).natDegree < k + 1) ∧
        ∀ γ ∈ G', ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  obtain ⟨R, hR, hRcount⟩ := exists_heavy_factor_cell G Index Ecell hIdx hnone hcover
    hnoneCard hbig
  obtain ⟨B, hBdeg, hBmatch⟩ := strict_coeffPolys_of_cell (domain := domain) (u := u)
    (hRirr R hR) (hwdvd R hR) hLk (hB R hR)
    (Ecell (some R)) P (hdvdP R hR)
    (Tset R) (hT R hR) (Sset R) (hSE R hR) (hScard R hR) (hagree R hR)
  refine ⟨Ecell (some R), hRcount, ?_, B, hBdeg, hBmatch⟩
  intro γ hγ
  exact Finset.mem_biUnion.mpr ⟨some R, hR, hγ⟩

/-- **Global-branch cells feed the Prop-5.5 subset extraction.**  This is the consumer-side
adapter from the existing branch-production lane to `strict_coeffPolys_of_heavy_cell`: if
each factor cell already carries a global section branch
`Y - branchOfCurveTuple(T_R)` and enough scalars in that cell agree with the corresponding
fold sections at the selected coordinates, then the heavy-cell coefficient-polynomial
subset follows directly.  The theorem does not construct the branches; it only packages
their degree and agreement consequences into the SK2 heavy-cell interface. -/
theorem strict_coeffPolys_of_heavy_cell_of_global_branches {n L k : ℕ}
    [Finite F₀] [DecidableEq F₀] (hk : 0 < k) (hL : 0 < L) (hLk : L - 1 ≤ k)
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (G : Finset F₀)
    {Idx : Type}
    (Index : Finset (Option Idx)) (Ecell : Option Idx → Finset F₀) (P : F₀ → F₀[X])
    {ℓ T : ℕ}
    (hIdx : Index.card ≤ ℓ + 1) (hnone : none ∈ Index)
    (hcover : G ⊆ Index.biUnion Ecell)
    (hnoneCard : (Ecell none).card ≤ T)
    (hbig : T < G.card)
    (Rof : Idx → (F₀[X])[X][Y])
    (hRirr : ∀ R, some R ∈ Index → Irreducible (Rof R))
    (hdvdP : ∀ R, some R ∈ Index → ∀ γ ∈ Ecell (some R),
      (Polynomial.X - Polynomial.C (P γ)) ∣
        (Rof R).map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (Tset : Idx → Finset (Fin n))
    (hTcard : ∀ R, some R ∈ Index → (Tset R).card = k)
    (hbranch : ∀ R, some R ∈ Index →
      (Polynomial.X - Polynomial.C
        (branchOfCurveTuple (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j))) ∣
          Rof R)
    (hEbig : ∀ R, some R ∈ Index → max (L - 1) k < (Ecell (some R)).card)
    (hagree : ∀ R, some R ∈ Index → ∀ t ∈ Tset R, ∀ z ∈ Ecell (some R),
      (P z).eval (domain t) = (foldSectionAt u t).eval z) :
    ∃ G' : Finset F₀, G.card ≤ T + ℓ * G'.card ∧ G' ⊆ Index.biUnion Ecell ∧
      ∃ B : ℕ → F₀[X],
        (∀ j, (B j).natDegree < k + 1) ∧
        ∀ γ ∈ G', ∀ j, (P γ).coeff j = (B j).eval γ := by
  classical
  letI : Fintype F₀ := Fintype.ofFinite F₀
  letI : DecidableEq Idx := Classical.decEq Idx
  let wof : Idx → F₀[X][Y] :=
    fun R => branchOfCurveTuple (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j)
  refine strict_coeffPolys_of_heavy_cell (domain := domain) (u := u) G Index Ecell P
    hIdx hnone hcover hnoneCard hbig Rof hRirr hdvdP wof (Bw := L - 1) (k := k)
    hLk hbranch ?_ Tset ?_ (fun R _ => Ecell (some R)) ?_ ?_ ?_
  · intro R _hR i
    have h := branchOfCurveTuple_coeff_natDegree_lt hL
      (fun j : Fin L => lagrangeCurveTuple domain u (Tset R) j) i
    simp [wof] at h ⊢
    omega
  · intro R hR
    have ha : ∀ j : Fin L,
        (lagrangeCurveTuple domain u (Tset R) j).natDegree < k := fun j =>
      lagrangeCurveTuple_natDegree_lt hk domain u (hTcard R hR) j
    have hpHat := branchOfCurveTuple_natDegree_lt hk ha
    rw [hTcard R hR]
    exact hpHat
  · intro R _hR _t _ht
    exact subset_rfl
  · intro R hR _t _ht
    exact hEbig R hR
  · intro R hR t ht z hz
    exact hagree R hR t ht z hz

end BCIKS20.CurveCellStrictExtraction

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.CurveCellStrictExtraction.decode_eq_surface_map
#print axioms BCIKS20.CurveCellStrictExtraction.foldSection_eq_of_heavy
#print axioms BCIKS20.CurveCellStrictExtraction.surface_coeff_natDegree_le
#print axioms BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell
#print axioms BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_cell_degree_lt_L
#print axioms BCIKS20.CurveCellStrictExtraction.exists_heavy_factor_cell
#print axioms BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_heavy_cell
#print axioms BCIKS20.CurveCellStrictExtraction.strict_coeffPolys_of_heavy_cell_of_global_branches
