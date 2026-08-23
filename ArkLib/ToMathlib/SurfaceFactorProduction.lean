/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSIntegerRepresentative

/-!
# The decoded-surface divisibility production over the GS factor set

This file composes the in-tree BCIKS20 §5 list-decoding chain into the **global surface
factor** for a Guruswami–Sudan factor: a member `R'` of the irreducible factor set
`pg_Rset` of the GS interpolant carries a trivariate linear factor
`(Y′ − C w) ∣ R'` whose surface `w ∈ F[Z][X]` is the *affine lift of the decoded family* —
it folds at every close parameter `z` to the canonical decoded polynomial `PzFamily z`.

The composition (every analytic step proven here or in-tree):

1. **Lane extraction** — `ProximityGap.exists_pg_factors_with_large_common_root_set_of_hypotheses`
   (Claim 5.7, from the `Claim57Residuals` standing inputs): a factor `R' ∈ pg_Rset` and a
   set of close parameters `z` of size `≥ #S / deg_Y Q` with
   `(eval_on_Z R' z).eval (Pz z) = 0` — the per-`z` fiber root.
2. **The weld** — `ProximityGap.exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound`
   (Claim 5.11): `k + 1` coordinates `Dtop` whose matching sets each contain the whole
   close set, so `PzFamily z (ωs x) = u₀ x + z · u₁ x` there.
3. **The affine surface** (this file, `PzFamily_eq_affine_of_matching`): Lagrange
   interpolation through `Dtop` collapses the whole decoded family to one affine pair —
   `PzFamily z = A₀ + z · A₁` for every close `z` — and `w := affinePairLift A₀ A₁` is its
   integral lift (`GuruswamiSudan.OverRatFunc.affinePairLift`), with `deg_X w ≤ k` and
   `Z`-degree `≤ 1`.
4. **The Z-direction global lift** (this file, `section_dvd_global_of_specializations`):
   per-`z` fiber divisibility `(Y′ − C (w(z,·))) ∣ R'|_{Z:=z}` on a parameter set larger
   than every `Z`-degree of the obstruction `R'.eval w ∈ F[Z][X]` forces the obstruction to
   vanish identically, i.e. `(Y′ − C w) ∣ R'`.  This is the inner-variable analogue of
   `SectionGlobalLift.section_dvd_global_of_fibers` (which lifts along the *middle*
   variable); no in-tree lemma covered the `Z` direction.

Combined with irreducibility of `pg_Rset` members the produced factor is necessarily of
`Y`-degree exactly `1` (`Bivariate.natDegreeY R' = 1`) — the §5 affine/direct-agreement
reading of the factor (consistent with the `GSSurfaceSupply` finding that a `Y`-linear
factor of an irreducible trivariate forces `natDegreeY = 1`).

## Residual hypotheses (not discharged here)

* the `Claim57Residuals` instance — the documented §5 standing inputs (graph side
  conditions, decoded matching data, close-set largeness), exactly as consumed by the
  in-tree Claim-5.7/5.11 chain;
* `hcover` / `hthreshold` / `hsmall` — the Claim-5.11 double-counting numerics, in their
  exact in-tree shapes;
* `hDZ` — a uniform bound `DZ` on the `Z`-degrees of the coefficients of `pg_Rset`
  members (in regime this follows from the `D_YZ` budget of the GS solution, but no
  in-tree lemma currently descends `Q`'s coefficient degree bounds to its normalized
  factors);
* `hbudget` — the new counting comparison `DZ + deg_Y Q < #S / deg_Y Q` making the
  obstruction-vanishing set beat the `Z`-degree budget.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claims 5.7, 5.10, 5.11; the matching surface).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace SurfaceFactorProduction

/-! ## Part 1 — coefficient-level `Z`-degree calculus

For `p ∈ F[Z][X]` (type-wise `F[X][Y]`) the relevant size is the sup of the `natDegree`s of
its base-level coefficients.  These lemmas mirror `SectionGlobalLift.eval_section_natDegree_le`
one coefficient layer deeper. -/

section ZCalculus

variable {F : Type} [Field F]

private lemma coeff_mul_natDegree_le {p q : F[X][Y]} {a b : ℕ}
    (hp : ∀ i, (p.coeff i).natDegree ≤ a) (hq : ∀ i, (q.coeff i).natDegree ≤ b) (i : ℕ) :
    ((p * q).coeff i).natDegree ≤ a + b := by
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact le_trans Polynomial.natDegree_mul_le (add_le_add (hp x.1) (hq x.2))

private lemma coeff_pow_natDegree_le {q : F[X][Y]} {b : ℕ}
    (hq : ∀ i, (q.coeff i).natDegree ≤ b) (j : ℕ) :
    ∀ i, ((q ^ j).coeff i).natDegree ≤ j * b := by
  induction j with
  | zero =>
    intro i
    rcases eq_or_ne i 0 with rfl | h
    · simp [Polynomial.coeff_one]
    · simp [Polynomial.coeff_one, h]
  | succ j ih =>
    intro i
    rw [pow_succ]
    have h1 := coeff_mul_natDegree_le ih hq i
    have h2 : j * b + b = (j + 1) * b := by ring
    omega

/-- **The coefficient-level obstruction budget**: every base-level coefficient of the
global obstruction `R.eval w ∈ F[Z][X]` has `natDegree ≤ DZ + natDegree R · b`, given the
uniform coefficient bounds `DZ` for `R` and `b` for `w`. -/
theorem eval_coeff_natDegree_le {R : F[X][X][Y]} {w : F[X][Y]} {DZ b : ℕ}
    (hR : ∀ j i, ((R.coeff j).coeff i).natDegree ≤ DZ)
    (hw : ∀ i, (w.coeff i).natDegree ≤ b) (i : ℕ) :
    ((R.eval w).coeff i).natDegree ≤ DZ + R.natDegree * b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.finset_sum_coeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have h1 := coeff_mul_natDegree_le (hR j) (coeff_pow_natDegree_le hw j) i
  have hjle : j ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h2 : j * b ≤ R.natDegree * b := Nat.mul_le_mul_right _ hjle
  omega

end ZCalculus

/-! ## Part 2 — the `Z`-direction global lift

The inner-variable analogue of `SectionGlobalLift.section_dvd_global_of_fibers`: the centre
runs over the **base** (`Z`) variable, fibers are taken with
`map (mapRingHom (evalRingHom z))` (the lane's `Trivariate.eval_on_Z`), and the obstruction
`R.eval w ∈ F[Z][X]` is killed coefficientwise by root-counting in `Z`. -/

section ZLift

variable {F : Type} [Field F]

/-- **Fiber/global commutation along `Z := z`**: specializing the global obstruction equals
reading the specialized surface at the specialized section. -/
theorem map_eval_comm (R : F[X][X][Y]) (w : F[X][Y]) (z : F) :
    (R.eval w).map (Polynomial.evalRingHom z) =
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).eval
        (w.map (Polynomial.evalRingHom z)) := by
  have h := Polynomial.eval₂_at_apply
    (p := R) (Polynomial.mapRingHom (Polynomial.evalRingHom z)) w
  rw [Polynomial.coe_mapRingHom] at h
  rw [Polynomial.eval_map]
  exact h.symm

/-- **The `Z`-direction global lift**: if the surface section roots every fiber
`R|_{Z:=z}` for `z` in a set `A` beating every `Z`-degree of the obstruction `R.eval w`,
then the surface factor divides globally: `(Y′ − C w) ∣ R`. -/
theorem section_dvd_global_of_specializations {R : F[X][X][Y]} {w : F[X][Y]} {A : Finset F}
    (hfib : ∀ z ∈ A,
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).eval
        (w.map (Polynomial.evalRingHom z)) = 0)
    (hdeg : ∀ i, ((R.eval w).coeff i).natDegree < A.card) :
    (Polynomial.X - Polynomial.C w) ∣ R := by
  rw [Polynomial.dvd_iff_isRoot]
  show R.eval w = 0
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero A ?_ ?_
  · refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast hdeg i
  · intro z hz
    have h0 : (R.eval w).map (Polynomial.evalRingHom z) = 0 := by
      rw [map_eval_comm R w z]
      exact hfib z hz
    have h1 := congrArg (fun p => p.coeff i) h0
    simpa [Polynomial.coeff_map] using h1

end ZLift

/-! ## Part 3 — degree facts for the integral affine-pair lift -/

section AffineLift

variable {F : Type} [Field F]

open GuruswamiSudan.OverRatFunc in
/-- Every coefficient of the affine-pair lift `a + Z·b` has `Z`-degree at most `1`. -/
lemma affinePairLift_coeff_natDegree_le_one (a b : F[X]) (i : ℕ) :
    ((affinePairLift a b).coeff i).natDegree ≤ 1 := by
  unfold GuruswamiSudan.OverRatFunc.affinePairLift
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map, Polynomial.coeff_map]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · simp
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp

open GuruswamiSudan.OverRatFunc in
/-- The `X`-degree of the affine-pair lift is bounded by the degrees of the pair. -/
lemma affinePairLift_natDegree_le (a b : F[X]) :
    (affinePairLift a b).natDegree ≤ max a.natDegree b.natDegree := by
  unfold GuruswamiSudan.OverRatFunc.affinePairLift
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le_max ?_ ?_)
  · exact Polynomial.natDegree_map_le
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp

end AffineLift

/-! ## Part 4 — the affine collapse of the decoded family and the production theorem -/

section Production

open ProximityGap Trivariate

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n m : ℕ} {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-- The graph-extraction side-condition package carried by a `Claim57Residuals` instance
(the class is the package plus the legacy `hfactor` bridge). -/
def graphHypothesesOfResiduals [DecidableEq (Polynomial F)] (k : ℕ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [hres : Claim57Residuals (F := F) k δ x₀ h_gs] :
    GraphExtractionHypotheses (F := F) (m := m) (n := n) (k := k)
      (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs where
  hx0 := hres.hx0
  hsep := hres.hsep
  hS_nonempty := hres.hS_nonempty
  A := hres.A
  hA := hres.hA
  hcount := hres.hcount
  hlarge := hres.hlarge

set_option maxHeartbeats 1000000 in
omit [DecidableEq (RatFunc F)] in
/-- **The affine collapse of the decoded family** (the §5-to-§6 interpolation step): once
Claim 5.11 selects `k + 1` coordinates whose matching sets contain the whole close set,
the canonical decoded family is one affine pencil — `PzFamily z = A₀ + z·A₁` with
`A₀, A₁` the Lagrange interpolants of `u₀, u₁` through the selected coordinates. -/
lemma PzFamily_eq_affine_of_matching (k : ℕ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {Dtop : Finset (Fin n)} (hDcard : Dtop.card = k + 1)
    (hsubset : ∀ x ∈ Dtop,
      coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ ⊆ matching_set_at_x k δ h_gs x)
    {z : F} (hz : z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
    PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z =
      Lagrange.interpolate Dtop (⇑ωs) u₀ +
        Polynomial.C z * Lagrange.interpolate Dtop (⇑ωs) u₁ := by
  have hinj : Set.InjOn (⇑ωs) Dtop := ωs.injective.injOn
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq Dtop hinj ?_ ?_ ?_
  · have h1 : (PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z).natDegree < k + 1 :=
      PzFamily_natDegree_lt_succ_of_mem (F := F) (n := n) (k := k) (δ := δ)
        (u₀ := u₀) (u₁ := u₁) (ωs := ωs) hz
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    rw [hDcard]
    exact_mod_cast h1
  · have h0 := Lagrange.degree_interpolate_lt (s := Dtop) (r := u₀) hinj
    have h1 := Lagrange.degree_interpolate_lt (s := Dtop) (r := u₁) hinj
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt h0 ?_)
    rcases eq_or_ne z 0 with rfl | hz0
    · simp only [Polynomial.C_0, zero_mul, Polynomial.degree_zero]
      exact lt_of_le_of_lt bot_le h1
    · rw [Polynomial.degree_C_mul hz0]
      exact h1
  · intro x hx
    have hmem : z ∈ matching_set_at_x k δ h_gs x := hsubset x hx hz
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Lagrange.eval_interpolate_at_node u₀ hinj hx,
      Lagrange.eval_interpolate_at_node u₁ hinj hx,
      PzFamily_eval_eq_lineValuePolynomial_eval_of_mem_matching_set_at_x
        (F := F) (m := m) (n := n) (k := k) (Q := Q) h_gs hmem,
      lineValuePolynomial_eval]

set_option maxHeartbeats 1000000 in
open GuruswamiSudan.OverRatFunc in
/-- **THE DECODED-SURFACE DIVISIBILITY PRODUCTION.**  From the §5 standing inputs
(`Claim57Residuals`), the Claim-5.11 double-counting numerics, a uniform `Z`-degree bound
on the GS factors (`hDZ`), and the counting budget (`hbudget`), some irreducible factor
`R'` of the GS interpolant carries the **global surface factor of the decoded family**:

* `R' ∈ pg_Rset` and `Irreducible R'`;
* `(Y′ − C w) ∣ R'` for an integral surface `w ∈ F[Z][X]`;
* hence `natDegreeY R' = 1` (the §5 affine/direct-agreement reading of the factor);
* `w` is affine in `Z` (`Z`-degree of every coefficient `≤ 1`) with `X`-degree `≤ k`;
* **coherence**: `w` folds at *every* close parameter `z` to the canonical decoded
  polynomial — `w(z, ·) = PzFamily z`. -/
theorem exists_pg_factor_with_global_section_divisor
    [NeZero n] [DecidableEq (Polynomial F)] (k : ℕ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [hres : Claim57Residuals (F := F) k δ x₀ h_gs]
    {D t DZ : ℕ}
    (hcover :
      (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card - 1 ≤
        (2 * k + 1)
          * (Bivariate.natDegreeY <| ProximityGap.H k δ x₀ h_gs)
          * (Bivariate.natDegreeY <| ProximityGap.R k δ x₀ h_gs)
          * D)
    (hthreshold :
      (2 * k + 1)
        * (Bivariate.natDegreeY <| ProximityGap.H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| ProximityGap.R k δ x₀ h_gs)
        * D + t ≤ (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card)
    (hsmall :
      ⌈δ * (n : ℚ)⌉₊ * (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card <
        (n - k) * t)
    (hDZ : ∀ R' ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs, ∀ j i, ((R'.coeff j).coeff i).natDegree ≤ DZ)
    (hbudget : DZ + Bivariate.natDegreeY Q <
        (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card / Bivariate.natDegreeY Q) :
    ∃ (R' : F[Z][X][Y]) (w : F[Z][X]),
      R' ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      Irreducible R' ∧
      (Polynomial.X - Polynomial.C w) ∣ R' ∧
      Bivariate.natDegreeY R' = 1 ∧
      w.natDegree ≤ k ∧
      (∀ i, (w.coeff i).natDegree ≤ 1) ∧
      (∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
        w.map (Polynomial.evalRingHom z) =
          PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z) := by
  classical
  -- 1. the lane extraction: a GS factor with a large per-`z` fiber-root set
  obtain ⟨R', Hp, hRmem, hRirr, _hHirr, _hHdeg, _hHdvd, _hRsep, hbig, _hlargeQ⟩ :=
    exists_pg_factors_with_large_common_root_set_of_hypotheses
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁)
      δ x₀ h_gs
      (graphHypothesesOfResiduals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) (δ := δ) (x₀ := x₀) k h_gs)
  -- 2. the weld: `k + 1` coordinates whose matching sets cover the close set
  obtain ⟨Dtop, hDcard, hsubset⟩ :=
    exists_points_with_close_subset_matching_set_of_natCeil_delta_nonmatching_bound
      (F := F) (m := m) (n := n) (k := k) (Q := Q) (δ := δ) (x₀ := x₀)
      h_gs (D := D) (t := t) hcover hthreshold hsmall
  -- 3. the affine surface interpolated through the selected coordinates
  set A₀ : F[X] := Lagrange.interpolate Dtop (⇑ωs) u₀ with hA₀
  set A₁ : F[X] := Lagrange.interpolate Dtop (⇑ωs) u₁ with hA₁
  set w : F[Z][X] := affinePairLift A₀ A₁ with hw
  have hinj : Set.InjOn (⇑ωs) Dtop := ωs.injective.injOn
  have hfold : ∀ z ∈ coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁,
      w.map (Polynomial.evalRingHom z) = PzFamily (F := F) (n := n) δ u₀ u₁ ωs k z := by
    intro z hz
    rw [hw, affinePairLift_specialize, hA₀, hA₁,
      PzFamily_eq_affine_of_matching (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
        (u₀ := u₀) (u₁ := u₁) (δ := δ) k h_gs hDcard hsubset hz]
  have hA₀deg : A₀.natDegree ≤ k := by
    have h0 := Lagrange.degree_interpolate_lt (s := Dtop) (r := u₀) hinj
    rw [← hA₀, hDcard] at h0
    by_cases hz : A₀ = 0
    · simp [hz]
    · have h1 := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by exact_mod_cast h0)
      omega
  have hA₁deg : A₁.natDegree ≤ k := by
    have h0 := Lagrange.degree_interpolate_lt (s := Dtop) (r := u₁) hinj
    rw [← hA₁, hDcard] at h0
    by_cases hz : A₁ = 0
    · simp [hz]
    · have h1 := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by exact_mod_cast h0)
      omega
  have hwdeg : w.natDegree ≤ k := by
    rw [hw]
    exact le_trans (affinePairLift_natDegree_le A₀ A₁) (max_le hA₀deg hA₁deg)
  have hwz : ∀ i, (w.coeff i).natDegree ≤ 1 := by
    intro i
    rw [hw]
    exact affinePairLift_coeff_natDegree_le_one A₀ A₁ i
  -- 4. the per-`z` specialization set, pushed down to `F`
  have hcardconv :
      (Finset.univ : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)).card =
        (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card := by
    rw [Finset.card_univ]
    exact Fintype.card_coe _
  rw [hcardconv] at hbig
  obtain ⟨Sfil, hmemP, hcard⟩ :
      ∃ Sfil : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁),
        (∀ z' ∈ Sfil,
          (Trivariate.eval_on_Z R' z'.1).eval
            (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z'.2) = 0) ∧
        (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁).card / Bivariate.natDegreeY Q ≤
          Sfil.card := by
    refine ⟨_, fun z' hz' => (Finset.mem_filter.mp hz').2.1, hbig⟩
  set Az : Finset F := Sfil.image (fun z' => (z'.1 : F)) with hAz
  have hAcard : Az.card = Sfil.card := by
    rw [hAz]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hfib : ∀ z ∈ Az,
      (R'.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).eval
        (w.map (Polynomial.evalRingHom z)) = 0 := by
    intro z hzA
    rw [hAz] at hzA
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hzA
    have h0 := hmemP z' hz'
    rw [Trivariate.eval_on_Z_eq] at h0
    rw [hfold _ z'.2,
      PzFamily_eq_Pz_of_mem (F := F) (n := n) (k := k) (δ := δ)
        (u₀ := u₀) (u₁ := u₁) (ωs := ωs) z'.2]
    exact h0
  -- 5. the `Z`-degree budget of the obstruction beats the parameter set
  have hdvdQ : R' ∣ Q := by
    have hmem' : R' ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
      have h := hRmem
      unfold pg_Rset at h
      simpa using h
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem'
  have hRdeg : R'.natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvdQ h_gs.Q_ne_0
  have hdeg : ∀ i, ((R'.eval w).coeff i).natDegree < Az.card := by
    intro i
    have h1 := eval_coeff_natDegree_le (hDZ R' hRmem) hwz i
    have h5 : DZ + Bivariate.natDegreeY Q < Sfil.card := lt_of_lt_of_le hbudget hcard
    have h6 : Bivariate.natDegreeY Q = Q.natDegree := rfl
    rw [h6] at h5
    omega
  -- 6. the `Z`-direction global lift fires
  have hdvd : (Polynomial.X - Polynomial.C w) ∣ R' :=
    section_dvd_global_of_specializations hfib hdeg
  -- 7. the `Y`-degree of the factor collapses to `1`
  have hYdeg : Bivariate.natDegreeY R' = 1 := by
    obtain ⟨d, hd⟩ := hdvd
    rcases hRirr.isUnit_or_isUnit hd with hu | hu
    · exact absurd hu (Polynomial.not_isUnit_X_sub_C w)
    · show R'.natDegree = 1
      have hdne : d ≠ 0 := hu.ne_zero
      rw [hd, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero w) hdne,
        Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu]
  exact ⟨R', w, hRmem, hRirr, hdvd, hYdeg, hwdeg, hwz, hfold⟩

end Production

end SurfaceFactorProduction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SurfaceFactorProduction.eval_coeff_natDegree_le
#print axioms ArkLib.SurfaceFactorProduction.map_eval_comm
#print axioms ArkLib.SurfaceFactorProduction.section_dvd_global_of_specializations
#print axioms ArkLib.SurfaceFactorProduction.affinePairLift_coeff_natDegree_le_one
#print axioms ArkLib.SurfaceFactorProduction.affinePairLift_natDegree_le
#print axioms ArkLib.SurfaceFactorProduction.graphHypothesesOfResiduals
#print axioms ArkLib.SurfaceFactorProduction.PzFamily_eq_affine_of_matching
#print axioms ArkLib.SurfaceFactorProduction.exists_pg_factor_with_global_section_divisor
