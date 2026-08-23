/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorAssignment
import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-!
# BCIKS20 Claim 5.7, combinatorial half — the `x₀`-fiber refinement and the pigeonhole

Issue #302 (Hab25 §3 / [BCI⁺20, ePrint 2020/654] Claim 5.7). The *algebraic* half of
Claim 5.7 — the per-`z` factor assignment `z ↦ i` with
`(Y − C q_z) ∣ (rep Rᵢ)|_{Z:=z}` — is proven in-tree
(`exists_specialized_factor_assignment`, `GSFactorAssignment.lean`). This file proves the
remaining *combinatorial* half:

> *"substituting `x₀` ⇒ some `j` with `H_{ij}(P_z(x₀), z) = 0`, where
> `Rᵢ(x₀,Y,Z) = Cᵢ(Z)·∏ⱼ H_{ij}(Y,Z)`; the number of pairs `(i,j)` is at most `D_Y`, so
> the most common cell `S_{x₀,R,H}` has `|S_{x₀,R,H}| ≥ |S| / D_Y`."*

* `pointEval_fiberX` — the **fiber–specialization commutation**: evaluating
  `A|_{Z:=z}` at `Y := q` then `X := x₀` equals the point evaluation of the `x₀`-fiber
  `A|_{X:=x₀} ∈ F[Z][Y]` at `(Y, Z) = (q(x₀), z)` (both are the total evaluation of `A` at
  `(x₀, q(x₀), z)`);
* `pointEval_fiberX_eq_zero_of_dvd` — the refinement core: a decoded linear divisor of
  `A|_{Z:=z}` places `(q_z(x₀), z)` on the `x₀`-fiber curve;
* `exists_posdeg_factor_pointEval_eq_zero` — the **`j`-assignment**: a point root of the
  fiber is a point root of one of its (≤ `deg_Y`-many) positive-`Y`-degree irreducible
  components, provided `z` avoids the roots of the `Z`-only components (`zOnlyPart`, an
  explicit nonzero avoidance polynomial — the paper's `Cᵢ(z) ≠ 0`);
* `card_posdeg_factors_le` / `sum_natDegree_distinct_factors_le` — the **cell count**
  `#(i,j) ≤ D_Y` (distinct positive-degree irreducible factors of a bivariate polynomial
  over a field are at most its outer degree);
* `exists_large_cell` — the pigeonhole;
* `claim57_cells` — the assembled combinatorial half, generically over any factor family
  with nonzero `x₀`-fibers (the S5 good-point output shape);
* `sum_fiberX_natDegree_le` — the fiber cell budget is the paper's `D_Y = deg_Y Q`: the
  integer representatives inherit the `Y`-degrees of the `K`-level factors;
* `claim57_pigeonhole` — **the capstone**, composing with the in-tree algebraic half: for
  the integer model `Q₀` of a nonzero `Q ∈ K[X][Y]`, there are representatives `rep`, an
  avoidance polynomial `bad`, and — for every `x₀` whose fibers are nonzero (the S5
  good-point hypothesis) — a per-`x₀` avoidance polynomial `badZ`, such that any finite
  set `S` of avoided scalars with decoded divisibilities `(Y − C q_z) ∣ Q₀|_{Z:=z}` is
  covered by at most `D_Y = deg_Y Q` incidence cells
  `S_{x₀,R,H} = {z ∈ S : (Y − C q_z) ∣ (rep R)|_{Z:=z} ∧ H(q_z(x₀), z) = 0}`,
  and `D_Y · T < |S|` forces a cell with more than `T` scalars — exactly the incidence
  threshold [BCI⁺20, Steps 5–7] consume.

Everything here is elementary bookkeeping; the genuinely deep remaining content for #302
(the `Λ`-weight/`β_t` analysis of Steps 5–7 forcing `R = (Y − (a+Zb))^{p^f}` above the
threshold) is unchanged and NOT claimed.

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc.Claim57

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-! ## The `x₀`-fiber and the point evaluation -/

/-- The `x₀`-fiber of an integer-model trivariate polynomial `A ∈ F[Z][X][Y]`: evaluate the
middle (lift) variable `X` at the constant `C x₀ ∈ F[Z]`, yielding the bivariate fiber
polynomial in `(Y, Z)` (`Y` outer, `Z` inner) — the paper's `Rᵢ(x₀, Y, Z)`. -/
noncomputable def fiberX (x₀ : F) (A : (F[X])[X][Y]) : F[X][Y] :=
  A.map (Polynomial.evalRingHom (Polynomial.C x₀))

/-- Point evaluation of a `(Y, Z)`-bivariate polynomial at `(y, z) ∈ F²`: specialize
`Z := z` coefficientwise, then evaluate `Y := y`. A ring hom into `F`. -/
noncomputable def pointEval (y z : F) : F[X][Y] →+* F :=
  (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom z))

lemma pointEval_apply (y z : F) (G : F[X][Y]) :
    pointEval y z G = (G.map (Polynomial.evalRingHom z)).eval y := rfl

/-! ## The fiber–specialization commutation (the refinement core) -/

/-- **Fiber–specialization commutation.** Evaluating the specialization `A|_{Z:=z}` at
`Y := q` and then `X := x₀` equals the point evaluation of the `x₀`-fiber at
`(q(x₀), z)`: both compute the total evaluation of `A` at `(X, Y, Z) = (x₀, q(x₀), z)`. -/
theorem pointEval_fiberX (x₀ z : F) (q : F[X]) (A : (F[X])[X][Y]) :
    pointEval (q.eval x₀) z (fiberX x₀ A) =
      Polynomial.eval x₀ (Polynomial.eval q
        (A.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))) := by
  have hhom : (Polynomial.evalRingHom z).comp (Polynomial.evalRingHom (Polynomial.C x₀))
      = (Polynomial.evalRingHom x₀).comp
          (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  calc pointEval (q.eval x₀) z (fiberX x₀ A)
      = ((A.map (Polynomial.evalRingHom (Polynomial.C x₀))).map
          (Polynomial.evalRingHom z)).eval (q.eval x₀) := rfl
    _ = (A.map ((Polynomial.evalRingHom z).comp
          (Polynomial.evalRingHom (Polynomial.C x₀)))).eval (q.eval x₀) := by
        rw [Polynomial.map_map]
    _ = Polynomial.eval₂ ((Polynomial.evalRingHom z).comp
          (Polynomial.evalRingHom (Polynomial.C x₀))) (q.eval x₀) A := by
        rw [Polynomial.eval_map]
    _ = Polynomial.eval₂ ((Polynomial.evalRingHom x₀).comp
          (Polynomial.mapRingHom (Polynomial.evalRingHom z))) (q.eval x₀) A := by
        rw [hhom]
    _ = Polynomial.eval x₀ (Polynomial.eval₂
          (Polynomial.mapRingHom (Polynomial.evalRingHom z)) q A) :=
        (Polynomial.hom_eval₂ A (Polynomial.mapRingHom (Polynomial.evalRingHom z))
          (Polynomial.evalRingHom x₀) q).symm
    _ = Polynomial.eval x₀ (Polynomial.eval q
          (A.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))) := by
        rw [Polynomial.eval_map]

/-- **The refinement core.** A decoded linear divisor `(Y − C q) ∣ A|_{Z:=z}` places the
point `(q(x₀), z)` on the `x₀`-fiber curve of `A`. -/
theorem pointEval_fiberX_eq_zero_of_dvd {x₀ z : F} {q : F[X]} {A : (F[X])[X][Y]}
    (h : (Polynomial.X - Polynomial.C q) ∣
      A.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    pointEval (q.eval x₀) z (fiberX x₀ A) = 0 := by
  have hroot : Polynomial.eval q
      (A.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) = 0 :=
    Polynomial.dvd_iff_isRoot.mp h
  rw [pointEval_fiberX, hroot, Polynomial.eval_zero]

/-! ## The `j`-assignment: point roots route through irreducible fiber components -/

/-- A point root of a nonzero bivariate polynomial is a point root of one of its
irreducible factors (the unit is an `F`-constant, killed by no point). -/
theorem exists_factor_pointEval_eq_zero {G : F[X][Y]} (hG : G ≠ 0) {y z : F}
    (h0 : pointEval y z G = 0) :
    ∃ p ∈ (UniqueFactorizationMonoid.factors G).toFinset, pointEval y z p = 0 := by
  classical
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hG
  have h1 : pointEval y z (UniqueFactorizationMonoid.factors G).prod *
      pointEval y z (u : F[X][Y]) = 0 := by
    rw [← map_mul, hu, h0]
  have hu0 : pointEval y z (u : F[X][Y]) ≠ 0 :=
    (u.isUnit.map (pointEval y z)).ne_zero
  have h2 : pointEval y z (UniqueFactorizationMonoid.factors G).prod = 0 :=
    (mul_eq_zero.mp h1).resolve_right hu0
  rw [map_multiset_prod] at h2
  obtain ⟨p, hp, hp0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h2)
  exact ⟨p, Multiset.mem_toFinset.mpr hp, hp0⟩

/-- The `Z`-only part of the distinct irreducible factors of a fiber polynomial: the
product of the constant (`Y`-degree-0) components, as an element of `F[Z]` — the paper's
`Cᵢ(Z)`. Scalars `z` avoiding its roots cannot be captured by a degenerate component. -/
noncomputable def zOnlyPart (G : F[X][Y]) : F[X] :=
  ∏ p ∈ (UniqueFactorizationMonoid.factors G).toFinset.filter
      (fun p => p.natDegree = 0), p.coeff 0

theorem zOnlyPart_ne_zero (G : F[X][Y]) : zOnlyPart G ≠ 0 := by
  rw [zOnlyPart, Finset.prod_ne_zero_iff]
  intro p hp h0
  have hirr : Irreducible p := UniqueFactorizationMonoid.irreducible_of_factor p
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
  exact hirr.ne_zero (by
    rw [Polynomial.eq_C_of_natDegree_eq_zero (Finset.mem_filter.mp hp).2, h0,
      Polynomial.C_0])

/-- **The `j`-assignment.** A point root of the nonzero fiber polynomial at an avoided `z`
(`zOnlyPart G` does not vanish — the paper's `Cᵢ(z) ≠ 0`) is a point root of a
positive-`Y`-degree irreducible component `H_{ij}`. -/
theorem exists_posdeg_factor_pointEval_eq_zero {G : F[X][Y]} (hG : G ≠ 0) {y z : F}
    (h0 : pointEval y z G = 0) (hz : (zOnlyPart G).eval z ≠ 0) :
    ∃ p ∈ (UniqueFactorizationMonoid.factors G).toFinset,
      0 < p.natDegree ∧ pointEval y z p = 0 := by
  obtain ⟨p, hp, hp0⟩ := exists_factor_pointEval_eq_zero hG h0
  refine ⟨p, hp, ?_, hp0⟩
  by_contra hdeg
  have hdeg0 : p.natDegree = 0 := Nat.eq_zero_of_not_pos hdeg
  have heval : (p.coeff 0).eval z = 0 := by
    have hPC := hp0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0] at hPC
    simpa [pointEval_apply] using hPC
  apply hz
  rw [zOnlyPart, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hp, hdeg0⟩) heval

/-! ## The cell count: distinct positive-degree factors are at most the degree -/

/-- The sum of the outer degrees of the *distinct* irreducible factors of a nonzero
bivariate polynomial over a field is at most its outer degree. -/
theorem sum_natDegree_distinct_factors_le {k : Type*} [Field k] {G : k[X][Y]}
    (hG : G ≠ 0) :
    ∑ p ∈ (UniqueFactorizationMonoid.factors G).toFinset, p.natDegree ≤ G.natDegree := by
  classical
  set s := UniqueFactorizationMonoid.factors G with hs
  have h0 : (0 : k[X][Y]) ∉ s := fun h =>
    (UniqueFactorizationMonoid.irreducible_of_factor 0 h).ne_zero rfl
  have h3 : ∑ p ∈ s.toFinset, p.natDegree ≤ (s.map Polynomial.natDegree).sum := by
    rw [Finset.sum_multiset_map_count]
    refine Finset.sum_le_sum fun p hp => ?_
    have hc : 0 < s.count p := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    calc p.natDegree = 1 * p.natDegree := (one_mul _).symm
      _ ≤ s.count p * p.natDegree := Nat.mul_le_mul_right _ hc
      _ = s.count p • p.natDegree := (smul_eq_mul _ _).symm
  have h4 : (s.map Polynomial.natDegree).sum = s.prod.natDegree :=
    (Polynomial.natDegree_multiset_prod s h0).symm
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hG
  have hprod0 : s.prod ≠ 0 := fun h =>
    h0 (Multiset.prod_eq_zero_iff.mp h)
  have h5 : G.natDegree = s.prod.natDegree := by
    rw [← hu, Polynomial.natDegree_mul hprod0 (Units.ne_zero u),
      Polynomial.natDegree_eq_zero_of_isUnit u.isUnit, Nat.add_zero]
  omega

/-- **The cell count `#(i,j) ≤ D_Y`, per factor.** A nonzero bivariate polynomial over a
field has at most `natDegree`-many distinct positive-degree irreducible factors. -/
theorem card_posdeg_factors_le {k : Type*} [Field k] {G : k[X][Y]} (hG : G ≠ 0) :
    ((UniqueFactorizationMonoid.factors G).toFinset.filter
      (fun p => 0 < p.natDegree)).card ≤ G.natDegree := by
  classical
  have h1 : ((UniqueFactorizationMonoid.factors G).toFinset.filter
      (fun p => 0 < p.natDegree)).card ≤
      ∑ p ∈ (UniqueFactorizationMonoid.factors G).toFinset.filter
        (fun p => 0 < p.natDegree), p.natDegree := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2
  have h2 : ∑ p ∈ (UniqueFactorizationMonoid.factors G).toFinset.filter
        (fun p => 0 < p.natDegree), p.natDegree ≤
      ∑ p ∈ (UniqueFactorizationMonoid.factors G).toFinset, p.natDegree :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact le_trans h1 (le_trans h2 (sum_natDegree_distinct_factors_le hG))

/-! ## The pigeonhole -/

/-- **Pigeonhole over a cell cover.** If `S` is covered by the cells of `Index` and
`|Index| · T < |S|`, some cell exceeds `T`. -/
theorem exists_large_cell {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (Index : Finset β) (cell : β → Finset α) (T : ℕ)
    (hcover : ∀ z ∈ S, ∃ c ∈ Index, z ∈ cell c)
    (hbig : Index.card * T < S.card) :
    ∃ c ∈ Index, T < (cell c).card := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ Index.biUnion cell := fun z hz => by
    obtain ⟨c, hc, hzc⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨c, hc, hzc⟩
  have h1 : S.card ≤ (Index.biUnion cell).card := Finset.card_le_card hsub
  have h2 : (Index.biUnion cell).card ≤ ∑ c ∈ Index, (cell c).card :=
    Finset.card_biUnion_le
  have h3 : ∑ c ∈ Index, (cell c).card ≤ Index.card * T := by
    calc ∑ c ∈ Index, (cell c).card ≤ ∑ _c ∈ Index, T := Finset.sum_le_sum hcon
      _ = Index.card * T := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-! ## The assembled combinatorial half -/

/-- The Claim-5.7 incidence cell `S_{x₀,R,H}`: the scalars of `S` whose decoded polynomial
divides the specialization of factor `c.1`'s representative AND whose fiber value lies on
the irreducible fiber component `c.2` — `{z ∈ S : (Y − C q_z) ∣ R|_{Z:=z} ∧
H(q_z(x₀), z) = 0}`. -/
noncomputable def cell {ι : Type*} (rep : ι → (F[X])[X][Y]) (x₀ : F) (qz : F → F[X])
    (S : Finset F) (c : ι × F[X][Y]) : Finset F :=
  S.filter fun z =>
    (Polynomial.X - Polynomial.C (qz z)) ∣
        (rep c.1).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ∧
      pointEval ((qz z).eval x₀) z c.2 = 0

lemma mem_cell {ι : Type*} {rep : ι → (F[X])[X][Y]} {x₀ : F} {qz : F → F[X]}
    {S : Finset F} {c : ι × F[X][Y]} {z : F} :
    z ∈ cell rep x₀ qz S c ↔ z ∈ S ∧
      ((Polynomial.X - Polynomial.C (qz z)) ∣
          (rep c.1).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ∧
        pointEval ((qz z).eval x₀) z c.2 = 0) := by
  rw [cell, Finset.mem_filter]

/-- **BCIKS20 Claim 5.7, combinatorial half (fiber refinement + cell count + pigeonhole),
generically.** Given a factor family `Fs` with representatives `rep` whose `x₀`-fibers are
nonzero (the S5 good-point output), a scalar set `S` with a per-`z` factor assignment (the
in-tree algebraic half) avoiding the `Z`-only fiber components: `S` is covered by at most
`∑_R deg_Y (fiber R)` incidence cells, and `(∑_R deg_Y (fiber R)) · T < |S|` forces a cell
with more than `T` scalars. -/
theorem claim57_cells {ι : Type*} [DecidableEq ι]
    (Fs : Finset ι) (rep : ι → (F[X])[X][Y]) (x₀ : F)
    (hfib : ∀ R ∈ Fs, fiberX x₀ (rep R) ≠ 0)
    (S : Finset F) (qz : F → F[X])
    (hassign : ∀ z ∈ S, ∃ R ∈ Fs,
      (Polynomial.X - Polynomial.C (qz z)) ∣
        (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hz : ∀ z ∈ S, ∀ R ∈ Fs, (zOnlyPart (fiberX x₀ (rep R))).eval z ≠ 0) :
    ∃ Index : Finset (ι × F[X][Y]),
      Index.card ≤ ∑ R ∈ Fs, (fiberX x₀ (rep R)).natDegree ∧
      (∀ c ∈ Index, c.1 ∈ Fs ∧
        c.2 ∈ (UniqueFactorizationMonoid.factors (fiberX x₀ (rep c.1))).toFinset ∧
        0 < c.2.natDegree) ∧
      (∀ z ∈ S, ∃ c ∈ Index, z ∈ cell rep x₀ qz S c) ∧
      (∀ T : ℕ, (∑ R ∈ Fs, (fiberX x₀ (rep R)).natDegree) * T < S.card →
        ∃ c ∈ Index, T < (cell rep x₀ qz S c).card) := by
  classical
  set Index : Finset (ι × F[X][Y]) := Fs.biUnion (fun R =>
      ((UniqueFactorizationMonoid.factors (fiberX x₀ (rep R))).toFinset.filter
        (fun p => 0 < p.natDegree)).image (fun p => (R, p))) with hIdx
  have hcard : Index.card ≤ ∑ R ∈ Fs, (fiberX x₀ (rep R)).natDegree := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun R hR => ?_)
    exact le_trans Finset.card_image_le (card_posdeg_factors_le (hfib R hR))
  have hshape : ∀ c ∈ Index, c.1 ∈ Fs ∧
      c.2 ∈ (UniqueFactorizationMonoid.factors (fiberX x₀ (rep c.1))).toFinset ∧
      0 < c.2.natDegree := by
    intro c hc
    obtain ⟨R, hR, hcim⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hcim
    obtain ⟨hpmem, hpdeg⟩ := Finset.mem_filter.mp hp
    rcases hpc.symm with rfl
    exact ⟨hR, hpmem, hpdeg⟩
  have hcover : ∀ z ∈ S, ∃ c ∈ Index, z ∈ cell rep x₀ qz S c := by
    intro z hzS
    obtain ⟨R, hR, hdvd⟩ := hassign z hzS
    have h0 : pointEval ((qz z).eval x₀) z (fiberX x₀ (rep R)) = 0 :=
      pointEval_fiberX_eq_zero_of_dvd hdvd
    obtain ⟨p, hp, hpdeg, hp0⟩ :=
      exists_posdeg_factor_pointEval_eq_zero (hfib R hR) h0 (hz z hzS R hR)
    refine ⟨(R, p), ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨R, hR, Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hp, hpdeg⟩, rfl⟩⟩
    · exact mem_cell.mpr ⟨hzS, hdvd, hp0⟩
  refine ⟨Index, hcard, hshape, hcover, fun T hT => ?_⟩
  exact exists_large_cell S Index _ T hcover
    (lt_of_le_of_lt (Nat.mul_le_mul_right T hcard) hT)

/-! ## The cell budget is the paper's `D_Y` -/

/-- **The fiber cell budget is `D_Y = deg_Y Q`.** Integer representatives inherit the
`Y`-degrees of the `K = F(Z)`-level factors (the denominator constant is degree-neutral and
the coefficient embedding is injective), fibers only lower degree, and distinct factors'
degrees sum below `deg_Y Q`. -/
theorem sum_fiberX_natDegree_le
    {Q : (RatFunc F)[X][Y]} (hQ0 : Q ≠ 0)
    (rep : (RatFunc F)[X][Y] → (F[X])[X][Y])
    (hrepR : ∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      ∃ dR : F[X], dR ≠ 0 ∧
        (rep R).map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
          Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) * R)
    (x₀ : F) :
    ∑ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      (fiberX x₀ (rep R)).natDegree ≤ Q.natDegree := by
  classical
  refine le_trans (Finset.sum_le_sum fun R hR => ?_)
    (sum_natDegree_distinct_factors_le hQ0)
  obtain ⟨dR, hdR, hpush⟩ := hrepR R hR
  have hinj : Function.Injective
      (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ (RatFunc.algebraMap_injective F)
  have hL : ((rep R).map (Polynomial.mapRingHom
      (algebraMap F[X] (RatFunc F)))).natDegree = (rep R).natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj _
  have hdRK : algebraMap F[X] (RatFunc F) dR ≠ 0 := fun h =>
    hdR ((map_eq_zero_iff _ (RatFunc.algebraMap_injective F)).mp h)
  have hRdeg : (Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) *
      R).natDegree = R.natDegree :=
    Polynomial.natDegree_C_mul (Polynomial.C_ne_zero.mpr hdRK)
  have h2 : (rep R).natDegree = R.natDegree := by
    rw [← hL, hpush, hRdeg]
  calc (fiberX x₀ (rep R)).natDegree ≤ (rep R).natDegree :=
        Polynomial.natDegree_map_le
    _ = R.natDegree := h2

/-! ## The capstone: Claim 5.7 with both halves composed -/

/-- **BCIKS20 Claim 5.7, complete (algebraic + combinatorial halves composed).**

For the integer model `Q₀ ↦ C(C d)·Q` of a nonzero GS interpolant `Q ∈ K[X][Y]`
(`K = F(Z)`), there are integer representatives `rep` of the irreducible factors of `Q`
and a nonzero avoidance polynomial `bad ∈ F[Z]` (the algebraic half,
`exists_specialized_factor_assignment`) such that: for every fiber point `x₀` at which all
factor fibers are nonzero (the S5 good-point hypothesis,
`gs_interpolant_good_specialization*` output shape), there is a second nonzero avoidance
polynomial `badZ ∈ F[Z]` with — for every finite scalar set `S` avoiding `badZ`'s roots
and every decoded family `q_z` with `(Y − C q_z) ∣ Q₀|_{Z:=z}` (the proven S10 bridge
output) — a cell cover of `S` by at most `D_Y = deg_Y Q` incidence cells
`S_{x₀,R,H} = {z ∈ S : (Y − C q_z) ∣ (rep R)|_{Z:=z} ∧ H((q_z)(x₀), z) = 0}` indexed by
(factor, positive-degree irreducible fiber component) pairs; and whenever
`deg_Y Q · T < |S|`, some cell exceeds `T` — the paper's
*"the most common cell has `|S_{x₀,R,H}| ≥ |S| / D_Y`"*, in the threshold form consumed by
[BCI⁺20, Steps 5–7]. -/
theorem claim57_pigeonhole
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hd : d ≠ 0) (hQ0 : Q ≠ 0)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q) :
    ∃ (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (bad : F[X]), bad ≠ 0 ∧
      (∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
        ∃ dR : F[X], dR ≠ 0 ∧
          (rep R).map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
            Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) dR)) * R) ∧
      ∀ x₀ : F,
        (∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          fiberX x₀ (rep R) ≠ 0) →
        ∃ badZ : F[X], badZ ≠ 0 ∧
          ∀ (S : Finset F) (qz : F → F[X]),
            (∀ z ∈ S, badZ.eval z ≠ 0) →
            (∀ z ∈ S, (Polynomial.X - Polynomial.C (qz z)) ∣
              Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) →
            ∃ Index : Finset ((RatFunc F)[X][Y] × F[X][Y]),
              Index.card ≤ Q.natDegree ∧
              (∀ c ∈ Index, c.1 ∈ (UniqueFactorizationMonoid.factors Q).toFinset ∧
                c.2 ∈ (UniqueFactorizationMonoid.factors (fiberX x₀ (rep c.1))).toFinset ∧
                0 < c.2.natDegree) ∧
              (∀ z ∈ S, ∃ c ∈ Index, z ∈ cell rep x₀ qz S c) ∧
              (∀ T : ℕ, Q.natDegree * T < S.card →
                ∃ c ∈ Index, T < (cell rep x₀ qz S c).card) := by
  classical
  obtain ⟨rep, bad, hbad, hrepR, hassign⟩ :=
    exists_specialized_factor_assignment hd hQ0 hrep
  refine ⟨rep, bad, hbad, hrepR, ?_⟩
  intro x₀ hfib
  refine ⟨bad * ∏ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      zOnlyPart (fiberX x₀ (rep R)),
    mul_ne_zero hbad (Finset.prod_ne_zero_iff.mpr fun R _hR =>
      zOnlyPart_ne_zero _), ?_⟩
  intro S qz hSz hSdvd
  have hbadz : ∀ z ∈ S, bad.eval z ≠ 0 := by
    intro z hz h0
    exact hSz z hz (by rw [Polynomial.eval_mul, h0, zero_mul])
  have hzOnly : ∀ z ∈ S, ∀ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      (zOnlyPart (fiberX x₀ (rep R))).eval z ≠ 0 := by
    intro z hz R hR h0
    refine hSz z hz ?_
    rw [Polynomial.eval_mul, Polynomial.eval_prod, Finset.prod_eq_zero hR h0, mul_zero]
  have hassign' : ∀ z ∈ S, ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      (Polynomial.X - Polynomial.C (qz z)) ∣
        (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
    fun z hz => hassign z (hbadz z hz) (qz z) (hSdvd z hz)
  obtain ⟨Index, hcard, hshape, hcover, hpig⟩ := claim57_cells
    (UniqueFactorizationMonoid.factors Q).toFinset rep x₀ hfib S qz hassign' hzOnly
  have hQdeg := sum_fiberX_natDegree_le hQ0 rep hrepR x₀
  exact ⟨Index, le_trans hcard hQdeg, hshape, hcover,
    fun T hT => hpig T (lt_of_le_of_lt (Nat.mul_le_mul_right T hQdeg) hT)⟩

end GuruswamiSudan.OverRatFunc.Claim57

/-!
## The pair-generator seam (wiring-map item 3)

`hasMutualCorrAgreement (genRSC parℓ φ m exp)` samples `r` uniformly from the finset
`Gen.Gen = Finset.image (fun r j => r ^ exp j) Finset.univ`, while every in-tree
probability bound (`Pr_proximityCondition_le_epsMCA`, the Hab25 `epsMCA` chain) samples
`γ` uniformly from `F`. The two are reconciled by a pushforward identity for uniform
sampling over the image of an *injective* map — injective whenever some exponent is `1`
(`exp = (0,1)` in the WHIR pair case). This section proves:

* `Pr_uniform_image_of_injective` — the generic pushforward: for injective `f : α → β`,
  `Pr_{y ←$ᵖ image f univ}[P y] = Pr_{x ←$ᵖ α}[P (f x)]`;
* `genRSC_genfun_injective` — the RS generator map `r ↦ (r^{exp j})_j` is injective when
  `exp j₀ = 1` for some `j₀`;
* `hasMutualCorrAgreement_genRSC_iff_uniform` — the seam: the `genRSC` MCA obligation is
  *equivalent* to its `F`-uniform form, eliminating the `Gen.Gen` sampling layer.
-/

namespace GuruswamiSudan.OverRatFunc.Claim57.GenSeam

set_option linter.unusedSectionVars false

open scoped ProbabilityTheory NNReal ENNReal
open ProbabilityTheory Generator RSGenerator

attribute [local instance] Classical.propDecidable

/-- **Uniform-over-image pushforward.** For an injective `f : α → β` and any event `P`,
sampling uniformly from the image finset `f '' univ` and testing `P` is the same as
sampling the argument uniformly from `α` and testing `P ∘ f`. Stated with the finset
abstracted by an equation so it applies directly to `Gen.Gen` without instance-motive
issues. -/
theorem Pr_uniform_image_of_injective {α β : Type} [Fintype α] [Nonempty α]
    [DecidableEq β] (f : α → β) (hf : Function.Injective f) (P : β → Prop)
    (s : Finset β) (hs : s = Finset.image f Finset.univ) [hne : Nonempty ↥s] :
    Pr_{let y ←$ᵖ s}[P ↑y] = Pr_{let x ←$ᵖ α}[P (f x)] := by
  classical
  subst hs
  rw [Pr_eq_tsum_indicator, Pr_eq_tsum_indicator]
  have hbij : Function.Bijective (fun x : α =>
      (⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x)⟩ :
        ↥(Finset.image f Finset.univ))) := by
    constructor
    · intro a b h
      exact hf (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, rfl⟩
  rw [← Equiv.tsum_eq (Equiv.ofBijective _ hbij)]
  refine tsum_congr fun x => ?_
  have hcard : Fintype.card ↥(Finset.image f Finset.univ) = Fintype.card α := by
    rw [Fintype.card_coe, Finset.card_image_of_injective _ hf, Finset.card_univ]
  rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, hcard]
  rfl

/-- The RS generator map `r ↦ (r^{exp j})ⱼ` is injective as soon as one exponent is `1`. -/
theorem genRSC_genfun_injective {F : Type} [Field F] {parℓ : Type} (exp : parℓ ↪ ℕ)
    (j₀ : parℓ) (h1 : exp j₀ = 1) :
    Function.Injective (fun r : F => fun j : parℓ => r ^ (exp j)) := by
  intro a b h
  have hj := congrFun h j₀
  simpa [h1] using hj

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Nonempty F]
         {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The seam, generically.** For any proximity generator whose sampling finset is the
image of an *injective* map `g : F → (Gen.parℓ → F)`, the mutual-correlated-agreement
obligation — sampling `r` uniformly from `Gen.Gen` — is *equivalent* to its `F`-uniform
form `Pr_{γ ←$ᵖ F}[proximityCondition f δ (g γ) Gen.C] ≤ errStar δ`, the shape produced
by the in-tree `epsMCA` chain (`Pr_proximityCondition_le_epsMCA`, Hab25 S11). -/
theorem hasMutualCorrAgreement_iff_uniform_of_gen_image
    (Gen : ProximityGenerator ι F) [hpℓ : Fintype Gen.parℓ]
    (g : F → Gen.parℓ → F) (hg : Function.Injective g)
    (hGen : Gen.Gen = Finset.image g Finset.univ)
    (BStar : ℝ) (errStar : ℝ → ENNReal) :
    MutualCorrAgreement.hasMutualCorrAgreement Gen BStar errStar ↔
      ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0), (0 < δ ∧ (δ : ℝ) < 1 - BStar) →
        Pr_{let γ ←$ᵖ F}[MutualCorrAgreement.proximityCondition f δ (g γ) Gen.C]
          ≤ errStar δ := by
  classical
  haveI : Nonempty ↥Gen.Gen := Gen.Gen_nonempty
  constructor
  · intro h f δ hδ
    have hh := h f δ hδ
    rwa [Pr_uniform_image_of_injective g hg
      (fun rv => MutualCorrAgreement.proximityCondition f δ rv Gen.C)
      _ hGen (hne := Gen.Gen_nonempty)] at hh
  · intro h
    refine fun f δ hδ => ?_
    rw [Pr_uniform_image_of_injective g hg
      (fun rv => MutualCorrAgreement.proximityCondition f δ rv Gen.C)
      _ hGen (hne := Gen.Gen_nonempty)]
    exact h f δ hδ

/-- **The pair-generator seam for `genRSC`.** Instantiation of the generic seam at the RS
generator `Gen.Gen = image (r ↦ (r^{exp j})ⱼ) univ`: requires only that some exponent is
`1` (true for the WHIR pair generator `exp = (0,1)`). The statement is phrased at the
generator's own `parℓ` projection (definitionally the given `parℓ`). -/
theorem hasMutualCorrAgreement_genRSC_iff_uniform
    (parℓ : Type) [hp : Fintype parℓ] (φ : ι ↪ F) [ReedSolomon.Smooth φ] (m : ℕ)
    (exp : parℓ ↪ ℕ) (j₀ : parℓ) (h1 : exp j₀ = 1)
    (BStar : ℝ) (errStar : ℝ → ENNReal) :
    (haveI : Fintype (RSGenerator.genRSC parℓ φ m exp).parℓ := hp;
      MutualCorrAgreement.hasMutualCorrAgreement (RSGenerator.genRSC parℓ φ m exp)
        BStar errStar) ↔
      ∀ (f : parℓ → ι → F) (δ : ℝ≥0), (0 < δ ∧ (δ : ℝ) < 1 - BStar) →
        Pr_{let γ ←$ᵖ F}[MutualCorrAgreement.proximityCondition f δ
          (fun j => γ ^ (exp j)) ((RSGenerator.genRSC parℓ φ m exp).C)]
          ≤ errStar δ := by
  classical
  exact hasMutualCorrAgreement_iff_uniform_of_gen_image
    (Gen := RSGenerator.genRSC parℓ φ m exp) (hpℓ := hp)
    (fun r : F => fun j : parℓ => r ^ (exp j))
    (genRSC_genfun_injective (F := F) exp j₀ h1)
    rfl BStar errStar

end GuruswamiSudan.OverRatFunc.Claim57.GenSeam

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.Claim57.pointEval_fiberX
#print axioms GuruswamiSudan.OverRatFunc.Claim57.pointEval_fiberX_eq_zero_of_dvd
#print axioms GuruswamiSudan.OverRatFunc.Claim57.exists_posdeg_factor_pointEval_eq_zero
#print axioms GuruswamiSudan.OverRatFunc.Claim57.card_posdeg_factors_le
#print axioms GuruswamiSudan.OverRatFunc.Claim57.exists_large_cell
#print axioms GuruswamiSudan.OverRatFunc.Claim57.claim57_cells
#print axioms GuruswamiSudan.OverRatFunc.Claim57.sum_fiberX_natDegree_le
#print axioms GuruswamiSudan.OverRatFunc.Claim57.claim57_pigeonhole
#print axioms GuruswamiSudan.OverRatFunc.Claim57.GenSeam.Pr_uniform_image_of_injective
#print axioms GuruswamiSudan.OverRatFunc.Claim57.GenSeam.genRSC_genfun_injective
#print axioms GuruswamiSudan.OverRatFunc.Claim57.GenSeam.hasMutualCorrAgreement_iff_uniform_of_gen_image
#print axioms GuruswamiSudan.OverRatFunc.Claim57.GenSeam.hasMutualCorrAgreement_genRSC_iff_uniform
