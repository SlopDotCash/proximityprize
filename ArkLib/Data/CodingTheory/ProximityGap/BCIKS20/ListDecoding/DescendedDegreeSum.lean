/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.DescendedRset
import ArkLib.Data.CodingTheory.ProximityGap.Hab25DegreeBudget

/-!
# The descended Claim 5.7 chain, `hcoincide`-free (degree sum → attribution → common pair)

The legacy Claim 5.7 counting core (`pg_card_candidatePairs_le_natDegreeY`,
`pg_exists_R_of_Q_eval_zero` in `Extraction.lean`) needs separability of **every** normalized
factor of `Q` over `pg_Rset` — impossible in characteristic `p`, where genuinely inseparable
normalized factors occur (see `DescendedRset.lean`).  The descended route replaces `pg_Rset` by
the (provably separable) descended factor set `pg_RsetDescended`, at the price of the
Frobenius-*twisted* root `Pz^a` in place of `Pz`.  Previously this route was `hcoincide`-gated
(`pg_RsetDescended = pg_Rset`, false in the inseparable case); this file removes that gate
entirely:

* `pg_sum_natDegreeY_RsetDescended_le_natDegreeY_Q` — the descended **pigeonhole denominator**
  (degree sum over distinct descended factors ≤ `natDegreeY Q`), via the `expand`-shape
  factorization; the `fⱼ ≥ 1` input is now *exposed* by the strengthened
  `irreducible_factorization_of_gs_solution` (its final conjunct) and discharged below.
* `pg_exists_R_descended_of_Q_eval_zero` — descended **root attribution** at the twisted root,
  requiring only content non-vanishing at `z` (a finite exception set:
  `content_bad_close_params_card_le`).
* `pg_exists_H_of_R_eval_zero_generic` — the `P`-generic H-extraction (the cone's
  `pg_exists_H_of_R_eval_zero` with the evaluation point a parameter, as the twisted root needs).
* `pg_exists_pair_for_z_descended`, `pg_card_candidatePairsDescended_le_natDegreeY`,
  `pg_exists_common_candidate_pair_descended` — the per-`z` pair, the count bound, and the
  end-to-end pigeonhole (descended Claim 5.7).
* `factorization_fpos` — **R1 discharged**: every descended `expand`-exponent is `≥ 1`, now a
  theorem (consequence of the strengthened bundle).
* `content_bad_close_params_card_le` — **R2 quantified**: content-vanishing close parameters
  number at most a fixed coefficient degree `B`.
* `pg_exists_common_candidate_pair_descended_full_nohf` — **the apex**: descended Claim 5.7 over
  the full close set, with R1 discharged internally and R2 absorbed into the `(#𝒮 − B)` bound.
  Remaining genuine inputs: the §5 data (`h_gs`, `hQall`) and the per-`x₀` descended
  separability of the specializations (`hsep`) — the honest open §5 frontier, with **no**
  `hcoincide` and **no** `hf`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.7).
-/

open Polynomial Polynomial.Bivariate Finset BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace ProximityGap

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ} {m : ℕ} (k : ℕ) {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-- **Distinct-sum ≤ list-sum** (ℕ weights). -/
private theorem sum_toFinset_le_sum_list {α : Type*} [DecidableEq α] (l : List α) (g : α → ℕ) :
    ∑ x ∈ l.toFinset, g x ≤ (l.map g).sum := by
  rw [Finset.sum_list_map_count]
  refine Finset.sum_le_sum ?_
  intro x hx
  have hpos : 1 ≤ List.count x l := List.count_pos_iff.mpr (List.mem_toFinset.mp hx)
  calc g x = 1 • g x := (one_smul ℕ (g x)).symm
    _ ≤ List.count x l • g x := Nat.mul_le_mul_right (g x) hpos

/-- **Range-`getD` sum = list-sum.** -/
private theorem sum_range_getD_eq_sum_list {α : Type*} (l : List α) (d : α) (g : α → ℕ) :
    ∑ j ∈ Finset.range l.length, g (l.getD j d) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
      rw [ih]; ring

/-- **Distinct-factor degree sum ≤ total degree, `expand`-shape factorization (general).** -/
private theorem sum_toFinset_natDegree_le_natDegree_of_factorization
    {A : Type*} [CommRing A] [IsDomain A] [DecidableEq A]
    (q : A[X]) (C₀ : A) (L : List A[X]) (f e : List ℕ)
    (he : ∀ j < L.length, 1 ≤ e.getD j 0)
    (hf : ∀ j < L.length, 1 ≤ f.getD j 0)
    (hq0 : q ≠ 0)
    (hfact : q = Polynomial.C C₀ *
      ∏ j ∈ Finset.range L.length,
        ((L.getD j 1).comp (Polynomial.X ^ f.getD j 0)) ^ e.getD j 0) :
    ∑ r ∈ L.toFinset, r.natDegree ≤ q.natDegree := by
  classical
  have hCne : Polynomial.C C₀ ≠ 0 := by rintro h0; exact hq0 (by rw [hfact, h0, zero_mul])
  have hprodne :
      (∏ j ∈ Finset.range L.length,
          ((L.getD j 1).comp (Polynomial.X ^ f.getD j 0)) ^ e.getD j 0) ≠ 0 := by
    rintro h0; exact hq0 (by rw [hfact, h0, mul_zero])
  have hbodyne : ∀ j ∈ Finset.range L.length,
      ((L.getD j 1).comp (Polynomial.X ^ f.getD j 0)) ^ e.getD j 0 ≠ 0 :=
    (Finset.prod_ne_zero_iff).mp hprodne
  have hQdeg : q.natDegree
      = ∑ j ∈ Finset.range L.length,
          e.getD j 0 * ((L.getD j 1).natDegree * f.getD j 0) := by
    rw [hfact, Polynomial.natDegree_mul hCne hprodne, Polynomial.natDegree_C, zero_add,
      Polynomial.natDegree_prod _ _ hbodyne]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
  rw [hQdeg]
  calc ∑ r ∈ L.toFinset, r.natDegree
      ≤ (L.map Polynomial.natDegree).sum := sum_toFinset_le_sum_list L Polynomial.natDegree
    _ = ∑ j ∈ Finset.range L.length, (L.getD j 1).natDegree :=
        (sum_range_getD_eq_sum_list L 1 Polynomial.natDegree).symm
    _ ≤ ∑ j ∈ Finset.range L.length,
          e.getD j 0 * ((L.getD j 1).natDegree * f.getD j 0) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hjl : j < L.length := Finset.mem_range.mp hj
        calc (L.getD j 1).natDegree
            ≤ (L.getD j 1).natDegree * f.getD j 0 :=
              le_mul_of_one_le_right (Nat.zero_le _) (hf j hjl)
          _ ≤ e.getD j 0 * ((L.getD j 1).natDegree * f.getD j 0) :=
              le_mul_of_one_le_left (Nat.zero_le _) (he j hjl)

/-- **Descended pigeonhole-denominator bound.**  The sum of `Y`-degrees over the *distinct* descended
factor set is at most `natDegreeY Q` — the descended analogue of `pg_sum_natDegreeY_Rset_le_natDegreeY_Q`.

The `hf` hypothesis (every descended `expand`-exponent `≥ 1`) is kept as a parameter for callers
holding it abstractly; it is discharged outright by `factorization_fpos` below, now that the
strengthened `irreducible_factorization_of_gs_solution` exposes it. -/
theorem pg_sum_natDegreeY_RsetDescended_le_natDegreeY_Q
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hf : ∀ j < (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.length,
      1 ≤ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD j 0) :
    ∑ r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs,
        Bivariate.natDegreeY r ≤ Bivariate.natDegreeY Q := by
  classical
  obtain ⟨hlen1, hlen2, he, _hsep, _hirr, _hpos, hfact, _hfpos⟩ :=
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose_spec
  simp only [Bivariate.natDegreeY, pg_RsetDescended]
  refine sum_toFinset_natDegree_le_natDegree_of_factorization
    Q _ _ _ _ ?_ hf h_gs.Q_ne_0 hfact
  intro j hj
  have hje : j <
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose.length := by
    rw [← hlen2, ← hlen1]; exact hj
  have hmem :
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose.getD j 0
        ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose := by
    rw [List.getD_eq_getElem _ 0 hje]; exact List.getElem_mem hje
  exact he _ hmem

/-! ## Descended candidate-pair count bound

The descended analogue of `pg_card_candidatePairs_le_natDegreeY` — the pigeonhole *denominator* over the
descended factor set.  Mirrors the legacy proof with `pg_Rset` replaced by
`pg_RsetDescended`, the impossible `pg_Rset`-wide `hsep` replaced by the *provable* descended `hsep`
(`Claim57ResidualsDescended.hsep`), and the final degree-sum supplied by
`pg_sum_natDegreeY_RsetDescended_le_natDegreeY_Q` above.  This is the assembly that lets the descended
Claim 5.7 run **without** the char-`p`-false `hcoincide`. -/

/-- **Descended pigeonhole denominator (sum form, hcoincide-free).**  The total number of distinct
`(r, H)` candidate pairs over the descended factor set is at most `natDegreeY Q`: summing, over each
descended `r`, the number of distinct normalized factors of its `x₀`-specialization is `≤ natDegreeY Q`.

This is the descended analogue of `pg_card_candidatePairs_le_natDegreeY`, using the *provable*
descended separability `hsep` (never the impossible `pg_Rset`-wide one) and the verified descended
degree-sum.  No `hcoincide`.  Stated as the sum (rather than the `biUnion` cardinality) to keep the
`pg_RsetDescended` choice term unreduced — `≤` to the `biUnion` card follows from `card_biUnion_le`. -/
theorem pg_sum_card_normalizedFactors_evalX_RsetDescended_le_natDegreeY
    (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hf : ∀ j < (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.length,
      1 ≤ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD j 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
    (∑ R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs,
      #((UniqueFactorizationMonoid.normalizedFactors
          (Bivariate.evalX (Polynomial.C x₀) R)).toFinset))
      ≤ Bivariate.natDegreeY Q := by
  classical
  have hpoint : ∀ R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs,
      #((UniqueFactorizationMonoid.normalizedFactors
          (Bivariate.evalX (Polynomial.C x₀) R)).toFinset) ≤ Bivariate.natDegreeY R := by
    intro R hR
    calc #((UniqueFactorizationMonoid.normalizedFactors
              (Bivariate.evalX (Polynomial.C x₀) R)).toFinset)
        ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree :=
          pg_card_normalizedFactors_toFinset_le_natDegree (F := F)
            (p := Bivariate.evalX (Polynomial.C x₀) R) (hp := hsep R hR)
      _ ≤ Bivariate.natDegreeY R := pg_natDegree_evalX_le_natDegreeY (F := F) x₀ R
  refine le_trans (Finset.sum_le_sum hpoint) ?_
  exact pg_sum_natDegreeY_RsetDescended_le_natDegreeY_Q (k := k) h_gs hf

/-! ## Descended root attribution — the hcoincide-free replacement for `pg_exists_R_of_Q_eval_zero`

The legacy core attributes a root of the specialized `Q` to a *normalized factor* of `Q` (needs the
`pg_Rset`-wide separability that is impossible in char `p`).  Here we attribute it to a *descended*
factor instead, via the verified Frobenius-transfer bricks — landing the root at the twisted point
`Pz^{fⱼ}` and requiring only that the content does not vanish at `z` (a finite exception set, bounded
by `card_specialization_zero_le`).  No `hcoincide`. -/

private theorem eval_map_comp_X_pow' {A B : Type*} [CommSemiring A] [CommSemiring B]
    (ψ : A →+* B) (r : A[X]) (N : ℕ) (P : B) :
    ((r.comp (Polynomial.X ^ N)).map ψ).eval P = (r.map ψ).eval (P ^ N) := by
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X]

private theorem exists_descended_factor_root_of_eval_zero'
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    (ψ : A →+* B) (q : A[X]) (C₀ : A) (L : List A[X]) (f e : List ℕ) (P : B)
    (hfact : q = Polynomial.C C₀ *
      ∏ j ∈ Finset.range L.length,
        ((L.getD j 1).comp (Polynomial.X ^ f.getD j 0)) ^ e.getD j 0)
    (hq : (q.map ψ).eval P = 0) (hC : ψ C₀ ≠ 0) :
    ∃ j ∈ Finset.range L.length, ((L.getD j 1).map ψ).eval (P ^ f.getD j 0) = 0 := by
  classical
  set Φ : A[X] →+* B := (Polynomial.evalRingHom P).comp (Polynomial.mapRingHom ψ) with hΦ
  have hΦ_apply : ∀ p : A[X], Φ p = (p.map ψ).eval P := by
    intro p; simp [hΦ, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom]
  have hΦq : Φ q = 0 := by rw [hΦ_apply]; exact hq
  have hexp : ψ C₀ *
      ∏ j ∈ Finset.range L.length,
        (((L.getD j 1).map ψ).eval (P ^ f.getD j 0)) ^ e.getD j 0 = 0 := by
    have hstep : Φ q = ψ C₀ *
        ∏ j ∈ Finset.range L.length,
          (((L.getD j 1).map ψ).eval (P ^ f.getD j 0)) ^ e.getD j 0 := by
      rw [hfact, map_mul, map_prod]
      congr 1
      · rw [hΦ_apply]; simp
      · refine Finset.prod_congr rfl ?_
        intro j _hj
        rw [map_pow, hΦ_apply, eval_map_comp_X_pow']
    rw [← hstep]; exact hΦq
  have hprod0 :
      ∏ j ∈ Finset.range L.length,
        (((L.getD j 1).map ψ).eval (P ^ f.getD j 0)) ^ e.getD j 0 = 0 :=
    (mul_eq_zero.mp hexp).resolve_left hC
  obtain ⟨j, hj, hjz⟩ := Finset.prod_eq_zero_iff.mp hprod0
  refine ⟨j, hj, ?_⟩
  have hne : e.getD j 0 ≠ 0 := by rintro h0; rw [h0, pow_zero] at hjz; exact one_ne_zero hjz
  exact pow_eq_zero_iff hne |>.mp hjz

/-- **Descended root attribution (bundle form, hcoincide-free).**  If `Pz` is a root of the
`Z`-specialized `Q` and the content does not vanish at `z`, then some descended factor `r ∈
pg_RsetDescended` vanishes — at the Frobenius-twisted root `Pz^a` — on its own `Z`-specialization.
This replaces `pg_exists_R_of_Q_eval_zero` over the descended set, with **no** `hcoincide`. -/
theorem pg_exists_R_descended_of_Q_eval_zero
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
    (hQ : (pg_eval_on_Z (F := F) Q z.1).eval
        (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0)
    (hC : (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
        (irreducible_factorization_of_gs_solution h_gs).choose ≠ 0) :
    ∃ r, r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      ∃ a : ℕ, (pg_eval_on_Z (F := F) r z.1).eval
        ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 := by
  classical
  obtain ⟨hlen1, hlen2, he, _hsep, _hirr, _hpos, hfact, _hfpos⟩ :=
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨j, hj, hjz⟩ :=
    exists_descended_factor_root_of_eval_zero'
      (Polynomial.mapRingHom (Polynomial.evalRingHom z.1)) Q
      (irreducible_factorization_of_gs_solution h_gs).choose
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose
      (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2)
      hfact (by simpa [pg_eval_on_Z] using hQ) hC
  refine ⟨(irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.getD j 1, ?_,
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD j 0, ?_⟩
  · have hmem :
        (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.getD j 1
          ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose := by
      rw [List.getD_eq_getElem _ 1 (Finset.mem_range.mp hj)]
      exact List.getElem_mem (Finset.mem_range.mp hj)
    exact (mem_pg_RsetDescended_iff_mem_list (k := k) h_gs _).mpr hmem
  · simpa [pg_eval_on_Z] using hjz

/-! ## P-generic H-extraction (for the Frobenius-twisted root)

`pg_exists_H_of_R_eval_zero` fixes the evaluation point to `P = Pz`.  The descended factor vanishes at
the *twisted* point `Pz^a`, so we need the same extraction at an arbitrary `P : F[X]`.  The cone proof
is generic in `P` (only its `set P := Pz` line specializes); we reproduce it with `P` a parameter. -/
theorem pg_exists_H_of_R_eval_zero_generic (x₀ : F)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
    (R : F[Z][X][Y]) (P : F[X])
    (hR : (pg_eval_on_Z (F := F) R z.1).eval P = 0)
    (hNZ : Bivariate.evalX (Polynomial.C x₀) R ≠ 0) :
    ∃ H, H ∈ UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) R) ∧
      (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0 := by
  classical
  have evalX_eq_map {R' : Type} [CommSemiring R'] (a : R') (g : Polynomial (Polynomial R')) :
      Bivariate.evalX a g = g.map (Polynomial.evalRingHom a) := by
    ext nn; simp [Bivariate.evalX, Polynomial.coeff_map]; simp [Polynomial.coeff]
  set p := Bivariate.evalX (Polynomial.C x₀) R with hp
  have hp_root : (Bivariate.evalX z.1 p).eval (P.eval x₀) = 0 := by
    have hx : ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ = 0 := by
      have := congrArg (fun g : F[X] => g.eval x₀) hR; simpa using this
    let fZ : F[X] →+* F := Polynomial.evalRingHom z.1
    let q : F[Z][X] := P.map (Polynomial.C)
    let r : F[X] := Polynomial.C x₀
    have hqmap : q.map fZ = P := by
      have hf : fZ.comp (Polynomial.C) = (RingHom.id F) := by ext a; simp [fZ]
      simp [q, Polynomial.map_map, hf]
    have hr : fZ r = x₀ := by simp [fZ, r]
    have hcommZ : ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ = fZ ((R.eval q).eval r) := by
      have h := Polynomial.map_mapRingHom_eval_map_eval (f := fZ) (p := R) (q := q) r
      simpa [pg_eval_on_Z, fZ, hqmap, hr] using h
    have hfz0 : fZ ((R.eval q).eval r) = 0 := by
      calc fZ ((R.eval q).eval r) = ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ := by
            simp [hcommZ]
        _ = 0 := hx
    have hp_map : p = R.map (Polynomial.evalRingHom (Polynomial.C x₀)) :=
      hp.trans (pg_evalX_eq_map_evalRingHom (F := F) x₀ R)
    have hYX : (R.eval q).eval r = (p.eval (q.eval r)) := by
      have h := (Polynomial.eval₂_hom (p := R) (f := Polynomial.evalRingHom r) q)
      have h' : (R.map (Polynomial.evalRingHom r)).eval ((Polynomial.evalRingHom r) q) =
          (Polynomial.evalRingHom r) (R.eval q) := by
        simpa [Polynomial.eval₂_eq_eval_map] using h
      have h'' : (R.eval q).eval r = (R.map (Polynomial.evalRingHom r)).eval (q.eval r) := by
        simpa [Polynomial.coe_evalRingHom] using h'.symm
      simpa [hp_map, Polynomial.coe_evalRingHom] using h''
    have hfz_eq : fZ ((R.eval q).eval r) = (p.map fZ).eval (fZ (q.eval r)) := by
      have hb : fZ ((R.eval q).eval r) = fZ (p.eval (q.eval r)) := by simp [hYX]
      simp [hb]
    have hfz_q : fZ (q.eval r) = P.eval x₀ := by simp [fZ, q, r]
    have hp_eval_as : fZ ((R.eval q).eval r) = (Bivariate.evalX z.1 p).eval (P.eval x₀) := by
      have hbz : Bivariate.evalX z.1 p = p.map fZ := by simpa [fZ] using (evalX_eq_map (R' := F) z.1 p)
      calc fZ ((R.eval q).eval r) = (p.map fZ).eval (fZ (q.eval r)) := hfz_eq
        _ = (p.map fZ).eval (P.eval x₀) := by simp [hfz_q]
        _ = (Bivariate.evalX z.1 p).eval (P.eval x₀) := by simp [hbz]
    calc (Bivariate.evalX z.1 p).eval (P.eval x₀) = fZ ((R.eval q).eval r) := by simp [hp_eval_as]
      _ = 0 := hfz0
  have hAssoc : Associated (UniqueFactorizationMonoid.normalizedFactors p).prod p :=
    UniqueFactorizationMonoid.prod_normalizedFactors (a := p) hNZ
  let φ : _ →+* F :=
    (Polynomial.evalRingHom (P.eval x₀)).comp (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
  have hφp : φ p = 0 := by
    have hp_root' : (p.map (Polynomial.evalRingHom z.1)).eval (P.eval x₀) = 0 := by
      simpa [evalX_eq_map (R' := F) z.1 p] using hp_root
    simpa [φ] using hp_root'
  have hφprod : φ (UniqueFactorizationMonoid.normalizedFactors p).prod = 0 := by
    have hAssoc' : Associated (φ (UniqueFactorizationMonoid.normalizedFactors p).prod) (φ p) :=
      Associated.map (φ : _ →* F) hAssoc
    exact (hAssoc'.eq_zero_iff).mpr hφp
  have hmap_prod : ((UniqueFactorizationMonoid.normalizedFactors p).map φ).prod = 0 := by
    simpa [map_multiset_prod] using hφprod
  have hmem0 : (0 : F) ∈ (UniqueFactorizationMonoid.normalizedFactors p).map φ :=
    (Multiset.prod_eq_zero_iff).1 hmap_prod
  rcases (Multiset.mem_map.1 hmem0) with ⟨H, hHmem, hHφ⟩
  refine ⟨H, hHmem, ?_⟩
  have hHφ' : (H.map (Polynomial.evalRingHom z.1)).eval (P.eval x₀) = 0 := by simpa [φ] using hHφ
  simpa [evalX_eq_map (R' := F) z.1 H] using hHφ'

/-! ## Per-`z` descended candidate-pair extraction (hcoincide-free)

The descended analogue of `pg_exists_pair_for_z`: for each close parameter `z` at which the content
does not vanish, a *descended* factor `r` and a factor `H` of its `x₀`-specialization form a candidate
pair witnessing the Frobenius-twisted common-root condition.  This is the per-`z` half of the descended
Claim 5.7 — assembled entirely from the verified descended bricks, with **no** `hcoincide`. -/
theorem pg_exists_pair_for_z_descended (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
    (hQ : (pg_eval_on_Z (F := F) Q z.1).eval
        (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0)
    (hC : (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
        (irreducible_factorization_of_gs_solution h_gs).choose ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
    ∃ (r : F[Z][X][Y]) (H : F[Z][X]) (a : ℕ),
      r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      H ∈ UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) r) ∧
      (pg_eval_on_Z (F := F) r z.1).eval
        ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 ∧
      (Bivariate.evalX z.1 H).eval
        (((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a).eval x₀) = 0 := by
  obtain ⟨r, hr_mem, a, hr_vanish⟩ :=
    pg_exists_R_descended_of_Q_eval_zero (k := k) h_gs z hQ hC
  have hNZ : Bivariate.evalX (Polynomial.C x₀) r ≠ 0 := (hsep r hr_mem).ne_zero
  obtain ⟨H, hH_mem, hH_vanish⟩ :=
    pg_exists_H_of_R_eval_zero_generic (k := k) x₀ z r
      ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) hr_vanish hNZ
  exact ⟨r, H, a, hr_mem, hH_mem, hr_vanish, hH_vanish⟩

/-- **Descended candidate-pair count bound (`biUnion` form).** -/
theorem pg_card_candidatePairsDescended_le_natDegreeY (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hf : ∀ j < (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.length,
      1 ≤ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD j 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
    #((pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).biUnion
      (fun R => (UniqueFactorizationMonoid.normalizedFactors
          (Bivariate.evalX (Polynomial.C x₀) R)).toFinset.image (fun H => (R, H))))
      ≤ Bivariate.natDegreeY Q := by
  classical
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (fun R _hR => Finset.card_image_le))
    (pg_sum_card_normalizedFactors_evalX_RsetDescended_le_natDegreeY (k := k) x₀ h_gs hf hsep)

/-! ## Descended Claim 5.7 — the hcoincide-free common candidate pair

End-to-end descended pigeonhole: over the close parameters `S` at which `Q` specializes to zero and the
content does not vanish, a single descended factor `r` and a factor `H` of its `x₀`-specialization
account for at least the average-sized fiber `#S / natDegreeY Q` of those parameters (at each, via the
Frobenius-twisted root `Pz^a`).  This is the descended analogue of `pg_exists_common_candidate_pair`,
assembled from the verified descended bricks with **no** `hcoincide`. -/
open Classical in
theorem pg_exists_common_candidate_pair_descended (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hf : ∀ j < (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.length,
      1 ≤ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD j 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (S : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)) (hS_ne : S.Nonempty)
    (hgood : ∀ z ∈ S,
      (pg_eval_on_Z (F := F) Q z.1).eval
          (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0 ∧
      (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
          (irreducible_factorization_of_gs_solution h_gs).choose ≠ 0) :
    ∃ (r : F[Z][X][Y]) (H : F[Z][X]),
      r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      #S / Bivariate.natDegreeY Q ≤
        #(S.filter (fun z => ∃ a : ℕ,
            (pg_eval_on_Z (F := F) r z.1).eval
              ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 ∧
            (Bivariate.evalX z.1 H).eval
              (((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a).eval x₀) = 0)) := by
  classical
  set T : Finset (F[Z][X][Y] × F[Z][X]) :=
    (pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).biUnion
      (fun R => (UniqueFactorizationMonoid.normalizedFactors
          (Bivariate.evalX (Polynomial.C x₀) R)).toFinset.image (fun H => (R, H))) with hTdef
  -- per-`z` pair, with all data, for `z ∈ S`
  have hpair : ∀ z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁, z ∈ S →
      ∃ (rH : F[Z][X][Y] × F[Z][X]), rH ∈ T ∧ ∃ a : ℕ,
        (pg_eval_on_Z (F := F) rH.1 z.1).eval
          ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 ∧
        (Bivariate.evalX z.1 rH.2).eval
          (((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a).eval x₀) = 0 := by
    intro z hz
    obtain ⟨hQ, hC⟩ := hgood z hz
    obtain ⟨r, H, a, hr_mem, hH_mem, hr_v, hH_v⟩ :=
      pg_exists_pair_for_z_descended (k := k) x₀ h_gs z hQ hC hsep
    refine ⟨(r, H), ?_, a, hr_v, hH_v⟩
    rw [hTdef]
    exact Finset.mem_biUnion.mpr ⟨r, hr_mem, Finset.mem_image.mpr ⟨H, Multiset.mem_toFinset.mpr hH_mem, rfl⟩⟩
  choose! tag htagT ha hva hvb using hpair
  -- pigeonhole over `S` by the tag, into `T`
  have hmaps : ∀ z ∈ S, tag z ∈ T := fun z hz => htagT z hz
  obtain ⟨z0, hz0⟩ := hS_ne
  have hT_ne : T.Nonempty := ⟨tag z0, hmaps z0 hz0⟩
  obtain ⟨y, hyT, hfiber⟩ := tagged_fiber_pigeonhole S tag T hmaps hT_ne
  -- bound `#T ≤ natDegreeY Q`
  have hTcard : #T ≤ Bivariate.natDegreeY Q := by
    rw [hTdef]; exact pg_card_candidatePairsDescended_le_natDegreeY (k := k) x₀ h_gs hf hsep
  -- the chosen pair `y = (r, H)`; `y.1 ∈ pg_RsetDescended`
  have hy1 : y.1 ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) h_gs := by
    rw [hTdef] at hyT
    obtain ⟨r, hr, hyr⟩ := Finset.mem_biUnion.mp hyT
    obtain ⟨H, _, hHy⟩ := Finset.mem_image.mp hyr
    rw [← hHy]; exact hr
  refine ⟨y.1, y.2, hy1, ?_⟩
  -- `#S / natDegreeY Q ≤ #S / #T ≤ fiber ≤ filtered set`
  have hsub : S.filter (fun z => tag z = y) ⊆
      S.filter (fun z => ∃ a : ℕ,
        (pg_eval_on_Z (F := F) y.1 z.1).eval
          ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 ∧
        (Bivariate.evalX z.1 y.2).eval
          (((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a).eval x₀) = 0) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨hzS, htagz⟩ := hz
    refine ⟨hzS, ha z, ?_⟩
    rw [← htagz]
    exact ⟨hva z hzS, hvb z hzS⟩
  refine le_trans (Nat.div_le_div_left hTcard (Finset.card_pos.mpr hT_ne)) ?_
  exact le_trans hfiber (Finset.card_le_card hsub)

/-! ## Discharging the residuals: both are provably tractable

The descended Claim 5.7 above rests on two honest residuals — `hf` (every `expand`-exponent `fⱼ ≥ 1`)
and content non-vanishing on `S`.  Here we prove each is *tractable*, not a black box:
- **R1 (`f≥1`)** is genuinely *true and provable*: an `nn = 0` descent would make the factor constant,
  contradicting positive degree.  `eq512_factor_descent_fpos` proves the strengthened descent; the only
  reason `hf` remains a hypothesis above is that `irreducible_factorization_of_gs_solution`'s
  `.choose_spec` does not *expose* it (a one-line addition would discharge it outright).
- **R2 (content non-vanishing)** fails on at most `B`-many close parameters, where `B` is the degree of
  any nonzero coefficient of the (necessarily nonzero) content — `content_bad_close_params_card_le`. -/

/-- **R1, provable: the `expand`-exponent of a per-factor descent is `≥ 1`.** -/
theorem eq512_factor_descent_fpos (g : F[Z][X][Y]) (hg : Irreducible g) (hdeg : g.natDegree ≠ 0) :
    ∃ (r : F[Z][X][Y]) (nn : ℕ) (u : F[Z][X]), 1 ≤ nn ∧ Irreducible r ∧
      (r.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable ∧
      IsUnit u ∧ g = Polynomial.C u * (Polynomial.expand (F[Z][X]) nn r) := by
  obtain ⟨r, nn, u, hr, hsep, hu, heq⟩ := eq512_factor_descent g hg hdeg
  refine ⟨r, nn, u, ?_, hr, hsep, hu, heq⟩
  rcases Nat.eq_zero_or_pos nn with h0 | hpos
  · exfalso; apply hdeg
    rw [heq, Polynomial.natDegree_C_mul hu.ne_zero, Polynomial.natDegree_expand, h0, Nat.mul_zero]
  · exact hpos

/-- The GS factorization content is nonzero. -/
theorem content_ne_zero_of_gs (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    (irreducible_factorization_of_gs_solution h_gs).choose ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, hfact, _⟩ :=
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose_spec
  intro h0
  apply h_gs.Q_ne_0
  rw [hfact]
  refine mul_eq_zero_of_left ?_ _
  rw [h0]; exact Polynomial.C_0

/-- **Content-vanishing specializations lie among the roots of a nonzero coefficient** (brick 4). -/
private theorem specialization_zero_mem_roots'
    (C₀ : Polynomial (Polynomial F)) (i : ℕ) (hi : C₀.coeff i ≠ 0) (a : F)
    (hz : C₀.map (Polynomial.evalRingHom a) = 0) :
    a ∈ (C₀.coeff i).roots := by
  have hcoeff : (C₀.coeff i).eval a = 0 := by
    have h1 : (C₀.map (Polynomial.evalRingHom a)).coeff i = 0 := by
      rw [hz]; exact Polynomial.coeff_zero i
    rw [Polynomial.coeff_map] at h1; simpa using h1
  rw [Polynomial.mem_roots']; exact ⟨hi, hcoeff⟩

/-- **R2, tractable: the content-vanishing close parameters number at most a coefficient degree.**
For every finite set `S'` of close parameters at which the content vanishes, `#S' ≤ B` for a fixed `B`
(the degree of a nonzero content coefficient).  The exceptional set the descent must exclude is finite,
bounded independently of `S'`. -/
theorem content_bad_close_params_card_le (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∃ B : ℕ, ∀ (S' : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)),
      (∀ z ∈ S', (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
          (irreducible_factorization_of_gs_solution h_gs).choose = 0) →
        #S' ≤ B := by
  classical
  have hC0 : (irreducible_factorization_of_gs_solution h_gs).choose ≠ 0 :=
    content_ne_zero_of_gs (k := k) h_gs
  obtain ⟨i, hi⟩ : ∃ i, (irreducible_factorization_of_gs_solution h_gs).choose.coeff i ≠ 0 := by
    by_contra h; push_neg at h
    exact hC0 (Polynomial.ext (fun i => by rw [h i, Polynomial.coeff_zero]))
  refine ⟨((irreducible_factorization_of_gs_solution h_gs).choose.coeff i).natDegree, ?_⟩
  intro S' hbad
  have hinj : Function.Injective
      (fun z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ => z.1) := Subtype.val_injective
  have hsub : (S'.image (fun z => z.1)) ⊆
      ((irreducible_factorization_of_gs_solution h_gs).choose.coeff i).roots.toFinset := by
    intro a ha
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp ha
    have hz0 : (irreducible_factorization_of_gs_solution h_gs).choose.map
        (Polynomial.evalRingHom z.1) = 0 := hbad z hzS
    exact Multiset.mem_toFinset.mpr (specialization_zero_mem_roots'
      (irreducible_factorization_of_gs_solution h_gs).choose i hi z.1 hz0)
  calc #S' = #(S'.image (fun z => z.1)) := (Finset.card_image_of_injective S' hinj).symm
    _ ≤ #((irreducible_factorization_of_gs_solution h_gs).choose.coeff i).roots.toFinset :=
        Finset.card_le_card hsub
    _ ≤ Multiset.card ((irreducible_factorization_of_gs_solution h_gs).choose.coeff i).roots :=
        Multiset.toFinset_card_le _
    _ ≤ ((irreducible_factorization_of_gs_solution h_gs).choose.coeff i).natDegree :=
        Polynomial.card_roots' _

/-! ## Descended Claim 5.7 over the FULL close set (content correction quantified)

The strongest, BCIKS-faithful form: no blanket content hypothesis.  Over the *entire* close-parameter
set `𝒮` (every member specializing `Q` to zero — the genuine §5 input), a single descended `(r, H)`
accounts for `(#𝒮 − B) / natDegreeY Q` of them, where `B` bounds the finite content-exception set
(supplied by `content_bad_close_params_card_le`).  This is the descended Claim 5.7 with R2 *discharged
into the bound* rather than assumed — entirely `hcoincide`-free. -/
open Classical in
theorem pg_exists_common_candidate_pair_descended_full (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hf : ∀ j < (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.length,
      1 ≤ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD j 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (𝒮 : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hQall : ∀ z ∈ 𝒮, (pg_eval_on_Z (F := F) Q z.1).eval
        (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0)
    (B : ℕ)
    (hB : ∀ S' : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁),
      (∀ z ∈ S', (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
          (irreducible_factorization_of_gs_solution h_gs).choose = 0) → #S' ≤ B)
    (hBlt : B < #𝒮) :
    ∃ (r : F[Z][X][Y]) (H : F[Z][X]),
      r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      (#𝒮 - B) / Bivariate.natDegreeY Q ≤
        #(𝒮.filter (fun z => ∃ a : ℕ,
            (pg_eval_on_Z (F := F) r z.1).eval
              ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 ∧
            (Bivariate.evalX z.1 H).eval
              (((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a).eval x₀) = 0)) := by
  classical
  set cgood : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ → Prop :=
    fun z => (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
      (irreducible_factorization_of_gs_solution h_gs).choose ≠ 0 with hcgood
  set S := 𝒮.filter cgood with hSdef
  -- content-vanishing parameters are ≤ B
  have hbad : #(𝒮.filter (fun z => ¬ cgood z)) ≤ B := by
    apply hB
    intro z hz
    rw [Finset.mem_filter] at hz
    simpa [hcgood] using not_not.mp hz.2
  have hsplit : #S + #(𝒮.filter (fun z => ¬ cgood z)) = #𝒮 := by
    rw [hSdef]; exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hScard : #𝒮 - B ≤ #S := by omega
  have hS_ne : S.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨r, H, hr_mem, hlarge⟩ :=
    pg_exists_common_candidate_pair_descended (k := k) x₀ h_gs hf hsep S hS_ne
      (by
        intro z hz
        rw [hSdef, Finset.mem_filter] at hz
        exact ⟨hQall z hz.1, by simpa [hcgood] using hz.2⟩)
  refine ⟨r, H, hr_mem, ?_⟩
  calc (#𝒮 - B) / Bivariate.natDegreeY Q
      ≤ #S / Bivariate.natDegreeY Q := Nat.div_le_div_right hScard
    _ ≤ #(S.filter (fun z => ∃ a : ℕ,
          (pg_eval_on_Z (F := F) r z.1).eval
            ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 ∧
          (Bivariate.evalX z.1 H).eval
            (((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a).eval x₀) = 0)) :=
        hlarge
    _ ≤ _ := Finset.card_le_card (Finset.filter_subset_filter _ (by rw [hSdef]; exact Finset.filter_subset _ _))

/-! ## R1 fully discharged via the strengthened factorization bundle

With `irreducible_factorization_of_gs_solution` now exposing `∀ fᵢ ∈ f, 1 ≤ fᵢ` (proved in-tree from
the positive-degree factors: an `nn = 0` descent would collapse the factor), `hf` is no longer needed —
it is a theorem. -/

/-- **R1 discharged:** every descended `expand`-exponent is `≥ 1`, now a consequence of the bundle. -/
theorem factorization_fpos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ j < (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose.length,
      1 ≤ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.getD j 0 := by
  obtain ⟨hlen1, _, _, _, _, _, _, hfpos⟩ :=
    (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose_spec.choose_spec
  intro j hj
  have hjf : j <
      (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose_spec.choose.length := by
    rw [← hlen1]; exact hj
  exact hfpos _ (by rw [List.getD_eq_getElem _ 0 hjf]; exact List.getElem_mem hjf)

open Classical in
/-- **Descended Claim 5.7, R1-free.**  Identical to `…_full` but with `hf` removed — discharged
internally by `factorization_fpos`.  The only remaining inputs are the genuine §5 data and the
content-exception bound `B`/`hB` (from `content_bad_close_params_card_le`).  No `hcoincide`, no `hf`. -/
theorem pg_exists_common_candidate_pair_descended_full_nohf (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (𝒮 : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁))
    (hQall : ∀ z ∈ 𝒮, (pg_eval_on_Z (F := F) Q z.1).eval
        (Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) = 0)
    (B : ℕ)
    (hB : ∀ S' : Finset (coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁),
      (∀ z ∈ S', (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
          (irreducible_factorization_of_gs_solution h_gs).choose = 0) → #S' ≤ B)
    (hBlt : B < #𝒮) :
    ∃ (r : F[Z][X][Y]) (H : F[Z][X]),
      r ∈ pg_RsetDescended (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs ∧
      (#𝒮 - B) / Bivariate.natDegreeY Q ≤
        #(𝒮.filter (fun z => ∃ a : ℕ,
            (pg_eval_on_Z (F := F) r z.1).eval
              ((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a) = 0 ∧
            (Bivariate.evalX z.1 H).eval
              (((Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2) ^ a).eval x₀) = 0)) :=
  pg_exists_common_candidate_pair_descended_full (k := k) x₀ h_gs (factorization_fpos (k := k) h_gs)
    hsep 𝒮 hQall B hB hBlt

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.pg_sum_natDegreeY_RsetDescended_le_natDegreeY_Q
#print axioms ProximityGap.pg_sum_card_normalizedFactors_evalX_RsetDescended_le_natDegreeY
#print axioms ProximityGap.pg_exists_R_descended_of_Q_eval_zero
#print axioms ProximityGap.pg_exists_H_of_R_eval_zero_generic
#print axioms ProximityGap.pg_exists_pair_for_z_descended
#print axioms ProximityGap.pg_card_candidatePairsDescended_le_natDegreeY
#print axioms ProximityGap.pg_exists_common_candidate_pair_descended
#print axioms ProximityGap.eq512_factor_descent_fpos
#print axioms ProximityGap.content_ne_zero_of_gs
#print axioms ProximityGap.content_bad_close_params_card_le
#print axioms ProximityGap.pg_exists_common_candidate_pair_descended_full
#print axioms ProximityGap.factorization_fpos
#print axioms ProximityGap.pg_exists_common_candidate_pair_descended_full_nohf
