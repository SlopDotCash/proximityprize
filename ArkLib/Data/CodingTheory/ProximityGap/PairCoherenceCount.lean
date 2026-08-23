/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExactCoherenceCount

/-!
# Exact pair counts (#389): merge-interpolation surjectivity

The heart of the second moment: for two cores overlapping in at most `k`
points, the joint condition map — coherence of both cores plus the value
match — is SURJECTIVE on the coefficient family, by merge interpolation:

* prescribe the `T`-interpolant `A` freely (its `m` coherence coordinates and
  its `X^k` coefficient carry the targets);
* prescribe the `T'`-interpolant as `B₀ + W` where `B₀` carries the `T'`
  targets and `W` (degree `< k`, interpolated on the ≤ `k` overlap points)
  patches the consistency `A = B` on `T ∩ T'`;
* interpolate the merged values on `T ∪ T'` (which fits, `|T∪T'| ≤ M`).

Hence (`card_pair_coherent_eq`):

  **`#{c : both cores coherent ∧ values match} · q^{2m+1} = q^M`** — EXACT.

This is the off-diagonal stratum of the second moment; with the diagonal and
the high-overlap strata it yields the capacity-failure bandwidth law.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Exact fiber count, general codomain**: a surjective subtraction-linear
map into a finite additive group has zero fiber of size exactly
`q^M / |β|`. -/
theorem card_zeroFiber_eq_of_surjective' {M : ℕ} {β : Type*} [Fintype β]
    [DecidableEq β] [AddGroup β] (φ : (Fin M → F) → β)
    (hsub : ∀ x y, φ (x - y) = φ x - φ y)
    (hsurj : Function.Surjective φ) :
    (Finset.univ.filter
        (fun c : Fin M → F => φ c = 0)).card * Fintype.card β
      = (Fintype.card F) ^ M := by
  have hfib : ∀ v : β, (Finset.univ.filter
      (fun c : Fin M → F => φ c = v)).card
      = (Finset.univ.filter (fun c : Fin M → F => φ c = 0)).card := by
    intro v
    obtain ⟨δv, hδv⟩ := hsurj v
    refine Finset.card_bij' (fun c _ => c - δv) (fun c _ => c + δv)
      ?_ ?_ ?_ ?_
    · intro c hc
      have hcval := (Finset.mem_filter.mp hc).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hsub, hcval, hδv, sub_self]
    · intro c hc
      have hcval := (Finset.mem_filter.mp hc).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h := hsub (c + δv) δv
      rw [add_sub_cancel_right] at h
      have h2 : φ (c + δv) - φ δv = φ c := h.symm
      rw [hcval, hδv] at h2
      have h3 : φ (c + δv) - v = 0 := h2
      have h4 : φ (c + δv) = v := by
        have := sub_eq_zero.mp h3
        exact this
      exact h4
    · intro c _
      simp
    · intro c _
      simp
  have hpart : (Fintype.card F) ^ M
      = ∑ v : β, (Finset.univ.filter
        (fun c : Fin M → F => φ c = v)).card := by
    calc (Fintype.card F) ^ M
        = Fintype.card (Fin M → F) := by
          rw [Fintype.card_fun, Fintype.card_fin]
      _ = (Finset.univ : Finset (Fin M → F)).card := Finset.card_univ.symm
      _ = ∑ v ∈ Finset.univ, (Finset.univ.filter
          (fun c : Fin M → F => φ c = v)).card :=
          Finset.card_eq_sum_card_fiberwise fun c _ => Finset.mem_univ (φ c)
  rw [Finset.sum_congr rfl (fun v _ => hfib v), Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hpart
  rw [mul_comm] at hpart
  exact hpart.symm

open Classical in
/-- Interpolation only depends on the values at the nodes. -/
theorem interpolate_congr_on (dom : Fin n ↪ F) (T : Finset (Fin n))
    {r r' : Fin n → F} (h : ∀ i ∈ T, r i = r' i) :
    Lagrange.interpolate T (⇑dom) r = Lagrange.interpolate T (⇑dom) r' := by
  rw [Lagrange.interpolate_apply, Lagrange.interpolate_apply]
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

open Classical in
/-- **The merge-interpolation pair surjectivity and exact count**: for cores
overlapping in at most `k` points, the joint coherence-and-value-match
condition cuts the family by exactly `q^{2m+1}`. -/
theorem card_pair_coherent_eq (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1)
    (hT' : T'.card = k + m + 1) (hcap : (T ∩ T').card ≤ k)
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        (IsCoherent dom k m T (coeffFamily M c)
          ∧ IsCoherent dom k m T' (coeffFamily M c))
        ∧ (coreInterp dom T (coeffFamily M c)).coeff k
            = (coreInterp dom T' (coeffFamily M c)).coeff k)).card
      * ((Fintype.card F) ^ m * (Fintype.card F) ^ m * Fintype.card F)
      = (Fintype.card F) ^ M := by
  -- the joint condition map
  set ψ : (Fin M → F) → ((Fin m → F) × (Fin m → F) × F) := fun c =>
    (fun j => (coreInterp dom T (coeffFamily M c)).coeff (k + 1 + j),
     fun j => (coreInterp dom T' (coeffFamily M c)).coeff (k + 1 + j),
     (coreInterp dom T (coeffFamily M c)).coeff k
       - (coreInterp dom T' (coeffFamily M c)).coeff k) with hψ
  -- subtraction-linearity
  have hIsub : ∀ (S : Finset (Fin n)) (x y : Fin M → F),
      coreInterp dom S (coeffFamily M (x - y))
        = coreInterp dom S (coeffFamily M x)
          - coreInterp dom S (coeffFamily M y) := by
    intro S x y
    rw [coeffFamily_sub, coreInterp, coreInterp, coreInterp]
    have hvals : (fun i => (coeffFamily M x - coeffFamily M y).eval (dom i))
        = (fun i => (coeffFamily M x).eval (dom i))
          - (fun i => (coeffFamily M y).eval (dom i)) := by
      funext i
      simp [eval_sub]
    rw [hvals, map_sub]
  have hsub : ∀ x y, ψ (x - y) = ψ x - ψ y := by
    intro x y
    rw [hψ]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext j
      show (coreInterp dom T (coeffFamily M (x - y))).coeff (k + 1 + (j : ℕ))
        = _
      rw [hIsub T x y, coeff_sub]
      rfl
    · funext j
      show (coreInterp dom T' (coeffFamily M (x - y))).coeff (k + 1 + (j : ℕ))
        = _
      rw [hIsub T' x y, coeff_sub]
      rfl
    · show (coreInterp dom T (coeffFamily M (x - y))).coeff k
        - (coreInterp dom T' (coeffFamily M (x - y))).coeff k = _
      rw [hIsub T x y, hIsub T' x y, coeff_sub, coeff_sub]
      show _ = ((coreInterp dom T (coeffFamily M x)).coeff k
          - (coreInterp dom T' (coeffFamily M x)).coeff k)
        - ((coreInterp dom T (coeffFamily M y)).coeff k
          - (coreInterp dom T' (coeffFamily M y)).coeff k)
      ring
  -- surjectivity by merge interpolation
  have hsurj : Function.Surjective ψ := by
    rintro ⟨s, t, e⟩
    -- the T-side target polynomial
    set A : F[X] := C e * X ^ k + ∑ j : Fin m, C (s j) * X ^ (k + 1 + (j : ℕ))
      with hA
    have hAdeg : A.natDegree ≤ k + m := by
      rw [hA]
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · calc (C e * X ^ k).natDegree
            ≤ (C e).natDegree + (X ^ k : F[X]).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ k + m := by rw [natDegree_C, natDegree_X_pow]; omega
      · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
        calc (C (s j) * X ^ (k + 1 + (j : ℕ))).natDegree
            ≤ (C (s j)).natDegree
                + (X ^ (k + 1 + (j : ℕ)) : F[X]).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ k + m := by
              rw [natDegree_C, natDegree_X_pow]
              have := j.2
              omega
    -- the T'-side base polynomial
    set B₀ : F[X] := ∑ j : Fin m, C (t j) * X ^ (k + 1 + (j : ℕ)) with hB₀
    have hB₀deg : B₀.natDegree ≤ k + m := by
      rw [hB₀]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      calc (C (t j) * X ^ (k + 1 + (j : ℕ))).natDegree
          ≤ (C (t j)).natDegree
              + (X ^ (k + 1 + (j : ℕ)) : F[X]).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ k + m := by
            rw [natDegree_C, natDegree_X_pow]
            have := j.2
            omega
    -- the overlap patch
    set W : F[X] := Lagrange.interpolate (T ∩ T') (⇑dom)
      (fun i => (A - B₀).eval (dom i)) with hW
    have hWdeg : W.degree < (k : ℕ) := by
      have hvs : Set.InjOn dom ((T ∩ T' : Finset (Fin n)) : Set (Fin n)) :=
        fun a _ b _ h => dom.injective h
      calc W.degree < ((T ∩ T').card : ℕ) :=
            Lagrange.degree_interpolate_lt _ hvs
        _ ≤ (k : ℕ) := by exact_mod_cast hcap
    set B : F[X] := B₀ + W with hB
    have hBdeg : B.natDegree ≤ k + m := by
      rw [hB]
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le hB₀deg ?_)
      by_cases hW0 : W = 0
      · rw [hW0, natDegree_zero]
        omega
      · have := (Polynomial.natDegree_lt_iff_degree_lt hW0).mpr hWdeg
        omega
    -- A and B agree on the overlap
    have hAB : ∀ i ∈ T ∩ T', A.eval (dom i) = B.eval (dom i) := by
      intro i hi
      have hvs : Set.InjOn dom ((T ∩ T' : Finset (Fin n)) : Set (Fin n)) :=
        fun a _ b _ h => dom.injective h
      have hWi : W.eval (dom i) = (A - B₀).eval (dom i) := by
        rw [hW]
        exact Lagrange.eval_interpolate_at_node _ hvs hi
      have hBe : B.eval (dom i) = B₀.eval (dom i) + W.eval (dom i) := by
        rw [hB, eval_add]
      rw [hBe, hWi, eval_sub]
      ring
    -- the merged word
    set vals : Fin n → F :=
      fun i => if i ∈ T then A.eval (dom i) else B.eval (dom i) with hvals
    set Q : F[X] := Lagrange.interpolate (T ∪ T') (⇑dom) vals with hQdef
    have hvsU : Set.InjOn dom ((T ∪ T' : Finset (Fin n)) : Set (Fin n)) :=
      fun a _ b _ h => dom.injective h
    have hQdeg : Q.natDegree < M := by
      by_cases hQ0 : Q = 0
      · rw [hQ0, natDegree_zero]
        omega
      · rw [Polynomial.natDegree_lt_iff_degree_lt hQ0]
        calc Q.degree < ((T ∪ T').card : ℕ) :=
              Lagrange.degree_interpolate_lt _ hvsU
          _ ≤ (M : WithBot ℕ) := by
              have h := Finset.card_union_le T T'
              rw [hT, hT'] at h
              exact_mod_cast le_trans h (by omega : k + m + 1 + (k + m + 1) ≤ M)
    have hQT : ∀ i ∈ T, Q.eval (dom i) = A.eval (dom i) := by
      intro i hi
      have h := Lagrange.eval_interpolate_at_node (r := vals) hvsU
        (Finset.mem_union_left T' hi)
      rw [hQdef, h]
      show (if i ∈ T then A.eval (dom i) else B.eval (dom i))
        = A.eval (dom i)
      rw [if_pos hi]
    have hQT' : ∀ i ∈ T', Q.eval (dom i) = B.eval (dom i) := by
      intro i hi
      have h := Lagrange.eval_interpolate_at_node (r := vals) hvsU
        (Finset.mem_union_right T hi)
      rw [hQdef, h]
      show (if i ∈ T then A.eval (dom i) else B.eval (dom i))
        = B.eval (dom i)
      by_cases hiT : i ∈ T
      · rw [if_pos hiT]
        exact hAB i (Finset.mem_inter.mpr ⟨hiT, hi⟩)
      · rw [if_neg hiT]
    -- the interpolants of the merged word are A and B
    have hIT : coreInterp dom T (coeffFamily M (fun j => Q.coeff (j : ℕ)))
        = A := by
      rw [coeffFamily_reconstruct M hQdeg, coreInterp]
      have hcongr := interpolate_congr_on dom T
        (r := fun i => Q.eval (dom i)) (r' := fun i => A.eval (dom i))
        hQT
      rw [hcongr]
      have hvsT : Set.InjOn dom T := fun a _ b _ h => dom.injective h
      exact (Lagrange.eq_interpolate hvsT (by
        rw [hT]
        calc A.degree ≤ (A.natDegree : WithBot ℕ) :=
              Polynomial.degree_le_natDegree
          _ < ((k + m + 1 : ℕ) : WithBot ℕ) := by
              exact_mod_cast by omega)).symm
    have hIT' : coreInterp dom T' (coeffFamily M (fun j => Q.coeff (j : ℕ)))
        = B := by
      rw [coeffFamily_reconstruct M hQdeg, coreInterp]
      have hcongr := interpolate_congr_on dom T'
        (r := fun i => Q.eval (dom i)) (r' := fun i => B.eval (dom i))
        hQT'
      rw [hcongr]
      have hvsT' : Set.InjOn dom T' := fun a _ b _ h => dom.injective h
      exact (Lagrange.eq_interpolate hvsT' (by
        rw [hT']
        calc B.degree ≤ (B.natDegree : WithBot ℕ) :=
              Polynomial.degree_le_natDegree
          _ < ((k + m + 1 : ℕ) : WithBot ℕ) := by
              exact_mod_cast by omega)).symm
    -- read off the targets
    refine ⟨fun j => Q.coeff (j : ℕ), ?_⟩
    rw [hψ]
    have hAcoeffs : ∀ j : Fin m, A.coeff (k + 1 + (j : ℕ)) = s j := by
      intro j
      rw [hA, coeff_add, coeff_C_mul, coeff_X_pow, if_neg (by omega),
        mul_zero, zero_add, Polynomial.finset_sum_coeff]
      calc ∑ i : Fin m, (C (s i) * X ^ (k + 1 + (i : ℕ))).coeff
            (k + 1 + (j : ℕ))
          = ∑ i : Fin m, (if i = j then s i else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [coeff_C_mul, coeff_X_pow]
            by_cases h2 : i = j
            · subst h2
              simp
            · rw [if_neg (by
                intro hji
                exact h2 (Fin.ext (by omega))), if_neg h2, mul_zero]
        _ = s j := by
            rw [Finset.sum_ite_eq' Finset.univ j (fun i => s i)]
            simp
    have hB₀coeffs : ∀ j : Fin m, B₀.coeff (k + 1 + (j : ℕ)) = t j := by
      intro j
      rw [hB₀, Polynomial.finset_sum_coeff]
      calc ∑ i : Fin m, (C (t i) * X ^ (k + 1 + (i : ℕ))).coeff
            (k + 1 + (j : ℕ))
          = ∑ i : Fin m, (if i = j then t i else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [coeff_C_mul, coeff_X_pow]
            by_cases h2 : i = j
            · subst h2
              simp
            · rw [if_neg (by
                intro hji
                exact h2 (Fin.ext (by omega))), if_neg h2, mul_zero]
        _ = t j := by
            rw [Finset.sum_ite_eq' Finset.univ j (fun i => t i)]
            simp
    have hWhigh : ∀ b : ℕ, k ≤ b → W.coeff b = 0 := by
      intro b hb
      refine Polynomial.coeff_eq_zero_of_degree_lt ?_
      exact lt_of_lt_of_le hWdeg (by exact_mod_cast hb)
    have hAk : A.coeff k = e := by
      rw [hA, coeff_add, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
      have hsum0 : (∑ j : Fin m, C (s j) * X ^ (k + 1 + (j : ℕ))).coeff k
          = 0 := by
        rw [Polynomial.finset_sum_coeff]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
      rw [hsum0, add_zero]
    have hBk : B.coeff k = 0 := by
      rw [hB, coeff_add, hWhigh k le_rfl, add_zero, hB₀,
        Polynomial.finset_sum_coeff]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext j
      show (coreInterp dom T
        (coeffFamily M (fun j => Q.coeff (j : ℕ)))).coeff (k + 1 + (j : ℕ))
        = s j
      rw [hIT]
      exact hAcoeffs j
    · funext j
      show (coreInterp dom T'
        (coeffFamily M (fun j => Q.coeff (j : ℕ)))).coeff (k + 1 + (j : ℕ))
        = t j
      rw [hIT']
      rw [hB, coeff_add, hWhigh (k + 1 + (j : ℕ)) (by omega), add_zero]
      exact hB₀coeffs j
    · show (coreInterp dom T
          (coeffFamily M (fun j => Q.coeff (j : ℕ)))).coeff k
        - (coreInterp dom T'
          (coeffFamily M (fun j => Q.coeff (j : ℕ)))).coeff k = e
      rw [hIT, hIT', hAk, hBk, sub_zero]
  -- the exact count
  have h := card_zeroFiber_eq_of_surjective' ψ hsub hsurj
  have hcardβ : Fintype.card ((Fin m → F) × (Fin m → F) × F)
      = (Fintype.card F) ^ m * (Fintype.card F) ^ m * Fintype.card F := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin]
    ring
  rw [hcardβ] at h
  have hfeq : (Finset.univ.filter (fun c : Fin M → F =>
        (IsCoherent dom k m T (coeffFamily M c)
          ∧ IsCoherent dom k m T' (coeffFamily M c))
        ∧ (coreInterp dom T (coeffFamily M c)).coeff k
            = (coreInterp dom T' (coeffFamily M c)).coeff k))
      = (Finset.univ.filter (fun c : Fin M → F => ψ c = 0)) := by
    refine Finset.filter_congr fun c _ => ?_
    rw [hψ]
    constructor
    · rintro ⟨⟨hcoh, hcoh'⟩, hval⟩
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext j
        exact hcoh j
      · funext j
        exact hcoh' j
      · show (coreInterp dom T (coeffFamily M c)).coeff k
          - (coreInterp dom T' (coeffFamily M c)).coeff k = 0
        rw [hval, sub_self]
    · intro hzero
      have h1 := congrArg Prod.fst hzero
      have h2 := congrArg (fun p => p.2.1) hzero
      have h3 := congrArg (fun p => p.2.2) hzero
      simp only at h1 h2 h3
      refine ⟨⟨fun j => congrFun h1 j, fun j => congrFun h2 j⟩, ?_⟩
      exact sub_eq_zero.mp h3
  rw [hfeq]
  exact h

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.card_zeroFiber_eq_of_surjective'
#print axioms ProximityGap.Ownership.card_pair_coherent_eq
