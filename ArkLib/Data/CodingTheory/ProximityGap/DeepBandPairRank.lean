/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The pair-coherence rank law, small-overlap strata (#389, route 2)

The first Lean brick of the second-moment route through the sub-Johnson supply
wall.  For a pair of `(k+m+1)`-cores `T, T'` with **overlap `≤ k`**, the
`2m + 1` linear conditions on the generator space `F^M` (`M ≥ 2(k+m+1)`) —
coherence of `T`, coherence of `T'`, and equality of the two pinned values —
are **jointly surjective**, hence cut the space by exactly `q^(2m+1)`:

* `card_kernel_eq_of_surjective` — the exact-kernel engine: a jointly
  surjective, subtraction-linear family of conditions indexed by a finite `ι`
  has zero set of size exactly `q^(M − #ι)`, in product form
  `#kernel · q^#ι = q^M`.
* `pair_conditions_surjective` — the surjectivity, by direct construction:
  prescribe the two interpolants' band coefficients freely as explicit
  monomial sums, patch consistency on the `≤ k` common points by a Lagrange
  correction of degree `< k` (invisible to the band), and lift to a generator
  through `≤ M` points.  No duality, no resultants: the overlap bound `≤ k`
  is exactly what lets the correction dodge the band.
* `pair_coherence_kernel_card` — the headline count:

    `#{c : F^M | IsCoherent T Qc ∧ IsCoherent T' Qc ∧ val T = val T'}
        · q^(2m+1) = q^M`.

Probe: `probe_pair_coherence_rank.py` — the rank law
`rank(T,T') = 2m+1 − max(0, |T∩T'|−k)` measured exact at every stratum of six
exhaustive instances; this file proves the `|T∩T'| ≤ k` (full-rank) strata,
which carry the second moment.  Deep strata (`> k`) and the moment assembly
are the registered follow-ups.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The exact-kernel engine -/

open Classical in
/-- **Exact kernel of a surjective linear condition family.**  A jointly
surjective, subtraction-linear family `φ : ι → (Fin M → F) → F` has zero set
of size exactly `q^(M − #ι)`, in product form. -/
theorem card_kernel_eq_of_surjective {M : ℕ} {ι : Type} [Fintype ι]
    (φ : ι → (Fin M → F) → F)
    (hsub : ∀ j x y, φ j (x - y) = φ j x - φ j y)
    (hsurj : ∀ t : ι → F, ∃ c, ∀ j, φ j c = t j) :
    (Finset.univ.filter (fun c : Fin M → F => ∀ j, φ j c = 0)).card
      * (Fintype.card F) ^ (Fintype.card ι) = (Fintype.card F) ^ M := by
  classical
  -- every fiber of the bundled map has the kernel's size
  have hfib : ∀ t : ι → F,
      (Finset.univ.filter (fun c : Fin M → F => ∀ j, φ j c = t j)).card
        = (Finset.univ.filter (fun c : Fin M → F => ∀ j, φ j c = 0)).card := by
    intro t
    obtain ⟨c₀, hc₀⟩ := hsurj t
    refine Finset.card_nbij (fun c => c - c₀) ?_ ?_ ?_
    · intro c hc
      obtain ⟨-, hcv⟩ := Finset.mem_filter.mp hc
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
      rw [hsub, hcv j, hc₀ j, sub_self]
    · intro a _ b _ hab
      have := congrArg (· + c₀) hab
      simpa using this
    · intro c hc
      obtain ⟨-, hcv⟩ := Finset.mem_filter.mp hc
      refine ⟨c + c₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩,
        by simp⟩
      have hkey : φ j (c + c₀) - φ j c₀ = φ j c := by
        rw [← hsub j (c + c₀) c₀]
        congr 1
        abel
      have : φ j (c + c₀) = φ j c + φ j c₀ := by
        rw [← hkey]
        ring
      rw [this, hcv j, hc₀ j, zero_add]
  -- partition the cube by the bundled value
  have hpart : (Fintype.card F) ^ M
      = ∑ t : ι → F,
        (Finset.univ.filter (fun c : Fin M → F => ∀ j, φ j c = t j)).card := by
    have hcard : (Finset.univ : Finset (Fin M → F)).card = (Fintype.card F) ^ M := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [← hcard,
      Finset.card_eq_sum_card_fiberwise
        (f := fun c : Fin M → F => fun j => φ j c)
        (t := (Finset.univ : Finset (ι → F))) (fun c _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    refine Finset.filter_congr fun c _ => ?_
    constructor
    · intro h j
      exact congrFun h j
    · intro h
      funext j
      exact h j
  rw [hpart]
  have hconst : ∀ t : ι → F,
      (Finset.univ.filter (fun c : Fin M → F => ∀ j, φ j c = t j)).card
        = (Finset.univ.filter (fun c : Fin M → F => ∀ j, φ j c = 0)).card :=
    hfib
  rw [Finset.sum_congr rfl (fun t _ => hconst t), Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, smul_eq_mul, mul_comm]

/-! ## The generator polynomial -/

/-- The generator polynomial of a coefficient vector. -/
noncomputable def genPoly {M : ℕ} (c : Fin M → F) : F[X] :=
  ∑ j : Fin M, C (c j) * X ^ (j : ℕ)

theorem genPoly_sub {M : ℕ} (x y : Fin M → F) :
    genPoly (x - y) = genPoly x - genPoly y := by
  rw [genPoly, genPoly, genPoly, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show C (x j - y j) * X ^ (j : ℕ) = _
  rw [C_sub]
  ring

theorem genPoly_degree_lt {M : ℕ} (c : Fin M → F) :
    (genPoly c).degree < (M : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [genPoly, Finset.univ_eq_empty, Finset.sum_empty, degree_zero]
    exact WithBot.bot_lt_coe 0
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe M)]
  intro j _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast j.isLt

/-- Every polynomial of degree `< M` is a generator polynomial. -/
theorem genPoly_coeff_eq {M : ℕ} {Q : F[X]} (hQ : Q.degree < (M : WithBot ℕ)) :
    genPoly (fun j : Fin M => Q.coeff (j : ℕ)) = Q := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hQ0 : Q = 0 := by
      rcases eq_or_ne Q 0 with rfl | hne
      · rfl
      · exact absurd hQ (by
          rw [not_lt]
          calc ((0 : ℕ) : WithBot ℕ) ≤ (Q.natDegree : WithBot ℕ) := by
                exact_mod_cast Nat.zero_le _
            _ = Q.degree := (Polynomial.degree_eq_natDegree hne).symm)
    rw [genPoly, Finset.univ_eq_empty, Finset.sum_empty, hQ0]
  · have hN : Q.natDegree < M := by
      rcases eq_or_ne Q 0 with rfl | hne
      · simpa using hM
      · exact (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hQ
    rw [genPoly, Fin.sum_univ_eq_sum_range (fun j => C (Q.coeff j) * X ^ j) M]
    conv_rhs => rw [Q.as_sum_range' M hN]
    exact Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial

/-! ## Subtraction-linearity of the condition functionals -/

theorem coreInterp_genPoly_sub (dom : Fin n ↪ F) (T : Finset (Fin n))
    {M : ℕ} (x y : Fin M → F) :
    coreInterp dom T (genPoly (x - y))
      = coreInterp dom T (genPoly x) - coreInterp dom T (genPoly y) := by
  rw [coreInterp, coreInterp, coreInterp, genPoly_sub]
  have hvals : (fun i => (genPoly x - genPoly y).eval (dom i))
      = (fun i => (genPoly x).eval (dom i)) - (fun i => (genPoly y).eval (dom i)) := by
    funext i
    simp [eval_sub]
  rw [hvals, map_sub]

/-! ## The surjectivity construction -/

open Classical in
/-- **Joint surjectivity of the pair conditions at overlap `≤ k`.**  Given any
band targets `a, b : Fin m → F` for the two coherence families and any target
`tv : F` for the value difference, some generator realizes them all:
prescribe interpolant `p = Σ aⱼ X^(k+1+j)` for `T`; for `T'` take the band
part `−tv·X^k + Σ bⱼ X^(k+1+j)` plus the degree-`< k` Lagrange patch matching
`p` on `T ∩ T'`; lift through `T ∪ T'`. -/
theorem pair_conditions_surjective (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hover : (T ∩ T').card ≤ k) {M : ℕ} (hM : 2 * (k + m + 1) ≤ M)
    (a b : Fin m → F) (tv : F) :
    ∃ c : Fin M → F,
      (∀ j : Fin m,
        (coreInterp dom T (genPoly c)).coeff (k + 1 + j) = a j) ∧
      (∀ j : Fin m,
        (coreInterp dom T' (genPoly c)).coeff (k + 1 + j) = b j) ∧
      (coreInterp dom T (genPoly c)).coeff k
        - (coreInterp dom T' (genPoly c)).coeff k = tv := by
  classical
  have hinj : ∀ s : Finset (Fin n), Set.InjOn (⇑dom) s :=
    fun s x _ y _ h => dom.injective h
  -- the prescribed interpolant for T
  set p : F[X] := ∑ j : Fin m, C (a j) * X ^ (k + 1 + (j : ℕ)) with hp
  have hpdeg : p.degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [hp, Finset.univ_eq_empty, Finset.sum_empty, degree_zero]
      exact WithBot.bot_lt_coe _
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (k + m + 1))]
    intro j _
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast (by omega : k + 1 + (j : ℕ) < k + m + 1)
  have hpcoeff : ∀ d : ℕ, p.coeff d
      = ∑ j : Fin m, if k + 1 + (j : ℕ) = d then a j else 0 := by
    intro d
    rw [hp, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_ne d (k + 1 + (j : ℕ)) with h | h
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]
  have hpband : ∀ j : Fin m, p.coeff (k + 1 + (j : ℕ)) = a j := by
    intro j
    rw [hpcoeff]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hne
      rw [if_neg (by
        intro h
        exact hne (Fin.ext (by omega)))]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hpk : p.coeff k = 0 := by
    rw [hpcoeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (by omega)]
  -- the band part for T'
  set B : F[X] := C (-tv) * X ^ k + ∑ j : Fin m, C (b j) * X ^ (k + 1 + (j : ℕ))
    with hB
  have hBdeg : B.degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast (by omega : k < k + m + 1)
    · rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [Finset.univ_eq_empty, Finset.sum_empty, degree_zero]
        exact WithBot.bot_lt_coe _
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (k + m + 1))]
      intro j _
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast (by omega : k + 1 + (j : ℕ) < k + m + 1)
  have hBcoeff_band : ∀ j : Fin m, B.coeff (k + 1 + (j : ℕ)) = b j := by
    intro j
    rw [hB, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (by omega), Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl]
      ring
    · intro j' _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by
        intro h
        exact hne (Fin.ext (by omega)))]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hBk : B.coeff k = -tv := by
    rw [hB, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_pos rfl, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_zero fun j _ => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
      ring]
    ring
  -- the Lagrange patch on the overlap
  set S₀ : Finset (Fin n) := T ∩ T' with hS₀
  set r : F[X] := Lagrange.interpolate S₀ (⇑dom)
    (fun i => (p - B).eval (dom i)) with hr
  have hrdeg : r.degree < ((T ∩ T').card : WithBot ℕ) := by
    rw [hr]
    exact_mod_cast Lagrange.degree_interpolate_lt _ (hinj S₀)
  have hrcoeff : ∀ d : ℕ, k ≤ d → r.coeff d = 0 := by
    intro d hd
    refine Polynomial.coeff_eq_zero_of_degree_lt ?_
    refine lt_of_lt_of_le hrdeg ?_
    exact_mod_cast le_trans hover hd
  -- the prescribed interpolant for T'
  set p' : F[X] := B + r with hp'
  have hp'deg : p'.degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hBdeg ?_)
    refine lt_of_lt_of_le hrdeg ?_
    exact_mod_cast le_trans hover (by omega : k ≤ k + m + 1)
  have hp'band : ∀ j : Fin m, p'.coeff (k + 1 + (j : ℕ)) = b j := by
    intro j
    rw [hp', Polynomial.coeff_add, hBcoeff_band j, hrcoeff _ (by omega), add_zero]
  have hp'k : p'.coeff k = -tv := by
    rw [hp', Polynomial.coeff_add, hBk, hrcoeff k le_rfl, add_zero]
  -- p and p' agree on the overlap
  have hagree : ∀ i ∈ S₀, p.eval (dom i) = p'.eval (dom i) := by
    intro i hi
    rw [hp', Polynomial.eval_add, hr,
      Lagrange.eval_interpolate_at_node _ (hinj S₀) hi]
    rw [Polynomial.eval_sub]
    ring
  -- the lift through the union
  set vals : Fin n → F := fun i => if i ∈ T then p.eval (dom i)
    else p'.eval (dom i) with hvals
  set Q : F[X] := Lagrange.interpolate (T ∪ T') (⇑dom) vals with hQdef
  have hQdeg : Q.degree < (M : WithBot ℕ) := by
    have hcard : (T ∪ T').card ≤ M := by
      calc (T ∪ T').card ≤ T.card + T'.card := Finset.card_union_le _ _
        _ = 2 * (k + m + 1) := by omega
        _ ≤ M := hM
    refine lt_of_lt_of_le ?_ (by exact_mod_cast hcard : ((T ∪ T').card : WithBot ℕ) ≤ (M : WithBot ℕ))
    exact_mod_cast Lagrange.degree_interpolate_lt _ (hinj (T ∪ T'))
  set c : Fin M → F := fun j => Q.coeff (j : ℕ) with hc
  have hgen : genPoly c = Q := genPoly_coeff_eq hQdeg
  -- Q's values on T are p's, on T' are p''s
  have hQT : ∀ i ∈ T, Q.eval (dom i) = p.eval (dom i) := by
    intro i hi
    rw [hQdef, Lagrange.eval_interpolate_at_node _ (hinj _)
      (Finset.mem_union_left _ hi)]
    show (if i ∈ T then p.eval (dom i) else p'.eval (dom i)) = p.eval (dom i)
    rw [if_pos hi]
  have hQT' : ∀ i ∈ T', Q.eval (dom i) = p'.eval (dom i) := by
    intro i hi
    rw [hQdef, Lagrange.eval_interpolate_at_node _ (hinj _)
      (Finset.mem_union_right _ hi)]
    show (if i ∈ T then p.eval (dom i) else p'.eval (dom i)) = p'.eval (dom i)
    by_cases hiT : i ∈ T
    · rw [if_pos hiT]
      exact hagree i (Finset.mem_inter.mpr ⟨hiT, hi⟩)
    · rw [if_neg hiT]
  -- the core interpolants are p and p'
  have hIT : coreInterp dom T Q = p := by
    rw [coreInterp]
    have h1 : Lagrange.interpolate T (⇑dom) (fun i => Q.eval (dom i))
        = Lagrange.interpolate T (⇑dom) (fun i => p.eval (dom i)) :=
      Lagrange.interpolate_eq_of_values_eq_on _ _ hQT
    rw [h1]
    exact (Lagrange.eq_interpolate (hinj T) (by rw [hT]; exact hpdeg)).symm
  have hIT' : coreInterp dom T' Q = p' := by
    rw [coreInterp]
    have h1 : Lagrange.interpolate T' (⇑dom) (fun i => Q.eval (dom i))
        = Lagrange.interpolate T' (⇑dom) (fun i => p'.eval (dom i)) :=
      Lagrange.interpolate_eq_of_values_eq_on _ _ hQT'
    rw [h1]
    exact (Lagrange.eq_interpolate (hinj T') (by rw [hT']; exact hp'deg)).symm
  refine ⟨c, ?_, ?_, ?_⟩
  · intro j
    rw [hgen, hIT]
    exact hpband j
  · intro j
    rw [hgen, hIT']
    exact hp'band j
  · rw [hgen, hIT, hIT', hpk, hp'k]
    ring

/-! ## The headline count -/

open Classical in
/-- **THE PAIR-COHERENCE KERNEL COUNT (small-overlap strata).**  For cores
`T, T'` of size `k+m+1` with `|T ∩ T'| ≤ k` and generator space `F^M`
(`M ≥ 2(k+m+1)`): the `2m+1` pair conditions — both coherences and equality
of the pinned values — cut the generator space by **exactly** `q^(2m+1)`:

  `#{c | IsCoherent T ∧ IsCoherent T' ∧ val T = val T'} · q^(2m+1) = q^M`.

This is the `|T∩T'| ≤ k` case of the probe-measured rank law
`rank(T,T') = 2m+1 − max(0, |T∩T'|−k)` — the strata that carry the second
moment of the coherent-core value map. -/
theorem pair_coherence_kernel_card (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hover : (T ∩ T').card ≤ k) {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (2 * m + 1) = (Fintype.card F) ^ M := by
  classical
  -- the condition family, indexed by Fin m ⊕ Fin m ⊕ Unit
  set φ : (Fin m ⊕ (Fin m ⊕ Unit)) → (Fin M → F) → F := fun j c =>
    match j with
    | Sum.inl j => (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ))
    | Sum.inr (Sum.inl j) => (coreInterp dom T' (genPoly c)).coeff (k + 1 + (j : ℕ))
    | Sum.inr (Sum.inr _) => (coreInterp dom T (genPoly c)).coeff k
        - (coreInterp dom T' (genPoly c)).coeff k
    with hφ
  have hsub : ∀ j x y, φ j (x - y) = φ j x - φ j y := by
    intro j x y
    rcases j with j | j | _
    · show (coreInterp dom T (genPoly (x - y))).coeff _ = _
      rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]
    · show (coreInterp dom T' (genPoly (x - y))).coeff _ = _
      rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]
    · show (coreInterp dom T (genPoly (x - y))).coeff k
          - (coreInterp dom T' (genPoly (x - y))).coeff k = _
      rw [coreInterp_genPoly_sub, coreInterp_genPoly_sub,
        Polynomial.coeff_sub, Polynomial.coeff_sub]
      ring
  have hsurj : ∀ t : (Fin m ⊕ (Fin m ⊕ Unit)) → F, ∃ c, ∀ j, φ j c = t j := by
    intro t
    obtain ⟨c, hca, hcb, hcv⟩ := pair_conditions_surjective dom hT hT' hover hM
      (fun j => t (Sum.inl j)) (fun j => t (Sum.inr (Sum.inl j)))
      (t (Sum.inr (Sum.inr ())))
    refine ⟨c, fun j => ?_⟩
    rcases j with j | j | u
    · exact hca j
    · exact hcb j
    · exact hcv
  have h := card_kernel_eq_of_surjective φ hsub hsurj
  have hcardι : Fintype.card (Fin m ⊕ (Fin m ⊕ Unit)) = 2 * m + 1 := by
    simp [Fintype.card_sum]
    omega
  rw [hcardι] at h
  rw [← h]
  congr 2
  refine Finset.filter_congr fun c _ => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩ j
    rcases j with j | j | _
    · exact h1 j
    · exact h2 j
    · show _ - _ = (0 : F)
      rw [h3, sub_self]
  · intro h
    refine ⟨fun j => h (Sum.inl j), fun j => h (Sum.inr (Sum.inl j)), ?_⟩
    have := h (Sum.inr (Sum.inr ()))
    exact sub_eq_zero.mp this

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.card_kernel_eq_of_surjective
#print axioms ProximityGap.PairRank.pair_conditions_surjective
#print axioms ProximityGap.PairRank.pair_coherence_kernel_card
