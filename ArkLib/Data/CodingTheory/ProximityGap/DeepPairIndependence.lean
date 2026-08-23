/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DegeneracyLocusRank

/-!
# The deep-stratum independence DISCHARGED: the upper-window witness (#389, route 2)

`DegeneracyLocusRank.lean` proves the exact degeneracy-locus rank `2m+1 − (j−k)`
conditional on the named per-pair hypothesis `DeepPairValIndependent` — "the finite
rank-nullity computation over the coefficient space".  This file performs that
computation, uniformly: **the witness is the UPPER WINDOW**.

For a deep pair (`|T| = |T'| = k+m+1`, overlap `j = k+d`, `1 ≤ d ≤ m`), choose the
surviving `T'`-band coordinates `surv : i ↦ i + (d−1)` — the coefficient positions
`k+d, …, k+m`.  The mechanism is **unitriangularity**: with `P_J := ∏_{i∈T∩T'}(X − xᵢ)`
(monic, degree `k+d`), the compatible interpolant pairs are exactly `(A, A + P_J·C)`
with `deg C < m+1−d`, and the linear map

  `C ↦ (coeff_{k+d+i}(P_J·C))_{i < m+1−d}`

has the leading coefficient of `C` on its top row (`coeff_mul_degree_add_degree` with
`P_J` monic) — injective, hence surjective (finite dimension).  Both fields of
`DeepPairValIndependent` follow:

* `surjective` — prescribe the `T`-interpolant freely; correct the upper window of the
  `T'`-side by the (surjective) window map; merge through `T ∪ T'` (the in-tree lift).
* `implies_full` — a `T`-coherent generator has `deg I_T ≤ k`; `I_{T'} − I_T` vanishes
  on the `k+d` shared nodes, so it is `P_J·C`; vanishing upper window forces `C = 0`
  (injectivity), so `I_{T'} = I_T` has degree `≤ k` and ALL its band coefficients vanish.

## Results

* `windowMap` + `windowMap_injective` + `windowMap_surjective` — the triangular window
  engine (generic: any monic `P`, any window).
* `deepPairValIndependent_upper` — **the named residual, discharged**: the canonical
  upper-window `surv` satisfies `DeepPairValIndependent` at every deep pair.
* `deep_pair_rank_eq` — **THE UNCONDITIONAL DEGENERACY-LOCUS RANK**: the pair-coherence
  kernel count `#kernel · q^(2m+1−(j−k)) = q^M`, no independence hypothesis — the
  probe-measured rank law is now a theorem on every stratum, completing the rank
  stratification of the second-moment route.

Probe `probe_deep_pair_upper_window.py` (pre-registered, exit 0): rank `= 2m+1−d` and
dropped-coordinate spanning at every one of 14,490 deep pairs over four instances
(`(13,9,2,1), (13,9,2,2), (13,10,3,1), (17,9,2,2)`); the LOWER window is deficient at
80–90 pairs per `m = 2` instance — the window choice is load-bearing, resolving the
honest-scope note of `DegeneracyLocusRank.lean` (the families measured to fail per-pair
all involve the value functional or the lower band; the upper window is uniform).

Honest scope: this closes residual (a) of the route-2 rank stratification.  The
sub-Johnson list-size wall (residual (b)) is untouched.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.DeepPairIndependence

open ProximityGap ProximityGap.Ownership ProximityGap.PairRank ProximityGap.FarPairRank
open ProximityGap.DegeneracyRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Coefficient facts about `genPoly` -/

theorem genPoly_add {M : ℕ} (x y : Fin M → F) :
    genPoly (x + y) = genPoly x + genPoly y := by
  simp only [genPoly]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show C (x j + y j) * X ^ (j : ℕ) = _
  rw [C_add]
  ring

theorem genPoly_smul {M : ℕ} (r : F) (x : Fin M → F) :
    genPoly (r • x) = C r * genPoly x := by
  simp only [genPoly]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show C (r * x j) * X ^ (j : ℕ) = _
  rw [C_mul]
  ring

theorem genPoly_coeff_self {M : ℕ} (c : Fin M → F) (i : Fin M) :
    (genPoly c).coeff (i : ℕ) = c i := by
  simp only [genPoly]
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hne (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The triangular window engine -/

/-- The window map of a monic multiplier: `c ↦ (coeff_{D+i}(P · genPoly c))_{i<e}`. -/
noncomputable def windowMap (P : F[X]) (D e : ℕ) : (Fin e → F) →ₗ[F] (Fin e → F) where
  toFun c := fun i => (P * genPoly c).coeff (D + (i : ℕ))
  map_add' x y := by
    funext i
    show (P * genPoly (x + y)).coeff (D + (i : ℕ)) = _
    rw [genPoly_add, mul_add, Polynomial.coeff_add]
    rfl
  map_smul' r x := by
    funext i
    show (P * genPoly (r • x)).coeff (D + (i : ℕ)) = _
    rw [genPoly_smul, mul_left_comm, Polynomial.coeff_C_mul]
    rfl

/-- **Injectivity of the window map** — the unitriangular mechanism: the top
nonzero coefficient of `C` survives in the window because `P` is monic. -/
theorem windowMap_injective {P : F[X]} {D e : ℕ} (hP : P.Monic)
    (hD : P.natDegree = D) :
    Function.Injective (windowMap (F := F) P D e) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra hc0
  have hg0 : genPoly c ≠ 0 := by
    intro h
    refine hc0 (funext fun i => ?_)
    have := genPoly_coeff_self c i
    rw [h, Polynomial.coeff_zero] at this
    exact this.symm
  have heC : (genPoly c).natDegree < e := by
    have := genPoly_degree_lt (M := e) c
    exact (Polynomial.natDegree_lt_iff_degree_lt hg0).mpr this
  have hlead : (P * genPoly c).coeff (D + (genPoly c).natDegree)
      = (genPoly c).leadingCoeff := by
    rw [← hD, Polynomial.coeff_mul_degree_add_degree, hP.leadingCoeff, one_mul]
  have hzero := congrFun hc (⟨(genPoly c).natDegree, heC⟩ : Fin e)
  show False
  apply Polynomial.leadingCoeff_ne_zero.mpr hg0
  rw [← hlead]
  exact hzero

/-- **Surjectivity of the window map** (injective endomorphism of a
finite-dimensional space). -/
theorem windowMap_surjective {P : F[X]} {D e : ℕ} (hP : P.Monic)
    (hD : P.natDegree = D) :
    Function.Surjective (windowMap (F := F) P D e) :=
  LinearMap.surjective_of_injective (windowMap_injective hP hD)

/-! ## The vanishing polynomial of the overlap and the factorization -/

/-- The monic vanishing polynomial of the node set `J`. -/
noncomputable def nodePoly (dom : Fin n ↪ F) (J : Finset (Fin n)) : F[X] :=
  ∏ i ∈ J, (X - C (dom i))

theorem nodePoly_monic (dom : Fin n ↪ F) (J : Finset (Fin n)) :
    (nodePoly dom J).Monic :=
  monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)

theorem nodePoly_natDegree (dom : Fin n ↪ F) (J : Finset (Fin n)) :
    (nodePoly dom J).natDegree = J.card := by
  rw [nodePoly, Polynomial.natDegree_prod _ _ (fun i _ => Polynomial.X_sub_C_ne_zero _)]
  simp only [Polynomial.natDegree_X_sub_C]
  rw [Finset.sum_const, smul_eq_mul, mul_one]

theorem nodePoly_eval_node (dom : Fin n ↪ F) {J : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ J) : (nodePoly dom J).eval (dom i) = 0 := by
  rw [nodePoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- **Divisibility from node vanishing**: a polynomial vanishing on the (distinct)
nodes of `J` is a multiple of `nodePoly dom J`. -/
theorem nodePoly_dvd_of_eval_eq_zero (dom : Fin n ↪ F) (J : Finset (Fin n))
    {W : F[X]} (hW : ∀ i ∈ J, W.eval (dom i) = 0) :
    nodePoly dom J ∣ W := by
  rcases eq_or_ne W 0 with rfl | hW0
  · exact dvd_zero _
  -- the node multiset embeds into the roots of W
  have hle : (J.val.map (⇑dom)) ≤ W.roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ J.val.map (⇑dom)
    · obtain ⟨i, hiJ, rfl⟩ := Multiset.mem_map.mp ha
      have hnodup : (J.val.map (⇑dom)).Nodup :=
        Multiset.Nodup.map dom.injective J.nodup
      have hcount1 : (J.val.map (⇑dom)).count (dom i) ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp hnodup _
      have hroot : 1 ≤ W.roots.count (dom i) := by
        rw [Polynomial.count_roots]
        exact (Polynomial.rootMultiplicity_pos hW0).mpr
          (hW i (by exact_mod_cast hiJ))
      omega
    · rw [Multiset.count_eq_zero_of_notMem ha]
      exact Nat.zero_le _
  calc nodePoly dom J
      = (Multiset.map (fun a => X - C a) (J.val.map (⇑dom))).prod := by
        rw [nodePoly, Finset.prod_eq_multiset_prod, Multiset.map_map]
        rfl
  _ ∣ (Multiset.map (fun a => X - C a) W.roots).prod :=
      Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
  _ ∣ W := Polynomial.prod_multiset_X_sub_C_dvd W

/-! ## The canonical surviving choice: the upper window -/

/-- The upper-window selection of surviving `T'`-band coordinates: positions
`k+d, …, k+m`, i.e. band indices `d−1, …, m−1`. -/
def survUpper {k m : ℕ} {T T' : Finset (Fin n)}
    (hdeep : k + 1 ≤ (T ∩ T').card) (hshallow : (T ∩ T').card ≤ k + m) :
    Fin (m + 1 - ((T ∩ T').card - k)) → Fin m :=
  fun i => ⟨(i : ℕ) + ((T ∩ T').card - k) - 1, by
    have h1 := i.isLt
    omega⟩

theorem survUpper_pos {k m : ℕ} {T T' : Finset (Fin n)}
    (hdeep : k + 1 ≤ (T ∩ T').card) (hshallow : (T ∩ T').card ≤ k + m)
    (i : Fin (m + 1 - ((T ∩ T').card - k))) :
    k + 1 + ((survUpper hdeep hshallow i : Fin m) : ℕ)
      = (T ∩ T').card + (i : ℕ) := by
  show k + 1 + ((i : ℕ) + ((T ∩ T').card - k) - 1) = _
  omega

/-! ## The `implies_full` field -/

theorem upper_kernel_implies_full (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) (hshallow : (T ∩ T').card ≤ k + m)
    {M : ℕ} (c : Fin M → F)
    (hcohT : ∀ j : Fin m, (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) = 0)
    (hwin : ∀ j : Fin (m + 1 - ((T ∩ T').card - k)),
      (coreInterp dom T' (genPoly c)).coeff
        (k + 1 + ((survUpper hdeep hshallow j : Fin m) : ℕ)) = 0) :
    IsCoherent dom k m T' (genPoly c) := by
  classical
  set A := coreInterp dom T (genPoly c) with hA
  set B := coreInterp dom T' (genPoly c) with hB
  -- A has degree ≤ k (coherence collapse, in-tree)
  have hAdeg : A.degree < ((k + 1 : ℕ) : WithBot ℕ) :=
    coherent_coreInterp_degree_le dom hT (fun j => hcohT j)
  -- B − A vanishes on the overlap nodes
  have hBA : ∀ i ∈ T ∩ T', (B - A).eval (dom i) = 0 := by
    intro i hi
    rw [Polynomial.eval_sub, hB, hA,
      coreInterp_eval_eq dom T' (genPoly c) (Finset.mem_inter.mp hi).2,
      coreInterp_eval_eq dom T (genPoly c) (Finset.mem_inter.mp hi).1, sub_self]
  obtain ⟨Cq, hCq⟩ := nodePoly_dvd_of_eval_eq_zero dom (T ∩ T') hBA
  -- degree bookkeeping for the cofactor
  have hBdeg : B.degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    have := coreInterp_degree_lt dom T' (genPoly c)
    rwa [hT'] at this
  have hCqdeg : Cq.degree < ((m + 1 - ((T ∩ T').card - k) : ℕ) : WithBot ℕ) := by
    rcases eq_or_ne Cq 0 with rfl | hCq0
    · rw [Polynomial.degree_zero]
      exact_mod_cast WithBot.bot_lt_coe _
    have hBA0 : B - A ≠ 0 := by
      intro h
      rw [h, zero_eq_mul] at hCq
      rcases hCq with h0 | h0
      · exact Polynomial.Monic.ne_zero (nodePoly_monic dom (T ∩ T')) h0
      · exact hCq0 h0
    have hdegBA : (B - A).degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hBdeg ?_)
      exact lt_of_lt_of_le hAdeg (by exact_mod_cast (by omega : k + 1 ≤ k + m + 1))
    have hnat : (B - A).natDegree < k + m + 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hBA0).mpr hdegBA
    have hmulnat : (B - A).natDegree = (T ∩ T').card + Cq.natDegree := by
      rw [hCq, Polynomial.natDegree_mul (Polynomial.Monic.ne_zero
        (nodePoly_monic dom (T ∩ T'))) hCq0, nodePoly_natDegree]
    have hcqn : Cq.natDegree < m + 1 - ((T ∩ T').card - k) := by omega
    exact (Polynomial.natDegree_lt_iff_degree_lt hCq0).mp hcqn
  -- the window map kills the cofactor
  have hCvec : genPoly (fun i : Fin (m + 1 - ((T ∩ T').card - k)) =>
      Cq.coeff (i : ℕ)) = Cq := genPoly_coeff_eq hCqdeg
  have hwin0 : windowMap (nodePoly dom (T ∩ T')) (T ∩ T').card
      (m + 1 - ((T ∩ T').card - k))
      (fun i : Fin (m + 1 - ((T ∩ T').card - k)) => Cq.coeff (i : ℕ)) = 0 := by
    funext i
    show (nodePoly dom (T ∩ T') * genPoly _).coeff ((T ∩ T').card + (i : ℕ)) = 0
    rw [hCvec, ← hCq]
    have hwini := hwin i
    rw [survUpper_pos hdeep hshallow i] at hwini
    rw [Polynomial.coeff_sub]
    rw [show (B : F[X]).coeff ((T ∩ T').card + (i : ℕ)) = 0 from hwini]
    rw [show (A : F[X]).coeff ((T ∩ T').card + (i : ℕ)) = 0 from
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hAdeg
        (by exact_mod_cast (by omega : k + 1 ≤ (T ∩ T').card + (i : ℕ))))]
    ring
  have hCq0 : Cq = 0 := by
    have := windowMap_injective (e := m + 1 - ((T ∩ T').card - k))
      (nodePoly_monic dom (T ∩ T'))
      (nodePoly_natDegree dom (T ∩ T'))
      (a₁ := fun i : Fin (m + 1 - ((T ∩ T').card - k)) => Cq.coeff (i : ℕ)) (a₂ := 0)
      (by rw [hwin0, map_zero])
    rw [← hCvec, this]
    show genPoly (fun _ : Fin (m + 1 - ((T ∩ T').card - k)) => (0 : F)) = 0
    rw [genPoly]
    refine Finset.sum_eq_zero fun j _ => ?_
    show C (0 : F) * X ^ (j : ℕ) = 0
    rw [map_zero, zero_mul]
  -- so B = A, degree ≤ k, all band coefficients vanish
  have hBA' : B = A := by
    have h := hCq
    rw [hCq0, mul_zero] at h
    exact sub_eq_zero.mp h
  intro j
  show B.coeff (k + 1 + (j : ℕ)) = 0
  rw [hBA']
  exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hAdeg
    (by exact_mod_cast (by omega : k + 1 ≤ k + 1 + (j : ℕ))))

/-! ## The `surjective` field -/

open Classical in
theorem upper_window_surjective (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) (hshallow : (T ∩ T').card ≤ k + m)
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M)
    (t : (Fin m ⊕ Fin (m + 1 - ((T ∩ T').card - k))) → F) :
    ∃ c : Fin M → F,
      (∀ j : Fin m,
        (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) = t (Sum.inl j)) ∧
      (∀ j : Fin (m + 1 - ((T ∩ T').card - k)),
        (coreInterp dom T' (genPoly c)).coeff
          (k + 1 + ((survUpper hdeep hshallow j : Fin m) : ℕ)) = t (Sum.inr j)) := by
  classical
  have hinj : ∀ s : Finset (Fin n), Set.InjOn (⇑dom) s :=
    fun s x _ y _ h => dom.injective h
  -- the prescribed interpolant for T
  set p : F[X] := ∑ j : Fin m, C (t (Sum.inl j)) * X ^ (k + 1 + (j : ℕ)) with hp
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
      = ∑ j : Fin m, if k + 1 + (j : ℕ) = d then t (Sum.inl j) else 0 := by
    intro d
    rw [hp, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_ne d (k + 1 + (j : ℕ)) with h | h
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]
  have hpband : ∀ j : Fin m, p.coeff (k + 1 + (j : ℕ)) = t (Sum.inl j) := by
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
  -- the window correction for T'
  obtain ⟨cC, hcC⟩ := windowMap_surjective (e := m + 1 - ((T ∩ T').card - k))
    (nodePoly_monic dom (T ∩ T'))
    (nodePoly_natDegree dom (T ∩ T'))
    (fun i : Fin (m + 1 - ((T ∩ T').card - k)) =>
      t (Sum.inr i) - p.coeff ((T ∩ T').card + (i : ℕ)))
  set p' : F[X] := p + nodePoly dom (T ∩ T') * genPoly cC with hp'
  have hPCdeg : (nodePoly dom (T ∩ T') * genPoly cC).degree
      < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rcases eq_or_ne (genPoly cC) 0 with h0 | h0
    · rw [h0, mul_zero, Polynomial.degree_zero]
      exact_mod_cast WithBot.bot_lt_coe _
    have hnd : (nodePoly dom (T ∩ T') * genPoly cC).natDegree < k + m + 1 := by
      rw [Polynomial.natDegree_mul (Polynomial.Monic.ne_zero
        (nodePoly_monic dom (T ∩ T'))) h0, nodePoly_natDegree]
      have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr
        (genPoly_degree_lt (M := m + 1 - ((T ∩ T').card - k)) cC)
      omega
    have hne : nodePoly dom (T ∩ T') * genPoly cC ≠ 0 :=
      mul_ne_zero (Polynomial.Monic.ne_zero (nodePoly_monic dom (T ∩ T'))) h0
    exact (Polynomial.natDegree_lt_iff_degree_lt hne).mp hnd
  have hp'deg : p'.degree < ((k + m + 1 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hpdeg hPCdeg)
  -- p' hits the upper-window targets
  have hp'win : ∀ i : Fin (m + 1 - ((T ∩ T').card - k)),
      p'.coeff ((T ∩ T').card + (i : ℕ)) = t (Sum.inr i) := by
    intro i
    have hw := congrFun hcC i
    show p.coeff ((T ∩ T').card + (i : ℕ))
        + (nodePoly dom (T ∩ T') * genPoly cC).coeff ((T ∩ T').card + (i : ℕ)) = _
    rw [show (nodePoly dom (T ∩ T') * genPoly cC).coeff ((T ∩ T').card + (i : ℕ))
        = t (Sum.inr i) - p.coeff ((T ∩ T').card + (i : ℕ)) from hw]
    ring
  -- p' agrees with p on the overlap nodes
  have hagree : ∀ i ∈ T ∩ T', p.eval (dom i) = p'.eval (dom i) := by
    intro i hi
    rw [hp', Polynomial.eval_add, Polynomial.eval_mul, nodePoly_eval_node dom hi,
      zero_mul, add_zero]
  -- the lift through the union
  set vals : Fin n → F := fun i => if i ∈ T then p.eval (dom i)
    else p'.eval (dom i) with hvals
  set Q : F[X] := Lagrange.interpolate (T ∪ T') (⇑dom) vals with hQdef
  have hQdeg : Q.degree < (M : WithBot ℕ) := by
    have hcard : (T ∪ T').card ≤ M := by
      calc (T ∪ T').card ≤ T.card + T'.card := Finset.card_union_le _ _
        _ = 2 * (k + m + 1) := by omega
        _ ≤ M := hM
    refine lt_of_lt_of_le ?_
      (by exact_mod_cast hcard : ((T ∪ T').card : WithBot ℕ) ≤ (M : WithBot ℕ))
    exact_mod_cast Lagrange.degree_interpolate_lt _ (hinj (T ∪ T'))
  set c : Fin M → F := fun j => Q.coeff (j : ℕ) with hc
  have hgen : genPoly c = Q := genPoly_coeff_eq hQdeg
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
  refine ⟨c, fun j => ?_, fun j => ?_⟩
  · rw [hgen, hIT]
    exact hpband j
  · rw [hgen, hIT', survUpper_pos hdeep hshallow j]
    exact hp'win j

/-! ## The discharge and the unconditional rank -/

open Classical in
/-- **THE NAMED RESIDUAL, DISCHARGED.**  The canonical upper-window selection
witnesses `DeepPairValIndependent` at every deep pair — the finite rank-nullity
computation of `DegeneracyLocusRank.lean`, performed uniformly. -/
theorem deepPairValIndependent_upper (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) (hshallow : (T ∩ T').card ≤ k + m)
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    DeepPairValIndependent dom k m T T' M (survUpper hdeep hshallow) where
  surjective := upper_window_surjective dom hT hT' hdeep hshallow hM
  implies_full := fun c hcohT hwin =>
    upper_kernel_implies_full dom hT hT' hdeep hshallow c hcohT hwin

open Classical in
/-- **THE UNCONDITIONAL DEGENERACY-LOCUS RANK.**  On the deep-overlap stratum
`k+1 ≤ |T∩T'| ≤ k+m`, with no independence hypothesis: the pair-coherence kernel
satisfies `#kernel · q^(2m+1 − (|T∩T'|−k)) = q^M` — the probe-measured rank law
`rank = 2m+1 − (j−k)` is a theorem on every stratum, completing the route-2 rank
stratification. -/
theorem deep_pair_rank_eq (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hdeep : k + 1 ≤ (T ∩ T').card) (hshallow : (T ∩ T').card ≤ k + m)
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (2 * m + 1 - ((T ∩ T').card - k)) = (Fintype.card F) ^ M :=
  deep_pair_rank_eq_of_indep dom hT hT' hdeep hshallow
    (deepPairValIndependent_upper dom hT hT' hdeep hshallow hM)

end ProximityGap.DeepPairIndependence

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DeepPairIndependence.windowMap_injective
#print axioms ProximityGap.DeepPairIndependence.windowMap_surjective
#print axioms ProximityGap.DeepPairIndependence.nodePoly_dvd_of_eval_eq_zero
#print axioms ProximityGap.DeepPairIndependence.upper_kernel_implies_full
#print axioms ProximityGap.DeepPairIndependence.upper_window_surjective
#print axioms ProximityGap.DeepPairIndependence.deepPairValIndependent_upper
#print axioms ProximityGap.DeepPairIndependence.deep_pair_rank_eq
