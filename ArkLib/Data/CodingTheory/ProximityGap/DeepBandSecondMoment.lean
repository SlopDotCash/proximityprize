/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandPairRank

/-!
# The deep-band second moment (#389, route 2, brick 2)

The moment assembly over the generator space.  With the pair-coherence rank
law (`pair_coherence_kernel_card`, brick 1) controlling the small-overlap
strata and per-core surjectivity controlling the rest:

* `core_coherence_kernel_card` — per-core exact count: the `m` coherence
  conditions cut the generator space by exactly `q^m` (upgrades the in-tree
  `≥` to equality).
* `sum_N1_eq` — the first moment, exactly: `Σ_c #coh(c) = P · q^(M−m)`.
* `sum_N2_le` — the second moment of the value map, strata-partitioned:

    `Σ_c #{(T,T') ∈ coh(c)² : val T = val T'}
        ≤ P² · q^(M−(2m+1)) + (D + P) · q^(M−m)`,

  where `P = C(n,k+m+1)` and `D` counts the deep pairs (overlap `> k`).
* `value_count_quadratic` — per generator, the fiber decomposition:
  `2L·N₁(c) ≤ N₂(c) + #values(c) · L²` (the integer Cauchy–Schwarz step,
  from `2Lf − f² ≤ L²` fiberwise).
* `exists_generator_many_values` — the pigeonhole payoff: whenever the
  moments satisfy `2L·(P·q^(M−m)) ≥ Σ-second-moment-bound + V·q^M`, some
  generator's coherent cores take **at least `V/L²` distinct values**.
* `deep_band_badSet_card_of_moments` — the consumer: each distinct value is
  a certified bad scalar (`mcaEvent_of_coherent`), so at every band radius

    `∃ Q₀ : V ≤ #badSet(Q₀, x^k) · L²` —

  the deterministic form of the probe-measured deep-band saturation
  (median #values = q at `C(n,k+m+1) ≫ q^(m+1)`,
  `probe_pair_coherence_rank.py`).

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Per-core exact kernel -/

open Classical in
/-- **Per-core exact count**: the `m` coherence conditions cut the generator
space by exactly `q^m` (surjectivity: prescribe the interpolant's band
coefficients as an explicit monomial sum). -/
theorem core_coherence_kernel_card (dom : Fin n ↪ F) {k m : ℕ}
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) {M : ℕ}
    (hM : k + m + 1 ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c))).card
      * (Fintype.card F) ^ m = (Fintype.card F) ^ M := by
  classical
  set φ : Fin m → (Fin M → F) → F := fun j c =>
    (coreInterp dom T (genPoly c)).coeff (k + 1 + (j : ℕ)) with hφ
  have hsub : ∀ j x y, φ j (x - y) = φ j x - φ j y := by
    intro j x y
    show (coreInterp dom T (genPoly (x - y))).coeff _ = _
    rw [coreInterp_genPoly_sub, Polynomial.coeff_sub]
  have hsurj : ∀ t : Fin m → F, ∃ c, ∀ j, φ j c = t j := by
    intro t
    set p : F[X] := ∑ j : Fin m, C (t j) * X ^ (k + 1 + (j : ℕ)) with hp
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
    have hpM : p.degree < (M : WithBot ℕ) :=
      lt_of_lt_of_le hpdeg (by exact_mod_cast hM)
    refine ⟨fun j => p.coeff (j : ℕ), fun j => ?_⟩
    show (coreInterp dom T (genPoly _)).coeff _ = t j
    rw [genPoly_coeff_eq hpM]
    have hIT : coreInterp dom T p = p := by
      rw [coreInterp]
      exact (Lagrange.eq_interpolate (fun x _ y _ h => dom.injective h)
        (by rw [hT]; exact hpdeg)).symm
    rw [hIT, hp, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro j' _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by
          intro h
          exact hne (Fin.ext (by omega))), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h := card_kernel_eq_of_surjective φ hsub hsurj
  rw [Fintype.card_fin] at h
  rw [← h]
  congr 2
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

/-! ## The moment sums -/

open Classical in
/-- The first moment, exactly: summed over all generators, the coherent-core
count is `P · q^(M−m)` in product form. -/
theorem sum_N1_eq (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : k + m + 1 ≤ M) :
    (∑ c : Fin M → F,
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c))).card)
      * (Fintype.card F) ^ m
      = ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
        * (Fintype.card F) ^ M := by
  classical
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  have hswap : ∑ c : Fin M → F, (Pm.filter
        (fun T => IsCoherent dom k m T (genPoly c))).card
      = ∑ T ∈ Pm, (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (genPoly c))).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun T hT => core_coherence_kernel_card dom
    ((Finset.mem_powersetCard.mp hT).2) hM]
  rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- **The second moment of the value map, strata-partitioned.**  `D` is the
deep-pair count (distinct cores with overlap `> k`); small-overlap distinct
pairs are bounded by all `P²` pairs at the exact `q^(M−(2m+1))` fiber, deep
pairs and the diagonal at the `q^(M−m)` per-core fiber. -/
theorem sum_N2_le (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) :
    (∑ c : Fin M → F,
      ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c)))).filter
        (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
          = (coreInterp dom p.2 (genPoly c)).coeff k)).card)
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m) := by
  classical
  set q := Fintype.card F with hq
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set P : ℕ := Pm.card with hP
  have hqpos : 0 < q := Fintype.card_pos
  set pred : (Finset (Fin n) × Finset (Fin n)) → (Fin M → F) → Prop :=
    fun p c => IsCoherent dom k m p.1 (genPoly c)
      ∧ IsCoherent dom k m p.2 (genPoly c)
      ∧ (coreInterp dom p.1 (genPoly c)).coeff k
        = (coreInterp dom p.2 (genPoly c)).coeff k with hpred
  -- rewrite the inner card over the FIXED product Pm ×ˢ Pm
  have hinner : ∀ c : Fin M → F,
      (((Pm.filter (fun T => IsCoherent dom k m T (genPoly c))) ×ˢ
        (Pm.filter (fun T => IsCoherent dom k m T (genPoly c)))).filter
        (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
          = (coreInterp dom p.2 (genPoly c)).coeff k)).card
      = ((Pm ×ˢ Pm).filter (fun p => pred p c)).card := by
    intro c
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, hpred]
    tauto
  rw [Finset.sum_congr rfl fun c _ => hinner c]
  -- swap the sums
  have hswap : ∑ c : Fin M → F, ((Pm ×ˢ Pm).filter (fun p => pred p c)).card
      = ∑ p ∈ Pm ×ˢ Pm,
          (Finset.univ.filter (fun c : Fin M → F => pred p c)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  -- the three strata
  set smallS := (Pm ×ˢ Pm).filter (fun p => p.1 ≠ p.2 ∧ (p.1 ∩ p.2).card ≤ k)
    with hsmallS
  set deepS := (Pm ×ˢ Pm).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)
    with hdeepS
  set diagS := (Pm ×ˢ Pm).filter (fun p => p.1 = p.2) with hdiagS
  have hsubset : Pm ×ˢ Pm ⊆ (smallS ∪ deepS) ∪ diagS := by
    intro p hp
    simp only [hsmallS, hdeepS, hdiagS, Finset.mem_union, Finset.mem_filter]
    by_cases he : p.1 = p.2
    · exact Or.inr ⟨hp, he⟩
    · by_cases hov : (p.1 ∩ p.2).card ≤ k
      · exact Or.inl (Or.inl ⟨hp, he, hov⟩)
      · exact Or.inl (Or.inr ⟨hp, he, not_le.mp hov⟩)
  -- per-stratum fiber values/bounds
  have hcoh_fiber : ∀ T ∈ Pm, (Finset.univ.filter
      (fun c : Fin M → F => IsCoherent dom k m T (genPoly c))).card
      = q ^ (M - m) := by
    intro T hT
    have h := core_coherence_kernel_card dom
      ((Finset.mem_powersetCard.mp hT).2) (M := M) (by omega)
    rw [← hq] at h
    have hqpow : q ^ M = q ^ (M - m) * q ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [hqpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hqpos _) h
  have hcrude : ∀ p ∈ Pm ×ˢ Pm,
      (Finset.univ.filter (fun c : Fin M → F => pred p c)).card ≤ q ^ (M - m) := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, -⟩
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (hcoh_fiber p.1 hp1))
    intro c hc
    obtain ⟨-, h1, -⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
  have hsmall_fiber : ∀ p ∈ smallS,
      (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
      = q ^ (M - (2 * m + 1)) := by
    intro p hp
    obtain ⟨hpmem, -, hover⟩ := Finset.mem_filter.mp hp
    rcases Finset.mem_product.mp hpmem with ⟨hp1, hp2⟩
    have h := pair_coherence_kernel_card dom
      ((Finset.mem_powersetCard.mp hp1).2) ((Finset.mem_powersetCard.mp hp2).2)
      hover hM
    rw [← hq] at h
    have hqpow : q ^ M = q ^ (M - (2 * m + 1)) * q ^ (2 * m + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hqpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hqpos _) h
  -- sum over each stratum
  have hsum_small : ∑ p ∈ smallS,
      (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
      ≤ P ^ 2 * q ^ (M - (2 * m + 1)) := by
    calc ∑ p ∈ smallS, (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
        = ∑ p ∈ smallS, q ^ (M - (2 * m + 1)) :=
          Finset.sum_congr rfl hsmall_fiber
      _ = smallS.card * q ^ (M - (2 * m + 1)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ P ^ 2 * q ^ (M - (2 * m + 1)) := by
          refine Nat.mul_le_mul_right _ ?_
          calc smallS.card ≤ (Pm ×ˢ Pm).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ = P ^ 2 := by rw [Finset.card_product, sq]
  have hsum_deep : ∑ p ∈ deepS,
      (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
      ≤ deepS.card * q ^ (M - m) := by
    calc ∑ p ∈ deepS, (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
        ≤ ∑ p ∈ deepS, q ^ (M - m) := Finset.sum_le_sum fun p hp =>
          hcrude p (Finset.filter_subset _ _ hp)
      _ = deepS.card * q ^ (M - m) := by rw [Finset.sum_const, smul_eq_mul]
  have hdiag_card : diagS.card ≤ P := by
    refine le_trans (Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_) le_rfl
    · intro p hp
      exact (Finset.mem_product.mp (Finset.filter_subset _ _ hp)).1
    · intro p hp p' hp' he
      have he' : p.1 = p'.1 := he
      have h1 := (Finset.mem_filter.mp hp).2
      have h2 := (Finset.mem_filter.mp hp').2
      have h22 : p.2 = p'.2 := by rw [← h1, ← h2, he']
      exact Prod.ext_iff.mpr ⟨he', h22⟩
  have hsum_diag : ∑ p ∈ diagS,
      (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
      ≤ P * q ^ (M - m) := by
    calc ∑ p ∈ diagS, (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
        ≤ ∑ p ∈ diagS, q ^ (M - m) := Finset.sum_le_sum fun p hp =>
          hcrude p (Finset.filter_subset _ _ hp)
      _ = diagS.card * q ^ (M - m) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ P * q ^ (M - m) := Nat.mul_le_mul_right _ hdiag_card
  -- assemble: the strata partition the product exactly
  have hdisj1 : Disjoint smallS deepS := by
    rw [Finset.disjoint_left]
    intro p hp hpd
    exact absurd (Finset.mem_filter.mp hpd).2.2
      (not_lt.mpr (Finset.mem_filter.mp hp).2.2)
  have hdisj2 : Disjoint (smallS ∪ deepS) diagS := by
    rw [Finset.disjoint_left]
    intro p hp hpd
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp hpd).2
    · exact (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp hpd).2
  have hpartition : Pm ×ˢ Pm = (smallS ∪ deepS) ∪ diagS := by
    refine Finset.Subset.antisymm hsubset ?_
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_union.mp h with h' | h'
      · exact Finset.filter_subset _ _ h'
      · exact Finset.filter_subset _ _ h'
    · exact Finset.filter_subset _ _ h
  calc ∑ p ∈ Pm ×ˢ Pm,
        (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
      = ((∑ p ∈ smallS,
          (Finset.univ.filter (fun c : Fin M → F => pred p c)).card)
        + ∑ p ∈ deepS,
          (Finset.univ.filter (fun c : Fin M → F => pred p c)).card)
        + ∑ p ∈ diagS,
          (Finset.univ.filter (fun c : Fin M → F => pred p c)).card := by
        rw [hpartition, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
    _ ≤ (P ^ 2 * q ^ (M - (2 * m + 1)) + deepS.card * q ^ (M - m))
        + P * q ^ (M - m) :=
        Nat.add_le_add (Nat.add_le_add hsum_small hsum_deep) hsum_diag
    _ = P ^ 2 * q ^ (M - (2 * m + 1)) + (deepS.card + P) * q ^ (M - m) := by
        ring

/-! ## The per-generator quadratic and the pigeonhole payoff -/

open Classical in
/-- **The integer Cauchy–Schwarz step**, per generator: with `N₁` the coherent
count, `N₂` the equal-value pair count, and `#values` the distinct-value count,
`2L·N₁ ≤ N₂ + #values·L²` (fiberwise `2Lf ≤ f² + L²`). -/
theorem value_count_quadratic (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (c : Fin M → F) (L : ℕ) :
    2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => IsCoherent dom k m T (genPoly c))).card
      ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c)))).filter
        (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
          = (coreInterp dom p.2 (genPoly c)).coeff k)).card
      + ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c))).image
          (fun T => (coreInterp dom T (genPoly c)).coeff k)).card * L ^ 2 := by
  classical
  set coh := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
    (fun T => IsCoherent dom k m T (genPoly c)) with hcoh
  set val : Finset (Fin n) → F :=
    fun T => (coreInterp dom T (genPoly c)).coeff k with hval
  set vals := coh.image val with hvals
  -- fiber decomposition of N₁
  have hN1 : coh.card = ∑ γ ∈ vals, (coh.filter (fun T => val T = γ)).card :=
    Finset.card_eq_sum_card_fiberwise fun T hT =>
      Finset.mem_image.mpr ⟨T, hT, rfl⟩
  -- fiber decomposition of N₂
  have hN2 : ((coh ×ˢ coh).filter (fun p => val p.1 = val p.2)).card
      = ∑ γ ∈ vals, ((coh.filter (fun T => val T = γ)).card) ^ 2 := by
    have hfib : ((coh ×ˢ coh).filter (fun p => val p.1 = val p.2)).card
        = ∑ γ ∈ vals, (((coh ×ˢ coh).filter (fun p => val p.1 = val p.2)).filter
            (fun p => val p.1 = γ)).card := by
      refine Finset.card_eq_sum_card_fiberwise fun p hp => ?_
      obtain ⟨hpm, -⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_image.mpr ⟨p.1, (Finset.mem_product.mp hpm).1, rfl⟩
    rw [hfib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hset : ((coh ×ˢ coh).filter (fun p => val p.1 = val p.2)).filter
        (fun p => val p.1 = γ)
        = (coh.filter (fun T => val T = γ)) ×ˢ (coh.filter (fun T => val T = γ)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, heq⟩, hγ⟩
        exact ⟨⟨h1, hγ⟩, h2, by rw [← heq, hγ]⟩
      · rintro ⟨⟨h1, hγ1⟩, h2, hγ2⟩
        exact ⟨⟨⟨h1, h2⟩, by rw [hγ1, hγ2]⟩, hγ1⟩
    rw [hset, Finset.card_product, sq]
  -- fiberwise 2Lf ≤ f² + L²
  have hquad : ∀ f : ℕ, 2 * L * f ≤ f ^ 2 + L ^ 2 := by
    intro f
    have h := two_mul_le_add_sq (f : ℤ) (L : ℤ)
    have : (2 * L * f : ℤ) ≤ (f : ℤ) ^ 2 + (L : ℤ) ^ 2 := by linarith
    exact_mod_cast this
  calc 2 * L * coh.card
      = ∑ γ ∈ vals, 2 * L * (coh.filter (fun T => val T = γ)).card := by
        rw [hN1, Finset.mul_sum]
    _ ≤ ∑ γ ∈ vals, ((coh.filter (fun T => val T = γ)).card ^ 2 + L ^ 2) :=
        Finset.sum_le_sum fun γ _ => hquad _
    _ = (∑ γ ∈ vals, (coh.filter (fun T => val T = γ)).card ^ 2)
        + vals.card * L ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    _ = ((coh ×ˢ coh).filter (fun p => val p.1 = val p.2)).card
        + vals.card * L ^ 2 := by rw [hN2]

open Classical in
/-- **The pigeonhole payoff**: if the moment budget clears, some generator's
coherent cores take many distinct values — `V ≤ #values(c) · L²`. -/
theorem exists_generator_many_values (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hbudget : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T (genPoly c))).card)) :
    ∃ c : Fin M → F,
      V ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c))).image
          (fun T => (coreInterp dom T (genPoly c)).coeff k)).card * L ^ 2 := by
  classical
  -- some generator has 2L·N₁ ≥ N₂ + V
  have hex : ∃ c : Fin M → F,
      ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c)))).filter
        (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
          = (coreInterp dom p.2 (genPoly c)).coeff k)).card + V
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c))).card := by
    by_contra hcon
    push_neg at hcon
    have hstrict : ∀ c : Fin M → F,
        2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c))).card + 1
        ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T (genPoly c)))).filter
          (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
            = (coreInterp dom p.2 (genPoly c)).coeff k)).card + V := by
      intro c
      exact Nat.succ_le_of_lt (hcon c)
    have hsum := Finset.sum_le_sum
      (fun c (_ : c ∈ (Finset.univ : Finset (Fin M → F))) => hstrict c)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, smul_eq_mul, mul_one, smul_eq_mul] at hsum
    -- hsum : 2L·S₁ + q^M ≤ S₂ + q^M·V
    have hS2 := sum_N2_le dom k m hM
    have hchain : 2 * L * (∑ c : Fin M → F,
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
          (fun T => IsCoherent dom k m T (genPoly c))).card)
        + (Fintype.card F) ^ M
        ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T (genPoly c))).card) := by
      calc 2 * L * (∑ c : Fin M → F, _) + (Fintype.card F) ^ M
          ≤ (∑ c : Fin M → F,
              ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
                  (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
                (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
                  (fun T => IsCoherent dom k m T (genPoly c)))).filter
                (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
                  = (coreInterp dom p.2 (genPoly c)).coeff k)).card)
            + (Fintype.card F) ^ M * V := hsum
        _ ≤ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
              * (Fintype.card F) ^ (M - (2 * m + 1))
            + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
                (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
                (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
              + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
              * (Fintype.card F) ^ (M - m))
            + (Fintype.card F) ^ M * V :=
            Nat.add_le_add_right hS2 _
        _ = ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
              * (Fintype.card F) ^ (M - (2 * m + 1))
            + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
                (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
                (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
              + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
              * (Fintype.card F) ^ (M - m)
            + V * (Fintype.card F) ^ M := by ring
        _ ≤ _ := hbudget
    have hqMpos : 0 < (Fintype.card F) ^ M := pow_pos Fintype.card_pos _
    set A := 2 * L * (∑ c : Fin M → F,
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => IsCoherent dom k m T (genPoly c))).card) with hA
    set Z := (Fintype.card F) ^ M with hZ
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  have hquad := value_count_quadratic dom k m c L
  -- N₂ + V ≤ 2L·N₁ ≤ N₂ + #vals·L² ⟹ V ≤ #vals·L²
  have hfinal := le_trans hc hquad
  exact Nat.le_of_add_le_add_left hfinal

/-! ## The consumer: deep-band failure from the moments -/

open Classical in
/-- **THE SECOND-MOMENT DEEP-BAND FAILURE.**  At every band radius
(`(1−δ)n ≤ k+m+1`), if the moment budget `hbudget` clears for some `(L, V)`,
then some stack of the generated family carries at least `V/L²` distinct bad
scalars:

  `∃ Q₀ : V ≤ #badSet(Q₀, x^k) · L²`.

Each distinct value of the coherent-core value map is a certified bad scalar
(`mcaEvent_of_coherent`); the deterministic form of the probe-measured
deep-band saturation. -/
theorem deep_band_badSet_card_of_moments (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hbudget : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T (genPoly c))).card)) :
    ∃ Q₀ : F[X],
      V ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * L ^ 2 := by
  classical
  obtain ⟨c, hc⟩ := exists_generator_many_values dom k m hM hbudget
  refine ⟨genPoly c, ?_⟩
  refine le_trans hc (Nat.mul_le_mul_right _ ?_)
  -- the negated value map injects the value set into the bad set
  set coh := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
    (fun T => IsCoherent dom k m T (genPoly c)) with hcoh
  set vals := coh.image (fun T => (coreInterp dom T (genPoly c)).coeff k)
    with hvals
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
    (fun i => (genPoly c).eval (dom i)) (fun i => (dom i) ^ k) γ) with hbad
  refine Finset.card_le_card_of_injOn (fun v => -v) ?_ ?_
  · intro v hv
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hTm, hTcoh⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact mcaEvent_of_coherent dom hk hhi
      ((Finset.mem_powersetCard.mp hTm).2) hTcoh
  · intro a _ b _ hab
    exact neg_injective hab

/-! ## The deep-pair count and the numeric budget -/

open Classical in
/-- **The deep-pair count bound**: every deep pair `(T,T')` (overlap `> k`)
has `T'` containing some `(k+1)`-subset of `T`, so
`D ≤ P · C(k+m+1, k+1) · C(n−(k+1), m)`. -/
theorem deepPairs_card_le (k m : ℕ) :
    (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
        (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card)
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
        * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) := by
  classical
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set deepS := (Pm ×ˢ Pm).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)
    with hdeepS
  -- supersets of a fixed (k+1)-set among the (k+m+1)-sets number ≤ C(n−(k+1), m)
  have hsup : ∀ S : Finset (Fin n), S.card = k + 1 →
      (Pm.filter (fun T' => S ⊆ T')).card ≤ (n - (k + 1)).choose m := by
    intro S hScard
    have hle : (Pm.filter (fun T' => S ⊆ T')).card
        ≤ ((Finset.univ \ S).powersetCard m).card := by
      refine Finset.card_le_card_of_injOn (fun T' => T' \ S) ?_ ?_
      · intro T' hT'
        obtain ⟨hT'm, hsub⟩ := Finset.mem_filter.mp hT'
        refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
        · intro x hx
          rw [Finset.mem_sdiff] at hx ⊢
          exact ⟨Finset.mem_univ _, hx.2⟩
        · rw [Finset.card_sdiff_of_subset hsub,
            (Finset.mem_powersetCard.mp hT'm).2, hScard]
          omega
      · intro a ha b hb he
        rw [Finset.mem_coe] at ha hb
        have he' : a \ S = b \ S := he
        have hsa : S ⊆ a := (Finset.mem_filter.mp ha).2
        have hsb : S ⊆ b := (Finset.mem_filter.mp hb).2
        calc a = (a \ S) ∪ S := (Finset.sdiff_union_of_subset hsa).symm
          _ = (b \ S) ∪ S := by rw [he']
          _ = b := Finset.sdiff_union_of_subset hsb
    refine le_trans hle (le_of_eq ?_)
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset
      (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hScard]
  -- fiber over the first component
  have hfib : deepS.card = ∑ T ∈ Pm, (deepS.filter (fun p => p.1 = T)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun p hp => ?_
    exact (Finset.mem_product.mp (Finset.filter_subset _ _ hp)).1
  rw [hfib]
  refine le_trans (Finset.sum_le_sum (fun T hT => ?_))
    (by rw [Finset.sum_const, smul_eq_mul])
  have hTcard : T.card = k + m + 1 := (Finset.mem_powersetCard.mp hT).2
  -- per T: the partner map is injective on the fiber
  have hpartner : (deepS.filter (fun p => p.1 = T)).card
      = ((deepS.filter (fun p => p.1 = T)).image Prod.snd).card := by
    rw [eq_comm]
    refine Finset.card_image_of_injOn ?_
    intro p hp p' hp' he
    rw [Finset.mem_coe] at hp hp'
    have h1 : p.1 = T := (Finset.mem_filter.mp hp).2
    have h1' : p'.1 = T := (Finset.mem_filter.mp hp').2
    exact Prod.ext_iff.mpr ⟨by rw [h1, h1'], he⟩
  rw [hpartner]
  -- the partners sit inside the biUnion over (k+1)-subsets of T
  have hcover : (deepS.filter (fun p => p.1 = T)).image Prod.snd
      ⊆ (T.powersetCard (k + 1)).biUnion
        (fun S => Pm.filter (fun T' => S ⊆ T')) := by
    intro T' hT'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hT'
    obtain ⟨hpd, hp1⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpm, -, hover⟩ := Finset.mem_filter.mp hpd
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hover
    refine Finset.mem_biUnion.mpr ⟨S, ?_, ?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, hScard⟩
      refine subset_trans hSsub ?_
      rw [← hp1]
      exact Finset.inter_subset_left
    · refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hpm).2, ?_⟩
      exact subset_trans hSsub Finset.inter_subset_right
  refine le_trans (Finset.card_le_card hcover) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  have hcard1 : (T.powersetCard (k + 1)).card = (k + m + 1).choose (k + 1) := by
    rw [Finset.card_powersetCard, hTcard]
  calc ∑ S ∈ T.powersetCard (k + 1), (Pm.filter (fun T' => S ⊆ T')).card
      ≤ ∑ S ∈ T.powersetCard (k + 1), (n - (k + 1)).choose m :=
        Finset.sum_le_sum fun S hS =>
          hsup S (Finset.mem_powersetCard.mp hS).2
    _ = (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m := by
        rw [Finset.sum_const, smul_eq_mul, hcard1]

open Classical in
/-- **The budget in pure numerics**: substituting the exact first moment
(`sum_N1_eq`), the moment budget of `deep_band_badSet_card_of_moments` follows
from the closed-form inequality

  `P²·q^(M−(2m+1)) + (D + P)·q^(M−m) + V·q^M ≤ 2L·P·q^(M−m)`. -/
theorem budget_of_numeric (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hnum : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (Fintype.card F) ^ (M - m))) :
    ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T (genPoly c))).card) := by
  classical
  refine le_trans hnum (Nat.mul_le_mul_left _ ?_)
  -- S₁ = P·q^(M−m) exactly, from sum_N1_eq by cancellation
  have h := sum_N1_eq dom k m (M := M) (by omega)
  have hqm : (Fintype.card F) ^ M
      = (Fintype.card F) ^ (M - m) * (Fintype.card F) ^ m := by
    rw [← pow_add]
    congr 1
    omega
  rw [hqm, ← mul_assoc] at h
  have := Nat.eq_of_mul_eq_mul_right (pow_pos Fintype.card_pos m) h
  omega

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.core_coherence_kernel_card
#print axioms ProximityGap.PairRank.sum_N1_eq
#print axioms ProximityGap.PairRank.sum_N2_le
#print axioms ProximityGap.PairRank.value_count_quadratic
#print axioms ProximityGap.PairRank.exists_generator_many_values
#print axioms ProximityGap.PairRank.deep_band_badSet_card_of_moments
#print axioms ProximityGap.PairRank.deepPairs_card_le
#print axioms ProximityGap.PairRank.budget_of_numeric
