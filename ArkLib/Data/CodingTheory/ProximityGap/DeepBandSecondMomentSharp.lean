/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.DeepPairIndependence

/-!
# The sharp deep-strata second moment: the deep term drops a full factor `q` (#389)

`sum_N2_le` (`DeepBandSecondMoment.lean`) bounds the deep-stratum pairs at the crude
per-core fiber `q^(M−m)` — the registered follow-up (ii) of the route-2 capstone.  With
the degeneracy-locus rank now **unconditional** (`DeepPairIndependence.deep_pair_rank_eq`:
every deep pair's fiber is exactly `q^(M−(2m+1−(j−k)))`, and `2m+1−(j−k) ≥ m+1` on the
whole deep stratum `j ≤ k+m`), the deep term improves by a full factor of `q`:

> **`sum_N2_le_sharp`** — `Σ_c N₂(c) ≤ P²·q^(M−(2m+1)) + D·q^(M−(m+1)) + P·q^(M−m)`

(`P = C(n,k+m+1)`, `D` the deep-pair count, diagonal at the per-core fiber).  Versus
`sum_N2_le`'s `(D+P)·q^(M−m)`, the deep contribution `D·q^(M−m)` becomes `D·q^(M−(m+1))`
— wherever the deep term binds in the closed-form budget (`deepPairs_card_le` makes it
`P·C'·q^(M−m)` with `C' = C(k+m+1,k+1)·C(n−(k+1),m)`), the effective constant improves
from `C'` toward `C'/q`, sharpening the `Λ ≈ max(P/q^(m+1), C')` floor of
`deep_band_failure_closed_form` at every parameter point where `C' ≤ q·P/q^(m+1)`.

The fiber is **exact** per pair (`deep_fiber_eq`), so this is the end of the line for the
deep term at the pair level: any further gain must come from the pair counts themselves.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

set_option linter.style.longLine false

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The exact deep fiber.**  For a deep pair (distinct cores, overlap `> k`), the
pair-coherence fiber is exactly `q^(M−(2m+1−(j−k)))` — the unconditional rank theorem
in fiber form. -/
theorem deep_fiber_eq (dom : Fin n ↪ F) {k m : ℕ} {T T' : Finset (Fin n)}
    (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1) (hne : T ≠ T')
    (hdeep : k < (T ∩ T').card) {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      = (Fintype.card F) ^ (M - (2 * m + 1 - ((T ∩ T').card - k))) := by
  classical
  have hqpos : 0 < Fintype.card F := Fintype.card_pos
  -- distinct cores of equal size have overlap ≤ k+m
  have hov_le : (T ∩ T').card ≤ k + m := by
    by_contra h
    push_neg at h
    have hle : (T ∩ T').card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
    have hinter : T ∩ T' = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub : T ⊆ T' := by
      intro x hx
      have : x ∈ T ∩ T' := hinter.symm ▸ hx
      exact (Finset.mem_inter.mp this).2
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  have h := ProximityGap.DeepPairIndependence.deep_pair_rank_eq dom hT hT'
    (by omega : k + 1 ≤ (T ∩ T').card) hov_le hM
  have hsM : 2 * m + 1 - ((T ∩ T').card - k) ≤ M := by omega
  have hqpow : (Fintype.card F) ^ M
      = (Fintype.card F) ^ (M - (2 * m + 1 - ((T ∩ T').card - k)))
        * (Fintype.card F) ^ (2 * m + 1 - ((T ∩ T').card - k)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hqpow] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hqpos _) h

open Classical in
/-- The sharp deep-fiber bound: `≤ q^(M−(m+1))` on the entire deep stratum
(`2m+1−(j−k) ≥ m+1` since `j ≤ k+m`). -/
theorem deep_fiber_le (dom : Fin n ↪ F) {k m : ℕ} {T T' : Finset (Fin n)}
    (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1) (hne : T ≠ T')
    (hdeep : k < (T ∩ T').card) {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      ≤ (Fintype.card F) ^ (M - (m + 1)) := by
  rw [deep_fiber_eq dom hT hT' hne hdeep hM]
  have hov_le : (T ∩ T').card ≤ k + m := by
    by_contra h
    push_neg at h
    have hle : (T ∩ T').card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
    have hinter : T ∩ T' = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub : T ⊆ T' := by
      intro x hx
      have : x ∈ T ∩ T' := hinter.symm ▸ hx
      exact (Finset.mem_inter.mp this).2
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  exact Nat.pow_le_pow_right Fintype.card_pos (by omega)

open Classical in
/-- **THE SHARP SECOND MOMENT.**  Identical to `sum_N2_le` except the deep stratum is
counted at the exact rank fiber: the deep term carries `q^(M−(m+1))`, a full factor `q`
below the crude bound. -/
theorem sum_N2_le_sharp (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
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
        + ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
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
  have hswap : ∑ c : Fin M → F, ((Pm ×ˢ Pm).filter (fun p => pred p c)).card
      = ∑ p ∈ Pm ×ˢ Pm,
          (Finset.univ.filter (fun c : Fin M → F => pred p c)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
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
  -- THE SHARP DEEP STRATUM: the exact rank fiber
  have hdeep_fiber : ∀ p ∈ deepS,
      (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
      ≤ q ^ (M - (m + 1)) := by
    intro p hp
    obtain ⟨hpmem, hne, hover⟩ := Finset.mem_filter.mp hp
    rcases Finset.mem_product.mp hpmem with ⟨hp1, hp2⟩
    have h := deep_fiber_le dom
      ((Finset.mem_powersetCard.mp hp1).2) ((Finset.mem_powersetCard.mp hp2).2)
      hne hover hM
    rw [← hq] at h
    exact h
  have hsum_deep : ∑ p ∈ deepS,
      (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
      ≤ deepS.card * q ^ (M - (m + 1)) := by
    calc ∑ p ∈ deepS, (Finset.univ.filter (fun c : Fin M → F => pred p c)).card
        ≤ ∑ p ∈ deepS, q ^ (M - (m + 1)) := Finset.sum_le_sum hdeep_fiber
      _ = deepS.card * q ^ (M - (m + 1)) := by rw [Finset.sum_const, smul_eq_mul]
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
    _ ≤ (P ^ 2 * q ^ (M - (2 * m + 1)) + deepS.card * q ^ (M - (m + 1)))
        + P * q ^ (M - m) :=
        Nat.add_le_add (Nat.add_le_add hsum_small hsum_deep) hsum_diag
    _ = P ^ 2 * q ^ (M - (2 * m + 1)) + deepS.card * q ^ (M - (m + 1))
        + P * q ^ (M - m) := by ring


/-! ## The sharp pigeonhole and the sharp consumer -/

open Classical in
/-- `exists_generator_many_values` with the SHARP moment budget: the deep term enters
at `q^(M−(m+1))`. -/
theorem exists_generator_many_values_sharp (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hbudget : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card)) :
    ∃ c : Fin M → F,
      V ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).image
          (fun T => (coreInterp dom T (genPoly c)).coeff k)).card * L ^ 2 := by
  classical
  have hex : ∃ c : Fin M → F,
      ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c)))).filter
        (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
          = (coreInterp dom p.2 (genPoly c)).coeff k)).card + V
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card := by
    by_contra hcon
    push_neg at hcon
    have hstrict : ∀ c : Fin M → F,
        2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card + 1
        ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c)))).filter
          (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
            = (coreInterp dom p.2 (genPoly c)).coeff k)).card + V := by
      intro c
      exact Nat.succ_le_of_lt (hcon c)
    have hsum := Finset.sum_le_sum
      (fun c (_ : c ∈ (Finset.univ : Finset (Fin M → F))) => hstrict c)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, smul_eq_mul, mul_one, smul_eq_mul] at hsum
    have hS2 := sum_N2_le_sharp dom k m hM
    have hchain : 2 * L * (∑ c : Fin M → F,
        (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card)
        + (Fintype.card F) ^ M
        ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card) := by
      calc 2 * L * (∑ c : Fin M → F, _) + (Fintype.card F) ^ M
          ≤ (∑ c : Fin M → F,
              ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c)) ×ˢ
                (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c)))).filter
                (fun p => (coreInterp dom p.1 (genPoly c)).coeff k
                  = (coreInterp dom p.2 (genPoly c)).coeff k)).card)
            + (Fintype.card F) ^ M * V := hsum
        _ ≤ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
            + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
            + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m))
            + (Fintype.card F) ^ M * V :=
            Nat.add_le_add_right hS2 _
        _ = ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
            + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
            + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
            + V * (Fintype.card F) ^ M := by ring
        _ ≤ _ := hbudget
    have hqMpos : 0 < (Fintype.card F) ^ M := pow_pos Fintype.card_pos _
    set A := 2 * L * (∑ c : Fin M → F,
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card) with hA
    set Z := (Fintype.card F) ^ M with hZ
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  have hquad := value_count_quadratic dom k m c L
  have hfinal := le_trans hc hquad
  exact Nat.le_of_add_le_add_left hfinal

open Classical in
/-- **THE SHARP SECOND-MOMENT DEEP-BAND FAILURE.**  `deep_band_badSet_card_of_moments`
with the sharp budget: the deep-pair term enters a full factor `q` lower. -/
theorem deep_band_badSet_card_of_moments_sharp (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hbudget : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card)) :
    ∃ Q₀ : F[X],
      V ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * L ^ 2 := by
  classical
  obtain ⟨c, hc⟩ := exists_generator_many_values_sharp dom k m hM hbudget
  refine ⟨genPoly c, ?_⟩
  refine le_trans hc (Nat.mul_le_mul_right _ ?_)
  set coh := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c)) with hcoh
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

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.deep_fiber_eq
#print axioms ProximityGap.PairRank.deep_fiber_le
#print axioms ProximityGap.PairRank.sum_N2_le_sharp
#print axioms ProximityGap.PairRank.exists_generator_many_values_sharp
#print axioms ProximityGap.PairRank.deep_band_badSet_card_of_moments_sharp
