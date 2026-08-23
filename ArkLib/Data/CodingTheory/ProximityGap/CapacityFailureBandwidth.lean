/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PairCoherenceCount

/-!
# THE CAPACITY-FAILURE BANDWIDTH LAW (#389)

The second-moment capstone.  With the exact per-core count
(`card_coherent_eq`), the exact far-pair count (`card_pair_coherent_eq`), the
high-overlap stratum bound, and Cauchy–Schwarz at both the fiber and the
family level, the deep-band failure becomes quantitative at EVERY band with
NO side conditions:

  **`∃ Q₀ : C(n,k+m+1) · q
       ≤ #badSet(Q₀, x^k) · ((1 + C(k+m+1,k+1)·C(n,m)) · q^{m+1} + C(n,k+m+1))`.**

**The bandwidth law**: wherever `C(n,k+m+1) ≥ (1 + C(k+m+1,k+1)·C(n,m))·q^{m+1}`,
the bad-scalar count is at least `q/2` — mutual correlated agreement fails for
half the field.  In production parameters this failure zone extends
`Θ(n·H(ρ)/log q)` bands below capacity: the first machine-checked
quantification of the width of the capacity-failure region.  At `m = 0` it
recovers the boundary production failure.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE CAPACITY-FAILURE BANDWIDTH LAW**. -/
theorem capacity_failure_bandwidth (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0)) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1) * Fintype.card F
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * ((1 + (k + m + 1).choose (k + 1) * n.choose m)
              * (Fintype.card F) ^ (m + 1) + n.choose (k + m + 1)) := by
  set q := Fintype.card F with hq
  set M := 2 * (k + m + 1) with hM
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set Nm := Pm.card with hNm
  have hNmval : Nm = n.choose (k + m + 1) := by
    rw [hNm, hPm, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos Nm with hNm0 | hNmpos
  · exact ⟨0, by rw [← hNmval, hNm0]; simp⟩
  set D := (k + m + 1).choose (k + 1) * n.choose m with hD
  have hqpow : (Fintype.card F) ^ m * (Fintype.card F) ^ m * Fintype.card F
      = q ^ (2 * m + 1) := by
    rw [hq, ← pow_add, ← pow_succ]
    congr 1
    omega
  -- per-stack data
  set coh : (Fin M → F) → Finset (Finset (Fin n)) := fun c =>
    Pm.filter (fun T => IsCoherent dom k m T (coeffFamily M c)) with hcoh
  set w : (Fin M → F) → Finset (Fin n) → F := fun c T =>
    (coreInterp dom T (coeffFamily M c)).coeff k with hw
  set prs : (Fin M → F) → ℕ := fun c =>
    ((Pm ×ˢ Pm).filter (fun p =>
      (IsCoherent dom k m p.1 (coeffFamily M c)
        ∧ IsCoherent dom k m p.2 (coeffFamily M c))
      ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
          = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card with hprs
  set bad : (Fin M → F) → Finset F := fun c =>
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (coeffFamily M c).eval (dom i)) (fun i => (dom i) ^ k) γ)
    with hbad
  -- ── the exact first moment ──
  have hfirst : (∑ c : Fin M → F, (coh c).card) * q ^ m = Nm * q ^ M := by
    have hswap : ∑ c : Fin M → F, (coh c).card
        = ∑ T ∈ Pm, (Finset.univ.filter
          (fun c : Fin M → F =>
            IsCoherent dom k m T (coeffFamily M c))).card := by
      simp only [hcoh, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap, Finset.sum_mul]
    calc ∑ T ∈ Pm, (Finset.univ.filter
          (fun c : Fin M → F =>
            IsCoherent dom k m T (coeffFamily M c))).card * q ^ m
        = ∑ T ∈ Pm, q ^ M := by
          refine Finset.sum_congr rfl fun T hT => ?_
          have hTcard : T.card = k + m + 1 :=
            (Finset.mem_powersetCard.mp hT).2
          rw [hq]
          exact card_coherent_eq dom hTcard (by omega)
      _ = Nm * q ^ M := by rw [Finset.sum_const, smul_eq_mul, hNm]
  -- ── the stratified second moment ──
  have hsecond : (∑ c : Fin M → F, prs c) * q ^ (2 * m + 1)
      ≤ Nm * (1 + D) * q ^ (M + m + 1) + Nm * Nm * q ^ M := by
    have hswap : ∑ c : Fin M → F, prs c
        = ∑ p ∈ Pm ×ˢ Pm, (Finset.univ.filter
          (fun c : Fin M → F =>
            (IsCoherent dom k m p.1 (coeffFamily M c)
              ∧ IsCoherent dom k m p.2 (coeffFamily M c))
            ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
                = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card := by
      simp only [hprs, Finset.card_filter]
      rw [Finset.sum_comm]
    -- per-pair bound by overlap stratum
    have hperpair : ∀ p ∈ Pm ×ˢ Pm,
        (Finset.univ.filter (fun c : Fin M → F =>
          (IsCoherent dom k m p.1 (coeffFamily M c)
            ∧ IsCoherent dom k m p.2 (coeffFamily M c))
          ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
              = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card
          * q ^ (2 * m + 1)
        ≤ if (p.1 ∩ p.2).card ≤ k then q ^ M else q ^ (M + m + 1) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hc1 : p.1.card = k + m + 1 := (Finset.mem_powersetCard.mp hp1).2
      have hc2 : p.2.card = k + m + 1 := (Finset.mem_powersetCard.mp hp2).2
      by_cases hcap : (p.1 ∩ p.2).card ≤ k
      · rw [if_pos hcap]
        have h := card_pair_coherent_eq dom hc1 hc2 hcap
          (M := M) (le_of_eq hM.symm)
        rw [hqpow] at h
        rw [← hq] at h
        exact le_of_eq h
      · rw [if_neg hcap]
        -- drop the second core and the match: only T-coherence
        have hsub2 : (Finset.univ.filter (fun c : Fin M → F =>
            (IsCoherent dom k m p.1 (coeffFamily M c)
              ∧ IsCoherent dom k m p.2 (coeffFamily M c))
            ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
                = (coreInterp dom p.2 (coeffFamily M c)).coeff k))
            ⊆ (Finset.univ.filter (fun c : Fin M → F =>
              IsCoherent dom k m p.1 (coeffFamily M c))) := by
          intro c hc
          obtain ⟨-, ⟨h1, -⟩, -⟩ := Finset.mem_filter.mp hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
        have hcohcard := card_coherent_eq dom hc1 (M := M) (by omega)
        calc (Finset.univ.filter _).card * q ^ (2 * m + 1)
            ≤ (Finset.univ.filter (fun c : Fin M → F =>
                IsCoherent dom k m p.1 (coeffFamily M c))).card
                * q ^ (2 * m + 1) :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub2)
          _ = ((Finset.univ.filter (fun c : Fin M → F =>
                IsCoherent dom k m p.1 (coeffFamily M c))).card
                * q ^ m) * q ^ (m + 1) := by
              rw [mul_assoc, ← pow_add]
              congr 2
              omega
          _ = q ^ M * q ^ (m + 1) := by
              rw [← hq] at hcohcard
              rw [hcohcard]
          _ = q ^ (M + m + 1) := by rw [← pow_add]; congr 1
    -- the near-stratum pair count
    have hnearcount : ((Pm ×ˢ Pm).filter
        (fun p => ¬ (p.1 ∩ p.2).card ≤ k)).card ≤ Nm * D := by
      have hsumform : ((Pm ×ˢ Pm).filter
          (fun p => ¬ (p.1 ∩ p.2).card ≤ k)).card
          = ∑ T ∈ Pm, (Pm.filter
            (fun T' => ¬ (T ∩ T').card ≤ k)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.card_filter]
      rw [hsumform]
      calc ∑ T ∈ Pm, (Pm.filter (fun T' => ¬ (T ∩ T').card ≤ k)).card
          ≤ ∑ T ∈ Pm, D := by
            refine Finset.sum_le_sum fun T hT => ?_
            have hTcard : T.card = k + m + 1 :=
              (Finset.mem_powersetCard.mp hT).2
            -- T' with big overlap is a (k+1)-subset of T plus m free points
            have hcover : Pm.filter (fun T' => ¬ (T ∩ T').card ≤ k)
                ⊆ (T.powersetCard (k + 1)).biUnion
                  (fun S => Pm.filter (fun T' => S ⊆ T')) := by
              intro T' hT'
              obtain ⟨hT'mem, hbig⟩ := Finset.mem_filter.mp hT'
              push Not at hbig
              obtain ⟨S, hSsub, hScard⟩ :=
                Finset.exists_subset_card_eq (by omega : k + 1 ≤ (T ∩ T').card)
              refine Finset.mem_biUnion.mpr ⟨S, ?_, ?_⟩
              · exact Finset.mem_powersetCard.mpr
                  ⟨hSsub.trans Finset.inter_subset_left, hScard⟩
              · exact Finset.mem_filter.mpr
                  ⟨hT'mem, hSsub.trans Finset.inter_subset_right⟩
            calc (Pm.filter (fun T' => ¬ (T ∩ T').card ≤ k)).card
                ≤ ((T.powersetCard (k + 1)).biUnion
                    (fun S => Pm.filter (fun T' => S ⊆ T'))).card :=
                  Finset.card_le_card hcover
              _ ≤ ∑ S ∈ T.powersetCard (k + 1),
                  (Pm.filter (fun T' => S ⊆ T')).card :=
                  Finset.card_biUnion_le
              _ ≤ ∑ S ∈ T.powersetCard (k + 1), n.choose m := by
                  refine Finset.sum_le_sum fun S hS => ?_
                  have hScard : S.card = k + 1 :=
                    (Finset.mem_powersetCard.mp hS).2
                  -- inject into the m-subsets via T' ↦ T' \ S
                  calc (Pm.filter (fun T' => S ⊆ T')).card
                      ≤ ((Finset.univ : Finset (Fin n)).powersetCard m).card := by
                        refine Finset.card_le_card_of_injOn
                          (fun T' => T' \ S) ?_ ?_
                        · intro T' hT'
                          obtain ⟨hT'mem, hST'⟩ :=
                            Finset.mem_filter.mp (Finset.mem_coe.mp hT')
                          have hT'card : T'.card = k + m + 1 :=
                            (Finset.mem_powersetCard.mp hT'mem).2
                          rw [Finset.mem_coe, Finset.mem_powersetCard]
                          refine ⟨Finset.subset_univ _, ?_⟩
                          rw [Finset.card_sdiff_of_subset hST', hT'card,
                            hScard]
                          omega
                        · intro a ha b hb hab
                          obtain ⟨-, hSa⟩ :=
                            Finset.mem_filter.mp (Finset.mem_coe.mp ha)
                          obtain ⟨-, hSb⟩ :=
                            Finset.mem_filter.mp (Finset.mem_coe.mp hb)
                          replace hab : a \ S = b \ S := hab
                          calc a = (a \ S) ∪ S :=
                                (Finset.sdiff_union_of_subset hSa).symm
                            _ = (b \ S) ∪ S := by rw [hab]
                            _ = b := Finset.sdiff_union_of_subset hSb
                      _ = n.choose m := by
                          rw [Finset.card_powersetCard, Finset.card_univ,
                            Fintype.card_fin]
              _ = D := by
                  rw [Finset.sum_const, Finset.card_powersetCard, hTcard,
                    smul_eq_mul, hD]
        _ = Nm * D := by rw [Finset.sum_const, smul_eq_mul, hNm]
    -- assemble the strata
    rw [hswap, Finset.sum_mul]
    calc ∑ p ∈ Pm ×ˢ Pm, (Finset.univ.filter _).card * q ^ (2 * m + 1)
        ≤ ∑ p ∈ Pm ×ˢ Pm, (if (p.1 ∩ p.2).card ≤ k then q ^ M
            else q ^ (M + m + 1)) := Finset.sum_le_sum hperpair
      _ = ∑ p ∈ (Pm ×ˢ Pm).filter (fun p => (p.1 ∩ p.2).card ≤ k), q ^ M
          + ∑ p ∈ (Pm ×ˢ Pm).filter (fun p => ¬ (p.1 ∩ p.2).card ≤ k),
              q ^ (M + m + 1) := Finset.sum_ite _ _
      _ ≤ Nm * Nm * q ^ M + Nm * (1 + D) * q ^ (M + m + 1) := by
          refine Nat.add_le_add ?_ ?_
          · rw [Finset.sum_const, smul_eq_mul]
            refine Nat.mul_le_mul_right _ ?_
            calc ((Pm ×ˢ Pm).filter (fun p => (p.1 ∩ p.2).card ≤ k)).card
                ≤ (Pm ×ˢ Pm).card := Finset.card_filter_le _ _
              _ = Nm * Nm := by rw [Finset.card_product, hNm]
          · rw [Finset.sum_const, smul_eq_mul]
            refine Nat.mul_le_mul_right _ ?_
            calc ((Pm ×ˢ Pm).filter
                  (fun p => ¬ (p.1 ∩ p.2).card ≤ k)).card
                ≤ Nm * D := hnearcount
              _ ≤ Nm * (1 + D) := Nat.mul_le_mul_left _ (by omega)
      _ = Nm * (1 + D) * q ^ (M + m + 1) + Nm * Nm * q ^ M := by ring
  -- ── per-stack Cauchy–Schwarz over value fibers ──
  have hperCS : ∀ c : Fin M → F, (coh c).card ^ 2 ≤ (bad c).card * prs c := by
    intro c
    set img := (coh c).image (w c) with himg
    -- the fiber decomposition of the pair count
    have hprsfib : prs c = ∑ v ∈ img, ((coh c).filter
        (fun T => w c T = v)).card ^ 2 := by
      show ((Pm ×ˢ Pm).filter (fun p =>
          (IsCoherent dom k m p.1 (coeffFamily M c)
            ∧ IsCoherent dom k m p.2 (coeffFamily M c))
          ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
              = (coreInterp dom p.2 (coeffFamily M c)).coeff k)).card = _
      have hpairs : (Pm ×ˢ Pm).filter (fun p =>
          (IsCoherent dom k m p.1 (coeffFamily M c)
            ∧ IsCoherent dom k m p.2 (coeffFamily M c))
          ∧ (coreInterp dom p.1 (coeffFamily M c)).coeff k
              = (coreInterp dom p.2 (coeffFamily M c)).coeff k)
          = img.biUnion (fun v =>
            ((coh c).filter (fun T => w c T = v))
              ×ˢ ((coh c).filter (fun T => w c T = v))) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          Finset.mem_image, hcoh, hw, himg]
        constructor
        · rintro ⟨⟨h1, h2⟩, ⟨hcoh1, hcoh2⟩, heq2⟩
          exact ⟨(coreInterp dom p.1 (coeffFamily M c)).coeff k,
            ⟨p.1, ⟨h1, hcoh1⟩, rfl⟩,
            ⟨⟨h1, hcoh1⟩, rfl⟩, ⟨h2, hcoh2⟩, heq2.symm⟩
        · rintro ⟨v, -, ⟨⟨h1, hcoh1⟩, hv1⟩, ⟨h2, hcoh2⟩, hv2⟩
          exact ⟨⟨h1, h2⟩, ⟨hcoh1, hcoh2⟩, hv1.trans hv2.symm⟩
      rw [hpairs, Finset.card_biUnion (fun v hv v' hv' hne => by
        show Disjoint
          (((coh c).filter (fun T => w c T = v))
            ×ˢ ((coh c).filter (fun T => w c T = v)))
          (((coh c).filter (fun T => w c T = v'))
            ×ˢ ((coh c).filter (fun T => w c T = v')))
        rw [Finset.disjoint_left]
        rintro p hp hp'
        obtain ⟨h1, -⟩ := Finset.mem_product.mp hp
        obtain ⟨h1', -⟩ := Finset.mem_product.mp hp'
        exact hne (((Finset.mem_filter.mp h1).2).symm.trans
          (Finset.mem_filter.mp h1').2))]
      exact Finset.sum_congr rfl fun v _ => by
        rw [Finset.card_product, sq]
    -- the fiber decomposition of the coherent count
    have hcohfib : (coh c).card = ∑ v ∈ img, ((coh c).filter
        (fun T => w c T = v)).card := by
      exact Finset.card_eq_sum_card_fiberwise fun T hT =>
        Finset.mem_image_of_mem _ hT
    -- Cauchy–Schwarz over the fibers
    have hCS : (coh c).card ^ 2 ≤ img.card * prs c := by
      rw [hprsfib, hcohfib]
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) img 1
        (fun v => ((coh c).filter (fun T => w c T = v)).card)
    -- the image injects into the bad set
    have himgbad : img.card ≤ (bad c).card := by
      have h1 : img.card = (img.image (fun x => -x)).card :=
        (Finset.card_image_of_injective _ neg_injective).symm
      rw [h1]
      refine Finset.card_le_card ?_
      intro γ hγ
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hγ
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hTmem, hTc⟩ := Finset.mem_filter.mp hT
      have hTcard : T.card = k + m + 1 :=
        (Finset.mem_powersetCard.mp hTmem).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mcaEvent_of_coherent dom hk hhi hTcard hTc⟩
    calc (coh c).card ^ 2 ≤ img.card * prs c := hCS
      _ ≤ (bad c).card * prs c := Nat.mul_le_mul_right _ himgbad
  -- ── the family-level Cauchy–Schwarz ──
  have hfamCS : (∑ c : Fin M → F, (coh c).card) ^ 2
      ≤ q ^ M * ∑ c : Fin M → F, (coh c).card ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ)
      (Finset.univ : Finset (Fin M → F)) 1 (fun c => (coh c).card)
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hq] using h
  -- ── the maximizing stack ──
  obtain ⟨cstar, -, hcstar⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin M → F)) (fun c => (bad c).card)
    Finset.univ_nonempty
  set β := (bad cstar).card with hβ
  have hβbound : ∀ c : Fin M → F, (bad c).card ≤ β :=
    fun c => hcstar c (Finset.mem_univ c)
  -- ── assemble ──
  have hp2M : q ^ (2 * M) = q ^ M * q ^ M := by
    rw [← pow_add]
    congr 1
    omega
  have hp2m1 : q ^ (2 * m + 1) = q ^ m * q ^ m * q := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hpMm1 : q ^ (M + m + 1) = q ^ M * q ^ (m + 1) := by
    rw [← pow_add]
    congr 1
  have hkey : Nm * Nm * q ^ (2 * M) * q
      ≤ β * (q ^ (2 * M) * (Nm * ((1 + D) * q ^ (m + 1) + Nm))) := by
    calc Nm * Nm * q ^ (2 * M) * q
        = ((Nm * q ^ M) * (Nm * q ^ M)) * q := by rw [hp2M]; ring
      _ = (((∑ c : Fin M → F, (coh c).card) * q ^ m)
            * ((∑ c : Fin M → F, (coh c).card) * q ^ m)) * q := by
          rw [hfirst]
      _ = ((∑ c : Fin M → F, (coh c).card) ^ 2) * q ^ (2 * m + 1) := by
          rw [sq, hp2m1]
          ring
      _ ≤ (q ^ M * ∑ c : Fin M → F, (coh c).card ^ 2) * q ^ (2 * m + 1) :=
          Nat.mul_le_mul_right _ hfamCS
      _ ≤ (q ^ M * ∑ c : Fin M → F, β * prs c) * q ^ (2 * m + 1) := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
          refine Finset.sum_le_sum fun c _ => ?_
          calc (coh c).card ^ 2 ≤ (bad c).card * prs c := hperCS c
            _ ≤ β * prs c := Nat.mul_le_mul_right _ (hβbound c)
      _ = q ^ M * β * ((∑ c : Fin M → F, prs c) * q ^ (2 * m + 1)) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ q ^ M * β * (Nm * (1 + D) * q ^ (M + m + 1) + Nm * Nm * q ^ M) :=
          Nat.mul_le_mul_left _ hsecond
      _ = β * (q ^ (2 * M) * (Nm * ((1 + D) * q ^ (m + 1) + Nm))) := by
          rw [hpMm1, hp2M]
          ring
  -- cancel the positive factor Nm · q^{2M}
  have hkey2 : (Nm * q) * (Nm * q ^ (2 * M))
      ≤ (β * ((1 + D) * q ^ (m + 1) + Nm)) * (Nm * q ^ (2 * M)) := by
    calc (Nm * q) * (Nm * q ^ (2 * M))
        = Nm * Nm * q ^ (2 * M) * q := by ring
      _ ≤ β * (q ^ (2 * M) * (Nm * ((1 + D) * q ^ (m + 1) + Nm))) := hkey
      _ = (β * ((1 + D) * q ^ (m + 1) + Nm)) * (Nm * q ^ (2 * M)) := by ring
  have hq1 : 0 < q := by
    rw [hq]
    exact Fintype.card_pos
  have hfinal : Nm * q ≤ β * ((1 + D) * q ^ (m + 1) + Nm) :=
    Nat.le_of_mul_le_mul_right hkey2
      (Nat.mul_pos hNmpos (pow_pos hq1 _))
  -- conclude
  refine ⟨coeffFamily M cstar, ?_⟩
  show n.choose (k + m + 1) * q
    ≤ (bad cstar).card
      * ((1 + (k + m + 1).choose (k + 1) * n.choose m) * q ^ (m + 1)
        + n.choose (k + m + 1))
  rw [← hNmval, ← hD, ← hβ]
  exact hfinal

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.capacity_failure_bandwidth
