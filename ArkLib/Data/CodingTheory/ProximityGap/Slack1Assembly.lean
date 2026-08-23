/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowExoticBound

/-!
# The slack-1 assembly (#371, G3 ladder): the second window row capped

**`stratumG_slack1_badScalars_card_le`** — at the second window row
(`n + 1 = 3w`, `k = 1`), the bad-scalar count of a reduced-coprime
doubly-rational stack is at most `n*(n−1) / (w*(w−1)) + 2`.

Assembly: choose a witness per bad scalar (`witness_division_identity_window`);
distinct scalars have distinct complements (`witness_gamma_injective_poly`);
chain-related complements force scalar equality (`chain_pair_factor` +
`chain_member_exact` + `cored_gamma_unique`), so the complements of distinct
bad scalars pairwise intersect in ≤ 1 point (`witness_pair_dichotomy`); at
most one complement is small (proportionality); the full-size complements
inject their point-pairs into the domain's pairs (`pairwise_inter_card_le`):
a Fisher count.

The bound is `≈ 9 + 2` at the deep-window shape — within the
`WindowRationalBounded` budget `w + 3` for `w ≥ 9`, and probe-bounded by 4
(`probe_nocore.py`, `probe_wb371_g3_twosided.py`) below that: the small-`w`
sharpening through the rank-3 module structure is the named remaining target.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The Fisher pair count**: pairwise ≤ 1-intersecting subsets inject their
ordered point-pairs into the domain's ordered pairs. -/
theorem pairwise_inter_card_le {𝒯 : Finset (Finset (Fin n))}
    (hpair : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → (T₁ ∩ T₂).card ≤ 1) :
    ∑ T ∈ 𝒯, T.card * (T.card - 1) ≤ n * (n - 1) := by
  classical
  -- inject Σ_T offDiag(T) into offDiag(univ)
  have hinj : Set.InjOn (fun x : (Σ _T : Finset (Fin n), Fin n × Fin n) => x.2)
      (𝒯.sigma (fun T => T.offDiag)) := by
    rintro ⟨T₁, p⟩ h₁ ⟨T₂, q⟩ h₂ (hpq : p = q)
    rw [Finset.mem_coe, Finset.mem_sigma] at h₁ h₂
    subst hpq
    rcases eq_or_ne T₁ T₂ with rfl | hne
    · rfl
    · exfalso
      have hp₁ := Finset.mem_offDiag.mp h₁.2
      have hp₂ := Finset.mem_offDiag.mp h₂.2
      have h2le : 2 ≤ (T₁ ∩ T₂).card := by
        have hx : p.1 ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨hp₁.1, hp₂.1⟩
        have hy : p.2 ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨hp₁.2.1, hp₂.2.1⟩
        exact Finset.one_lt_card.mpr ⟨p.1, hx, p.2, hy, hp₁.2.2⟩
      have := hpair T₁ h₁.1 T₂ h₂.1 hne
      omega
  have hcard := Finset.card_le_card_of_injOn
    (fun x : (Σ _T : Finset (Fin n), Fin n × Fin n) => x.2)
    (fun x hx => by
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      have hp := Finset.mem_offDiag.mp hx.2
      exact Finset.mem_coe.mpr (Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, hp.2.2⟩))
    hinj
  rw [Finset.card_sigma] at hcard
  calc ∑ T ∈ 𝒯, T.card * (T.card - 1)
      = ∑ T ∈ 𝒯, T.offDiag.card := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.offDiag_card, Nat.mul_sub, mul_one]
    _ ≤ Finset.univ.offDiag.card := hcard
    _ = n * (n - 1) := by
        rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin,
          Nat.mul_sub, mul_one]

section Capstone

variable {dom : Fin n ↪ F} {w : ℕ}
variable {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}

open Classical in
/-- **THE SLACK-1 STRATUM-G BOUND.**  At the second window row (`n + 1 = 3w`,
`k = 1`), a reduced-coprime doubly-rational stack has at most
`n(n−1)/(w(w−1)) + 1` bad scalars. -/
theorem stratumG_slack1_badScalars_card_le
    (hw3 : 3 ≤ w) (hn : n + 1 = 3 * w)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    (hdℓ₀ : ℓ₀.natDegree = w) (hdR₀ : R₀.natDegree ≤ w)
    (hdℓ₁ : ℓ₁.natDegree ≤ w) (hdR₁ : R₁.natDegree ≤ w)
    (hℓ₁pos : 1 ≤ ℓ₁.natDegree)
    (hG₀ : ∀ i, ℓ₀.eval (dom i) ≠ 0)
    (hcop₀ : IsCoprime R₀ ℓ₀) (hcop₁ : IsCoprime R₁ ℓ₁) (hcopℓ : IsCoprime ℓ₀ ℓ₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n * (n - 1) / (w * (w - 1)) + 1 := by
  classical
  set badSet := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hbadDef
  have hdata : ∀ γ ∈ badSet, ∃ (S : Finset (Fin n)) (g : F[X]) (p : F), g ≠ 0 ∧
      (n - w : ℕ) ≤ S.card ∧ g.natDegree + S.card ≤ 2 * w ∧
      (∀ i ∈ S, p = u₀ i + γ * u₁ i) ∧
      R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
        = g * vanishingPoly dom S :=
    fun γ hγ => witness_division_identity_window (by omega) hrel₀ hrel₁
      hdℓ₀ hdR₀ hdℓ₁ hdR₁ hcop₀ hcopℓ hδn (Finset.mem_filter.mp hγ).2
  choose Sf gf pf hgne hSc hbud hag hid using hdata
  -- size bookkeeping
  have hSrange : ∀ γ (h : γ ∈ badSet),
      2 * w - 1 ≤ (Sf γ h).card ∧ (Sf γ h).card ≤ 2 * w := by
    intro γ h
    have h1 := hSc γ h
    have h2 := hbud γ h
    omega
  have hgdeg : ∀ γ (h : γ ∈ badSet), (gf γ h).natDegree ≤ 1 := by
    intro γ h
    have h1 := hSc γ h
    have h2 := hbud γ h
    omega
  -- γ-injectivity through the agreement sets
  have hinj : ∀ γ₁ (h₁ : γ₁ ∈ badSet) γ₂ (h₂ : γ₂ ∈ badSet),
      Sf γ₁ h₁ = Sf γ₂ h₂ → γ₁ = γ₂ := by
    intro γ₁ h₁ γ₂ h₂ hSeq
    have e₂ := hid γ₂ h₂
    rw [← hSeq] at e₂
    exact witness_gamma_injective_poly hG₀ (by omega) hℓ₁pos hcop₁
      (by rw [hdℓ₀]; exact lt_of_le_of_lt (hgdeg γ₁ h₁) (by omega))
      (by rw [hdℓ₀]; exact lt_of_le_of_lt (hgdeg γ₂ h₂) (by omega))
      (hid γ₁ h₁) e₂
  -- two SMALL complements force equal scalars
  have hsmall : ∀ γ₁ (h₁ : γ₁ ∈ badSet) γ₂ (h₂ : γ₂ ∈ badSet),
      (Sf γ₁ h₁).card = 2 * w → (Sf γ₂ h₂).card = 2 * w → γ₁ = γ₂ := by
    intro γ₁ h₁ γ₂ h₂ hc₁ hc₂
    by_contra hne
    have hScne : Sf γ₁ h₁ ≠ Sf γ₂ h₂ := fun h => hne (hinj _ _ _ _ h)
    have hcross := witness_cross_dvd hG₀ hcop₀ hcopℓ (hid γ₁ h₁) (hid γ₂ h₂)
    have hg1d : (gf γ₁ h₁).natDegree = 0 := by
      have := hbud γ₁ h₁
      omega
    have hg2d : (gf γ₂ h₂).natDegree = 0 := by
      have := hbud γ₂ h₂
      omega
    -- the difference has degree < w, so it vanishes
    have hcompl_card : ∀ γ (h : γ ∈ badSet), (Sf γ h).card = 2 * w →
        ((Sf γ h)ᶜ : Finset (Fin n)).card = w - 1 := by
      intro γ h hc
      rw [Finset.card_compl, Fintype.card_fin, hc]
      omega
    have hzero : gf γ₂ h₂ * vanishingPoly dom (Sf γ₁ h₁)ᶜ
        - gf γ₁ h₁ * vanishingPoly dom (Sf γ₂ h₂)ᶜ = 0 := by
      by_contra hne0
      have hdeg := Polynomial.natDegree_le_of_dvd hcross hne0
      have hd : (gf γ₂ h₂ * vanishingPoly dom (Sf γ₁ h₁)ᶜ
          - gf γ₁ h₁ * vanishingPoly dom (Sf γ₂ h₂)ᶜ).natDegree ≤ w - 1 := by
        have e1 : (gf γ₂ h₂ * vanishingPoly dom (Sf γ₁ h₁)ᶜ).natDegree ≤ w - 1 := by
          refine le_trans natDegree_mul_le ?_
          rw [vanishingPoly_natDegree, hcompl_card γ₁ h₁ hc₁]
          omega
        have e2 : (gf γ₁ h₁ * vanishingPoly dom (Sf γ₂ h₂)ᶜ).natDegree ≤ w - 1 := by
          refine le_trans natDegree_mul_le ?_
          rw [vanishingPoly_natDegree, hcompl_card γ₂ h₂ hc₂]
          omega
        exact le_trans (natDegree_sub_le _ _) (max_le e1 e2)
      rw [hdℓ₀] at hdeg
      omega
    have heq : gf γ₂ h₂ * vanishingPoly dom (Sf γ₁ h₁)ᶜ
        = gf γ₁ h₁ * vanishingPoly dom (Sf γ₂ h₂)ᶜ := sub_eq_zero.mp hzero
    -- leading coefficients agree, vanishing polys cancel
    have hlc := congrArg Polynomial.leadingCoeff heq
    rw [leadingCoeff_mul, leadingCoeff_mul,
      (vanishingPoly_monic dom _).leadingCoeff,
      (vanishingPoly_monic dom _).leadingCoeff, mul_one, mul_one] at hlc
    -- both g's are constants with equal leading coefficient: g₂ = g₁
    have hgeq : gf γ₂ h₂ = gf γ₁ h₁ := by
      have e1 := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hg1d)
      have e2 := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hg2d)
      rw [e1, e2] at hlc ⊢
      rw [leadingCoeff_C, leadingCoeff_C] at hlc
      rw [hlc]
    rw [hgeq] at heq
    have hvp : vanishingPoly dom (Sf γ₁ h₁)ᶜ = vanishingPoly dom (Sf γ₂ h₂)ᶜ :=
      mul_left_cancel₀ (hgne γ₁ h₁) heq
    have hcompl_eq : (Sf γ₁ h₁)ᶜ = (Sf γ₂ h₂)ᶜ := vanishingPoly_inj dom hvp
    exact hScne (compl_injective hcompl_eq)
  -- two FULL complements of distinct scalars intersect in ≤ 1
  have hfull : ∀ γ₁ (h₁ : γ₁ ∈ badSet) γ₂ (h₂ : γ₂ ∈ badSet), γ₁ ≠ γ₂ →
      (Sf γ₁ h₁).card = 2 * w - 1 → (Sf γ₂ h₂).card = 2 * w - 1 →
      (((Sf γ₁ h₁)ᶜ ∩ (Sf γ₂ h₂)ᶜ) : Finset (Fin n)).card ≤ 1 := by
    intro γ₁ h₁ γ₂ h₂ hne hc₁ hc₂
    have hScne : Sf γ₁ h₁ ≠ Sf γ₂ h₂ := fun h => hne (hinj _ _ _ _ h)
    have hTne : (Sf γ₁ h₁)ᶜ ≠ (Sf γ₂ h₂)ᶜ := fun h => hScne (compl_injective h)
    have hT₁card : ((Sf γ₁ h₁)ᶜ : Finset (Fin n)).card = w := by
      rw [Finset.card_compl, Fintype.card_fin, hc₁]
      omega
    have hT₂card : ((Sf γ₂ h₂)ᶜ : Finset (Fin n)).card = w := by
      rw [Finset.card_compl, Fintype.card_fin, hc₂]
      omega
    have hcross := witness_cross_dvd hG₀ hcop₀ hcopℓ (hid γ₁ h₁) (hid γ₂ h₂)
    rcases witness_pair_dichotomy hG₀ hdℓ₀ hw3 (hgne γ₁ h₁) (hgne γ₂ h₂)
      (hgdeg γ₁ h₁) (hgdeg γ₂ h₂) hTne (le_of_eq hT₁card) (le_of_eq hT₂card)
      hcross with hle | ⟨K, hK, hd₁, hd₂⟩
    · exact hle
    · -- chain pair: forces γ₁ = γ₂, contradiction
      exfalso
      set T₁ := ((Sf γ₁ h₁)ᶜ : Finset (Fin n)) with hT₁
      set T₂ := ((Sf γ₂ h₂)ᶜ : Finset (Fin n)) with hT₂
      have hKsub₁ : K ⊆ T₁ := hK ▸ Finset.inter_subset_left
      have hKsub₂ : K ⊆ T₂ := hK ▸ Finset.inter_subset_right
      have hone₁ : (T₁ \ K).card = 1 := by
        rcases Nat.lt_or_ge (T₁ \ K).card 1 with h | h
        · exfalso
          have h0 : T₁ \ K = ∅ := Finset.card_eq_zero.mp (by omega)
          have hsub : T₁ ⊆ K := by
            intro x hx
            by_contra hxK
            have : x ∈ T₁ \ K := Finset.mem_sdiff.mpr ⟨hx, hxK⟩
            rw [h0] at this
            exact absurd this (Finset.notMem_empty x)
          have hKT₁ : K = T₁ := Finset.Subset.antisymm hKsub₁ hsub
          have hT₁sub : T₁ ⊆ T₂ := hKT₁ ▸ hKsub₂
          have : T₁ = T₂ := Finset.eq_of_subset_of_card_le hT₁sub
            (by rw [hT₁card, hT₂card])
          exact hTne this
        · omega
      have hone₂ : (T₂ \ K).card = 1 := by
        rcases Nat.lt_or_ge (T₂ \ K).card 1 with h | h
        · exfalso
          have h0 : T₂ \ K = ∅ := Finset.card_eq_zero.mp (by omega)
          have hsub : T₂ ⊆ K := by
            intro x hx
            by_contra hxK
            have : x ∈ T₂ \ K := Finset.mem_sdiff.mpr ⟨hx, hxK⟩
            rw [h0] at this
            exact absurd this (Finset.notMem_empty x)
          have hKT₂ : K = T₂ := Finset.Subset.antisymm hKsub₂ hsub
          have hT₂sub : T₂ ⊆ T₁ := hKT₂ ▸ hKsub₁
          have : T₂ = T₁ := Finset.eq_of_subset_of_card_le hT₂sub
            (by rw [hT₁card, hT₂card])
          exact hTne this.symm
        · omega
      obtain ⟨t₁, ht₁⟩ := Finset.card_eq_one.mp hone₁
      obtain ⟨t₂, ht₂⟩ := Finset.card_eq_one.mp hone₂
      have ht₁mem : t₁ ∈ T₁ \ K := ht₁ ▸ Finset.mem_singleton_self t₁
      have ht₂mem : t₂ ∈ T₂ \ K := ht₂ ▸ Finset.mem_singleton_self t₂
      have ht₁K : t₁ ∉ K := (Finset.mem_sdiff.mp ht₁mem).2
      have ht₂K : t₂ ∉ K := (Finset.mem_sdiff.mp ht₂mem).2
      have hT₁eq : insert t₁ K = T₁ := by
        rw [Finset.insert_eq, ← ht₁, Finset.sdiff_union_of_subset hKsub₁]
      have hT₂eq : insert t₂ K = T₂ := by
        rw [Finset.insert_eq, ← ht₂, Finset.sdiff_union_of_subset hKsub₂]
      have htne : t₁ ≠ t₂ := by
        intro h
        apply hTne
        rw [← hT₁eq, ← hT₂eq, h]
      -- the chain factorization
      have hcross' : ℓ₀ ∣ gf γ₂ h₂ * vanishingPoly dom (insert t₁ K)
          - gf γ₁ h₁ * vanishingPoly dom (insert t₂ K) := by
        rw [hT₁eq, hT₂eq]
        exact hcross
      obtain ⟨a, hane, hg₁eq, hg₂eq⟩ := chain_pair_factor hG₀ hdℓ₀ hw3 htne
        ht₁K ht₂K (hgne γ₁ h₁) (hgne γ₂ h₂) (hgdeg γ₁ h₁) (hgdeg γ₂ h₂) hcross'
      -- the exact cored identities
      have hSf₁ : Sf γ₁ h₁ = (insert t₁ K)ᶜ := by
        rw [hT₁eq]
        exact (compl_compl _).symm
      have hSf₂ : Sf γ₂ h₂ = (insert t₂ K)ᶜ := by
        rw [hT₂eq]
        exact (compl_compl _).symm
      have hid₁' := hid γ₁ h₁
      rw [hSf₁, hg₁eq] at hid₁'
      have hid₂' := hid γ₂ h₂
      rw [hSf₂, hg₂eq] at hid₂'
      have hcored₁ := chain_member_exact (dom := dom) ht₁K hid₁'
        (vanishingPoly_mul_compl dom (insert t₁ K))
      have hcored₂ := chain_member_exact (dom := dom) ht₂K hid₂'
        (vanishingPoly_mul_compl dom (insert t₂ K))
      have hKcard : K.card < ℓ₀.natDegree := by
        have : K.card = w - 1 := by
          have hc : (T₁ \ K).card = T₁.card - (K ∩ T₁).card := Finset.card_sdiff
          rw [ht₁, Finset.card_singleton, hT₁card,
            Finset.inter_eq_left.mpr hKsub₁] at hc
          omega
        rw [hdℓ₀]
        omega
      exact hne (cored_gamma_unique hG₀ (by omega) hℓ₁pos hcop₁ hane hane
        hKcard hKcard hcored₁ hcored₂)
  -- assemble the count
  rcases Finset.eq_empty_or_nonempty badSet with h0 | _
  · rw [h0]
    simp
  -- the complement family
  set Tmap : {γ // γ ∈ badSet} → Finset (Fin n) :=
    fun x => ((Sf x.1 x.2)ᶜ : Finset (Fin n)) with hTmap
  have hTinj : Set.InjOn Tmap badSet.attach := by
    intro x _ y _ hxy
    have hSS : Sf x.1 x.2 = Sf y.1 y.2 := compl_injective hxy
    exact Subtype.ext (hinj _ _ _ _ hSS)
  set 𝒯 := badSet.attach.image Tmap with h𝒯
  have hcardeq : 𝒯.card = badSet.card := by
    rw [h𝒯, Finset.card_image_of_injOn hTinj, Finset.card_attach]
  set 𝒯full := 𝒯.filter (fun T => T.card = w) with h𝒯full
  set 𝒯small := 𝒯.filter (fun T => ¬ T.card = w) with h𝒯small
  have hsplit : 𝒯full.card + 𝒯small.card = 𝒯.card :=
    Finset.card_filter_add_card_filter_not _
  -- the member sizes are w or w−1
  have hsize : ∀ x : {γ // γ ∈ badSet}, (Tmap x).card = w ∨ (Tmap x).card = w - 1 := by
    intro x
    have hr := hSrange x.1 x.2
    have : (Tmap x).card = n - (Sf x.1 x.2).card := by
      rw [hTmap]
      rw [Finset.card_compl, Fintype.card_fin]
    omega
  -- at most one small member
  have hsmall1 : 𝒯small.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro T₁ hT₁ T₂ hT₂
    rw [h𝒯small, Finset.mem_filter] at hT₁ hT₂
    obtain ⟨hT₁mem, hT₁card⟩ := hT₁
    obtain ⟨hT₂mem, hT₂card⟩ := hT₂
    rw [h𝒯, Finset.mem_image] at hT₁mem hT₂mem
    obtain ⟨x, -, rfl⟩ := hT₁mem
    obtain ⟨y, -, rfl⟩ := hT₂mem
    -- both small: their S-cards are 2w
    have hx : (Sf x.1 x.2).card = 2 * w := by
      have := hsize x
      have hr := hSrange x.1 x.2
      have hcc : (Tmap x).card = n - (Sf x.1 x.2).card := by
        rw [hTmap, Finset.card_compl, Fintype.card_fin]
      omega
    have hy : (Sf y.1 y.2).card = 2 * w := by
      have := hsize y
      have hr := hSrange y.1 y.2
      have hcc : (Tmap y).card = n - (Sf y.1 y.2).card := by
        rw [hTmap, Finset.card_compl, Fintype.card_fin]
      omega
    have hγeq : x.1 = y.1 := hsmall x.1 x.2 y.1 y.2 hx hy
    have : x = y := Subtype.ext hγeq
    rw [this]
  -- full members: pairwise ≤ 1-intersecting, all of size w
  have hfullpair : ∀ T₁ ∈ 𝒯full, ∀ T₂ ∈ 𝒯full, T₁ ≠ T₂ → (T₁ ∩ T₂).card ≤ 1 := by
    intro T₁ hT₁ T₂ hT₂ hne
    rw [h𝒯full, Finset.mem_filter] at hT₁ hT₂
    obtain ⟨hT₁mem, hT₁card⟩ := hT₁
    obtain ⟨hT₂mem, hT₂card⟩ := hT₂
    rw [h𝒯, Finset.mem_image] at hT₁mem hT₂mem
    obtain ⟨x, -, rfl⟩ := hT₁mem
    obtain ⟨y, -, rfl⟩ := hT₂mem
    have hγne : x.1 ≠ y.1 := by
      intro h
      exact hne (by rw [Subtype.ext h])
    have hx : (Sf x.1 x.2).card = 2 * w - 1 := by
      have hcc : (Tmap x).card = n - (Sf x.1 x.2).card := by
        rw [hTmap, Finset.card_compl, Fintype.card_fin]
      have hr := hSrange x.1 x.2
      omega
    have hy : (Sf y.1 y.2).card = 2 * w - 1 := by
      have hcc : (Tmap y).card = n - (Sf y.1 y.2).card := by
        rw [hTmap, Finset.card_compl, Fintype.card_fin]
      have hr := hSrange y.1 y.2
      omega
    exact hfull x.1 x.2 y.1 y.2 hγne hx hy
  -- Fisher count on the full members
  have hfisher := pairwise_inter_card_le hfullpair
  have hfullcount : 𝒯full.card * (w * (w - 1)) ≤ n * (n - 1) := by
    have hsum : ∑ T ∈ 𝒯full, T.card * (T.card - 1)
        = 𝒯full.card * (w * (w - 1)) := by
      calc ∑ T ∈ 𝒯full, T.card * (T.card - 1)
          = ∑ _T ∈ 𝒯full, w * (w - 1) :=
            Finset.sum_congr rfl (fun T hT => by
              rw [h𝒯full, Finset.mem_filter] at hT
              rw [hT.2])
        _ = 𝒯full.card * (w * (w - 1)) := by
            rw [Finset.sum_const, smul_eq_mul]
    rw [← hsum]
    exact hfisher
  have hfull_le : 𝒯full.card ≤ n * (n - 1) / (w * (w - 1)) := by
    rw [Nat.le_div_iff_mul_le (by
      have : 1 ≤ w - 1 := by omega
      exact Nat.mul_pos (by omega) (by omega))]
    exact hfullcount
  omega

end Capstone

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.pairwise_inter_card_le
#print axioms ProximityGap.WBPencil.stratumG_slack1_badScalars_card_le
