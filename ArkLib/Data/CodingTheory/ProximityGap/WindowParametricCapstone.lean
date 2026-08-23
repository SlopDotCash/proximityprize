/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowTelescope

/-!
# The parametric window capstone (#371, G3 ladder)

**`stratumG_window_badScalars_card_le`** — ONE theorem for half the window:
at every row with `2·D_def < w` (`D_def = 3w − n`, k = 1), a reduced-coprime
doubly-rational stack has at most `C(n, D_def+1) / C(w − D_def, D_def+1)` bad
scalars.

Assembly: witnesses from the parametric engine; distinct scalars have distinct
agreement sets (`witness_gamma_injective_poly`, `deg g ≤ D_def < w`); the
TELESCOPE (`window_pair_telescope`) forces distinct scalars' complements to
share at most `D_def` points; complements have size ≥ `w − D_def > D_def`; the
`(D_def+1)`-subset Fisher count (`pairwise_inter_le_subsets_card_le`) closes.

Specializations: `D_def = 0` recovers the pencil-row shape (`≤ n/w`-order);
`D_def = 1` the slack-1 row.  At fixed `D_def` and growing `w` the bound is
`≈ 3^{D_def+1}` — inside the `WindowRationalBounded` budget `w + 3` on the top
`Θ(log w)` rows of the window.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The `(s+1)`-subset Fisher count**: members of size ≥ `m`, pairwise
intersecting in ≤ `s` points, inject their `(s+1)`-subsets into the domain's. -/
theorem pairwise_inter_le_subsets_card_le {𝒯 : Finset (Finset (Fin n))}
    {s m : ℕ} (hsm : s < m)
    (hcard : ∀ T ∈ 𝒯, m ≤ T.card)
    (hpair : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → (T₁ ∩ T₂).card ≤ s) :
    𝒯.card * Nat.choose m (s + 1) ≤ Nat.choose n (s + 1) := by
  classical
  have hinj : Set.InjOn
      (fun x : (Σ _T : Finset (Fin n), Finset (Fin n)) => x.2)
      (𝒯.sigma (fun T => T.powersetCard (s + 1))) := by
    rintro ⟨T₁, P⟩ h₁ ⟨T₂, Q⟩ h₂ (hPQ : P = Q)
    rw [Finset.mem_coe, Finset.mem_sigma] at h₁ h₂
    subst hPQ
    rcases eq_or_ne T₁ T₂ with rfl | hne
    · rfl
    · exfalso
      have hp₁ := Finset.mem_powersetCard.mp h₁.2
      have hp₂ := Finset.mem_powersetCard.mp h₂.2
      have hsub : P ⊆ T₁ ∩ T₂ :=
        Finset.subset_inter hp₁.1 hp₂.1
      have hge : s + 1 ≤ (T₁ ∩ T₂).card := by
        rw [← hp₁.2]
        exact Finset.card_le_card hsub
      have := hpair T₁ h₁.1 T₂ h₂.1 hne
      omega
  have hmaps : ∀ x ∈ (𝒯.sigma (fun T => T.powersetCard (s + 1)) :
      Finset (Σ _T : Finset (Fin n), Finset (Fin n))),
      (fun x : (Σ _T : Finset (Fin n), Finset (Fin n)) => x.2) x
        ∈ (Finset.univ.powersetCard (s + 1) :
            Finset (Finset (Fin n))) := by
    intro x hx
    rw [Finset.mem_sigma] at hx
    have hp := Finset.mem_powersetCard.mp hx.2
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hp.2⟩
  have hcard_le := Finset.card_le_card_of_injOn
    (fun x : (Σ _T : Finset (Fin n), Finset (Fin n)) => x.2)
    (fun x hx => Finset.mem_coe.mpr (hmaps x (Finset.mem_coe.mp hx)))
    hinj
  rw [Finset.card_sigma] at hcard_le
  have htarget : (Finset.univ.powersetCard (s + 1) :
      Finset (Finset (Fin n))).card = Nat.choose n (s + 1) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hterm : ∀ T ∈ 𝒯, Nat.choose m (s + 1)
      ≤ (T.powersetCard (s + 1)).card := by
    intro T hT
    rw [Finset.card_powersetCard]
    exact Nat.choose_le_choose _ (hcard T hT)
  calc 𝒯.card * Nat.choose m (s + 1)
      = ∑ _T ∈ 𝒯, Nat.choose m (s + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ T ∈ 𝒯, (T.powersetCard (s + 1)).card :=
        Finset.sum_le_sum hterm
    _ ≤ (Finset.univ.powersetCard (s + 1) :
        Finset (Finset (Fin n))).card := hcard_le
    _ = Nat.choose n (s + 1) := htarget

section Capstone

variable {dom : Fin n ↪ F} {w : ℕ}
variable {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}

open Classical in
/-- **THE PARAMETRIC WINDOW CAPSTONE.**  At every window row with
`2(3w − n) < w` (the top half of the window), a reduced-coprime doubly-rational
stack has at most `C(n, D+1)/C(w−D, D+1)` bad scalars, `D := 3w − n`. -/
theorem stratumG_window_badScalars_card_le
    (hw : 1 ≤ w) (hn2w : 2 * w < n) (htop : 2 * (3 * w - n) < w) (hnw : n ≤ 3 * w)
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
        * Nat.choose (w - (3 * w - n)) (3 * w - n + 1)
      ≤ Nat.choose n (3 * w - n + 1) := by
  classical
  set Ddef := 3 * w - n with hDdef
  set badSet := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hbadDef
  have hdata : ∀ γ ∈ badSet, ∃ (S : Finset (Fin n)) (g : F[X]) (p : F), g ≠ 0 ∧
      (n - w : ℕ) ≤ S.card ∧ g.natDegree + S.card ≤ 2 * w ∧
      (∀ i ∈ S, p = u₀ i + γ * u₁ i) ∧
      R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
        = g * vanishingPoly dom S :=
    fun γ hγ => witness_division_identity_window hw hrel₀ hrel₁
      hdℓ₀ hdR₀ hdℓ₁ hdR₁ hcop₀ hcopℓ hδn (Finset.mem_filter.mp hγ).2
  choose Sf gf pf hgne hSc hbud hag hid using hdata
  have hgdeg : ∀ γ (h : γ ∈ badSet), (gf γ h).natDegree ≤ Ddef := by
    intro γ h
    have h1 := hSc γ h
    have h2 := hbud γ h
    omega
  -- distinct scalars, distinct agreement sets
  have hinj : ∀ γ₁ (h₁ : γ₁ ∈ badSet) γ₂ (h₂ : γ₂ ∈ badSet),
      Sf γ₁ h₁ = Sf γ₂ h₂ → γ₁ = γ₂ := by
    intro γ₁ h₁ γ₂ h₂ hSeq
    have e₂ := hid γ₂ h₂
    rw [← hSeq] at e₂
    exact witness_gamma_injective_poly hG₀ (by omega) hℓ₁pos hcop₁
      (by rw [hdℓ₀]; exact lt_of_le_of_lt (hgdeg γ₁ h₁) (by omega))
      (by rw [hdℓ₀]; exact lt_of_le_of_lt (hgdeg γ₂ h₂) (by omega))
      (hid γ₁ h₁) e₂
  -- the telescope: distinct scalars' complements share at most D points
  have htel : ∀ γ₁ (h₁ : γ₁ ∈ badSet) γ₂ (h₂ : γ₂ ∈ badSet), γ₁ ≠ γ₂ →
      (((Sf γ₁ h₁)ᶜ ∩ (Sf γ₂ h₂)ᶜ : Finset (Fin n))).card ≤ Ddef := by
    intro γ₁ h₁ γ₂ h₂ hne
    by_contra hbig
    push_neg at hbig
    exact hne (window_pair_telescope hG₀ hdℓ₀ hw hn2w hℓ₁pos hcop₀ hcop₁ hcopℓ
      (hgne γ₁ h₁) (hgne γ₂ h₂) (hSc γ₁ h₁) (hSc γ₂ h₂)
      (hbud γ₁ h₁) (hbud γ₂ h₂) (hid γ₁ h₁) (hid γ₂ h₂) (by omega))
  -- the complement family
  set Tmap : {γ // γ ∈ badSet} → Finset (Fin n) :=
    fun x => ((Sf x.1 x.2)ᶜ : Finset (Fin n)) with hTmap
  have hTinj : Set.InjOn Tmap badSet.attach := by
    intro x _ y _ hxy
    exact Subtype.ext (hinj _ _ _ _ (compl_injective hxy))
  set 𝒯 := badSet.attach.image Tmap with h𝒯
  have hcardeq : 𝒯.card = badSet.card := by
    rw [h𝒯, Finset.card_image_of_injOn hTinj, Finset.card_attach]
  -- sizes: complements have ≥ w − D points
  have hsizes : ∀ T ∈ 𝒯, w - Ddef ≤ T.card := by
    intro T hT
    rw [h𝒯, Finset.mem_image] at hT
    obtain ⟨x, -, rfl⟩ := hT
    have h1 := hSc x.1 x.2
    have h2 := hbud x.1 x.2
    have hcc : (Tmap x).card = n - (Sf x.1 x.2).card := by
      rw [hTmap, Finset.card_compl, Fintype.card_fin]
    have hSn : (Sf x.1 x.2).card ≤ n := by
      have := Finset.card_le_univ (Sf x.1 x.2)
      rwa [Fintype.card_fin] at this
    omega
  -- pairwise ≤ D
  have hpairs : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → (T₁ ∩ T₂).card ≤ Ddef := by
    intro T₁ hT₁ T₂ hT₂ hne
    rw [h𝒯, Finset.mem_image] at hT₁ hT₂
    obtain ⟨x, -, rfl⟩ := hT₁
    obtain ⟨y, -, rfl⟩ := hT₂
    have hγne : x.1 ≠ y.1 := fun h => hne (by rw [Subtype.ext h])
    exact htel x.1 x.2 y.1 y.2 hγne
  -- Fisher
  have hfisher := pairwise_inter_le_subsets_card_le
    (s := Ddef) (m := w - Ddef) (by omega) hsizes hpairs
  rw [hcardeq] at hfisher
  exact hfisher

end Capstone

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.pairwise_inter_le_subsets_card_le
#print axioms ProximityGap.WBPencil.stratumG_window_badScalars_card_le
