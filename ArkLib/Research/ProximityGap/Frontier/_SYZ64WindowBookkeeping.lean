/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Research.ProximityGap.Frontier._SYZ63ExchangeStep

/-!
# SYZ64 — the window bookkeeping: the μ-basis window isomorphism, discharged

SYZ63 discharged the graded leading-vector exchange step unconditionally: the syzygy kernel of a
coprime triple is the `K[X]`-span of a degree-minimal (μ-)basis `(e₁, e₂)` (`syzygyKernel_muBasis_span`).
SYZ60 reduced `SYZ44.TwoRamp` (the two-ramp Hilbert shape) to the single named residual
`SYZ60.MuBasisWindowIso` — a windowed `K`-dimension count.

**This file discharges `MuBasisWindowIso` for the syzygy kernel, unconditionally and axiom-clean.**

## The window isomorphism

Fix weights `d` and a rank-`2` submodule `N ⊆ K[X]³` with degree-minimal μ-basis `(e₁, e₂)` of
product-degrees `n₁ ≤ n₂` (SYZ63's selection). The core structural fact is the **no-cancellation
lemma** (`pdeg_pair_combo_eq`): because the leading vectors `lv d n₁ e₁`, `lv d n₂ e₂` are
`K`-independent, the top terms of `q₁ • e₁` and `q₂ • e₂` never cancel, so

  `pdeg d (q₁ • e₁ + q₂ • e₂) = max (pdeg d (q₁ • e₁)) (pdeg d (q₂ • e₂))`.

Two consequences:

* **Injectivity.** `q₁ • e₁ + q₂ • e₂ = 0 ⟹ q₁ = q₂ = 0` (`eq_zero_of_combo_eq_zero`).
* **Degree control.** every element `w` of the degree-`D` kernel window is `q₁ • e₁ + q₂ • e₂` with
  `pdeg (qᵢ • eᵢ) ≤ pdeg w ≤ D` — no representation can exceed the window.

The `K`-linear map `Φ_D : degreeLT (D+1−n₁) × degreeLT (D+1−n₂) → K_D`,
`(q₁, q₂) ↦ q₁ • e₁ + q₂ • e₂`, is therefore injective (no-cancellation) and surjective onto the
window `K_D := {w ∈ N : pdeg d w ≤ D}` (span generation + degree control). Hence

  `finrank K K_D = finrank K (domain) = (D+1−n₁) + (D+1−n₂)`   (`finrank_windowKD`).

That is exactly `SYZ60.MuBasisWindowIso K (fun D => finrank K K_D) n₁ n₂`, so the two-ramp Hilbert
shape `SYZ44.TwoRamp` holds unconditionally for the syzygy kernel (`twoRamp_windowKD`).

## Scrupulous honesty — scope

This lands **`TwoRamp` unconditionally** for the coprime-triple syzygy kernel (the μ-basis
window-count black box (b)/(c) is now proved theory, no longer a hypothesis). It does **not**
discharge `SYZ44.RankNullity` — the *degree-controlled Bézout surjectivity* onto `{p : deg p ≤ D}`
for the balanced window — which remains a separate named residual (SYZ57 provides only the ungraded
Bézout seed, without degree control). So the degree-sum law `n₁ + n₂ = d₀ + d₁ + d₂`
(`degree_sum_of_rankNullity`) is proved here **conditional on `RankNullity` alone**: `TwoRamp` is
discharged, `RankNullity` is the single remaining structural input. This does **not** claim δ*
closure, and the imbalance bound `ι ≤ 1` remains the open balance input downstream.

Axiom-clean; `#print axioms` at the bottom. No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Module Polynomial
open ArkLib.ProximityGap.SYZ62
open ArkLib.ProximityGap.SYZ63
open scoped Cardinal

namespace ArkLib.ProximityGap.SYZ64

variable {K : Type*} [Field K]

/-! ## 1. The no-cancellation lemma -/

variable {d : Fin 3 → ℕ}

/-- **Leading vector of a monomial-shifted generator at a target degree.**  For `pdeg d e = n` and any
target `M ≥ pdeg d (q • e)`, the leading vector of `q • e` at `M` is `leadingCoeff q • lv d n e` when
`q • e` attains `M`, and `0` otherwise. -/
theorem lv_smul_at (q : K[X]) {e : Fin 3 → K[X]} {n : ℕ} (hpe : pdeg d e = (n : WithBot ℕ))
    {M : ℕ} (hle : pdeg d (q • e) ≤ (M : WithBot ℕ)) :
    lv d M (q • e)
      = (if pdeg d (q • e) = (M : WithBot ℕ) then q.leadingCoeff else 0) • lv d n e := by
  by_cases hcase : pdeg d (q • e) = (M : WithBot ℕ)
  · -- attaining
    have hqne : q ≠ 0 := by
      intro h0
      rw [h0, zero_smul, pdeg_zero] at hcase
      exact (WithBot.bot_ne_coe).elim hcase
    have hval : q.natDegree + n = M := by
      have hh : pdeg d (q • e) = q.degree + (n : WithBot ℕ) := by rw [pdeg_smul, hpe]
      rw [hh, degree_eq_natDegree hqne, ← Nat.cast_add] at hcase
      exact Nat.cast_inj.mp hcase
    have hshift := lv_smul_top (d := d) (q := q) hqne hpe
    rw [hval] at hshift
    rw [hshift, if_pos hcase]
  · -- not attaining
    have hlt : pdeg d (q • e) < (M : WithBot ℕ) := lt_of_le_of_ne hle hcase
    rw [lv_eq_zero_of_pdeg_lt d M (q • e) hlt, if_neg hcase, zero_smul]

/-- **No cancellation of leading terms.**  When the two leading vectors are `K`-independent, the
product-degree of `q₁ • e₁ + q₂ • e₂` is the max of the two per-term product-degrees: the top terms
never cancel. -/
theorem pdeg_combo_ge {e₁ e₂ : Fin 3 → K[X]} {n₁ n₂ : ℕ}
    (hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ)) (hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ))
    (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂]) (q₁ q₂ : K[X]) :
    max (pdeg d (q₁ • e₁)) (pdeg d (q₂ • e₂)) ≤ pdeg d (q₁ • e₁ + q₂ • e₂) := by
  by_contra hlt
  push_neg at hlt
  set A : WithBot ℕ := pdeg d (q₁ • e₁) with hA
  set B : WithBot ℕ := pdeg d (q₂ • e₂) with hB
  -- max A B ≠ ⊥ (else it would be ≤ anything)
  have hM'ne : max A B ≠ ⊥ := by
    intro h
    rw [h] at hlt
    exact absurd hlt (not_lt_bot)
  obtain ⟨M, hM⟩ := WithBot.ne_bot_iff_exists.mp hM'ne
  rw [← Nat.cast_withBot] at hM
  have hMeq : max A B = (M : WithBot ℕ) := hM.symm
  have hltM : pdeg d (q₁ • e₁ + q₂ • e₂) < (M : WithBot ℕ) := hMeq ▸ hlt
  have hleA : A ≤ (M : WithBot ℕ) := hMeq ▸ le_max_left A B
  have hleB : B ≤ (M : WithBot ℕ) := hMeq ▸ le_max_right A B
  -- lv d M of the sum vanishes
  have hlv0 : lv d M (q₁ • e₁ + q₂ • e₂) = 0 := lv_eq_zero_of_pdeg_lt d M _ hltM
  rw [lv_add] at hlv0
  rw [lv_smul_at q₁ hpd₁ hleA, lv_smul_at q₂ hpd₂ hleB] at hlv0
  set γ₁ : K := if A = (M : WithBot ℕ) then q₁.leadingCoeff else 0 with hγ₁
  set γ₂ : K := if B = (M : WithBot ℕ) then q₂.leadingCoeff else 0 with hγ₂
  -- independence forces γ₁ = γ₂ = 0
  have hpairγ := (LinearIndependent.pair_iff.mp hpair) γ₁ γ₂ hlv0
  obtain ⟨hγ₁0, hγ₂0⟩ := hpairγ
  -- but max A B = M forces one of A, B to equal M, giving a nonzero leadingCoeff
  have hchoice : A = (M : WithBot ℕ) ∨ B = (M : WithBot ℕ) := by
    rcases max_choice A B with h | h
    · left; rw [← h, hMeq]
    · right; rw [← h, hMeq]
  rcases hchoice with hAeq | hBeq
  · have hq₁ne : q₁ ≠ 0 := by
      intro h0
      rw [hA, h0, zero_smul, pdeg_zero] at hAeq
      exact (WithBot.bot_ne_coe).elim hAeq
    have : γ₁ = q₁.leadingCoeff := by rw [hγ₁, if_pos hAeq]
    exact (leadingCoeff_ne_zero.mpr hq₁ne) (this ▸ hγ₁0)
  · have hq₂ne : q₂ ≠ 0 := by
      intro h0
      rw [hB, h0, zero_smul, pdeg_zero] at hBeq
      exact (WithBot.bot_ne_coe).elim hBeq
    have : γ₂ = q₂.leadingCoeff := by rw [hγ₂, if_pos hBeq]
    exact (leadingCoeff_ne_zero.mpr hq₂ne) (this ▸ hγ₂0)

/-- The product-degree of a pair combination is exactly the max of the two per-term degrees. -/
theorem pdeg_combo_eq {e₁ e₂ : Fin 3 → K[X]} {n₁ n₂ : ℕ}
    (hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ)) (hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ))
    (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂]) (q₁ q₂ : K[X]) :
    pdeg d (q₁ • e₁ + q₂ • e₂) = max (pdeg d (q₁ • e₁)) (pdeg d (q₂ • e₂)) :=
  le_antisymm (pdeg_add_le d _ _) (pdeg_combo_ge hpd₁ hpd₂ hpair q₁ q₂)

/-- **Injectivity of the pair combination.**  A vanishing `K[X]`-combination of the two independent
generators has both coefficients zero. -/
theorem eq_zero_of_combo_eq_zero {e₁ e₂ : Fin 3 → K[X]} {n₁ n₂ : ℕ}
    (hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ)) (hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ))
    (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂]) {q₁ q₂ : K[X]}
    (h : q₁ • e₁ + q₂ • e₂ = 0) : q₁ = 0 ∧ q₂ = 0 := by
  have hmax : max (pdeg d (q₁ • e₁)) (pdeg d (q₂ • e₂)) = ⊥ := by
    have hge := pdeg_combo_ge hpd₁ hpd₂ hpair q₁ q₂
    rw [h, pdeg_zero] at hge
    exact le_bot_iff.mp hge
  have h1 : pdeg d (q₁ • e₁) = ⊥ := le_bot_iff.mp (le_trans (le_max_left _ _) (le_of_eq hmax))
  have h2 : pdeg d (q₂ • e₂) = ⊥ := le_bot_iff.mp (le_trans (le_max_right _ _) (le_of_eq hmax))
  constructor
  · rw [pdeg_smul, hpd₁, WithBot.add_eq_bot] at h1
    rcases h1 with hb | hb
    · exact degree_eq_bot.mp hb
    · exact absurd hb (WithBot.natCast_ne_bot n₁)
  · rw [pdeg_smul, hpd₂, WithBot.add_eq_bot] at h2
    rcases h2 with hb | hb
    · exact degree_eq_bot.mp hb
    · exact absurd hb (WithBot.natCast_ne_bot n₂)

/-! ## 2. The μ-basis data with full structure (delegated to SYZ63) -/

/-- **The degree-minimal μ-basis, with all structural data.**  Re-export of the canonical
`SYZ63.exists_muBasisData` (the selection argument lives only there): for any rank-`2` submodule
`N ⊆ K[X]³` and weights `d`, there is a degree-minimal pair `(e₁, e₂)` of members with
product-degrees `n₁ ≤ n₂`, `K`-independent leading vectors, generating `N`. -/
theorem exists_muBasisData (d : Fin 3 → ℕ) (N : Submodule K[X] (Fin 3 → K[X]))
    (hrank : Module.rank K[X] N = 2) :
    ∃ (e₁ e₂ : Fin 3 → K[X]) (n₁ n₂ : ℕ),
      e₁ ∈ N ∧ e₂ ∈ N ∧
      pdeg d e₁ = (n₁ : WithBot ℕ) ∧ pdeg d e₂ = (n₂ : WithBot ℕ) ∧ n₁ ≤ n₂ ∧
      LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂] ∧
      N = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X])) :=
  SYZ63.exists_muBasisData d N hrank

/-! ## 3. The degree-`D` kernel window as a `K`-submodule -/

/-- **The degree-`D` window** `K_D = {w ∈ N : pdeg d w ≤ D}` as a `K`-submodule of `K[X]³`. -/
noncomputable def windowKD (d : Fin 3 → ℕ) (N : Submodule K[X] (Fin 3 → K[X])) (D : ℕ) :
    Submodule K (Fin 3 → K[X]) where
  carrier := {w | w ∈ N ∧ pdeg d w ≤ (D : WithBot ℕ)}
  add_mem' := by
    rintro a b ⟨haN, hade⟩ ⟨hbN, hbde⟩
    exact ⟨N.add_mem haN hbN, le_trans (pdeg_add_le d a b) (max_le hade hbde)⟩
  zero_mem' := ⟨N.zero_mem, by rw [pdeg_zero]; exact bot_le⟩
  smul_mem' := by
    rintro c w ⟨hwN, hwde⟩
    have hcw : c • w = (C c) • w := by
      rw [← Polynomial.algebraMap_eq]; exact (algebraMap_smul K[X] c w).symm
    refine ⟨?_, ?_⟩
    · rw [hcw]; exact N.smul_mem _ hwN
    · rw [hcw, pdeg_smul]
      calc (C c).degree + pdeg d w ≤ 0 + pdeg d w := by gcongr; exact degree_C_le
        _ = pdeg d w := by rw [zero_add]
        _ ≤ (D : WithBot ℕ) := hwde

@[simp] theorem mem_windowKD {d : Fin 3 → ℕ} {N : Submodule K[X] (Fin 3 → K[X])} {D : ℕ}
    {w : Fin 3 → K[X]} : w ∈ windowKD d N D ↔ w ∈ N ∧ pdeg d w ≤ (D : WithBot ℕ) := Iff.rfl

/-! ## 4. The window isomorphism and the finrank computation -/

/-- Membership witness for the domain window from a per-term product-degree bound. -/
theorem mem_degreeLT_of_pdeg_le {a : K[X]} {n D : ℕ}
    (hle : a.degree + (n : WithBot ℕ) ≤ (D : WithBot ℕ)) : a ∈ degreeLT K (D + 1 - n) := by
  rw [mem_degreeLT]
  rcases eq_or_ne a 0 with h0 | h0
  · rw [h0, degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree h0] at hle ⊢
    rw [← Nat.cast_add, Nat.cast_le] at hle
    rw [Nat.cast_lt]
    omega

/-- **The window isomorphism finrank identity (main deliverable).**  Given the μ-basis data, the
degree-`D` kernel window `K_D` has `K`-dimension `(D+1−n₁) + (D+1−n₂)`. -/
theorem finrank_windowKD {d : Fin 3 → ℕ} {N : Submodule K[X] (Fin 3 → K[X])}
    {e₁ e₂ : Fin 3 → K[X]} {n₁ n₂ : ℕ}
    (hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ)) (hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ))
    (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂])
    (hspan : N = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X]))) (D : ℕ) :
    finrank K (windowKD d N D) = (D + 1 - n₁) + (D + 1 - n₂) := by
  -- The K-linear combination map on the product of degree windows.
  set g₁ : K[X] →ₗ[K] (Fin 3 → K[X]) :=
    (LinearMap.toSpanSingleton K[X] (Fin 3 → K[X]) e₁).restrictScalars K with hg₁
  set g₂ : K[X] →ₗ[K] (Fin 3 → K[X]) :=
    (LinearMap.toSpanSingleton K[X] (Fin 3 → K[X]) e₂).restrictScalars K with hg₂
  set F : (degreeLT K (D + 1 - n₁) × degreeLT K (D + 1 - n₂)) →ₗ[K] (Fin 3 → K[X]) :=
    (g₁ ∘ₗ (degreeLT K (D + 1 - n₁)).subtype ∘ₗ LinearMap.fst K _ _) +
      (g₂ ∘ₗ (degreeLT K (D + 1 - n₂)).subtype ∘ₗ LinearMap.snd K _ _) with hF
  have hFapply : ∀ p : (degreeLT K (D + 1 - n₁) × degreeLT K (D + 1 - n₂)),
      F p = (p.1 : K[X]) • e₁ + (p.2 : K[X]) • e₂ := by
    intro p
    simp only [hF, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.subtype_apply, hg₁, hg₂, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply]
  -- Injectivity from no-cancellation.
  have hInj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hFapply] at hp
    obtain ⟨h1, h2⟩ := eq_zero_of_combo_eq_zero hpd₁ hpd₂ hpair hp
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using h1
    · simpa using h2
  -- Range equals the window.
  have hRange : LinearMap.range F = windowKD d N D := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hFapply]
      have he₁N : e₁ ∈ N := hspan ▸ Submodule.subset_span (by simp)
      have he₂N : e₂ ∈ N := hspan ▸ Submodule.subset_span (by simp)
      refine ⟨N.add_mem (N.smul_mem _ he₁N) (N.smul_mem _ he₂N), ?_⟩
      refine le_trans (pdeg_add_le d _ _) (max_le ?_ ?_)
      · rw [pdeg_smul, hpd₁]
        have hmem := p.1.2
        rw [mem_degreeLT] at hmem
        rcases eq_or_ne (p.1 : K[X]) 0 with h0 | h0
        · rw [h0, degree_zero]; simp
        · rw [degree_eq_natDegree h0] at hmem ⊢
          rw [← Nat.cast_add, Nat.cast_le]
          rw [Nat.cast_lt] at hmem
          omega
      · rw [pdeg_smul, hpd₂]
        have hmem := p.2.2
        rw [mem_degreeLT] at hmem
        rcases eq_or_ne (p.2 : K[X]) 0 with h0 | h0
        · rw [h0, degree_zero]; simp
        · rw [degree_eq_natDegree h0] at hmem ⊢
          rw [← Nat.cast_add, Nat.cast_le]
          rw [Nat.cast_lt] at hmem
          omega
    · intro w hw
      rw [mem_windowKD] at hw
      obtain ⟨hwN, hwde⟩ := hw
      rw [hspan, Submodule.mem_span_pair] at hwN
      obtain ⟨a, b, hab⟩ := hwN
      -- degree control from no-cancellation
      have hcombo := pdeg_combo_ge hpd₁ hpd₂ hpair a b
      rw [hab] at hcombo
      have hale : pdeg d (a • e₁) ≤ (D : WithBot ℕ) :=
        le_trans (le_trans (le_max_left _ _) hcombo) hwde
      have hble : pdeg d (b • e₂) ≤ (D : WithBot ℕ) :=
        le_trans (le_trans (le_max_right _ _) hcombo) hwde
      rw [pdeg_smul, hpd₁] at hale
      rw [pdeg_smul, hpd₂] at hble
      refine ⟨(⟨a, mem_degreeLT_of_pdeg_le hale⟩, ⟨b, mem_degreeLT_of_pdeg_le hble⟩), ?_⟩
      rw [hFapply]
      exact hab
  -- Compute the finrank.
  have hfr := LinearMap.finrank_range_of_inj hInj
  rw [hRange] at hfr
  rw [hfr, Module.finrank_prod,
    ArkLib.ProximityGap.SYZ60.finrank_degreeLT K (D + 1 - n₁),
    ArkLib.ProximityGap.SYZ60.finrank_degreeLT K (D + 1 - n₂)]

/-! ## 5. `MuBasisWindowIso` and `TwoRamp`, discharged for the syzygy kernel -/

/-- **`MuBasisWindowIso` discharged.**  For the syzygy kernel of a coprime triple and weights `d`,
the windowed dimension `fun D => finrank K K_D` realises the graded pair-window count of the μ-basis
degrees `n₁, n₂` — the exact residual `SYZ60.MuBasisWindowIso`. -/
theorem muBasisWindowIso_windowKD {d : Fin 3 → ℕ} {N : Submodule K[X] (Fin 3 → K[X])}
    {e₁ e₂ : Fin 3 → K[X]} {n₁ n₂ : ℕ}
    (hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ)) (hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ))
    (hpair : LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂])
    (hspan : N = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X]))) :
    ArkLib.ProximityGap.SYZ60.MuBasisWindowIso K (fun D => finrank K (windowKD d N D)) n₁ n₂ := by
  intro D
  show finrank K (windowKD d N D) = _
  rw [finrank_windowKD hpd₁ hpd₂ hpair hspan D]
  exact (ArkLib.ProximityGap.SYZ60.finrank_pair_window K n₁ n₂ D).symm

/-- **`TwoRamp` discharged (unconditional).**  The windowed kernel dimension of the syzygy kernel of
a coprime triple has the two-ramp shape with the μ-basis degrees — no longer a named hypothesis. -/
theorem twoRamp_windowKD {d : Fin 3 → ℕ} {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    ∃ n₁ n₂ : ℕ, n₁ ≤ n₂ ∧
      ArkLib.ProximityGap.SYZ44.TwoRamp
        (fun D => finrank K (windowKD d (LinearMap.ker (SYZ61.syzygyMap f g h)) D)) n₁ n₂ := by
  obtain ⟨e₁, e₂, n₁, n₂, _, _, hpd₁, hpd₂, hn₁₂, hpair, hspan⟩ :=
    exists_muBasisData d (LinearMap.ker (SYZ61.syzygyMap f g h))
      (SYZ61.rank_syzygyKernel hfg hfh)
  refine ⟨n₁, n₂, hn₁₂, ?_⟩
  exact ArkLib.ProximityGap.SYZ60.twoRamp_of_muBasisWindowIso K _ n₁ n₂
    (muBasisWindowIso_windowKD hpd₁ hpd₂ hpair hspan)

/-! ## 6. The degree-sum law, conditional on `RankNullity` alone -/

/-- **The degree-sum law, conditional on `RankNullity` alone.**  `TwoRamp` is now discharged
(`twoRamp_windowKD`); granting the remaining Bézout-surjectivity input `RankNullity` for the same
windowed dimension, there is a μ-basis `(e₁, e₂)` of the syzygy kernel — members of the kernel,
of product-degrees `pdeg d eᵢ = nᵢ` with `n₁ ≤ n₂`, `K`-independent leading vectors, generating
the kernel — whose degrees satisfy `n₁ + n₂ = d₀ + d₁ + d₂`.  (The μ-basis data is exported so
that the degree-sum equation is tied to the kernel, not a bare existential over `ℕ`.) -/
theorem degree_sum_of_rankNullity {d : Fin 3 → ℕ} {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) (D₀ : ℕ)
    (hRankNull : ArkLib.ProximityGap.SYZ44.RankNullity
      (fun D => finrank K (windowKD d (LinearMap.ker (SYZ61.syzygyMap f g h)) D))
      (d 0) (d 1) (d 2) D₀) :
    ∃ (e₁ e₂ : Fin 3 → K[X]) (n₁ n₂ : ℕ),
      e₁ ∈ LinearMap.ker (SYZ61.syzygyMap f g h) ∧ e₂ ∈ LinearMap.ker (SYZ61.syzygyMap f g h) ∧
      pdeg d e₁ = (n₁ : WithBot ℕ) ∧ pdeg d e₂ = (n₂ : WithBot ℕ) ∧ n₁ ≤ n₂ ∧
      LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂] ∧
      LinearMap.ker (SYZ61.syzygyMap f g h) = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X])) ∧
      n₁ + n₂ = d 0 + d 1 + d 2 := by
  obtain ⟨e₁, e₂, n₁, n₂, he₁, he₂, hpd₁, hpd₂, hn₁₂, hpair, hspan⟩ :=
    exists_muBasisData d (LinearMap.ker (SYZ61.syzygyMap f g h))
      (SYZ61.rank_syzygyKernel hfg hfh)
  refine ⟨e₁, e₂, n₁, n₂, he₁, he₂, hpd₁, hpd₂, hn₁₂, hpair, hspan, ?_⟩
  have hTwoRamp : ArkLib.ProximityGap.SYZ44.TwoRamp
      (fun D => finrank K (windowKD d (LinearMap.ker (SYZ61.syzygyMap f g h)) D)) n₁ n₂ :=
    ArkLib.ProximityGap.SYZ60.twoRamp_of_muBasisWindowIso K _ n₁ n₂
      (muBasisWindowIso_windowKD hpd₁ hpd₂ hpair hspan)
  exact ArkLib.ProximityGap.SYZ44.degree_sum_of_hilbert _ (d 0) (d 1) (d 2) n₁ n₂ D₀
    hRankNull hTwoRamp

end ArkLib.ProximityGap.SYZ64

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.SYZ64.pdeg_combo_eq
#print axioms ArkLib.ProximityGap.SYZ64.eq_zero_of_combo_eq_zero
#print axioms ArkLib.ProximityGap.SYZ64.exists_muBasisData
#print axioms ArkLib.ProximityGap.SYZ64.finrank_windowKD
#print axioms ArkLib.ProximityGap.SYZ64.muBasisWindowIso_windowKD
#print axioms ArkLib.ProximityGap.SYZ64.twoRamp_windowKD
#print axioms ArkLib.ProximityGap.SYZ64.degree_sum_of_rankNullity
