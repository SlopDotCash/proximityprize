/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ63ExchangeStep

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

/-! ## 2. The μ-basis data with full structure (re-derives SYZ63's selection) -/

/-- **The degree-minimal μ-basis, with all structural data.**  A richer form of SYZ63's
`exists_gradedExchange`: for any rank-`2` submodule `N ⊆ K[X]³` and weights `d`, there is a
degree-minimal pair `(e₁, e₂)` of members with product-degrees `n₁ ≤ n₂`, `K`-independent leading
vectors, generating `N`. -/
theorem exists_muBasisData (d : Fin 3 → ℕ) (N : Submodule K[X] (Fin 3 → K[X]))
    (hrank : Module.rank K[X] N = 2) :
    ∃ (e₁ e₂ : Fin 3 → K[X]) (n₁ n₂ : ℕ),
      e₁ ∈ N ∧ e₂ ∈ N ∧
      pdeg d e₁ = (n₁ : WithBot ℕ) ∧ pdeg d e₂ = (n₂ : WithBot ℕ) ∧ n₁ ≤ n₂ ∧
      LinearIndependent K ![lv d n₁ e₁, lv d n₂ e₂] ∧
      N = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X])) := by
  -- N ≠ ⊥
  have hNbot : N ≠ ⊥ := by
    intro h; rw [h] at hrank; simp [rank_bot] at hrank
  obtain ⟨x₀, hx₀N, hx₀ne⟩ := (Submodule.ne_bot_iff N).mp hNbot
  have hwf : WellFounded ((· < ·) : WithBot ℕ → WithBot ℕ → Prop) := wellFounded_lt
  -- (1) minimal nonzero e₁
  set S₁ : Set (WithBot ℕ) := (fun w => pdeg d w) '' {w | w ∈ N ∧ w ≠ 0} with hS₁
  have hS₁ne : S₁.Nonempty := ⟨pdeg d x₀, x₀, ⟨hx₀N, hx₀ne⟩, rfl⟩
  obtain ⟨v₁, hv₁S, hv₁min⟩ := hwf.has_min S₁ hS₁ne
  obtain ⟨e₁, ⟨he₁N, he₁ne⟩, he₁pd⟩ := hv₁S
  have hmin₁ : ∀ w ∈ N, w ≠ 0 → v₁ ≤ pdeg d w := by
    intro w hwN hwne
    by_contra hlt
    push_neg at hlt
    exact hv₁min (pdeg d w) ⟨w, ⟨hwN, hwne⟩, rfl⟩ hlt
  -- span{e₁} ≠ N
  have hexists₂ : ∃ w ∈ N, w ∉ Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X])) := by
    by_contra hall
    push_neg at hall
    have hle : N ≤ Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X])) := hall
    have h1 : Module.rank K[X] (N : Submodule K[X] _)
        ≤ Module.rank K[X] (Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X]))) :=
      Submodule.rank_mono (R := K[X]) hle
    have h2 : Module.rank K[X] (Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X]))) ≤ 1 := by
      have hh := rank_span_le (R := K[X]) ({e₁} : Set (Fin 3 → K[X]))
      rwa [Cardinal.mk_singleton] at hh
    rw [hrank] at h1
    exact absurd (le_trans h1 h2) (by norm_num)
  -- (2) minimal e₂ outside span{e₁}
  set S₂ : Set (WithBot ℕ) :=
    (fun w => pdeg d w) '' {w | w ∈ N ∧ w ∉ Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X]))} with hS₂
  have hS₂ne : S₂.Nonempty := by
    obtain ⟨w, hwN, hwout⟩ := hexists₂
    exact ⟨pdeg d w, w, ⟨hwN, hwout⟩, rfl⟩
  obtain ⟨v₂, hv₂S, hv₂min⟩ := hwf.has_min S₂ hS₂ne
  obtain ⟨e₂, ⟨he₂N, he₂out⟩, he₂pd⟩ := hv₂S
  have he₂ne : e₂ ≠ 0 := by
    intro h0; apply he₂out; rw [h0]; exact Submodule.zero_mem _
  have hmin₂ : ∀ w ∈ N, w ∉ Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X])) → v₂ ≤ pdeg d w := by
    intro w hwN hwout
    by_contra hlt
    push_neg at hlt
    exact hv₂min (pdeg d w) ⟨w, ⟨hwN, hwout⟩, rfl⟩ hlt
  -- naturals n₁ ≤ n₂
  have hv₁ne : v₁ ≠ ⊥ := by rw [← he₁pd]; exact pdeg_ne_bot_of_ne_zero he₁ne
  have hv₂ne : v₂ ≠ ⊥ := by rw [← he₂pd]; exact pdeg_ne_bot_of_ne_zero he₂ne
  obtain ⟨n₁, hn₁⟩ := WithBot.ne_bot_iff_exists.mp hv₁ne
  obtain ⟨n₂, hn₂⟩ := WithBot.ne_bot_iff_exists.mp hv₂ne
  have hv₁eq : v₁ = (n₁ : WithBot ℕ) := hn₁.symm
  have hv₂eq : v₂ = (n₂ : WithBot ℕ) := hn₂.symm
  have hpd₁ : pdeg d e₁ = (n₁ : WithBot ℕ) := he₁pd.trans hv₁eq
  have hpd₂ : pdeg d e₂ = (n₂ : WithBot ℕ) := he₂pd.trans hv₂eq
  have hn₁₂ : n₁ ≤ n₂ := by
    have hle : v₁ ≤ pdeg d e₂ := hmin₁ e₂ he₂N he₂ne
    rw [hv₁eq, hpd₂] at hle
    exact Nat.cast_le.mp hle
  -- leading vectors
  set lc₁ : Fin 3 → K := lv d n₁ e₁ with hlc₁
  set lc₂ : Fin 3 → K := lv d n₂ e₂ with hlc₂
  have hlc₁ne : lc₁ ≠ 0 := lv_ne_zero_of_pdeg_eq hpd₁
  have hlc₂ne : lc₂ ≠ 0 := lv_ne_zero_of_pdeg_eq hpd₂
  -- lc₂ ∉ K·lc₁
  have hnotprop : ∀ c : K, c • lc₁ ≠ lc₂ := by
    intro c hc
    set q : K[X] := C c * X ^ (n₂ - n₁) with hq
    have hcne : c ≠ 0 := by
      rintro rfl; simp only [zero_smul] at hc; exact hlc₂ne hc.symm
    have hqne : q ≠ 0 := by
      rw [hq]; exact mul_ne_zero (by simpa using hcne) (pow_ne_zero _ X_ne_zero)
    have hqnd : q.natDegree = n₂ - n₁ := by
      rw [hq, natDegree_C_mul (by simpa using hcne), natDegree_X_pow]
    have hqlead : q.leadingCoeff = c := by
      rw [hq, leadingCoeff_mul, leadingCoeff_X_pow, mul_one, leadingCoeff_C]
    have hpdq : pdeg d (q • e₁) = (n₂ : WithBot ℕ) := by
      rw [pdeg_smul, hpd₁, degree_eq_natDegree hqne, hqnd, ← Nat.cast_add]
      congr 1; omega
    have hlvq : lv d n₂ (q • e₁) = c • lc₁ := by
      have := lv_smul_top (d := d) (q := q) hqne hpd₁
      rw [hqnd] at this
      have hidx : n₂ - n₁ + n₁ = n₂ := by omega
      rw [hidx] at this
      rw [this, hqlead, hlc₁]
    set e₂' : Fin 3 → K[X] := e₂ - q • e₁ with he₂'
    have he₂'N : e₂' ∈ N := N.sub_mem he₂N (N.smul_mem _ he₁N)
    have he₂'out : e₂' ∉ Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X])) := by
      intro hmem
      apply he₂out
      have : e₂ = e₂' + q • e₁ := by rw [he₂']; ring
      rw [this]
      exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hlv0 : lv d n₂ e₂' = 0 := by
      rw [he₂', show e₂ - q • e₁ = e₂ + (-1 : K) • (q • e₁) by rw [neg_one_smul]; ring]
      rw [lv_add, lv_smulK, hlvq, ← hlc₂]
      rw [← hc]
      simp
    have hpdle : pdeg d e₂' ≤ (n₂ : WithBot ℕ) := by
      rw [he₂']
      calc pdeg d (e₂ - q • e₁) = pdeg d (e₂ + (-1 : K[X]) • (q • e₁)) := by
              congr 1; rw [neg_one_smul]; ring
        _ ≤ max (pdeg d e₂) (pdeg d ((-1 : K[X]) • (q • e₁))) := pdeg_add_le d _ _
        _ ≤ (n₂ : WithBot ℕ) := by
              apply max_le
              · rw [hpd₂]
              · rw [pdeg_smul, hpdq]; simp
    have hdrop : pdeg d e₂' < (n₂ : WithBot ℕ) := pdeg_lt_of_lv_eq_zero hpdle hlv0
    have hge := hmin₂ e₂' he₂'N he₂'out
    rw [hv₂eq] at hge
    exact absurd (lt_of_le_of_lt hge hdrop) (lt_irrefl _)
  -- K-independence of lc₁, lc₂
  have hpair : LinearIndependent K ![lc₁, lc₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      simp only [zero_smul, add_zero] at hst
      have : s = 0 := by
        rcases eq_or_ne s 0 with h | h
        · exact h
        · exact absurd ((smul_eq_zero.mp hst).resolve_left h) hlc₁ne
      exact ⟨this, rfl⟩
    · exfalso
      apply hnotprop (-(t⁻¹ * s))
      have hts : t • lc₂ = -(s • lc₁) := eq_neg_of_add_eq_zero_right hst
      have h1 : (-(t⁻¹ * s)) • lc₁ = t⁻¹ • (-(s • lc₁)) := by
        rw [neg_smul, mul_smul, ← smul_neg]
      rw [h1, ← hts, smul_smul, inv_mul_cancel₀ ht, one_smul]
  -- GradedExchange for e₁, e₂ (⟹ span)
  have hex : GradedExchange (d := d) N e₁ e₂ := by
    intro w hwN hwne
    by_cases hwspan : w ∈ Submodule.span K[X] ({e₁} : Set (Fin 3 → K[X]))
    · rw [Submodule.mem_span_singleton] at hwspan
      obtain ⟨a, ha⟩ := hwspan
      refine ⟨a, 0, ?_⟩
      rw [zero_smul, add_zero, ha, sub_self, pdeg_zero]
      exact bot_lt_iff_ne_bot.mpr (pdeg_ne_bot_of_ne_zero hwne)
    · obtain ⟨Dn, hDn⟩ := WithBot.ne_bot_iff_exists.mp (pdeg_ne_bot_of_ne_zero hwne)
      rw [← Nat.cast_withBot] at hDn
      have hpdw : pdeg d w = (Dn : WithBot ℕ) := hDn.symm
      have hD₂ : n₂ ≤ Dn := by
        have hge := hmin₂ w hwN hwspan
        rw [hv₂eq, hpdw] at hge
        exact Nat.cast_le.mp hge
      have hD₁ : n₁ ≤ Dn := le_trans hn₁₂ hD₂
      have hspan : ∃ c₁ c₂ : K, c₁ • lc₁ + c₂ • lc₂ = lv d Dn w := by
        by_contra hno
        push_neg at hno
        have htriple : LinearIndependent K (fun i => lv d (![n₁, n₂, Dn] i) (![e₁, e₂, w] i)) := by
          rw [Fintype.linearIndependent_iff]
          intro g hg
          rw [Fin.sum_univ_three] at hg
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons] at hg
          have hg' : g 0 • lc₁ + g 1 • lc₂ + g 2 • lv d Dn w = 0 := by
            rw [hlc₁, hlc₂]; exact hg
          rcases eq_or_ne (g 2) 0 with h2 | h2
          · rw [h2, zero_smul, add_zero] at hg'
            have := (LinearIndependent.pair_iff.mp hpair) (g 0) (g 1) hg'
            intro i; fin_cases i
            · exact this.1
            · exact this.2
            · exact h2
          · exfalso
            apply hno (-(g 2)⁻¹ * g 0) (-(g 2)⁻¹ * g 1)
            have hiso : g 2 • lv d Dn w = -(g 0 • lc₁ + g 1 • lc₂) :=
              eq_neg_of_add_eq_zero_right hg'
            have : lv d Dn w = (g 2)⁻¹ • (-(g 0 • lc₁ + g 1 • lc₂)) := by
              rw [← hiso, smul_smul, inv_mul_cancel₀ h2, one_smul]
            rw [this]; module
        exact no_three_independent_lv hrank ![e₁, e₂, w]
          (by intro i; fin_cases i <;> simpa using ‹_›)
          (by intro i; fin_cases i <;> simp_all)
          ![n₁, n₂, Dn]
          (by intro i; fin_cases i <;> simp_all)
          htriple
      obtain ⟨c₁, c₂, hc⟩ := hspan
      set q₁ : K[X] := C c₁ * X ^ (Dn - n₁) with hq₁
      set q₂ : K[X] := C c₂ * X ^ (Dn - n₂) with hq₂
      refine ⟨q₁, q₂, ?_⟩
      set r : Fin 3 → K[X] := w - (q₁ • e₁ + q₂ • e₂) with hr
      have hlvq : ∀ (c : K) (nⱼ : ℕ) (eⱼ : Fin 3 → K[X]),
          n₁ ≤ Dn → pdeg d eⱼ = (nⱼ : WithBot ℕ) → nⱼ ≤ Dn →
          lv d Dn ((C c * X ^ (Dn - nⱼ)) • eⱼ) = c • lv d nⱼ eⱼ := by
        intro c nⱼ eⱼ _ hpdⱼ hnⱼ
        rcases eq_or_ne c 0 with hc0 | hc0
        · subst hc0; simp only [map_zero, zero_mul, zero_smul]; funext i; simp [lv]
        · set qc : K[X] := C c * X ^ (Dn - nⱼ) with hqc
          have hqcne : qc ≠ 0 := mul_ne_zero (by simpa using hc0) (pow_ne_zero _ X_ne_zero)
          have hqcnd : qc.natDegree = Dn - nⱼ := by
            rw [hqc, natDegree_C_mul (by simpa using hc0), natDegree_X_pow]
          have hqclead : qc.leadingCoeff = c := by
            rw [hqc, leadingCoeff_mul, leadingCoeff_X_pow, mul_one, leadingCoeff_C]
          have := lv_smul_top (d := d) (q := qc) hqcne hpdⱼ
          rw [hqcnd] at this
          have hidx : Dn - nⱼ + nⱼ = Dn := by omega
          rw [hidx] at this
          rw [this, hqclead]
      have hlvq₁ : lv d Dn (q₁ • e₁) = c₁ • lc₁ := by
        rw [hq₁, hlvq c₁ n₁ e₁ hD₁ hpd₁ hD₁, hlc₁]
      have hlvq₂ : lv d Dn (q₂ • e₂) = c₂ • lc₂ := by
        rw [hq₂, hlvq c₂ n₂ e₂ hD₁ hpd₂ hD₂, hlc₂]
      have hlvr : lv d Dn r = 0 := by
        rw [hr, show w - (q₁ • e₁ + q₂ • e₂)
              = w + (-1 : K) • (q₁ • e₁) + (-1 : K) • (q₂ • e₂) by
                rw [neg_one_smul, neg_one_smul]; ring]
        rw [lv_add, lv_add, lv_smulK, lv_smulK, hlvq₁, hlvq₂, ← hc]
        module
      have hpdqle : ∀ (c : K) (nⱼ : ℕ) (eⱼ : Fin 3 → K[X]),
          pdeg d eⱼ = (nⱼ : WithBot ℕ) → nⱼ ≤ Dn →
          pdeg d ((C c * X ^ (Dn - nⱼ)) • eⱼ) ≤ (Dn : WithBot ℕ) := by
        intro c nⱼ eⱼ hpdⱼ hnⱼ
        rw [pdeg_smul, hpdⱼ]
        rcases eq_or_ne c 0 with hc0 | hc0
        · subst hc0; simp
        · have hqcne : (C c * X ^ (Dn - nⱼ)) ≠ 0 :=
            mul_ne_zero (by simpa using hc0) (pow_ne_zero _ X_ne_zero)
          have hnd : (C c * X ^ (Dn - nⱼ)).natDegree = Dn - nⱼ := by
            rw [natDegree_C_mul (by simpa using hc0), natDegree_X_pow]
          rw [degree_eq_natDegree hqcne, hnd, ← Nat.cast_add, Nat.cast_le]
          omega
      have hpdle : pdeg d r ≤ (Dn : WithBot ℕ) := by
        rw [hr]
        refine le_trans (pdeg_sub_le (d := d) _ _) (max_le ?_ ?_)
        · exact le_of_eq hpdw
        · refine le_trans (pdeg_add_le d _ _) (max_le ?_ ?_)
          · rw [hq₁]; exact hpdqle c₁ n₁ e₁ hpd₁ hD₁
          · rw [hq₂]; exact hpdqle c₂ n₂ e₂ hpd₂ hD₂
      rw [hpdw]
      exact pdeg_lt_of_lv_eq_zero hpdle hlvr
  -- span equality
  have hspanN : N = Submodule.span K[X] ({e₁, e₂} : Set (Fin 3 → K[X])) := by
    apply le_antisymm
    · intro w hw
      exact SYZ62.span_of_gradedExchange he₁N he₂N hex w hw
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with hx | hx <;> simp_all
  exact ⟨e₁, e₂, n₁, n₂, he₁N, he₂N, hpd₁, hpd₂, hn₁₂, hpair, hspanN⟩

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
windowed dimension, the μ-basis degrees satisfy `n₁ + n₂ = d₀ + d₁ + d₂`. -/
theorem degree_sum_of_rankNullity {d : Fin 3 → ℕ} {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) (D₀ : ℕ)
    (hRankNull : ArkLib.ProximityGap.SYZ44.RankNullity
      (fun D => finrank K (windowKD d (LinearMap.ker (SYZ61.syzygyMap f g h)) D))
      (d 0) (d 1) (d 2) D₀) :
    ∃ n₁ n₂ : ℕ, n₁ ≤ n₂ ∧ n₁ + n₂ = d 0 + d 1 + d 2 := by
  obtain ⟨e₁, e₂, n₁, n₂, _, _, hpd₁, hpd₂, hn₁₂, hpair, hspan⟩ :=
    exists_muBasisData d (LinearMap.ker (SYZ61.syzygyMap f g h))
      (SYZ61.rank_syzygyKernel hfg hfh)
  refine ⟨n₁, n₂, hn₁₂, ?_⟩
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
