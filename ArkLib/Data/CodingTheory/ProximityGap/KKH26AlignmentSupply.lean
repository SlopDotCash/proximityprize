/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalAlignmentLaw
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# The KKH26 alignment supply: the deep census lower bound is the fibre family (#371)

The alignment-census probes found that at the deep ceiling band the only surviving
alignable supply is the KKH26 fibre structure, and that it is exactly extremal among
character lines.  This file proves the **supply side in census form**: for the KKH26 line
`(x^{rm}, x^{(r−1)m})` on a smooth domain of order `s·m`, every `r`-subset `T` of the
`m`-power subgroup yields a **`γ_T`-aligned `rm`-point set with a non-degenerate tuple** —
the squaring/`m`-power fibre union

  `S_T = {i : (g^i)^m ∈ T}`,   `γ_T = −∑_{a∈T} a`,

at code dimension `k = (r−2)m + 1` (`kkh26_fibreUnion_aligned_nondegenerate`).  Hence by
the universal alignment law the deep alignable supply of the KKH26 line is at least the
`r`-subset family — the lower half of the census two-regime law, now welded to
`UniversalAlignmentLaw` (whose `badScalars_card_le_alignable` is the upper half).

Inputs reused: `badline_pointwise_agreement` (the vanishing-polynomial identity behind the
KKH26 construction — a pure polynomial fact), `fiber_count` (the `m`-power fibres have
exactly `m` points each), and the explainability dictionary of the alignment law.  The
non-degeneracy is the degree clash: `x^{(r−1)m}` cannot agree with a degree-`< k`
polynomial on `rm > (r−1)m` distinct points.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap ArkLib.ProximityGap.KKH26

variable {p : ℕ} [Fact p.Prime]

/-- Power injectivity below the order (elementary cancellation, valid at a field). -/
private lemma pow_inj_below_order'' {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

private lemma g_ne_zero' {g : ZMod p} {N : ℕ} (hN : 1 ≤ N) (hg : orderOf g = N) :
    g ≠ 0 := by
  rintro rfl
  have h1 : (0 : ZMod p) ^ N = 1 := by rw [← hg]; exact pow_orderOf_eq_one 0
  rw [zero_pow (by omega : N ≠ 0)] at h1
  exact absurd h1 zero_ne_one

/-- The smooth domain embedding `i ↦ g^i`. -/
noncomputable def smoothDom (g : ZMod p) (n : ℕ) [NeZero n] (hg : orderOf g = n) :
    Fin n ↪ ZMod p :=
  ⟨fun i => g ^ (i : ℕ), by
    intro a b hab
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    exact Fin.ext (pow_inj_below_order'' (g_ne_zero' hn1 hg) hg a a.isLt b b.isLt hab)⟩

open Classical in
/-- **THE KKH26 ALIGNMENT SUPPLY.**  For the KKH26 line `(x^{rm}, x^{(r−1)m})` at code
dimension `k = (r−2)m+1` on the smooth `s·m`-point domain, every `r`-subset `T` of the
`m`-power subgroup produces a `(−∑T)`-aligned fibre-union of exactly `rm` points carrying
a non-degenerate tuple — a deep alignable set in the sense of the universal alignment law,
at the exact ceiling band of the construction. -/
theorem kkh26_fibreUnion_aligned_nondegenerate
    {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) {n : ℕ} [NeZero n] (hn : n = s * m)
    {g : ZMod p} (hg : orderOf g = n)
    {T : Finset (ZMod p)} (hTsub : T ⊆ (Finset.range s).image (fun j => (g ^ m) ^ j))
    {r : ℕ} (hr2 : 2 ≤ r) (hTcard : T.card = r) :
    ∃ S : Finset (Fin n), S.card = r * m ∧
      Aligned (smoothDom g n hg) ((r - 2) * m + 1)
        (fun i => (g ^ (i : ℕ)) ^ (r * m)) (fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m))
        (-(∑ a ∈ T, a)) S ∧
      ∃ t : Fin ((r - 2) * m + 1 + 1) → Fin n, Function.Injective t ∧
        (∀ b, t b ∈ S) ∧
        ¬ (residual (smoothDom g n hg) ((r - 2) * m + 1) t
            (fun i => (g ^ (i : ℕ)) ^ (r * m)) = 0 ∧
          residual (smoothDom g n hg) ((r - 2) * m + 1) t
            (fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m)) = 0) := by
  classical
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set dom := smoothDom g n hg with hdom
  set k := (r - 2) * m + 1 with hkdef
  set u₀ : Fin n → ZMod p := fun i => (g ^ (i : ℕ)) ^ (r * m) with hu₀
  set u₁ : Fin n → ZMod p := fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m) with hu₁
  -- the index-level fibre union
  set S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (g ^ (i : ℕ)) ^ m ∈ T)
    with hSdef
  -- its cardinality: bridge to the domain-level fiber_count
  have hScard : S.card = r * m := by
    have hbij : S.card = (((Finset.range (s * m)).image (fun i => g ^ i)).filter
        (fun x => x ^ m ∈ T)).card := by
      refine Finset.card_bij (fun i _ => g ^ (i : ℕ)) ?_ ?_ ?_
      · intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
          ⟨(i : ℕ), Finset.mem_range.mpr (hn ▸ i.isLt), rfl⟩, ?_⟩
        exact (Finset.mem_filter.mp hi).2
      · intro a ha b hb hab
        exact Fin.ext (pow_inj_below_order'' (g_ne_zero' hn1 hg) hg a a.isLt b b.isLt hab)
      · intro x hx
        obtain ⟨hmem, hpm⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
        refine ⟨⟨i, hn ▸ Finset.mem_range.mp hi⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpm⟩
    rw [hbij, fiber_count hm hs (hn ▸ hg) T hTsub, hTcard, Nat.mul_comm]
  -- the combined word agrees with a degree ≤ (r−2)m codeword on S
  obtain ⟨q, hqdeg, hq⟩ := badline_pointwise_agreement (p := p) hm T (hTcard ▸ hr2)
  rw [hTcard] at hqdeg
  have hcombined : ∃ c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)),
      ∀ i ∈ S, c i = u₀ i + (-(∑ a ∈ T, a)) * u₁ i := by
    refine ⟨fun i => q.eval (dom i), ⟨q, ?_, rfl⟩, fun i hi => ?_⟩
    · -- degree q < k
      calc q.degree ≤ (q.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (((r - 2) * m : ℕ) : WithBot ℕ) := by exact_mod_cast hqdeg
      _ < (k : WithBot ℕ) := by
          rw [hkdef]
          exact_mod_cast Nat.lt_succ_self _
    · have hfib : (g ^ (i : ℕ)) ^ m ∈ T := (Finset.mem_filter.mp hi).2
      have h := hq (g ^ (i : ℕ)) hfib
      have hTr : T.card = r := hTcard
      rw [hTr] at h
      show q.eval (g ^ (i : ℕ)) = u₀ i + (-(∑ a ∈ T, a)) * u₁ i
      rw [hu₀, hu₁]
      linear_combination -h
  -- alignment from explainability of the combined word
  have halign : Aligned dom k u₀ u₁ (-(∑ a ∈ T, a)) S := by
    intro t htinj htmem
    have hall := (explainableOn_iff_forall_residual dom (by omega : 1 ≤ k)
      (u := fun i => u₀ i + (-(∑ a ∈ T, a)) * u₁ i) (S := S)).mp
      (by
        obtain ⟨c, hcmem, hcag⟩ := hcombined
        exact ⟨c, hcmem, hcag⟩) t htinj htmem
    rwa [residual_line] at hall
  -- non-degeneracy: u₁ is not jointly explainable (degree clash on rm points)
  have hnotexpl : ¬ ∃ c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)),
      ∀ i ∈ S, c i = u₁ i := by
    rintro ⟨c, ⟨P, hPdeg, rfl⟩, hag⟩
    set D := Polynomial.X ^ ((r - 1) * m) - P with hDdef
    have hDne : D ≠ 0 := by
      intro hD0
      have hXP : (Polynomial.X : Polynomial (ZMod p)) ^ ((r - 1) * m) = P :=
        sub_eq_zero.mp hD0
      have hdegX : ((Polynomial.X : Polynomial (ZMod p)) ^ ((r - 1) * m)).degree
          = (((r - 1) * m : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_X_pow]
      have hklt : (k : ℕ) ≤ (r - 1) * m := by
        rw [hkdef]
        have : (r - 2) * m + m ≤ (r - 1) * m := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right m (by omega)
        omega
      rw [hXP] at hdegX
      rw [hdegX] at hPdeg
      have : ((r - 1) * m : ℕ) < k := by exact_mod_cast hPdeg
      omega
    have hDvan : ∀ x ∈ S.image (fun i : Fin n => g ^ (i : ℕ)), D.eval x = 0 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hagi : P.eval (g ^ (i : ℕ)) = (g ^ (i : ℕ)) ^ ((r - 1) * m) := hag i hi
      rw [hDdef]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hagi]
      ring
    have hcard : (S.image (fun i : Fin n => g ^ (i : ℕ))).card = r * m := by
      rw [Finset.card_image_of_injective _ (fun a b hab =>
        Fin.ext (pow_inj_below_order'' (g_ne_zero' hn1 hg) hg a a.isLt b b.isLt hab)),
        hScard]
    have hdegD : D.degree < ((S.image (fun i : Fin n => g ^ (i : ℕ))).card : ℕ) := by
      rw [hcard]
      calc D.degree ≤ max ((Polynomial.X ^ ((r - 1) * m) :
            Polynomial (ZMod p)).degree) P.degree := Polynomial.degree_sub_le _ _
      _ < (((r * m) : ℕ) : WithBot ℕ) := by
          rw [max_lt_iff]
          have hrm : (r - 1) * m < r * m := by
            have h0 : 0 < m := by omega
            have h1 : r - 1 < r := by omega
            exact (Nat.mul_lt_mul_right h0).mpr h1
          constructor
          · rw [Polynomial.degree_X_pow]
            exact_mod_cast hrm
          · refine lt_trans hPdeg ?_
            rw [hkdef]
            have hkrm : (r - 2) * m + 1 < r * m := by
              have h1 : (r - 2) * m + 2 * m ≤ r * m := by
                rw [← Nat.add_mul]
                exact Nat.mul_le_mul_right m (by omega)
              omega
            exact_mod_cast hkrm
    exact hDne (Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (s := S.image (fun i : Fin n => g ^ (i : ℕ))) hdegD hDvan)
  -- extract the non-degenerate tuple
  have hnall : ¬ ∀ t : Fin (k + 1) → Fin n, Function.Injective t → (∀ b, t b ∈ S) →
      residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0 := by
    intro hcontra
    exact hnotexpl ((explainableOn_iff_forall_residual dom (by omega : 1 ≤ k)).mpr
      (fun t h1 h2 => (hcontra t h1 h2).2))
  push Not at hnall
  obtain ⟨t, htinj, htmem, hnd'⟩ := hnall
  exact ⟨S, hScard, halign, t, htinj, htmem, fun hc => hnd' hc.1 hc.2⟩

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.kkh26_fibreUnion_aligned_nondegenerate
