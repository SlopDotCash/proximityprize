/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalSpikeFloor
import Mathlib.Tactic.Module

/-!
# The universal staircase collapse: at most `j` bad scalars on the first `j` bands (#357)

The upper half of the staircase law, matching the universal spike floor
(`UniversalSpikeFloor.lean`).  For every linear code with **no nonzero codeword of
weight `≤ 3(j−1)`** (distance `≥ 3j−2`) and every radius with `δ·n < j`, every stack
has at most `j` bad scalars (`badScalars_card_le`), hence `ε_mca(C, δ) ≤ j/|F|`
(`epsMCA_le_j_div_card`).

**The proof.**  Suppose `γ₀, …, γⱼ` are `j+1` distinct bad scalars with witnesses
`Tᵢ` (complements of size `≤ j−1`, `witness_compl_card_le`) and line codewords `wᵢ`.
1. *Differencing*: `dd i k := (γᵢ−γₖ)⁻¹•(wᵢ−wₖ)` agrees with `u₁` on `Tᵢ ∩ Tₖ`.
2. *Chaining*: two `dd`'s sharing an index agree off `≤ 3(j−1)` positions, hence are
   equal by distance forcing (`codeword_eq_of_eq_off`); every pair connects to every
   other through shared indices (five mechanical cases), so all `dd i k` equal one
   codeword `D`, and all `wᵢ − γᵢ•D` equal one codeword `U`.
3. *Pointwise pinning*: on `Tᵢ ∩ Tₖ` two independent affine relations force
   `u₁ = D` and `u₀ = U`.
4. *The stray double count*: a *stray of `i`* is a point of `Tᵢ` in no other
   witness.  If every `i` had a stray, strays would be pairwise distinct and each
   would lie in `j` of the `j+1` witness complements, giving
   `(j+1)·j ≤ Σ|Tₖᶜ| ≤ (j+1)(j−1)` — absurd.  So some `Tᵢ` is covered by the other
   witnesses, `(U, D)` jointly explains `(u₀,u₁)` on all of `Tᵢ` by step 3, and
   `γᵢ`'s no-joint clause is contradicted.  ∎

The distance condition is sharp at `j = 2` (the band-two trichotomy: `d = 3` jumps,
`d ≥ 4` collapses) and consistent with every measured instance (band 3 fails at
`d = 5`, holds at `d = 7`; band 4 jumps at `d = 7`).  Combined with the spike floor
this pins the staircase exactly and, downstream, `mcaDeltaStar` on the entire
granularity ladder.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.SpikeFloor

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
variable {j : ℕ}

/-- Distance forcing: two codewords agreeing off a set of size `≤ m` are equal,
for codes with no nonzero codeword of weight `≤ m`. -/
theorem codeword_eq_of_eq_off (C : Submodule F (ι → A)) {m : ℕ}
    (hC : NoWeightLE C m) {w w' : ι → A} (hw : w ∈ C) (hw' : w' ∈ C)
    {B : Finset ι} (hB : B.card ≤ m) (h : ∀ i ∉ B, w i = w' i) : w = w' := by
  have hz : w - w' = 0 := hC _ (C.sub_mem hw hw')
    ⟨B, hB, fun i hi => by simp [h i hi]⟩
  funext i
  have hzi := congrFun hz i
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hzi
  exact hzi

/-- Witness complements on the first `j` bands have at most `j−1` elements. -/
theorem witness_compl_card_le {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < j)
    {T : Finset ι} (hT : (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    Tᶜ.card ≤ j - 1 := by
  by_cases hδn : δ * (Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0)
  · have hsum : (Fintype.card ι : ℝ≥0) < (T.card : ℝ≥0) + (j : ℝ≥0) := by
      have h1 : (T.card : ℝ≥0) ≥ (Fintype.card ι : ℝ≥0) - δ * Fintype.card ι := by
        calc (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := hT
          _ = (Fintype.card ι : ℝ≥0) - δ * Fintype.card ι := by
              rw [tsub_mul, one_mul]
      calc (Fintype.card ι : ℝ≥0)
          = ((Fintype.card ι : ℝ≥0) - δ * Fintype.card ι) + δ * Fintype.card ι :=
            (tsub_add_cancel_of_le hδn).symm
        _ < ((Fintype.card ι : ℝ≥0) - δ * Fintype.card ι) + (j : ℝ≥0) := by gcongr
        _ ≤ (T.card : ℝ≥0) + (j : ℝ≥0) := by gcongr
    have hnat : Fintype.card ι < T.card + j := by
      have h2 := hsum
      rw [show (T.card : ℝ≥0) + (j : ℝ≥0) = ((T.card + j : ℕ) : ℝ≥0) by
        push_cast; ring] at h2
      exact_mod_cast h2
    rw [Finset.card_compl]
    omega
  · push Not at hδn
    have hnj : Fintype.card ι < j := by
      exact_mod_cast lt_trans hδn hδ
    calc Tᶜ.card ≤ Fintype.card ι := Finset.card_le_univ _
      _ ≤ j - 1 := by omega

section Collapse

variable [NoZeroSMulDivisors F A]

open Classical in
/-- **The universal staircase collapse (per-stack bound).**  On the first `j` bands
(`δ·n < j`), codes with no nonzero codeword of weight `≤ 3(j−1)` admit at most `j`
bad scalars per stack. -/
theorem badScalars_card_le (C : Submodule F (ι → A))
    (hC3 : NoWeightLE C (3 * (j - 1))) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < j) (u₀ u₁ : ι → A) :
    (Finset.univ.filter
      (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card ≤ j := by
  by_contra hgt
  push Not at hgt
  have hj1 : 1 ≤ j := by
    by_contra hj
    have hj0 : j = 0 := by omega
    rw [hj0] at hδ
    exact absurd hδ (by simp)
  -- extract j+1 distinct bad scalars, enumerated
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ.filter (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ))
    (n := j + 1) (by omega)
  set γfun : Fin (j + 1) → F :=
    fun i => (s.equivFin.symm (Fin.cast hs_card.symm i) : F) with hγfun
  have hγinj : Function.Injective γfun := fun a b hab => by
    have h1 := Subtype.val_injective hab
    have h2 := s.equivFin.symm.injective h1
    exact Fin.cast_injective _ h2
  have hbad : ∀ i, mcaEvent (C : Set (ι → A)) δ u₀ u₁ (γfun i) := fun i =>
    (Finset.mem_filter.mp (hs_sub (s.equivFin.symm (Fin.cast hs_card.symm i)).2)).2
  choose T hTsz hwEx hno using hbad
  choose w hwC hwAg using hwEx
  have hcompl : ∀ i, (T i)ᶜ.card ≤ j - 1 := fun i =>
    witness_compl_card_le hδ (hTsz i)
  -- step 1: difference codewords
  set dd : Fin (j + 1) → Fin (j + 1) → (ι → A) :=
    fun i k => (γfun i - γfun k)⁻¹ • (w i - w k) with hdd
  have hddC : ∀ i k, dd i k ∈ C := fun i k =>
    C.smul_mem _ (C.sub_mem (hwC i) (hwC k))
  have hγne : ∀ {i k : Fin (j + 1)}, i ≠ k → γfun i - γfun k ≠ 0 :=
    fun {i k} hik => sub_ne_zero.mpr (fun h => hik (hγinj h))
  have hdd_agree : ∀ i k, i ≠ k → ∀ x ∈ T i ∩ T k, dd i k x = u₁ x := by
    intro i k hik x hx
    obtain ⟨hxi, hxk⟩ := Finset.mem_inter.mp hx
    have hdiff : w i x - w k x = (γfun i - γfun k) • u₁ x := by
      rw [hwAg i x hxi, hwAg k x hxk, sub_smul]
      abel
    calc dd i k x = (γfun i - γfun k)⁻¹ • (w i x - w k x) := rfl
      _ = (γfun i - γfun k)⁻¹ • ((γfun i - γfun k) • u₁ x) := by rw [hdiff]
      _ = u₁ x := by rw [smul_smul, inv_mul_cancel₀ (hγne hik), one_smul]
  have hdd_symm : ∀ i k, dd i k = dd k i := by
    intro i k
    funext x
    show (γfun i - γfun k)⁻¹ • (w i x - w k x)
      = (γfun k - γfun i)⁻¹ • (w k x - w i x)
    rw [show γfun k - γfun i = -(γfun i - γfun k) by ring,
      show w k x - w i x = -(w i x - w k x) by abel, inv_neg, neg_smul_neg]
  -- step 2a: shared-index forcing
  have hforce : ∀ i k k', i ≠ k → i ≠ k' → k ≠ k' → dd i k = dd i k' := by
    intro i k k' hik hik' hkk'
    refine codeword_eq_of_eq_off C hC3 (hddC i k) (hddC i k')
      (B := ((T i)ᶜ ∪ (T k)ᶜ) ∪ (T k')ᶜ) ?_ ?_
    · have hu1 := Finset.card_union_le ((T i)ᶜ ∪ (T k)ᶜ) ((T k')ᶜ)
      have hu2 := Finset.card_union_le ((T i)ᶜ) ((T k)ᶜ)
      have h1 := hcompl i
      have h2 := hcompl k
      have h3 := hcompl k'
      omega
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_compl, not_or, not_not] at hx
      obtain ⟨⟨hxi, hxk⟩, hxk'⟩ := hx
      rw [hdd_agree i k hik x (Finset.mem_inter.mpr ⟨hxi, hxk⟩),
        hdd_agree i k' hik' x (Finset.mem_inter.mpr ⟨hxi, hxk'⟩)]
  -- step 2b: all dd's equal (five mechanical connectivity cases)
  have hDall : ∀ i k i' k', i ≠ k → i' ≠ k' → dd i k = dd i' k' := by
    intro i k i' k' hik hik'
    by_cases hii' : i = i'
    · by_cases hkk' : k = k'
      · rw [hii', hkk']
      · rw [hii'] at hik ⊢
        exact hforce i' k k' hik hik' hkk'
    · by_cases hikk : i = k'
      · by_cases hki' : k = i'
        · rw [hikk, hki']
          exact hdd_symm k' i' ▸ (hdd_symm i' k').symm ▸ hdd_symm i' k'
        · -- i = k', k ∉ {i, i'}
          calc dd i k = dd i i' := hforce i k i' hik hii' hki'
            _ = dd i' i := hdd_symm i i'
            _ = dd i' k' := by rw [hikk]
      · by_cases hki' : k = i'
        · -- k = i', i ∉ {i', k'}
          calc dd i k = dd k i := hdd_symm i k
            _ = dd k k' := hforce k i k' (fun h => hik h.symm) (hki' ▸ hik') hikk
            _ = dd i' k' := by rw [← hki']
        · by_cases hkk' : k = k'
          · -- k = k', all of i, i', k distinct
            calc dd i k = dd k i := hdd_symm i k
              _ = dd k i' := hforce k i i' (fun h => hik h.symm)
                  (fun h => hki' h) hii'
              _ = dd i' k := hdd_symm k i'
              _ = dd i' k' := by rw [hkk']
          · -- all four distinct
            calc dd i k = dd i k' := hforce i k k' hik hikk hkk'
              _ = dd k' i := hdd_symm i k'
              _ = dd k' i' := hforce k' i i' (fun h => hikk h.symm)
                  (fun h => hik' h.symm) hii'
              _ = dd i' k' := hdd_symm k' i'
  -- the common pair (U, D)
  have hi01 : (⟨0, by omega⟩ : Fin (j + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  set i₀ : Fin (j + 1) := ⟨0, by omega⟩
  set i₁ : Fin (j + 1) := ⟨1, by omega⟩
  set D : ι → A := dd i₀ i₁ with hD
  set U : ι → A := w i₀ - γfun i₀ • D with hU
  have hDC : D ∈ C := hddC i₀ i₁
  have hUC : U ∈ C := C.sub_mem (hwC i₀) (C.smul_mem _ hDC)
  have hwD : ∀ i, w i = U + γfun i • D := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      funext x
      show w i₀ x = (w i₀ x - γfun i₀ • D x) + γfun i₀ • D x
      abel
    · have hddD : dd i i₀ = D := hDall i i₀ i₀ i₁ hi hi01
      funext x
      have hmul : w i x - w i₀ x = (γfun i - γfun i₀) • D x := by
        rw [← hddD]
        show w i x - w i₀ x
          = (γfun i - γfun i₀) • ((γfun i - γfun i₀)⁻¹ • (w i x - w i₀ x))
        rw [smul_smul, mul_inv_cancel₀ (hγne hi), one_smul]
      show w i x = (w i₀ x - γfun i₀ • D x) + γfun i • D x
      have hwix : w i x = w i₀ x + (γfun i - γfun i₀) • D x := by
        rw [← hmul]; abel
      rw [hwix, sub_smul]
      abel
  -- step 3: pointwise pinning on pairwise intersections
  have hpin : ∀ i k, i ≠ k → ∀ x ∈ T i ∩ T k, u₁ x = D x ∧ u₀ x = U x := by
    intro i k hik x hx
    obtain ⟨hxi, hxk⟩ := Finset.mem_inter.mp hx
    have ei : u₀ x + γfun i • u₁ x = U x + γfun i • D x := by
      rw [← hwAg i x hxi, hwD i]
      simp [Pi.add_apply, Pi.smul_apply]
    have ek : u₀ x + γfun k • u₁ x = U x + γfun k • D x := by
      rw [← hwAg k x hxk, hwD k]
      simp [Pi.add_apply, Pi.smul_apply]
    have hsub : (γfun i - γfun k) • (u₁ x - D x) = 0 := by
      have hkey : (γfun i - γfun k) • (u₁ x - D x)
          = (u₀ x + γfun i • u₁ x - (U x + γfun i • D x))
            - (u₀ x + γfun k • u₁ x - (U x + γfun k • D x)) := by
        module
      rw [hkey, ei, ek]
      abel
    have hu1 : u₁ x = D x := by
      rcases smul_eq_zero.mp hsub with h | h
      · exact absurd h (hγne hik)
      · exact sub_eq_zero.mp h
    refine ⟨hu1, ?_⟩
    have := ei
    rw [hu1] at this
    have h3 : u₀ x + γfun i • D x = U x + γfun i • D x := this
    exact add_right_cancel h3
  -- step 4: some witness has no strays
  have hstray : ∃ i, ∀ x ∈ T i, ∃ k, k ≠ i ∧ x ∈ T k := by
    by_contra hall
    push Not at hall
    choose xs hxsT hxsNot using hall
    have hinj : Function.Injective xs := by
      intro a b hab
      by_contra hne
      have h1 : xs a ∈ T a := hxsT a
      have h2 : xs b ∉ T a := hxsNot b a hne
      rw [hab] at h1
      exact h2 h1
    have hlow : ∀ i, j ≤ (Finset.univ.filter
        (fun k : Fin (j + 1) => xs i ∈ (T k)ᶜ)).card := by
      intro i
      have hsub2 : Finset.univ.filter (fun k : Fin (j + 1) => k ≠ i)
          ⊆ Finset.univ.filter (fun k => xs i ∈ (T k)ᶜ) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        rw [Finset.mem_compl]
        exact hxsNot i k hk
      calc j = (Finset.univ.filter (fun k : Fin (j + 1) => k ≠ i)).card := by
            rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin]
            omega
        _ ≤ _ := Finset.card_le_card hsub2
    have hup : ∀ k : Fin (j + 1), (Finset.univ.filter
        (fun i => xs i ∈ (T k)ᶜ)).card ≤ (T k)ᶜ.card := by
      intro k
      have himg : (Finset.univ.filter (fun i => xs i ∈ (T k)ᶜ)).card
          = ((Finset.univ.filter (fun i => xs i ∈ (T k)ᶜ)).image xs).card :=
        (Finset.card_image_of_injective _ hinj).symm
      rw [himg]
      apply Finset.card_le_card
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hi).2
    have hswap : ∑ i : Fin (j + 1), (Finset.univ.filter
          (fun k => xs i ∈ (T k)ᶜ)).card
        = ∑ k : Fin (j + 1), (Finset.univ.filter
          (fun i => xs i ∈ (T k)ᶜ)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hsum1 : (j + 1) * j ≤ ∑ i : Fin (j + 1), (Finset.univ.filter
        (fun k => xs i ∈ (T k)ᶜ)).card := by
      calc (j + 1) * j = ∑ _i : Fin (j + 1), j := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hlow i)
    have hsum2 : ∑ k : Fin (j + 1), (Finset.univ.filter
        (fun i => xs i ∈ (T k)ᶜ)).card ≤ (j + 1) * (j - 1) := by
      calc ∑ k : Fin (j + 1), (Finset.univ.filter
            (fun i => xs i ∈ (T k)ᶜ)).card
          ≤ ∑ _k : Fin (j + 1), (j - 1) :=
            Finset.sum_le_sum (fun k _ => le_trans (hup k) (hcompl k))
        _ = (j + 1) * (j - 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hcontra : (j + 1) * j ≤ (j + 1) * (j - 1) :=
      le_trans hsum1 (le_trans (le_of_eq hswap) hsum2)
    have hjj : j ≤ j - 1 := Nat.le_of_mul_le_mul_left hcontra (by omega)
    omega
  -- step 5: the covered witness yields a joint explanation — contradiction
  obtain ⟨i, hcov⟩ := hstray
  apply hno i
  refine ⟨U, hUC, D, hDC, fun x hx => ?_⟩
  obtain ⟨k, hki, hxk⟩ := hcov x hx
  have hp := hpin i k (Ne.symm hki) x (Finset.mem_inter.mpr ⟨hx, hxk⟩)
  exact ⟨hp.2.symm, hp.1.symm⟩

open Classical in
/-- **The universal staircase collapse.**  `ε_mca(C, δ) ≤ j/|F|` on the first `j`
bands, for every linear code with no nonzero codeword of weight `≤ 3(j−1)`. -/
theorem epsMCA_le_j_div_card (C : Submodule F (ι → A))
    (hC3 : NoWeightLE C (3 * (j - 1))) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < j) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ (j : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast badScalars_card_le C hC3 hδ (u 0) (u 1)


open Classical in
/-- **THE EXACT STAIRCASE.**  `ε_mca(C, δ) = j/|F|` on the `j`-th granularity band
(`j−1 ≤ δ·n < j`), for every linear code with no nonzero codeword of weight
`≤ 3(j−1)` and of weight `≤ j` (both hold at distance `≥ 3j−2` for `j ≥ 2`). -/
theorem epsMCA_eq_j_div_card (C : Submodule F (ι → A))
    (hC3 : NoWeightLE C (3 * (j - 1))) (hCj : NoWeightLE C j)
    {δ : ℝ≥0} (hδlo : ((j - 1 : ℕ) : ℝ≥0) ≤ δ * Fintype.card ι)
    (hδhi : δ * (Fintype.card ι : ℝ≥0) < j)
    (hj1 : 1 ≤ j) (hjn : j ≤ Fintype.card ι) (hjF : j ≤ Fintype.card F)
    [Nontrivial A] :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = (j : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm (epsMCA_le_j_div_card C hC3 hδhi) ?_
  obtain ⟨p⟩ : Nonempty (Fin j ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hjn)
  obtain ⟨a⟩ : Nonempty (Fin j ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hjF)
  obtain ⟨b, hb⟩ := exists_ne (0 : A)
  exact epsMCA_ge_j_div_card C hCj hδlo hj1 hjn p a hb

open Classical in
/-- **THE GRANULARITY LADDER CLOSED FORM.**  For every linear code with no nonzero
codeword of weight `≤ max(3(j−1), j+1)` and every threshold
`ε* ∈ [j/|F|, (j+1)/|F|)`:

  `mcaDeltaStar C ε* = j / n`.

The first closed-form δ* theorem over a family of codes and thresholds: the good
side is the universal collapse (every radius with `δ·n < j` has mass `≤ j/q ≤ ε*`),
the bad side is the universal spike floor at `j+1` (`mcaDeltaStar_le_granularity`).
Both machine-checked exact pins (`mcaDeltaStar_C542_eq_quarter`,
`mcaDeltaStar_C84_eq_quarter`) are instances. -/
theorem mcaDeltaStar_eq_granularity (C : Submodule F (ι → A))
    (hC3 : NoWeightLE C (3 * (j - 1))) (hCj1 : NoWeightLE C (j + 1))
    (hj1 : 1 ≤ j) (hj1n : j + 1 ≤ Fintype.card ι) (hj1F : j + 1 ≤ Fintype.card F)
    [Nontrivial A] {εstar : ℝ≥0∞}
    (hlo : (j : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((j + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar
      = (j : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
  have hn0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  refine le_antisymm ?_ ?_
  · -- bad side: the spike floor at j+1
    have h := mcaDeltaStar_le_granularity (j := j + 1) C hCj1 (by omega) hj1n hj1F
      (by simpa using hhi)
    simpa using h
  · -- good side: the collapse on every radius below j/n
    by_contra h
    push Not at h
    obtain ⟨c, hc1, hc2⟩ := exists_between h
    have hcn : c * (Fintype.card ι : ℝ≥0) < j := by
      have h2 := hc2
      rwa [lt_div_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm hn0))] at h2
    have hc1' : c ≤ 1 := by
      calc c ≤ (j : ℝ≥0) / (Fintype.card ι : ℝ≥0) := le_of_lt hc2
        _ ≤ 1 := by
            rw [div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm hn0))]
            exact_mod_cast le_trans (by omega : j ≤ j + 1) hj1n
    have hgood : c ∈ MCAThresholdLedger.mcaGoodRadii (F := F) (A := A)
        (C : Set (ι → A)) εstar :=
      ⟨hc1', le_trans (epsMCA_le_j_div_card C hC3 hcn) hlo⟩
    have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F) (A := A)
      (C : Set (ι → A)) εstar hgood.1 hgood.2
    exact absurd hle (not_le.mpr hc1)

end Collapse

end ProximityGap.SpikeFloor

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SpikeFloor.badScalars_card_le
#print axioms ProximityGap.SpikeFloor.epsMCA_le_j_div_card
#print axioms ProximityGap.SpikeFloor.epsMCA_eq_j_div_card
#print axioms ProximityGap.SpikeFloor.mcaDeltaStar_eq_granularity
