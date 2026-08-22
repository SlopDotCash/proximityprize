/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDRBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement

/-!
# Factor-2 unique-decoding-radius MCA bound for Reed-Solomon (up to (1-ρ)/2)

The in-tree `MCAUDRBound.epsMCA_rs_udr_le` bounds `ε_mca(RS,δ) ≤ 2(n-t)/q` only in the factor-3
regime `3(n-t) < d` (`d = n-k+1` the RS minimum distance, `t = ⌈(1-δ)n⌉`), i.e. `δ ≲ (1-ρ)/3`.
That proof builds the candidate codeword-pair by 2-point Lagrange interpolation from two bad
scalars and verifies every other scalar against it, costing a *triple* coordinate intersection
`S_{γ_a} ∩ S_{γ_b} ∩ S_γ`, hence the factor 3.

This file improves the reach to the **true unique-decoding radius** `δ ≤ relUDR = (1-ρ)/2` (regime
`2(n-t) < d`), with `ε_mca(RS,δ) ≤ n/q`.  The key idea: instead of interpolating from two scalars,
take the **γ-independent** codeword-pair `(v₀,v₁)` supplied by the in-tree Berlekamp-Welch /
Polishchuk-Spielman correlated-agreement extractor `RS_jointAgreement_of_goodCoeffs_card_gt` (valid
up to `relUDR`).  Its line `v₀+γ•v₁` is δ-close to the received line `u₀+γ•u₁` at *every* `γ` (on the
single agreement set `S₀`), so each bad witness `w_γ` is forced equal to `v₀+γ•v₁` by a **double**
(not triple) distance bound `Δ₀(w_γ, v₀+γv₁) ≤ 2(n-t) < d`.  Each bad `γ` is then a root
`-e₀(i)/e₁(i)` of the affine error `e₀+γe₁` at some `i ∈ supp(e₁) ⊆ S₀ᶜ`, so the bad count is
`≤ |supp e₁| ≤ n-t` — reusing the in-tree `badGamma_le` line-root count.

## Main results

* `badCount_udr2_le` — the factor-2 bad-count core (given the global pair).
* `epsMCA_rs_udr2_le` — `ε_mca(RS,δ) ≤ n/q` for `δ ≤ relUDR`, regime `2(n-t) < n-k+1`.

## References

- [BCIKS20] Ben-Sasson-Carmon-Ishai-Kopparty-Saraf, the correlated-agreement extractor.
- [ABF26] Arnon-Boneh-Fenzi, the Grand MCA Challenge (§1, §4.5).
-/

set_option linter.style.longLine false


open Finset ProximityGap
open scoped NNReal ENNReal BigOperators

namespace ProximityGap.UDR2

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Factor-2 UDR bad-count bound (the math core).** Given a *global* close codeword-pair `(v₀,v₁)`
agreeing with `(u₀,u₁)` per-coordinate on a γ-independent set `S₀` of size `≥ t`, in the true
unique-decoding regime `2(n−t) < d`, the MCA bad-scalar count is `≤ n − t`.

Key over the factor-3 `badCount_udr_le`: the γ-independent curve `v₀+γv₁` is close to the line at
EVERY γ (on `S₀`), so each witness `w_γ` is forced equal to it by a *double* (not triple) distance
bound. Then each bad γ is a root `-e₀(i)/e₁(i)` for some `i ∈ supp(e₁) ⊆ S₀ᶜ`. -/
theorem badCount_udr2_le (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) (d t : ℕ)
    (hmd : ∀ a ∈ C, ∀ b ∈ C, (univ.filter (fun i => a i ≠ b i)).card < d → a = b)
    (hreg : 2 * (Fintype.card ι - t) < d)
    (v₀ v₁ : ι → F) (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C)
    (S₀ : Finset ι) (hS₀ : t ≤ S₀.card)
    (hv₀S : ∀ i ∈ S₀, v₀ i = u₀ i) (hv₁S : ∀ i ∈ S₀, v₁ i = u₁ i)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hSt : ∀ γ ∈ G, t ≤ (S γ).card)
    (hwC : ∀ γ ∈ G, w γ ∈ C)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = u₀ i + γ • u₁ i)
    (hno : ∀ γ ∈ G, ¬ pairJointAgreesOn (C : Set (ι → F)) (S γ) u₀ u₁) :
    G.card ≤ Fintype.card ι - t := by
  classical
  set e₀ : ι → F := u₀ - v₀ with he₀def
  set e₁ : ι → F := u₁ - v₁ with he₁def
  -- e₁ vanishes on S₀
  have he₁S : ∀ i ∈ S₀, e₁ i = 0 := by
    intro i hi; simp only [he₁def, Pi.sub_apply, hv₁S i hi, sub_self]
  -- |supp e₁| ≤ n - t
  have hsupp : (univ.filter (fun i => e₁ i ≠ 0)).card ≤ Fintype.card ι - t := by
    have hsub : (univ.filter (fun i => e₁ i ≠ 0)) ⊆ S₀ᶜ := by
      intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
      simp only [mem_compl]; intro hiS; exact hi (he₁S i hiS)
    calc (univ.filter (fun i => e₁ i ≠ 0)).card ≤ S₀ᶜ.card := card_le_card hsub
      _ = Fintype.card ι - S₀.card := card_compl S₀
      _ ≤ Fintype.card ι - t := by omega
  -- G ⊆ root set
  have hGsub : G ⊆ univ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0) := by
    intro γ hγ
    simp only [mem_filter, mem_univ, true_and]
    -- w_γ = v₀ + γ•v₁ by unique decoding (double distance)
    have hcollapse : w γ = v₀ + γ • v₁ := by
      apply hmd _ (hwC γ hγ) _ (C.add_mem hv₀ (C.smul_mem _ hv₁))
      -- disagreement of w_γ and v₀+γv₁ ⊆ (S γ ∩ S₀)ᶜ, card ≤ 2(n-t) < d
      have hsub2 : (univ.filter (fun i => w γ i ≠ (v₀ + γ • v₁) i)) ⊆ (S γ ∩ S₀)ᶜ := by
        intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
        simp only [mem_compl, mem_inter, not_and]; intro hiSγ hiS₀
        apply hi
        -- on S γ ∩ S₀: w_γ = line = v₀+γv₁
        have ew := hwS γ hγ i hiSγ
        have e0 := hv₀S i hiS₀; have e1 := hv₁S i hiS₀
        rw [ew]
        simp only [Pi.add_apply, Pi.smul_apply, e0, e1, smul_eq_mul]
      have hcardle : (univ.filter (fun i => w γ i ≠ (v₀ + γ • v₁) i)).card < d := by
        have hle := card_le_card hsub2
        rw [card_compl] at hle
        have hun : (S γ ∪ S₀).card ≤ Fintype.card ι := by simpa using card_le_univ (S γ ∪ S₀)
        have hui : (S γ ∪ S₀).card + (S γ ∩ S₀).card = (S γ).card + S₀.card :=
          card_union_add_card_inter (S γ) S₀
        have hsg := hSt γ hγ
        omega
      exact hcardle
    -- ¬pairJointAgreesOn gives a disagreement coordinate i ∈ S γ
    have hnpj := hno γ hγ
    have hexi : ∃ i ∈ S γ, ¬ (v₀ i = u₀ i ∧ v₁ i = u₁ i) := by
      by_contra hcon; push Not at hcon
      exact hnpj ⟨v₀, hv₀, v₁, hv₁, fun i hi => hcon i hi⟩
    obtain ⟨i, hiS, hidis⟩ := hexi
    -- at i: line = w_γ = v₀+γv₁, so e₀ i + γ e₁ i = 0
    have hci := congrFun hcollapse i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hci
    have hsi := hwS γ hγ i hiS
    rw [smul_eq_mul] at hsi
    have hc : u₀ i + γ * u₁ i = v₀ i + γ * v₁ i := by rw [← hsi, hci]
    have haff : e₀ i + γ * e₁ i = 0 := by
      simp only [he₀def, he₁def, Pi.sub_apply]; linear_combination hc
    have he₁i : e₁ i ≠ 0 := by
      intro h0
      rw [h0, mul_zero, add_zero] at haff
      apply hidis
      refine ⟨?_, ?_⟩
      · have hz : u₀ i - v₀ i = 0 := by simpa only [he₀def, Pi.sub_apply] using haff
        exact (sub_eq_zero.mp hz).symm
      · have hz : u₁ i - v₁ i = 0 := by simpa only [he₁def, Pi.sub_apply] using h0
        exact (sub_eq_zero.mp hz).symm
    exact ⟨i, he₁i, haff⟩
  calc G.card
      ≤ (univ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card := card_le_card hGsub
    _ ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := UDRwire.badGamma_le e₀ e₁
    _ ≤ Fintype.card ι - t := hsupp

open Classical in
theorem epsMCA_rs_udr2_le (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ_udr : δ ≤ Code.relativeUniqueDecodingRadius (ReedSolomon.code α k : Set (ι → F)))
    (htn : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ < Fintype.card ι)
    (hreg : 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < Fintype.card ι - k + 1) :
    epsMCA (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
      ≤ (Fintype.card ι : ℕ) / (Fintype.card F : ℝ≥0∞) := by
  set t : ℕ := ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ with htdef
  have hmd := UDRwire.rs_min_dist α k hk
  apply epsMCA_le_of_badCount_le (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
    (Fintype.card ι)
  intro u
  set G : Finset F :=
    univ.filter (fun γ : F => mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ) with hGdef
  -- witness extraction
  set S : F → Finset ι := fun γ =>
    if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ then h.choose else ∅ with hSdef
  set w : F → ι → F := fun γ =>
    if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ
      then (h.choose_spec.2.1).choose else 0 with hwdef
  have hSt : ∀ γ ∈ G, t ≤ (S γ).card := by
    intro γ hγ; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hSdef, dif_pos h]
    have hcardR : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ ((h.choose.card : ℕ) : ℝ≥0) := h.choose_spec.1
    rw [htdef]; exact Nat.ceil_le.mpr hcardR
  have hwC : ∀ γ ∈ G, w γ ∈ (ReedSolomon.code α k : Submodule F (ι → F)) := by
    intro γ hγ; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hwdef, dif_pos h]; exact (h.choose_spec.2.1).choose_spec.1
  have hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = (u 0) i + γ • (u 1) i := by
    intro γ hγ i hi; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hwdef, dif_pos h]; simp only [hSdef, dif_pos h] at hi
    exact (h.choose_spec.2.1).choose_spec.2 i hi
  have hno : ∀ γ ∈ G, ¬ pairJointAgreesOn (ReedSolomon.code α k : Set (ι → F)) (S γ) (u 0) (u 1) := by
    intro γ hγ; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hSdef, dif_pos h]; exact h.choose_spec.2.2
  -- branch on goodCoeffs size
  by_cases hcase : (RS_goodCoeffs (deg := k) (domain := α) u δ).card > Fintype.card ι
  · -- jointAgreement gives the global pair
    have hja := RS_jointAgreement_of_goodCoeffs_card_gt (deg := k) (domain := α) hδ_udr u hcase
    obtain ⟨S₀, hS₀card, v, hv⟩ := hja
    have hv₀ : v 0 ∈ (ReedSolomon.code α k : Submodule F (ι → F)) := (hv 0).1
    have hv₁ : v 1 ∈ (ReedSolomon.code α k : Submodule F (ι → F)) := (hv 1).1
    have hS₀t : t ≤ S₀.card := by rw [htdef]; exact Nat.ceil_le.mpr (by exact_mod_cast hS₀card)
    have hv₀S : ∀ i ∈ S₀, v 0 i = (u 0) i := by
      intro i hi; have := (hv 0).2 hi; exact (mem_filter.mp this).2
    have hv₁S : ∀ i ∈ S₀, v 1 i = (u 1) i := by
      intro i hi; have := (hv 1).2 hi; exact (mem_filter.mp this).2
    have hbc := badCount_udr2_le (ReedSolomon.code α k) (u 0) (u 1) (Fintype.card ι - k + 1) t
      hmd hreg (v 0) (v 1) hv₀ hv₁ S₀ hS₀t hv₀S hv₁S G S w hSt hwC hwS hno
    exact le_trans hbc (Nat.sub_le _ _)
  · -- few good coeffs: badCount ≤ goodCoeffs ≤ n
    rw [not_lt] at hcase
    have hGsub : G ⊆ RS_goodCoeffs (deg := k) (domain := α) u δ := by
      intro γ hγ; rw [hGdef, mem_filter] at hγ
      simp only [RS_goodCoeffs, mem_filter, mem_univ, true_and]
      exact mcaEvent_imp_relCloseToCode _ δ (u 0) (u 1) γ hγ.2
    calc G.card ≤ (RS_goodCoeffs (deg := k) (domain := α) u δ).card := card_le_card hGsub
      _ ≤ Fintype.card ι := hcase


/-- **Multi-curve bad-count bound (Johnson/capacity-reaching, given the GS list cover).** Given `L`
codeword-pairs `(v₀ j, v₁ j)` each agreeing with `(u₀,u₁)` per-coordinate on a set `S₀ j` of size
`≥ t`, such that every bad witness `w_γ` lies on *one* of the `L` curves (`w_γ = v₀ j + γ•v₁ j`),
the MCA bad-scalar count is `≤ L·(n-t)`.  No minimum-distance hypothesis: the witness-to-curve
assignment is supplied by the list cover (the GS list-decoding output), so this reaches any radius
where such a cover exists (Johnson, capacity). Each curve contributes `≤ |supp e₁ j| ≤ n-t` roots. -/
theorem badCount_listcover_le (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) (t L : ℕ)
    (v₀ v₁ : Fin L → ι → F)
    (hv₀ : ∀ j, v₀ j ∈ C) (hv₁ : ∀ j, v₁ j ∈ C)
    (S₀ : Fin L → Finset ι) (hS₀ : ∀ j, t ≤ (S₀ j).card)
    (hv₁S : ∀ j, ∀ i ∈ S₀ j, v₁ j i = u₁ i)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = u₀ i + γ • u₁ i)
    (hno : ∀ γ ∈ G, ¬ pairJointAgreesOn (C : Set (ι → F)) (S γ) u₀ u₁)
    (hcover : ∀ γ ∈ G, ∃ j, w γ = v₀ j + γ • v₁ j) :
    G.card ≤ L * (Fintype.card ι - t) := by
  classical
  -- assign each bad γ to a curve j and a root coordinate i
  -- e₀ j = u₀ - v₀ j, e₁ j = u₁ - v₁ j; e₁ j vanishes on S₀ j.
  set e₀ : Fin L → ι → F := fun j => u₀ - v₀ j with he₀def
  set e₁ : Fin L → ι → F := fun j => u₁ - v₁ j with he₁def
  -- support bound per curve
  have hsupp : ∀ j, (univ.filter (fun i => e₁ j i ≠ 0)).card ≤ Fintype.card ι - t := by
    intro j
    have hsub : (univ.filter (fun i => e₁ j i ≠ 0)) ⊆ (S₀ j)ᶜ := by
      intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
      simp only [mem_compl]; intro hiS
      exact hi (by simp only [he₁def, Pi.sub_apply, hv₁S j i hiS, sub_self])
    calc (univ.filter (fun i => e₁ j i ≠ 0)).card ≤ (S₀ j)ᶜ.card := card_le_card hsub
      _ = Fintype.card ι - (S₀ j).card := card_compl (S₀ j)
      _ ≤ Fintype.card ι - t := by have := hS₀ j; omega
  -- G ⊆ ⋃_j {γ : ∃i, e₁ j i ≠ 0 ∧ e₀ j i + γ e₁ j i = 0}
  have hGsub : G ⊆ univ.biUnion (fun j : Fin L =>
      univ.filter (fun γ : F => ∃ i, e₁ j i ≠ 0 ∧ e₀ j i + γ * e₁ j i = 0)) := by
    intro γ hγ
    obtain ⟨j, hj⟩ := hcover γ hγ
    rw [mem_biUnion]
    refine ⟨j, mem_univ _, ?_⟩
    rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
    -- ¬pairJointAgreesOn gives i∈S γ with disagreement; w γ=v₀j+γv₁j and =line on S γ
    have hexi : ∃ i ∈ S γ, ¬ (v₀ j i = u₀ i ∧ v₁ j i = u₁ i) := by
      by_contra hcon; push Not at hcon
      exact hno γ hγ ⟨v₀ j, hv₀ j, v₁ j, hv₁ j, fun i hi => hcon i hi⟩
    obtain ⟨i, hiS, hidis⟩ := hexi
    have hci := congrFun hj i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hci
    have hsi := hwS γ hγ i hiS; rw [smul_eq_mul] at hsi
    have hc : u₀ i + γ * u₁ i = v₀ j i + γ * v₁ j i := by rw [← hsi, hci]
    have haff : e₀ j i + γ * e₁ j i = 0 := by
      simp only [he₀def, he₁def, Pi.sub_apply]; linear_combination hc
    have he₁i : e₁ j i ≠ 0 := by
      intro h0; rw [h0, mul_zero, add_zero] at haff
      apply hidis
      refine ⟨?_, ?_⟩
      · have hz : u₀ i - v₀ j i = 0 := by simpa only [he₀def, Pi.sub_apply] using haff
        exact (sub_eq_zero.mp hz).symm
      · have hz : u₁ i - v₁ j i = 0 := by simpa only [he₁def, Pi.sub_apply] using h0
        exact (sub_eq_zero.mp hz).symm
    exact ⟨i, he₁i, haff⟩
  calc G.card
      ≤ (univ.biUnion (fun j : Fin L =>
          univ.filter (fun γ : F => ∃ i, e₁ j i ≠ 0 ∧ e₀ j i + γ * e₁ j i = 0))).card :=
        card_le_card hGsub
    _ ≤ ∑ j : Fin L, (univ.filter (fun γ : F => ∃ i, e₁ j i ≠ 0 ∧ e₀ j i + γ * e₁ j i = 0)).card :=
        card_biUnion_le
    _ ≤ ∑ _j : Fin L, (Fintype.card ι - t) :=
        Finset.sum_le_sum (fun j _ => le_trans (UDRwire.badGamma_le (e₀ j) (e₁ j)) (hsupp j))
    _ = L * (Fintype.card ι - t) := by rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]


open Classical in
/-- **Conditional Johnson/capacity MCA bound from an explicit `L`-curve list cover.** If for every
received line `(u 0, u 1)` there are `L` codeword-pairs `(v₀ j, v₁ j)` with `v₁ j = u 1` on a set
`S₀ j` of size `≥ t`, such that *every* codeword agreeing with the line on a set of size `≥ (1-δ)n`
lies on one of the `L` curves, then `ε_mca(C, δ) ≤ L·(n-t)/q`.

No minimum-distance / unique-decoding hypothesis: the cover is the GS list-decoding output, so this
reaches any radius where the list cover exists (Johnson, capacity).  The cover is exactly the
content of the in-tree `RSCurveListSizeResidual` (the trivariate Guruswami–Sudan list-size bound). -/
theorem epsMCA_le_of_listCover (C : Submodule F (ι → F)) (δ : ℝ≥0) (t L : ℕ)
    (hcover : ∀ u : Code.WordStack F (Fin 2) ι,
      ∃ (v₀ v₁ : Fin L → ι → F) (S₀ : Fin L → Finset ι),
        (∀ j, v₀ j ∈ C) ∧ (∀ j, v₁ j ∈ C) ∧ (∀ j, t ≤ (S₀ j).card) ∧
        (∀ j, ∀ i ∈ S₀ j, v₁ j i = (u 1) i) ∧
        (∀ w ∈ C, ∀ γ : F, (∃ S : Finset ι, ((1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0))
            ∧ (∀ i ∈ S, w i = (u 0) i + γ • (u 1) i)) →
          ∃ j, w = v₀ j + γ • v₁ j)) :
    epsMCA (F := F) (A := F) (C : Set (ι → F)) δ
      ≤ ((L * (Fintype.card ι - t) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  apply epsMCA_le_of_badCount_le (F := F) (A := F) (C : Set (ι → F)) δ (L * (Fintype.card ι - t))
  intro u
  obtain ⟨v₀, v₁, S₀, hv₀, hv₁, hS₀, hv₁S, hlist⟩ := hcover u
  set G : Finset F :=
    univ.filter (fun γ : F => mcaEvent (C : Set (ι → F)) δ (u 0) (u 1) γ) with hGdef
  set S : F → Finset ι := fun γ =>
    if h : mcaEvent (C : Set (ι → F)) δ (u 0) (u 1) γ then h.choose else ∅ with hSdef
  set w : F → ι → F := fun γ =>
    if h : mcaEvent (C : Set (ι → F)) δ (u 0) (u 1) γ
      then (h.choose_spec.2.1).choose else 0 with hwdef
  have hwC : ∀ γ ∈ G, w γ ∈ C := by
    intro γ hγ; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hwdef, dif_pos h]; exact (h.choose_spec.2.1).choose_spec.1
  have hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = (u 0) i + γ • (u 1) i := by
    intro γ hγ i hi; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hwdef, dif_pos h]; simp only [hSdef, dif_pos h] at hi
    exact (h.choose_spec.2.1).choose_spec.2 i hi
  have hno : ∀ γ ∈ G, ¬ pairJointAgreesOn (C : Set (ι → F)) (S γ) (u 0) (u 1) := by
    intro γ hγ; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hSdef, dif_pos h]; exact h.choose_spec.2.2
  have hScard : ∀ γ ∈ G, (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ ((S γ).card : ℝ≥0) := by
    intro γ hγ; rw [hGdef, mem_filter] at hγ; have h := hγ.2
    simp only [hSdef, dif_pos h]; exact h.choose_spec.1
  have hcov : ∀ γ ∈ G, ∃ j, w γ = v₀ j + γ • v₁ j := by
    intro γ hγ
    exact hlist (w γ) (hwC γ hγ) γ ⟨S γ, hScard γ hγ, hwS γ hγ⟩
  rw [hGdef] at *
  exact badCount_listcover_le C (u 0) (u 1) t L v₀ v₁ hv₀ hv₁ S₀ hS₀ hv₁S
    _ S w hwS hno hcov

end ProximityGap.UDR2
