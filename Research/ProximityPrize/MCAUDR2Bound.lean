/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.MCAUDRBound
import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement

/-!
# List-cover MCA bounds for linear codes (beyond the unique-decoding radius)

The full unique-decoding-radius Reed–Solomon bound `ε_mca(RS, δ) ≤ n/q` for `δ ≤ relUDR`
(regime `2(n − t) < n − k + 1`, `t = ⌈(1-δ)n⌉`) is `UDRwire.epsMCA_rs_udr_le_full` in
`Research.ProximityPrize.MCAUDRBound`, with bad-count core
`UDRwire.badCount_udr_le_jointAgreement`. (This file previously carried verbatim copies of both,
`UDR2.badCount_udr2_le` / `UDR2.epsMCA_rs_udr2_le`, under a header that wrongly claimed the
in-tree bound only reached the factor-3 regime; they were removed and their consumers retargeted.)

This file keeps the genuinely new multi-curve generalisation: if every bad witness lies on one of
`L` codeword curves `v₀ j + γ • v₁ j` (a structural list cover), the bad count is `≤ L·(n − t)`,
with no minimum-distance hypothesis.

## Main results

* `badCount_listcover_le` — the `L`-curve bad-count core.
* `epsMCA_le_of_listCover` — `ε_mca(C, δ) ≤ L·(n − t)/q`, conditional on an explicit list cover.

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

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

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
    exact UDRwire.exists_root_of_curve_witness C u₀ u₁ (v₀ j) (v₁ j) (hv₀ j) (hv₁ j)
      (S γ) γ (w γ) (hwS γ hγ) (hno γ hγ) hj
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
reaches any radius where the list cover exists (Johnson, capacity).  The cover is a structural
hypothesis (every close codeword at every `γ` lies on one of `L` fixed curves); it is *not* the
counting inequality `RSCurveListSizeResidual` (`|G.image cw| · (k·n) < |G|` along a good curve),
and no bridge from that residual to this cover is proved in-tree. -/
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
