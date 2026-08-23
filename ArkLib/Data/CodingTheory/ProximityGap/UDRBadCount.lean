/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# The unique-decoding-regime MCA bad-scalar bound, from scratch (#232 positive side)

The Table-1 row-2 MCA upper bound `ε_mca(C, δ) ≤ O(δn)/|F|` below the unique-decoding radius
([ACFY25],[BCIKS20], currently an external admit) reduces to a per-stack bound on the number of
"bad" scalars. This file proves that bound from scratch:

  `badCount_udr_le` — for a code `C ⊆ F^ι` with the minimum-distance property `hmd` (codewords
  disagreeing on `< d` coordinates are equal), a stack `(u₀,u₁)` whose bad scalars `G` each carry a
  witness set `S γ` of size `≥ t` and witness codeword `w γ` (`= u₀ + γ·u₁` on `S γ`, not
  pair-joint on `S γ`), in the regime `3(n−t) < d`, satisfies `|G| ≤ 2(n−t)`.

Since `n − t ≈ δn` (the witness miss budget) and the RS minimum distance is `d = n − k + 1`, this
gives `ε_mca ≤ 2δn/|F|` below the unique-decoding radius via
`ProximityGap.epsMCA_le_of_badCount_le`. The proof combines two engines:

* `badGamma_affine_card_le` — bad scalars on the affine error line `e₀ + γ·e₁` are pinned to the
  support of `e₁` (`#bad ≤ weight(e₁)`).
* the line dichotomy — two distinct bad scalars produce nearby codewords `c₀, c₁` agreeing with
  `u₀, u₁` on the witness overlap; minimum distance collapses every bad witness codeword to
  `c₀ + γ·c₁`, so each bad `γ` makes `(u₀−c₀) + γ(u₁−c₁)` vanish on its witness set, with `e₁`
  supported on the `≤ 2(n−t)` coordinates off the overlap.

`pairJoint` here is the local copy of `ProximityGap.pairJointAgreesOn`; wiring this to `mcaEvent`
(extracting the witness data + the RS minimum distance) is the remaining plumbing step toward
tightening the positive-side lower witness past `δ = 0`.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  #232.
- [ACFY25] WHIR; [BCIKS20] Proximity gaps for Reed–Solomon codes.
-/

namespace ProximityGap.UDR

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- Pair-joint agreement on a coordinate set (local copy of `ProximityGap.pairJointAgreesOn`). -/
def pairJoint (C : Submodule F (ι → F)) (S : Finset ι) (u₀ u₁ : ι → F) : Prop :=
  ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i

/-- Root-counting on an arbitrary finite set of scalars: every bad scalar is pinned to a
nonzero coordinate of `e₁`. -/
theorem badGammaOn_le (Γ : Finset F) (e₀ e₁ : ι → F) :
    (Γ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card
      ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun γ =>
      if h : ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0 then h.choose
      else Classical.arbitrary ι)
  · intro γ hγ
    have hp : ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0 := (Finset.mem_filter.mp hγ).2
    simp only [dif_pos hp]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.choose_spec.1⟩
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    have hp₁ : ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ₁ * e₁ i = 0 := (Finset.mem_filter.mp hγ₁).2
    have hp₂ : ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ₂ * e₁ i = 0 := (Finset.mem_filter.mp hγ₂).2
    simp only [dif_pos hp₁, dif_pos hp₂] at heq
    have h1 := hp₁.choose_spec; have h2 := hp₂.choose_spec
    rw [← heq] at h2
    exact mul_right_cancel₀ h1.1
      (by linear_combination h1.2 - h2.2 : γ₁ * e₁ hp₁.choose = γ₂ * e₁ hp₁.choose)

/-- Finite-field specialization of `badGammaOn_le`. -/
theorem badGamma_le [Fintype F] (e₀ e₁ : ι → F) :
    (univ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card
      ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := by
  simpa using badGammaOn_le (univ : Finset F) e₀ e₁

theorem badCount_udr_le (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) (d t : ℕ)
    (htn : t < Fintype.card ι)
    (hmd : ∀ a ∈ C, ∀ b ∈ C, (univ.filter (fun i => a i ≠ b i)).card < d → a = b)
    (hreg : 3 * (Fintype.card ι - t) < d)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hSt : ∀ γ ∈ G, t ≤ (S γ).card)
    (hwC : ∀ γ ∈ G, w γ ∈ C)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = u₀ i + γ • u₁ i)
    (hno : ∀ γ ∈ G, ¬ pairJoint C (S γ) u₀ u₁) :
    G.card ≤ 2 * (Fintype.card ι - t) := by
  classical
  by_cases hG : ∃ γa ∈ G, ∃ γb ∈ G, γa ≠ γb
  · obtain ⟨γa, haG, γb, hbG, hab⟩ := hG
    set T : Finset ι := S γa ∩ S γb with hTdef
    have hd_ab : γa - γb ≠ 0 := sub_ne_zero.mpr hab
    set c₁ : ι → F := (γa - γb)⁻¹ • (w γa - w γb) with hc₁def
    have hc₁C : c₁ ∈ C := C.smul_mem _ (C.sub_mem (hwC γa haG) (hwC γb hbG))
    have hc₁T : ∀ i ∈ T, c₁ i = u₁ i := by
      intro i hi
      rw [hTdef, mem_inter] at hi
      have ea := hwS γa haG i hi.1
      have eb := hwS γb hbG i hi.2
      have hwi : (w γa - w γb) i = (γa - γb) • u₁ i := by
        simp only [Pi.sub_apply, ea, eb, sub_smul]; abel
      simp only [hc₁def, Pi.smul_apply, hwi, inv_smul_smul₀ hd_ab]
    set c₀ : ι → F := w γa - γa • c₁ with hc₀def
    have hc₀C : c₀ ∈ C := C.sub_mem (hwC γa haG) (C.smul_mem _ hc₁C)
    have hc₀T : ∀ i ∈ T, c₀ i = u₀ i := by
      intro i hi
      have hci := hc₁T i hi
      have hmem := hi; rw [hTdef, mem_inter] at hmem
      have ea := hwS γa haG i hmem.1
      simp only [hc₀def, Pi.sub_apply, Pi.smul_apply, hci, ea, smul_eq_mul]; ring
    have hTcard : 2 * t ≤ Fintype.card ι + T.card := by
      have hun : (S γa ∪ S γb).card ≤ Fintype.card ι := by simpa using card_le_univ (S γa ∪ S γb)
      have hui : (S γa ∪ S γb).card + T.card = (S γa).card + (S γb).card :=
        card_union_add_card_inter (S γa) (S γb)
      have ha := hSt γa haG; have hb := hSt γb hbG
      omega
    set e₀ : ι → F := u₀ - c₀ with he₀def
    set e₁ : ι → F := u₁ - c₁ with he₁def
    have he₁T : ∀ i ∈ T, e₁ i = 0 := by
      intro i hi; simp only [he₁def, Pi.sub_apply, hc₁T i hi, sub_self]
    have hsupp : (univ.filter (fun i => e₁ i ≠ 0)).card ≤ 2 * (Fintype.card ι - t) := by
      have hsub : (univ.filter (fun i => e₁ i ≠ 0)) ⊆ Tᶜ := by
        intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
        simp only [mem_compl]; intro hiT; exact hi (he₁T i hiT)
      calc (univ.filter (fun i => e₁ i ≠ 0)).card ≤ Tᶜ.card := card_le_card hsub
        _ = Fintype.card ι - T.card := card_compl T
        _ ≤ 2 * (Fintype.card ι - t) := by omega
    have hGsub : G ⊆ G.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0) := by
      intro γ hγ
      simp only [mem_filter, hγ, true_and]
      have hcollapse : w γ = c₀ + γ • c₁ := by
        apply hmd _ (hwC γ hγ) _ (C.add_mem hc₀C (C.smul_mem _ hc₁C))
        have hsub2 : (univ.filter (fun i => w γ i ≠ (c₀ + γ • c₁) i)) ⊆ (T ∩ S γ)ᶜ := by
          intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
          simp only [mem_compl, mem_inter, not_and]; intro hiT hiS
          apply hi
          have e1 := hc₀T i hiT; have e2 := hc₁T i hiT; have e3 := hwS γ hγ i hiS
          simp only [Pi.add_apply, Pi.smul_apply, e1, e2, e3, smul_eq_mul]
      -- card bound on disagreement
        have hcardle : (univ.filter (fun i => w γ i ≠ (c₀ + γ • c₁) i)).card < d := by
          have hle := card_le_card hsub2
          rw [card_compl] at hle
          have hun : (T ∪ S γ).card ≤ Fintype.card ι := by simpa using card_le_univ (T ∪ S γ)
          have hui : (T ∪ S γ).card + (T ∩ S γ).card = T.card + (S γ).card :=
            card_union_add_card_inter T (S γ)
          have hsg := hSt γ hγ
          omega
        exact hcardle
      have hnpj := hno γ hγ
      have hexi : ∃ i ∈ S γ, ¬ (c₀ i = u₀ i ∧ c₁ i = u₁ i) := by
        by_contra hcon; push Not at hcon
        exact hnpj ⟨c₀, hc₀C, c₁, hc₁C, fun i hi => hcon i hi⟩
      obtain ⟨i, hiS, hidis⟩ := hexi
      have hci := congrFun hcollapse i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hci
      have hsi := hwS γ hγ i hiS
      rw [smul_eq_mul] at hsi
      have hc : u₀ i + γ * u₁ i = c₀ i + γ * c₁ i := by rw [← hsi, hci]
      have haff : e₀ i + γ * e₁ i = 0 := by
        simp only [he₀def, he₁def, Pi.sub_apply]; linear_combination hc
      have he₁i : e₁ i ≠ 0 := by
        intro h0
        rw [h0, mul_zero, add_zero] at haff
        apply hidis
        refine ⟨?_, ?_⟩
        · have hz : u₀ i - c₀ i = 0 := by simpa only [he₀def, Pi.sub_apply] using haff
          exact (sub_eq_zero.mp hz).symm
        · have hz : u₁ i - c₁ i = 0 := by simpa only [he₁def, Pi.sub_apply] using h0
          exact (sub_eq_zero.mp hz).symm
      exact ⟨i, he₁i, haff⟩
    calc G.card
        ≤ (G.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card :=
          card_le_card hGsub
      _ ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := badGammaOn_le G e₀ e₁
      _ ≤ 2 * (Fintype.card ι - t) := hsupp
  · push Not at hG
    have h1 : G.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => hG a ha b hb)
    omega


#print axioms badGammaOn_le
#print axioms badGamma_le
#print axioms badCount_udr_le

end ProximityGap.UDR
