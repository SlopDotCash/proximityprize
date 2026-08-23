/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HigherOrderMDSList
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The general-position list bound (#389, layer 4)

The general-position case of the Brakensiek–Gopi–Makam list-decoding bound, proven from
the layer-3 dual squeeze.  For `L+1` messages `m₀,…,m_L` whose difference functionals
`dⱼ = m_{j+1} − m₀` are **linearly independent** (the messages are affinely independent —
"in general position"), ordinary MDS alone caps the list at the capacity radius:

* `mds_genpos_inter_card_le` — the common agreement set has `|⋂ᵢ Aᵢ| ≤ k − L`.
* `card_common_inter_ge` — Bonferroni: `|⋂ᵢ Aᵢ| ≥ Σ|Aᵢ| − L·n`.
* `mds_genpos_list_bound` — hence `(L+1)·a ≤ L·n + (k − L)`: above the capacity radius
  `(Ln + k − L)/(L+1)` the affinely-independent list has size `≤ L`.

Mechanism: each column `v_ζ` with `ζ ∈ ⋂Aᵢ` is killed by all `L` independent differences,
so lies in `D.dualCoannihilator` (`D = span{dⱼ}`, dim `L`), which has dimension `k − L`;
MDS makes any `≤ k` columns independent, so at most `k − L` fit.  The affinely *dependent*
clusters are exactly what higher-order MDS (`IsHigherMDS`) is needed for — the deep/open
direction for explicit smooth domains.

Issue #389.
-/

open Finset Module ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq K]

/-- **The general-position (affinely-independent) common-agreement bound.**  If the
difference functionals `dⱼ = m_{j+1} − m₀` are linearly independent, the columns indexed
by any set `S` on which every `dⱼ` vanishes number at most `k − L`. -/
theorem mds_genpos_inter_card_le {L : ℕ} (hL1 : 1 ≤ L) (hL : L < finrank K V) {v : ι → V}
    (hv : IsMDSFrame K v) {m : Fin (L + 1) → Module.Dual K V}
    (hindep : LinearIndependent K (fun j : Fin L => m j.succ - m 0))
    {S : Finset ι} (hSzero : ∀ ζ ∈ S, ∀ j : Fin L, (m j.succ - m 0) (v ζ) = 0) :
    S.card ≤ finrank K V - L := by
  classical
  set d : Fin L → Module.Dual K V := fun j => m j.succ - m 0 with hd
  set D : Submodule K (Module.Dual K V) := Submodule.span K (Set.range d) with hD
  have hDfin : finrank K ↥D = L := by
    rw [hD, finrank_span_eq_card hindep, Fintype.card_fin]
  have hW : finrank K ↥D.dualCoannihilator = finrank K V - L := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq D
    rw [hDfin] at h; omega
  have hmemW : ∀ ζ ∈ S, v ζ ∈ D.dualCoannihilator := by
    intro ζ hζ
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    refine Submodule.span_induction (p := fun φ _ => φ (v ζ) = 0) ?_ ?_ ?_ ?_ hφ
    · rintro x ⟨j, rfl⟩; exact hSzero ζ hζ j
    · simp
    · intro a b _ _ ha hb; simp [ha, hb]
    · intro c x _ hx; simp [hx]
  by_contra hcon
  push_neg at hcon
  obtain ⟨S', hS'sub, hS'card⟩ :=
    Finset.exists_subset_card_eq (show finrank K V - L + 1 ≤ S.card by omega)
  have hS'le : S'.card ≤ finrank K V := by rw [hS'card]; omega
  have hspan_le : frameSpan K v S' ≤ D.dualCoannihilator := by
    rw [frameSpan, Submodule.span_le]
    rintro x ⟨ζ, hζ, rfl⟩
    exact hmemW ζ (hS'sub hζ)
  have h1 : finrank K ↥(frameSpan K v S') = finrank K V - L + 1 := by
    rw [finrank_frameSpan hv hS'le, hS'card]
  have h2 : finrank K ↥(frameSpan K v S') ≤ finrank K ↥D.dualCoannihilator :=
    Submodule.finrank_mono hspan_le
  rw [h1, hW] at h2
  omega

/-- Bonferroni: the common intersection of `L+1` finsets has `|⋂ Aᵢ| ≥ Σ|Aᵢ| − L·n`. -/
theorem card_common_inter_ge {L : ℕ} (A : Fin (L + 1) → Finset ι) :
    ∑ i, (A i).card ≤
      (Finset.univ.filter (fun ζ => ∀ i, ζ ∈ A i)).card + L * Fintype.card ι := by
  classical
  set S := Finset.univ.filter (fun ζ : ι => ∀ i, ζ ∈ A i) with hS
  have hcompl : Sᶜ = Finset.univ.biUnion (fun i => (A i)ᶜ) := by
    ext ζ
    simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, not_forall]
  have hcard_compl : Sᶜ.card ≤ ∑ i, (A i)ᶜ.card := by
    rw [hcompl]; exact Finset.card_biUnion_le
  have hScompl : S.card + Sᶜ.card = Fintype.card ι := Finset.card_add_card_compl S
  have hpair : (∑ i, (A i)ᶜ.card) + ∑ i, (A i).card = (L + 1) * Fintype.card ι := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun i _ => Finset.card_compl_add_card (A i)),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hexp : (L + 1) * Fintype.card ι = L * Fintype.card ι + Fintype.card ι := by ring
  omega

/-- **The general-position capacity list bound.**  An affinely-independent family of
`L+1` messages (differences linearly independent) cannot all agree with `y` on `≥ a`
coordinates once `(L+1)·a > L·n + (k − L)` — the affinely-independent list at agreement
`a` has size `≤ L` above the capacity radius.  (Affinely *dependent* clusters need
higher-order MDS — the deep direction for explicit smooth domains.) -/
theorem mds_genpos_list_bound {L : ℕ} (hL1 : 1 ≤ L) (hL : L < finrank K V) {v : ι → V}
    (hv : IsMDSFrame K v) {m : Fin (L + 1) → Module.Dual K V} {y : ι → K}
    (hindep : LinearIndependent K (fun j : Fin L => m j.succ - m 0))
    {a : ℕ} (hagree : ∀ i, a ≤ (agreeFinset v y (m i)).card) :
    (L + 1) * a ≤ L * Fintype.card ι + (finrank K V - L) := by
  classical
  set A : Fin (L + 1) → Finset ι := fun i => agreeFinset v y (m i) with hA
  set S := Finset.univ.filter (fun ζ : ι => ∀ i, ζ ∈ A i) with hS
  have hSzero : ∀ ζ ∈ S, ∀ j : Fin L, (m j.succ - m 0) (v ζ) = 0 := by
    intro ζ hζ j
    have hmem := (Finset.mem_filter.mp hζ).2
    have h0 : m 0 (v ζ) = y ζ := (mem_agreeFinset).mp (hmem 0)
    have hj : m j.succ (v ζ) = y ζ := (mem_agreeFinset).mp (hmem j.succ)
    show m j.succ (v ζ) - m 0 (v ζ) = 0
    rw [hj, h0, sub_self]
  have hScard : S.card ≤ finrank K V - L :=
    mds_genpos_inter_card_le hL1 hL hv hindep hSzero
  have hbon := card_common_inter_ge A
  have hsum : (L + 1) * a ≤ ∑ i, (A i).card := by
    calc (L + 1) * a = ∑ _i : Fin (L + 1), a := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ i, (A i).card := Finset.sum_le_sum (fun i _ => hagree i)
  rw [← hS] at hbon
  omega

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.mds_genpos_inter_card_le
#print axioms ArkLib.HigherOrderMDS.card_common_inter_ge
#print axioms ArkLib.HigherOrderMDS.mds_genpos_list_bound
