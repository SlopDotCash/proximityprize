/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HigherOrderMDSFrame
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Higher-order MDS and list decoding: the dual-annihilator entry (#389, layer 3)

The Brakensiek–Gopi–Makam list-decoding argument, set up over the frame model of
layer 2.  Messages are dual functionals `m : Module.Dual K V`; the codeword value at
coordinate `ζ` is `m (v ζ)` (for RS, `m` is the message polynomial's coefficient
functional and `m (v ζ) = p(ζ)`).  A received word is `y : ι → K`, and the agreement
set of a message is `{ζ : m (v ζ) = y ζ}`.

**The entry lemma** (`diff_mem_dualAnnihilator`): if two messages `m, m'` agree with `y`
on a common set `J`, their difference `m − m'` lies in the **dual annihilator** of the
column-span `frameSpan K v J`.  Under an MDS frame that annihilator has dimension
`k − |J|` (`finrank_dualAnnihilator_frameSpan`), so a *large* common agreement set forces
the difference into a *small* subspace — the dimension squeeze that, iterated over `L+1`
codewords against higher-order genericity, yields the BGM list bound.

This is the entry point; the full bound (MDS(L+1) ⟹ list ≤ L past Johnson) chains these
squeezes against `IsHigherMDS`.

Issue #389.
-/

open Finset Module ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq K]

/-- The agreement set of a message functional `m` with a received word `y`. -/
noncomputable def agreeFinset (v : ι → V) (y : ι → K) (m : Module.Dual K V) : Finset ι :=
  Finset.univ.filter (fun ζ => m (v ζ) = y ζ)

@[simp] theorem mem_agreeFinset {v : ι → V} {y : ι → K} {m : Module.Dual K V} {ζ : ι} :
    ζ ∈ agreeFinset v y m ↔ m (v ζ) = y ζ := by
  simp [agreeFinset]

/-- **The dual-annihilator entry lemma.**  If messages `m, m'` both agree with `y` on
every coordinate of `J`, their difference annihilates the column-span `frameSpan K v J`. -/
theorem diff_mem_dualAnnihilator (K : Type*) [Field K] [Module K V] (v : ι → V)
    {y : ι → K} {m m' : Module.Dual K V} {J : Finset ι}
    (hm : ∀ ζ ∈ J, m (v ζ) = y ζ) (hm' : ∀ ζ ∈ J, m' (v ζ) = y ζ) :
    (m - m') ∈ (frameSpan K v J).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro w hw
  -- vanish on the spanning set, then on the span
  refine Submodule.span_induction (p := fun w _ => (m - m') w = 0) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨ζ, hζ, rfl⟩
    have : (m - m') (v ζ) = m (v ζ) - m' (v ζ) := by simp
    rw [this, hm ζ hζ, hm' ζ hζ, sub_self]
  · simp
  · intro x z _ _ hx hz; simp [map_add, hx, hz]
  · intro a x _ hx; simp [map_smul, hx]

/-- Under an MDS frame, the difference annihilator from a `≤ k` agreement set has the
*small* dimension `k − |J|`: a large agreement set squeezes the difference. -/
theorem finrank_dualAnnihilator_frameSpan {v : ι → V} (hv : IsMDSFrame K v)
    {J : Finset ι} (hJ : J.card ≤ finrank K V) :
    finrank K ↥(frameSpan K v J).dualAnnihilator = finrank K V - J.card := by
  have hadd := Subspace.finrank_add_finrank_dualAnnihilator_eq (frameSpan K v J)
  rw [finrank_frameSpan hv hJ] at hadd
  omega

/-! ## The `L = 1` case: the MDS minimum-distance bound, via the squeeze -/

/-- Under an MDS frame, a `≥ k`-column span is everything. -/
theorem frameSpan_eq_top_of_card_ge {v : ι → V} (hv : IsMDSFrame K v) {J : Finset ι}
    (hJ : finrank K V ≤ J.card) : frameSpan K v J = ⊤ := by
  classical
  obtain ⟨J', hJ'sub, hJ'card⟩ := Finset.exists_subset_card_eq hJ
  have hsub : frameSpan K v J' ≤ frameSpan K v J :=
    Submodule.span_mono (Set.image_mono (by exact_mod_cast hJ'sub))
  have htop : frameSpan K v J' = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_frameSpan hv (by omega), hJ'card])
  exact top_le_iff.mp (htop ▸ hsub)

/-- **The MDS minimum-distance bound, derived through the higher-order-MDS dual squeeze.**
Two *distinct* message functionals agree on at most `k − 1` coordinates (codeword
Hamming distance `≥ n − k + 1`).  This is the `L = 1` (unique-decoding) case of the BGM
list argument: the difference is squeezed into the dual annihilator of the agreement
column-span, which collapses to `0` once the agreement reaches `k`. -/
theorem messages_agree_card_lt_of_ne {v : ι → V} (hv : IsMDSFrame K v)
    {m m' : Module.Dual K V} (hne : m ≠ m') :
    (Finset.univ.filter (fun ζ => m (v ζ) = m' (v ζ))).card < finrank K V := by
  classical
  by_contra hge
  push_neg at hge
  set J := Finset.univ.filter (fun ζ => m (v ζ) = m' (v ζ)) with hJ
  have hmem : (m - m') ∈ (frameSpan K v J).dualAnnihilator :=
    diff_mem_dualAnnihilator K v (y := fun ζ => m' (v ζ))
      (fun ζ hζ => (Finset.mem_filter.mp hζ).2) (fun _ _ => rfl)
  rw [frameSpan_eq_top_of_card_ge hv hge, Submodule.dualAnnihilator_top,
    Submodule.mem_bot] at hmem
  exact hne (sub_eq_zero.mp hmem)

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.diff_mem_dualAnnihilator
#print axioms ArkLib.HigherOrderMDS.finrank_dualAnnihilator_frameSpan
#print axioms ArkLib.HigherOrderMDS.frameSpan_eq_top_of_card_ge
#print axioms ArkLib.HigherOrderMDS.messages_agree_card_lt_of_ne
