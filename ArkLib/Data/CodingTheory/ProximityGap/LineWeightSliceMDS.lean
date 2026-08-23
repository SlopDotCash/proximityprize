/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineClosePairsLinear

/-!
# Issue #232: the MDS information-set collapse of the per-line weight slice (round 14h)

The per-line chain (rounds 14–14g) reduced the second-moment off-diagonal to `|C| · |weightSlice|`,
the `w ≤ 2(n−a)` slice of the code's weight enumerator. This file instantiates that for an **MDS**
code (Reed–Solomon is MDS) via the genuine MDS property — the **information-set / Singleton-sharp**
fact that *any `k` coordinates determine the codeword*, equivalently: a codeword with at least `k`
zero coordinates is the zero codeword.

**MDS weight-slice vanishing.** Under that property, the weight slice is empty up to `r = n − k`:
    `weightSlice C r = ∅`  whenever  `r ≤ n − k`.
Reason: a nonzero codeword of weight `≤ r` has `≥ n − r ≥ k` zero coordinates (when `r ≤ n − k`), so
by the MDS property it is `0` — contradiction. This is the Singleton bound `d = n − k + 1` recovered
from the information-set property (`r ≤ n − k = d − 1 ⟹ A_r = 0`), the fundamental reason the
per-line chain is trivial above the unique-decoding radius.

**Per-line MDS unique decoding.** Feeding this into the close-pair collapse, for an MDS code every
line point decodes to at most one codeword once `a ≥ (n+k)/2`:
    `2(n−a) ≤ n − k ⟺ n + k ≤ 2a ⟺ a ≥ (n+k)/2`,
the explicit Reed–Solomon half-minimum-distance radius. Above it the proximity-gap list is trivial on
every line; the open interior `(1−√ρ, 1−ρ)` lies strictly below, where `2(n−a) > n − k` and the
weight slice `∑_{w=d}^{2(n−a)} A_w` is genuinely nonzero — the RS object the prize turns on.

Axiom-clean: `propext, Classical.choice, Quot.sound`.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The zero-coordinate set of a word equals its off-support against `0`. -/
theorem zeros_eq_offSupp (e : Fin n → F) :
    Finset.univ.filter (fun i => e i = 0) = offSupp e 0 := by
  ext i; simp [offSupp]

/-- A word of weight `≤ r` has at least `n − r` zero coordinates. -/
theorem zeros_card_ge_of_weight_le (e : Fin n → F) (r : ℕ) (hw : (supp e 0).card ≤ r) :
    n - r ≤ (offSupp e 0).card := by
  have hpart := offSupp_card_add_supp_card e (0 : Fin n → F)
  omega

/-- **MDS weight-slice vanishing.** If the code has the information-set property — any codeword with
`≥ k` zero coordinates is `0` — then the weight slice is empty up to radius `n − k`. -/
theorem weightSlice_eq_empty_of_mds (C : Finset (Fin n → F)) (k r : ℕ)
    (hMDS : ∀ e ∈ C, k ≤ (offSupp e (0 : Fin n → F)).card → e = 0)
    (hkn : k ≤ n) (hr : r ≤ n - k) :
    weightSlice C r = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_weightSlice] at he
  obtain ⟨heC, hene, hew⟩ := he
  -- `e` has `≥ n − r ≥ k` zeros, so the MDS property forces `e = 0`, contradicting `e ≠ 0`.
  have hzeros : k ≤ (offSupp e (0 : Fin n → F)).card := by
    have := zeros_card_ge_of_weight_le e r hew
    omega
  exact hene (hMDS e heC hzeros)

/-- **Per-line MDS unique decoding.** For a linear MDS code, once `a ≥ (n+k)/2` (equivalently
`2(n−a) ≤ n − k`), every line point's agreement-`≥a` list has size at most `1` — the explicit
Reed–Solomon half-minimum-distance radius, proven per line. -/
theorem line_uniqueDecode_of_mds (C : Finset (Fin n → F)) (f g : Fin n → F) (a k : ℕ)
    (hg : ∀ i, g i ≠ 0) (hn : n < 2 * a)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c' - c ∈ C)
    (hMDS : ∀ e ∈ C, k ≤ (offSupp e (0 : Fin n → F)).card → e = 0)
    (hkn : k ≤ n) (hrad : 2 * (n - a) ≤ n - k) (γ : F) :
    (lineList C f g a γ).card ≤ 1 := by
  classical
  -- The weight slice vanishes, so there are no close pairs, so the off-diagonal is `0`.
  have hslice : weightSlice C (2 * (n - a)) = ∅ :=
    weightSlice_eq_empty_of_mds C k (2 * (n - a)) hMDS hkn hrad
  have hclose : closePairs C a = ∅ := by
    rw [← Finset.card_eq_zero, closePairs_card_linear C a hC, hslice, Finset.card_empty,
      Nat.mul_zero]
  -- Off-diagonal of the per-line second moment vanishes ⟹ `∑|Λ|² = ∑|Λ|` ⟹ `|Λ(γ)| ≤ 1`.
  have hoff : ∑ p ∈ C.offDiag, (badSet f g p.1 p.2 a).card = 0 := by
    rw [offDiag_badSet_sum_eq_close C f g a hn, hclose, Finset.sum_empty]
  have hsq : ∑ δ : F, (lineList C f g a δ).card ^ 2
      = ∑ δ : F, (lineList C f g a δ).card := by
    rw [line_sq_sum_eq, hoff, add_zero]
  have hle : ∀ δ ∈ (Finset.univ : Finset F),
      (lineList C f g a δ).card ≤ (lineList C f g a δ).card ^ 2 := by
    intro δ _; nlinarith [Nat.zero_le (lineList C f g a δ).card]
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hsq.symm γ (Finset.mem_univ γ)
  nlinarith [heq, Nat.zero_le (lineList C f g a γ).card]

end LinePairCooccurrence
