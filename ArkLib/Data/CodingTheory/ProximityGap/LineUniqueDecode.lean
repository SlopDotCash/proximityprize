/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineSecondMomentSharp

/-!
# Issue #232: per-line unique decoding above the unique-decoding radius (round 14f)

The capstone of the per-line decode chain (rounds 14–14e): when the agreement threshold `a` is large
enough that `2(n−a)` falls below the code's minimum distance, **every line point decodes to at most
one codeword** — the per-line unique-decoding theorem. It needs no linearity, no RS structure, only
the proven close-pair sharpening: in that regime there are no close pairs at all, so the per-line
second moment collapses onto the first moment, forcing every list to size `≤ 1`.

**Statement.** If every distinct codeword pair is at Hamming distance `> 2(n−a)` (i.e. the minimum
distance `d` satisfies `2(n−a) < d`, equivalently `a` is above the unique-decoding radius
`n − d/2`), then for every line point `γ`, `|Λ(γ,a)| ≤ 1`.

**Proof.** `closePairs = ∅` (no pair is within `2(n−a)`), so by `offDiag_badSet_sum_eq_close` the
entire off-diagonal of the per-line second moment vanishes; `line_sq_sum_eq` then reads
`∑_γ |Λ(γ,a)|² = ∑_γ |Λ(γ,a)|`. Since `|Λ| ≤ |Λ|²` termwise over `ℕ`, equality of the sums forces
`|Λ(γ)|² = |Λ(γ)|` for every `γ`, i.e. `|Λ(γ)| ∈ {0,1}`.

For Reed–Solomon (MDS, `d = n − k + 1`) the hypothesis is `2(n−a) < n − k + 1`, i.e.
`a > (n + k − 1)/2` — exactly the classical unique-decoding (half-minimum-distance) radius, now
proven *per line*: above it, the proximity-gap list is trivial on every line.

Axiom-clean: `propext, Classical.choice, Quot.sound`.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **No close pairs above the unique-decoding radius.** If every distinct codeword pair is at
distance `> 2(n−a)`, the close-pair set is empty. -/
theorem closePairs_empty_of_minDist (C : Finset (Fin n → F)) (a : ℕ)
    (hmin : ∀ p ∈ C.offDiag, 2 * (n - a) < (supp p.1 p.2).card) :
    closePairs C a = ∅ := by
  classical
  rw [closePairs, Finset.filter_eq_empty_iff]
  intro p hp
  exact Nat.not_le.mpr (hmin p hp)

/-- **Per-line unique decoding above the unique-decoding radius.** If every distinct codeword pair
is at distance `> 2(n−a)`, then every line point's agreement-`≥a` list has size at most `1`. -/
theorem line_uniqueDecode_of_minDist (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ)
    (hn : n < 2 * a)
    (hmin : ∀ p ∈ C.offDiag, 2 * (n - a) < (supp p.1 p.2).card) (γ : F) :
    (lineList C f g a γ).card ≤ 1 := by
  classical
  -- The off-diagonal of the per-line second moment vanishes (no close pairs).
  have hoff : ∑ p ∈ C.offDiag, (badSet f g p.1 p.2 a).card = 0 := by
    rw [offDiag_badSet_sum_eq_close C f g a hn, closePairs_empty_of_minDist C a hmin,
      Finset.sum_empty]
  -- Hence `∑_γ |Λ(γ)|² = ∑_γ |Λ(γ)|`.
  have hsq : ∑ γ : F, (lineList C f g a γ).card ^ 2
      = ∑ γ : F, (lineList C f g a γ).card := by
    rw [line_sq_sum_eq, hoff, add_zero]
  -- Termwise `|Λ| ≤ |Λ|²`, so the sum equality forces `|Λ(γ)|² = |Λ(γ)|` everywhere.
  have hle : ∀ δ ∈ (Finset.univ : Finset F),
      (lineList C f g a δ).card ≤ (lineList C f g a δ).card ^ 2 := by
    intro δ _; nlinarith [Nat.zero_le (lineList C f g a δ).card]
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hsq.symm γ (Finset.mem_univ γ)
  -- `|Λ(γ)| = |Λ(γ)|²` over `ℕ` forces `|Λ(γ)| ≤ 1`.
  nlinarith [heq, Nat.zero_le (lineList C f g a γ).card]

/-- **List form.** Above the unique-decoding radius the per-line list is empty or a singleton. -/
theorem lineList_subsingleton_of_minDist (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ)
    (hn : n < 2 * a)
    (hmin : ∀ p ∈ C.offDiag, 2 * (n - a) < (supp p.1 p.2).card) (γ : F) :
    (lineList C f g a γ).card = 0 ∨ (lineList C f g a γ).card = 1 := by
  have h := line_uniqueDecode_of_minDist C f g a hn hmin γ
  omega

end LinePairCooccurrence
