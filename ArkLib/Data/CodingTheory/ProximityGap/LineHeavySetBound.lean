/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineSecondMomentBound

/-!
# Issue #232: the per-line heavy-decode-set bound (round 14c)

The proximity gap property is a *dichotomy*: on a line `{f + γ·g}`, either almost no point is
`δ`-close to the code, or essentially all of it is. The hard direction the prize needs is the
quantitative "few bad points" side: **how many line points decode heavily?** This file gives the
per-line answer by the second-moment method, on top of the proven per-line second-moment chain
(rounds 14/14b).

**Heavy-set bound (Markov on squares over the line).** Let `Λ(γ,a)` be the agreement-`≥a` list of a
code `C` at the line point `γ`. For any threshold `L`,
    `#{γ : |Λ(γ,a)| ≥ L} · L²  ≤  ∑_γ |Λ(γ,a)|²`.
Combined with the distance-uniform per-line second-moment bound (`line_second_moment_bound`, valid in
the regime `2a > n`, i.e. `δ < 1/2` — the whole `ρ = 1/2` prize window), this gives the closed bound
    `#{γ : |Λ(γ,a)| ≥ L} · L² · (2a−d)  ≤  (∑_γ |Λ(γ,a)|) · (2a−d) + (|C|²−|C|) · 2(n−d)`.

So the number of heavily-decoding line points falls off as `1/L²` against the second moment, whose
off-diagonal is a *distance-uniform constant per pair* (the round-14 gain) rather than the
past-Johnson-blowing ball-intersection volume. This is the per-line, quantitative form of the
proximity-gap "few bad points" side — the object the per-code threshold `δ*` is read from.

Axiom-clean: `propext, Classical.choice, Quot.sound`.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **heavy set**: line parameters whose agreement-`≥a` list has size at least `L`. -/
def heavyLineSet (C : Finset (Fin n → F)) (f g : Fin n → F) (a L : ℕ) : Finset F :=
  Finset.univ.filter (fun γ => L ≤ (lineList C f g a γ).card)

@[simp] theorem mem_heavyLineSet {C : Finset (Fin n → F)} {f g : Fin n → F} {a L : ℕ} {γ : F} :
    γ ∈ heavyLineSet C f g a L ↔ L ≤ (lineList C f g a γ).card := by
  simp [heavyLineSet]

/-- **Markov on squares over the line.** The number of line points with list size `≥ L`, times
`L²`, is at most the per-line second moment `∑_γ |Λ(γ,a)|²`. -/
theorem heavyLineSet_card_mul_sq_le (C : Finset (Fin n → F)) (f g : Fin n → F) (a L : ℕ) :
    (heavyLineSet C f g a L).card * L ^ 2 ≤ ∑ γ : F, (lineList C f g a γ).card ^ 2 := by
  classical
  calc (heavyLineSet C f g a L).card * L ^ 2
      = ∑ _γ ∈ heavyLineSet C f g a L, L ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ heavyLineSet C f g a L, (lineList C f g a γ).card ^ 2 :=
        Finset.sum_le_sum (fun γ hγ =>
          Nat.pow_le_pow_left (mem_heavyLineSet.mp hγ) 2)
    _ ≤ ∑ γ : F, (lineList C f g a γ).card ^ 2 :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The per-line heavy-decode-set bound** (`2a > n` regime, code of minimum pair distance `d`):
the number of line points whose agreement-`≥a` list reaches size `L`, scaled by `L²·(2a−d)`, is
bounded by the per-line first moment plus the distance-uniform off-diagonal term. As `L` grows the
heavy set shrinks as `1/L²` against a second moment whose off-diagonal is a per-pair *constant*
(not the past-Johnson ball-intersection volume) — the per-line quantitative "few bad points". -/
theorem heavyLineSet_card_bound (C : Finset (Fin n → F)) (f g : Fin n → F) (a d L : ℕ)
    (hg : ∀ i, g i ≠ 0) (hn : n < 2 * a)
    (hd : ∀ p ∈ C.offDiag, d ≤ (supp p.1 p.2).card) :
    (heavyLineSet C f g a L).card * L ^ 2 * (2 * a - d)
      ≤ (∑ γ : F, (lineList C f g a γ).card) * (2 * a - d)
        + (C.card * C.card - C.card) * (2 * (n - d)) := by
  calc (heavyLineSet C f g a L).card * L ^ 2 * (2 * a - d)
      = ((heavyLineSet C f g a L).card * L ^ 2) * (2 * a - d) := by ring
    _ ≤ (∑ γ : F, (lineList C f g a γ).card ^ 2) * (2 * a - d) :=
        Nat.mul_le_mul_right _ (heavyLineSet_card_mul_sq_le C f g a L)
    _ ≤ (∑ γ : F, (lineList C f g a γ).card) * (2 * a - d)
          + (C.card * C.card - C.card) * (2 * (n - d)) :=
        line_second_moment_bound C f g a d hg hn hd

/-- **Singleton-heavy specialisation.** With `L = 1` the heavy set is the set of line points that
decode at all (`Λ(γ,a)` nonempty), recovering a first-moment count; the interest is `L ≥ 2`, where
the `L²` denominator makes the heavy set genuinely sparse. Recorded as the base instance. -/
theorem decodingLineSet_card_le (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ) :
    (heavyLineSet C f g a 1).card ≤ ∑ γ : F, (lineList C f g a γ).card ^ 2 := by
  simpa using heavyLineSet_card_mul_sq_le C f g a 1

end LinePairCooccurrence
