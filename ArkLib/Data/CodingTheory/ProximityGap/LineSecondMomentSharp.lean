/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineSecondMomentBound

/-!
# Issue #232: the close-pair-restricted per-line second moment (round 14e)

The round-14b second-moment bound charges the off-diagonal to the *trivial* pair count
`|C|² − |C|` (all ordered codeword pairs). This is lossy: by the proven `badSet_eq_empty`, a pair
at Hamming distance `w > 2(n−a)` (the **far** pairs) contributes **zero** to the off-diagonal — no
line point can decode both. Only the **close** pairs `w ≤ 2(n−a)` count, and their number is exactly
the object the MDS / RS weight enumerator controls (and is tiny for a high-distance code).

Crucially, in the `2a > n` window (`δ < 1/2`, the whole `ρ = 1/2` prize window) every close pair
automatically satisfies the uniform-bound hypothesis `2a > w`: `w ≤ 2(n−a) = 2n − 2a < 2a ⟺ n < 2a`.
So the two round-14 facts dovetail exactly — far pairs vanish, close pairs obey the uniform bound —
with no gap between the regimes.

**Sharp per-line second moment.** With `closePairs := {p ∈ C.offDiag : Δ(p) ≤ 2(n−a)}`,
    `(∑_γ |Λ(γ,a)|²) · (2a−d)  ≤  (∑_γ |Λ(γ,a)|) · (2a−d) + |closePairs| · 2(n−d)`.
This replaces `|C|² − |C|` by `|closePairs|` — the genuine RS object, the `w ≤ 2(n−a)` slice of the
weight enumerator. Combined with the first moment (`M·a ≤ |C|·n`, round-14d) the per-line decode
heaviness is now controlled by `(|C|·n` and `|closePairs|)` — the latter is where smooth-domain RS
structure must finally enter the prize.

Axiom-clean: `propext, Classical.choice, Quot.sound`.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **close pairs**: ordered codeword pairs at Hamming distance `≤ 2(n−a)`. Only these
contribute to the per-line second-moment off-diagonal. -/
def closePairs (C : Finset (Fin n → F)) (a : ℕ) : Finset ((Fin n → F) × (Fin n → F)) :=
  C.offDiag.filter (fun p => (supp p.1 p.2).card ≤ 2 * (n - a))

/-- **Far pairs vanish.** A pair at distance `> 2(n−a)` has empty per-line bad set: no line point
decodes both. (The proven `badSet_eq_empty`, fed `2·|offSupp|+|supp| = 2n − w < 2a`.) -/
theorem badSet_empty_of_far (f g c c' : Fin n → F) (a : ℕ) (hn : n < 2 * a)
    (hfar : 2 * (n - a) < (supp c c').card) :
    badSet f g c c' a = ∅ := by
  apply badSet_eq_empty
  have hpart := offSupp_card_add_supp_card c c'
  set w := (supp c c').card with hw
  have hwn : w ≤ n := by omega
  have hoff : (offSupp c c').card = n - w := by omega
  rw [hoff]
  -- `2(n−w) + w = 2n − w`; far means `w > 2(n−a) = 2n − 2a`, so `2n − w < 2a`.
  omega

/-- **Off-diagonal restricts to close pairs.** The far terms are zero, so the full off-diagonal sum
equals the sum over `closePairs`. -/
theorem offDiag_badSet_sum_eq_close (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ)
    (hn : n < 2 * a) :
    ∑ p ∈ C.offDiag, (badSet f g p.1 p.2 a).card
      = ∑ p ∈ closePairs C a, (badSet f g p.1 p.2 a).card := by
  classical
  rw [closePairs, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  by_cases hclose : (supp p.1 p.2).card ≤ 2 * (n - a)
  · rw [if_pos hclose]
  · rw [if_neg hclose]
    rw [badSet_empty_of_far f g p.1 p.2 a hn (by omega), Finset.card_empty]

/-- **The close-pair-restricted per-line second moment.** Strictly sharper than
`line_second_moment_bound`: the off-diagonal is charged to `|closePairs|` (the `w ≤ 2(n−a)` weight
slice) instead of the trivial `|C|² − |C|`. -/
theorem line_second_moment_bound_sharp (C : Finset (Fin n → F)) (f g : Fin n → F) (a d : ℕ)
    (hg : ∀ i, g i ≠ 0) (hn : n < 2 * a)
    (hd : ∀ p ∈ C.offDiag, d ≤ (supp p.1 p.2).card) :
    (∑ γ : F, (lineList C f g a γ).card ^ 2) * (2 * a - d)
      ≤ (∑ γ : F, (lineList C f g a γ).card) * (2 * a - d)
        + (closePairs C a).card * (2 * (n - d)) := by
  classical
  rw [line_sq_sum_eq, add_mul]
  have hsubset : closePairs C a ⊆ C.offDiag := Finset.filter_subset _ _
  have hpairs : (∑ p ∈ C.offDiag, (badSet f g p.1 p.2 a).card) * (2 * a - d)
      ≤ (closePairs C a).card * (2 * (n - d)) := by
    rw [offDiag_badSet_sum_eq_close C f g a hn, Finset.sum_mul]
    calc ∑ p ∈ closePairs C a, (badSet f g p.1 p.2 a).card * (2 * a - d)
        ≤ ∑ _p ∈ closePairs C a, 2 * (n - d) :=
          Finset.sum_le_sum (fun p hp =>
            badSet_card_uniform_bound f g p.1 p.2 a d hg (hd p (hsubset hp)) hn)
      _ = (closePairs C a).card * (2 * (n - d)) := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-- `|closePairs| ≤ |C|² − |C|` — the sharp bound is never worse than round-14b. (Sanity: the
refinement is a genuine subset restriction.) -/
theorem closePairs_card_le (C : Finset (Fin n → F)) (a : ℕ) :
    (closePairs C a).card ≤ C.card * C.card - C.card := by
  rw [← Finset.offDiag_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

end LinePairCooccurrence
