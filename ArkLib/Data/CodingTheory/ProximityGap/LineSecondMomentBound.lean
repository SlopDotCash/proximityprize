/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LinePairCooccurrenceBound

/-!
# Issue #232: the per-line second moment (round 14b)

Assembles `LinePairCooccurrenceBound` into the per-line analogue of the O28/O29 global
second-moment chain. Three results:

1. **Partition** `|supp| + |offSupp| = n`.
2. **Uniform pair bound** (`badSet_card_uniform_bound`): in the regime `2a > n` (for RS rate-`ρ`
   codes at agreement `a = (1−δ)n` this is exactly `δ < 1/2` — the whole prize window at `ρ = 1/2`),
   the per-pair co-occurrence bound `2(n−w)/(2a−w)` is monotone decreasing in `w`
   (`(n−w)(2a−d) ≤ (n−d)(2a−w) ⟺ (w−d)(2a−n) ≥ 0`), so every pair at distance `≥ d` obeys the
   single uniform bound `B·(2a−d) ≤ 2(n−d)`.
3. **Per-line second-moment identity and bound** (`line_sq_sum_eq`, `line_second_moment_bound`):
       `∑_γ |Λ(γ,a)|² = ∑_γ |Λ(γ,a)| + ∑_{(c,c') ∈ C.offDiag} |badSet(c,c')|`
   — the exact per-line counterpart of the O28 kernel identity (`∑_w |Λ(w)|² = ∑ pairs of ball
   co-memberships`), with the ball-intersection volume replaced by the *line* co-occurrence count —
   and hence, for a code of minimum distance `d` in the `2a > n` regime,
       `(∑_γ |Λ(γ,a)|²)·(2a−d) ≤ (∑_γ |Λ(γ,a)|)·(2a−d) + (|C|²−|C|)·2(n−d)`.

Compared to the global chain the gain is structural: the off-diagonal term is now bounded by a
*distance-uniform constant per pair* (`2(n−d)/(2a−d)`, e.g. `≤ 1` on the `RS[8,4]/F₁₇` witness
instance) instead of the ball-intersection volume `I(w,r)` whose weight-enumerator-weighted sum
blows up past Johnson. The remaining open content for the prize is bounding the number of pairs
that actually co-occur on a line (the `|C|² − |C|` factor is the trivial count; the numeric scan
shows the true count is far smaller), which is where the RS structure must enter.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] in
/-- The support/off-support partition: `|offSupp| + |supp| = n`. -/
theorem offSupp_card_add_supp_card (c c' : Fin n → F) :
    (offSupp c c').card + (supp c c').card = n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => c i = c' i)
  simpa [offSupp, supp, Finset.card_univ] using h

/-- **Uniform pair bound in the `2a > n` regime.** For any pair at distance `≥ d`, the
co-occurrence count obeys the single distance-`d` bound: `B·(2a−d) ≤ 2(n−d)`. The monotonicity
in `w` is exactly `(w−d)·(2a−n) ≥ 0`, which is where the regime hypothesis enters. -/
theorem badSet_card_uniform_bound (f g c c' : Fin n → F) (a d : ℕ) (hg : ∀ i, g i ≠ 0)
    (hd : d ≤ (supp c c').card) (hn : n < 2 * a) :
    (badSet f g c c' a).card * (2 * a - d) ≤ 2 * (n - d) := by
  have hb := badSet_card_bound f g c c' a hg
  have hpart := offSupp_card_add_supp_card c c'
  set B := (badSet f g c c' a).card with hB
  set w := (supp c c').card with hw
  have hwn : w ≤ n := by omega
  have hdn : d ≤ n := le_trans hd hwn
  have hoff : (offSupp c c').card = n - w := by omega
  rw [hoff] at hb
  -- B·2a ≤ B·w + 2(n−w), d ≤ w ≤ n < 2a ⊢ B·(2a−d) ≤ 2(n−d)
  -- route: B·(2a−w) ≤ 2(n−w); multiply by (2a−d); cross (n−w)(2a−d) ≤ (n−d)(2a−w); cancel (2a−w).
  have hstep : B * (2 * a - w) ≤ 2 * (n - w) := by
    have hexp : B * (2 * a - w) = B * (2 * a) - B * w := by
      rw [Nat.mul_sub]
    omega
  have hcross : (n - w) * (2 * a - d) ≤ (n - d) * (2 * a - w) := by
    zify [hwn, hdn, hd, show d ≤ 2 * a by omega, show w ≤ 2 * a by omega]
    nlinarith [sub_nonneg.mpr (show (d : ℤ) ≤ w by exact_mod_cast hd),
               sub_nonneg.mpr (show (n : ℤ) ≤ 2 * a by exact_mod_cast hn.le)]
  have hkey : B * (2 * a - d) * (2 * a - w) ≤ 2 * (n - d) * (2 * a - w) := by
    calc B * (2 * a - d) * (2 * a - w)
        = B * (2 * a - w) * (2 * a - d) := by ring
      _ ≤ 2 * (n - w) * (2 * a - d) := Nat.mul_le_mul_right _ hstep
      _ = 2 * ((n - w) * (2 * a - d)) := by ring
      _ ≤ 2 * ((n - d) * (2 * a - w)) := Nat.mul_le_mul_left _ hcross
      _ = 2 * (n - d) * (2 * a - w) := by ring
  exact Nat.le_of_mul_le_mul_right hkey (by omega)

/-- The agreement-≥`a` list of code `C` at the line point `γ`. -/
def lineList (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ) (γ : F) :
    Finset (Fin n → F) :=
  C.filter (fun c => a ≤ (agreeSet (linePt f g γ) c).card)

/-- **Per-line second-moment identity** (the line counterpart of the O28 kernel identity):
`∑_γ |Λ(γ)|² = ∑_γ |Λ(γ)| + ∑_{(c,c') ∈ C.offDiag} |badSet(c,c')|`. -/
theorem line_sq_sum_eq (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ) :
    ∑ γ : F, (lineList C f g a γ).card ^ 2
      = (∑ γ : F, (lineList C f g a γ).card)
        + ∑ p ∈ C.offDiag, (badSet f g p.1 p.2 a).card := by
  classical
  have hsq : ∀ γ : F, (lineList C f g a γ).card ^ 2
      = (lineList C f g a γ).card + ((lineList C f g a γ).offDiag).card := by
    intro γ
    have hoffd := Finset.offDiag_card (lineList C f g a γ)
    rw [pow_two]
    set m := (lineList C f g a γ).card with hm
    have hle : m ≤ m * m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_left _ h
    omega
  rw [Finset.sum_congr rfl (fun γ _ => hsq γ), Finset.sum_add_distrib]
  congr 1
  -- the off-diagonal of the list is the code's off-diagonal filtered by double goodness
  have hA : ∀ γ : F, ((lineList C f g a γ).offDiag).card
      = (C.offDiag.filter (fun p =>
          a ≤ (agreeSet (linePt f g γ) p.1).card
            ∧ a ≤ (agreeSet (linePt f g γ) p.2).card)).card := by
    intro γ
    congr 1
    ext ⟨c, c'⟩
    simp only [Finset.mem_offDiag, Finset.mem_filter, lineList]
    tauto
  simp_rw [hA, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Finset.card_filter]
  rfl

/-- **Per-line second-moment bound** in the `2a > n` regime, for a code of minimum pair
distance `d`: `(∑_γ |Λ(γ)|²)·(2a−d) ≤ (∑_γ |Λ(γ)|)·(2a−d) + (|C|²−|C|)·2(n−d)`. -/
theorem line_second_moment_bound (C : Finset (Fin n → F)) (f g : Fin n → F) (a d : ℕ)
    (hg : ∀ i, g i ≠ 0) (hn : n < 2 * a)
    (hd : ∀ p ∈ C.offDiag, d ≤ (supp p.1 p.2).card) :
    (∑ γ : F, (lineList C f g a γ).card ^ 2) * (2 * a - d)
      ≤ (∑ γ : F, (lineList C f g a γ).card) * (2 * a - d)
        + (C.card * C.card - C.card) * (2 * (n - d)) := by
  rw [line_sq_sum_eq, add_mul]
  have hpairs : (∑ p ∈ C.offDiag, (badSet f g p.1 p.2 a).card) * (2 * a - d)
      ≤ (C.card * C.card - C.card) * (2 * (n - d)) := by
    rw [Finset.sum_mul]
    calc ∑ p ∈ C.offDiag, (badSet f g p.1 p.2 a).card * (2 * a - d)
        ≤ ∑ _p ∈ C.offDiag, 2 * (n - d) :=
          Finset.sum_le_sum (fun p hp =>
            badSet_card_uniform_bound f g p.1 p.2 a d hg (hd p hp) hn)
      _ = C.offDiag.card * (2 * (n - d)) := by rw [Finset.sum_const, smul_eq_mul]
      _ = (C.card * C.card - C.card) * (2 * (n - d)) := by rw [Finset.offDiag_card]
  omega

end LinePairCooccurrence
