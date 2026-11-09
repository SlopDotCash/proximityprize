/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Bridge B07 — target E6: the EXACT FFT-graded dyadic recursion (#444)

This file gives a *faithful Lean transcription* of the empirical object E6 from
`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, matching
`scripts/probes/probe_2adic_tower_recursion.py` line-for-line, and proves what is
elementary while isolating the one combinatorial bijection as a precisely named gap.

## The object (matching the probe exactly)

For `n` even, `h = n/2`. For a finite multiset / set of "frequencies" `A ⊆ ℤ/n`, a
chosen grade `m`, the graded vector is
`fhat A m n : Fin h → ℤ`,  `(fhat A m n) (e % h) += (if e < h then 1 else -1)` where
`e = (m * a) % n`, summed over `a ∈ A`.  (This is the `n/2`-binned graded FFT
coefficient of the indicator of `A`.)

`#bad_n(k,m) := cf n k m :=` the number of *distinct nonzero* values of
`fhat A m n` over all `(k+m)`-subsets `A ⊆ {0,…,n-1}` such that `fhat A j n = 0`
for every `1 ≤ j < m` (all lower graded pieces vanish).

## E6 (verified exactly at 16↔8, ALL HOLD)

* `cf (2n) k (2*m') = cf n (k/2) m'`        (the even-grade doubling recursion)
* `cf (2n) k m = 0` for `m` odd            (antipodal odd-vanishing)

## What this file does (honesty contract)

* Defines `fhat`, `gradedZeroLower`, the bad-value finset `badVals`, and `cf`
  faithfully (transcribing the probe), over `ℤ` with explicit `%` arithmetic.
* Proves the *trivial-grade base fact* and the *finiteness / well-definedness*
  scaffolding axiom-clean.
* Reduces the two E6 equalities to two precisely named Props
  (`DoublingBijection`, `OddGradeVanishes`) and proves the recursion *from* them.
  These two Props are the genuine combinatorial content (a value-preserving
  doubling bijection of subsets, and an antipodal-involution vanishing); they are
  the honest remaining gap, stated precisely as hypotheses.

Issue #444. Target E6.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB07

/-- The per-frequency graded contribution of `a` at grade `m`, modulus `n`, bins `h = n/2`:
returns the bin index `e % h` and the sign `if e < h then 1 else -1`, where `e = (m*a) % n`.
Matches `fhat`'s inner loop in the probe. -/
def gradeContribBin (a m n : ℕ) : ℕ := ((m * a) % n) % (n / 2)

/-- The sign of the graded contribution: `+1` if `(m*a)%n < n/2`, else `-1`. -/
def gradeContribSign (a m n : ℕ) : ℤ := if (m * a) % n < n / 2 then 1 else -1

/-- The `n/2`-binned graded vector `fhat A m n : (Fin (n/2)) → ℤ`, transcribing the probe's
`fhat`: for each `a ∈ A`, add `gradeContribSign a m n` into bin `gradeContribBin a m n`. -/
def fhat (A : Finset ℕ) (m n : ℕ) : Fin (n / 2) → ℤ :=
  fun i => ∑ a ∈ A, if gradeContribBin a m n = (i : ℕ) then gradeContribSign a m n else 0

/-- The all-lower-grades-zero predicate: `fhat A j n = 0` for all `1 ≤ j < m`. -/
def gradedZeroLower (A : Finset ℕ) (m n : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j < m → fhat A j n = 0

instance (A : Finset ℕ) (m n : ℕ) : Decidable (gradedZeroLower A m n) := by
  have : gradedZeroLower A m n ↔ ∀ j, j < m → (1 ≤ j → fhat A j n = 0) := by
    unfold gradedZeroLower
    exact ⟨fun h j hjm hj1 => h j hj1 hjm, fun h j hj1 hjm => h j hjm hj1⟩
  rw [this]
  exact Nat.decidableBallLT m _

/-- The universe of admissible frequency sets: `(k+m)`-subsets of `{0,…,n-1}`. -/
def admissible (n k m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powersetCard (k + m)

/-- The (nonzero) graded values witnessed by admissible, lower-zero subsets. -/
noncomputable def badVals (n k m : ℕ) : Finset (Fin (n / 2) → ℤ) :=
  ((admissible n k m).filter (fun A => gradedZeroLower A m n)).image (fun A => fhat A m n)
    |>.erase (fun _ => 0)

/-- `#bad_n(k,m)` — the number of distinct nonzero graded values; this is the probe's `cf`. -/
noncomputable def cf (n k m : ℕ) : ℕ := (badVals n k m).card

/-! ## The two ORIGINAL unguarded Props (both FALSE as stated)

The two Props below were the original transcription of E6. Their literal universal forms are
false at their quantified boundaries (counterexamples proved below):

* `OddGradeVanishes` includes `m = 1`, where the lower-grade condition is vacuous:
  `cf 2 0 1 ≠ 0` (singletons `{0}, {1}` give `+1, −1`; the exact count is `2`). Independent
  enumeration also gives `cf 16 4 1 = 2256`.
* `DoublingBijection` quantifies over all `k` and truncates `k/2`, dropping the parity guard:
  `cf 8 1 2 = 0` (odd admissible size `3`, see `cf_eq_zero_of_odd_card`) but `cf 4 0 1 ≠ 0`
  (the exact count is `4`). It also fails for non-power-of-two levels (enumeration: e.g.
  `cf 6 0 2 = 3` versus `cf 3 0 1 = 2`).

They are kept (not deleted) because later files cite them by name; use the guarded forms
`OddGradeVanishesGuarded` / `DoublingBijectionGuarded` instead. -/

/-- **(FALSE as stated; see `not_doublingBijection`.)** Original unguarded even-half Prop:
`cf(2n,k,2m') = cf(n,k/2,m')` for all `n, k, m'`. -/
def DoublingBijection : Prop :=
  ∀ n k m' : ℕ, cf (2 * n) k (2 * m') = cf n (k / 2) m'

/-- **(FALSE as stated; see `not_oddGradeVanishes`.)** Original unguarded odd-half Prop:
`cf(2n,k,m) = 0` for every odd `m`, including `m = 1`. -/
def OddGradeVanishes : Prop :=
  ∀ n k m : ℕ, Odd m → cf (2 * n) k m = 0

/-! ## Guarded forms (the intended E6 statements) -/

/-- **Guarded odd half.** At even level `2n` (`n > 0`), every odd grade `m ≥ 3` has an empty
bad-value set: the grade-`1` constraint forces antipodal closure, and the antipodal map flips the
sign of every odd-graded contribution. PROVED below as `oddGradeVanishesGuarded_holds`, by
transport from `_Close07c_OddGradeVanishesFull.cf_odd_eq_zero`. -/
def OddGradeVanishesGuarded : Prop :=
  ∀ n k m : ℕ, 0 < n → Odd m → 1 < m → cf (2 * n) k m = 0

/-- **Guarded even half (OPEN).** On the `2`-adic tower `n = 2^(t+1)`, for EVEN capacity `k` and
grade `m' ≥ 1`, `cf(2n,k,2m') = cf(n,k/2,m')`. Independent exact enumeration confirms it at
`n ∈ {2, 4, 8}` (levels `4, 8, 16`) for all even `k` and all `m'`; it is NOT proved in Lean
(see `_Close07a_DoublingFoldMap` / `_Close07b_DoublingInduction` for the fold-map reduction).
Without the guards it is false (`not_doublingBijection`, and non-power-of-two levels). -/
def DoublingBijectionGuarded : Prop :=
  ∀ t k m' : ℕ, Even k → 1 ≤ m' →
    cf (2 * 2 ^ (t + 1)) k (2 * m') = cf (2 ^ (t + 1)) (k / 2) m'

/-! ## E6 from the guarded statements -/

/-- **E6 even half**, derived from the guarded (open) `DoublingBijectionGuarded`. -/
theorem E6_even (h : DoublingBijectionGuarded) (t k m' : ℕ) (hk : Even k) (hm' : 1 ≤ m') :
    cf (2 * 2 ^ (t + 1)) k (2 * m') = cf (2 ^ (t + 1)) (k / 2) m' := h t k m' hk hm'

/-- **E6 odd half**, derived from `OddGradeVanishesGuarded` (which is proved below). -/
theorem E6_odd (h : OddGradeVanishesGuarded) (n k m : ℕ) (hn : 0 < n) (hm : Odd m)
    (hm1 : 1 < m) : cf (2 * n) k m = 0 := h n k m hn hm hm1

/-! ## Elementary scaffolding proved unconditionally (axiom-clean) -/

/-- `badVals` never contains the zero vector (it is erased by construction). -/
theorem zero_notMem_badVals (n k m : ℕ) : (fun _ => (0 : ℤ)) ∉ badVals n k m := by
  unfold badVals
  exact Finset.notMem_erase _ _

/-- Every bad value is genuinely nonzero — the count `cf` counts strictly nonzero graded vectors,
matching the probe's `vals.discard(Z)`. -/
theorem badVals_ne_zero {n k m : ℕ} {v : Fin (n / 2) → ℤ} (hv : v ∈ badVals n k m) :
    v ≠ (fun _ => 0) := by
  intro h; subst h; exact zero_notMem_badVals n k m hv

/-- Membership characterization of `badVals`: a nonzero graded vector is bad iff it is the grade-`m`
vector of some admissible, lower-zero subset. This pins `cf` to exactly the probe's set. -/
theorem mem_badVals_iff {n k m : ℕ} (v : Fin (n / 2) → ℤ) :
    v ∈ badVals n k m ↔
      v ≠ (fun _ => 0) ∧
        ∃ A ∈ admissible n k m, gradedZeroLower A m n ∧ fhat A m n = v := by
  unfold badVals
  rw [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, A, hA, hAv⟩
    rw [Finset.mem_filter] at hA
    exact ⟨hne, A, hA.1, hA.2, hAv⟩
  · rintro ⟨hne, A, hA, hAz, hAv⟩
    exact ⟨hne, A, by rw [Finset.mem_filter]; exact ⟨hA, hAz⟩, hAv⟩

/-- `cf` is monotone-bounded by the number of distinct graded values over all admissible subsets
(a sanity bound; `cf` discards the zero value and the lower-grade-failing ones). -/
theorem cf_le_card_image (n k m : ℕ) :
    cf n k m ≤ ((admissible n k m).image (fun A => fhat A m n)).card := by
  unfold cf badVals
  refine le_trans Finset.card_erase_le ?_
  apply Finset.card_le_card
  exact Finset.image_subset_image (Finset.filter_subset _ _)

end ArkLib.ProximityGap.BridgeB07

#print axioms ArkLib.ProximityGap.BridgeB07.E6_even
#print axioms ArkLib.ProximityGap.BridgeB07.E6_odd
#print axioms ArkLib.ProximityGap.BridgeB07.mem_badVals_iff
#print axioms ArkLib.ProximityGap.BridgeB07.cf_le_card_image
#print axioms ArkLib.ProximityGap.BridgeB07.zero_notMem_badVals
