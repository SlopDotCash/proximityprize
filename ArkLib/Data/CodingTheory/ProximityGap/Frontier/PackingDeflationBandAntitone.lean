/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AgreementSetTuplePacking

/-!
# The packing distinct-`γ` floor is BAND-ANTITONE: the deepest band gives the sharpest cap
# (issue #444, under-det / agreement-sharing face)

`AgreementSetTuplePacking.pinnedScalars_card_le_choose_div` gives the multiplicity-aware packing
floor on the distinct-`γ` count,

  **`#pinnedScalars ≤ C(n, k+1) / C(a, k+1)`**   (`Nat` floor division),

under the general-position hypothesis, and `EpsMCAPackingFloor` deploys it into
`epsMCA ≤ (C(n,k+1)/C(a,k+1)) / |F|`.  Both files' scope notes **assert** (but never prove) the
monotone-in-band behaviour the deployment relies on — that going to a DEEPER band `a` makes the
packed floor `C(n,k+1)/C(a,k+1)` SMALLER (sharper), and that at the prize band `a ≈ n/2` it lands
at a *constant-factor* deflation, NOT a sub-Johnson `√n` count.  This file lands the structural
core of that assertion as an axiom-clean theorem.

## The deflation floor and its band-antitonicity

Write the packing deflation floor (the `Nat` quantity the bound deploys)

  `packingDeflationFloor n k a := C(n, k+1) / C(a, k+1)`.

The headline:

  **`packingFloor_antitone_in_band`** : for `k+1 ≤ a ≤ a'` (both bands at least the tuple size, so
  both binomials are positive),

  > `packingDeflationFloor n k a' ≤ packingDeflationFloor n k a`.

i.e. the DEEPER band `a'` gives the TIGHTER (smaller-or-equal) distinct-`γ` packing cap.  The
mechanism is two monotonicities composed: `C(a,k+1)` is monotone increasing in the band `a`
(`Nat.choose_le_choose`), and `Nat` floor division `m / ·` is antitone in its (positive) divisor
(`Nat.div_le_div_left`).  So a deeper band has a larger denominator, hence a smaller floor.

As an immediate corollary the floor is dominated by its value at the SHALLOWEST in-window band, and
the SHARPEST packing distinct-`γ` cap available in any band-window `[a₀, A]` is the one at the
DEEPEST band `A` — the structural justification for evaluating the packing floor at the deepest
admissible band (`a ≈ ⌈(1−δ)n⌉`, the deep agreement band the census actually uses).

## Honest scope (rules 1, 3, 4, 6 + ASYMPTOTIC GUARD)

* Field-universal pure-`Nat` combinatorics about the deflation floor itself: NOT thinness-essential,
  NOT a moment/Wick/energy move, NOT an orbit/spectrum re-derivation.  It is the band-monotonicity
  the packing-floor deployment ASSERTS — now a theorem, not prose.
* **It does NOT improve CORE.**  Quite the opposite, and that is the honest content: by the
  ASYMPTOTIC GUARD, at the prize band `a ≈ n/2` the *real* ratio `C(n,k+1)/C(a,k+1) → 2^(k+1)` from
  above (a CONSTANT in `n` for fixed `k`), so the packed distinct-`γ` floor is `Θ(1)` — it does NOT
  scale like `√n` and does NOT reach the CORE budget `M(μ_n) ≤ C√(n·log(p/n))`.  The packing /
  agreement-sharing face therefore COLLAPSES to a constant-factor deflation; any beyond-Johnson lift
  lives in the per-`γ` character-sum (BGK) wall, untouched.  This theorem makes the COLLAPSE
  direction structural: deeper bands help (antitone), but the help saturates at `2^(k+1)` (probe).
  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

Probe `scripts/probes/probe_deflation_band_monotone.py` (the cliff-at-`n/2` from the packing side):
* (A) `Nat`-floor antitony of `D(a)` over `a ∈ [k+1, n]` — CONFIRMED, `n ∈ {16..256}`, `k ∈ {1,2,3}`.
* (B) at `a = n/2` the real ratio `R(n/2) → 2^(k+1)` from above (`R/2^(k+1) → 1`): `k=2` gives
  `10.0, 8.86, 8.40, 8.19, 8.10, 8.02` at `n = 16..1024` — a constant, NOT `√n`.
* (C) the underlying real ratio `R(a)` is antitone everywhere.
* verdict: `D(n/2) = O(1)` (literally `8` for `k=2` at `n = 256, 1024, 4096`), so the packing floor
  does NOT reach CORE — it confirms the cliff-at-`n/2` collapse from the under-det packing side.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The **packing deflation floor**: the `Nat`-floor distinct-`γ` cap the agreement-sharing packing
brick deploys, `C(n, k+1) / C(a, k+1)`. -/
def packingDeflationFloor (n k a : ℕ) : ℕ := n.choose (k + 1) / a.choose (k + 1)

/-- **The deflation floor is band-antitone.**  For `k+1 ≤ a ≤ a'` the DEEPER band `a'` gives the
SMALLER (sharper) packed distinct-`γ` floor:

> `packingDeflationFloor n k a' ≤ packingDeflationFloor n k a`.

Mechanism: `C(a,k+1)` is monotone in the band `a` (`Nat.choose_le_choose`), and `Nat` floor
division is antitone in its positive divisor (`Nat.div_le_div_left`).  Deeper band ⟹ bigger
denominator ⟹ smaller floor. -/
theorem packingFloor_antitone_in_band {n k a a' : ℕ} (haa' : a ≤ a') (hka : k + 1 ≤ a) :
    packingDeflationFloor n k a' ≤ packingDeflationFloor n k a := by
  unfold packingDeflationFloor
  have hden_mono : a.choose (k + 1) ≤ a'.choose (k + 1) := Nat.choose_le_choose (k + 1) haa'
  have hden_pos : 0 < a.choose (k + 1) := Nat.choose_pos hka
  exact Nat.div_le_div_left hden_mono hden_pos

/-- **The shallowest in-window band dominates the floor.**  For any band `a` with `k+1 ≤ a₀ ≤ a`,
the floor at `a` is at most the floor at the shallowest band `a₀`.  (Immediate from the headline:
the floor only shrinks as the band deepens.) -/
theorem packingFloor_le_shallowest {n k a₀ a : ℕ} (ha₀a : a₀ ≤ a) (hka₀ : k + 1 ≤ a₀) :
    packingDeflationFloor n k a ≤ packingDeflationFloor n k a₀ :=
  packingFloor_antitone_in_band ha₀a hka₀

/-- **The deepest band gives the sharpest packing distinct-`γ` cap.**  If the distinct-`γ` count is
bounded by the deflation floor at a deep band `A` (the bound the packing brick produces), then for
EVERY admissible band `a` with `k+1 ≤ a ≤ A` the same count is bounded by the (larger) floor at the
shallower band `a` — i.e. the floor at the DEEPEST band `A` is the strongest of the in-window
bounds.  This is the structural justification (asserted in the deployment scope notes) for
evaluating the packing floor at the DEEPEST admissible band `A ≈ ⌈(1−δ)n⌉`. -/
theorem pinnedScalars_le_floor_at_shallower_band
    (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) {a A : ℕ}
    (haA : a ≤ A) (hka : k + 1 ≤ a)
    (hdeep : (pinnedScalars dom k A u₀ u₁).card ≤ packingDeflationFloor n k A) :
    (pinnedScalars dom k A u₀ u₁).card ≤ packingDeflationFloor n k a :=
  le_trans hdeep (packingFloor_antitone_in_band haA hka)

/-- **Restatement of the deployed packing floor in terms of `packingDeflationFloor`.**  The
under-det packing brick (`pinnedScalars_card_le_choose_div`) is exactly: the distinct-`γ` count is
bounded by `packingDeflationFloor n k a`, under the general-position hypothesis.  Stated here so the
band-antitonicity above can be chained onto the actual deployed bound. -/
theorem pinnedScalars_card_le_packingDeflationFloor
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hpos : 0 < a.choose (k + 1))
    (hown : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∃ S : Finset (Fin n), S.card = a ∧ Aligned dom k u₀ u₁ γ S ∧
        AllSubtuplesNondeg dom k u₀ u₁ S) :
    (pinnedScalars dom k a u₀ u₁).card ≤ packingDeflationFloor n k a :=
  pinnedScalars_card_le_choose_div dom k a u₀ u₁ hpos hown

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.packingFloor_antitone_in_band
#print axioms ProximityGap.Ownership.packingFloor_le_shallowest
#print axioms ProximityGap.Ownership.pinnedScalars_le_floor_at_shallower_band
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_packingDeflationFloor
