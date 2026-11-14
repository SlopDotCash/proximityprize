/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# Surface 2: the restricted-large-values route over monomial frequencies does not escape (#407)

This scratch lane records the honest verdict of the **Surface 2** investigation: the prize does
NOT need the *global* character-sum sup-norm `B = max_{b≠0} |η_b|`; it only needs the *worst-line
incidence* `I(δ) = #{bad scalars γ}` over the structured family of monomial lines.  The hope was
that restricting the moment / large-values count to the `n²` monomial-line frequencies (rather
than all `p` frequencies) escapes the moment no-go (`_MomentMethodNoGo.lean`, which only forbids
certifying the *global* sup `< n`).

**The measured verdict (probes `/tmp/s2/probe_s2_*.py`, exact, `n ∈ {8,16}`, `ρ ∈ {1/2,1/4}`):**

* For the worst MONOMIAL line `u₀ = X^i, u₁ = X^j` (`i,j ≥ k`), the `mcaEvent` bad-scalar count
  (ABF26 Def 4.3, *with* the joint-agreement exclusion) at the prize-window agreement `w = k+1`
  (i.e. `δ = 1 − ρ − 1/n`, just above capacity) is **exactly `q-INDEPENDENT`** (`= 40` for `n=8`,
  `9584` for the worst `n=16` direction `(9,12)`), identical across every prime `q = n^β`,
  `β ∈ {3.5,…,4.0}`.
* The agreement PLATEAUS at exactly `w = k+1`: the bad count drops to `0` at `w = k+2`
  (`δ = 1 − ρ − 2/n`) — a sharp cliff (also for non-monomial high-span directions at `n=8,16`).
* The per-codeword incidence is `O(1)` (the in-tree line-ball brick,
  `LineBallSingleCodewordEnvelope.lean`); the bad count is `(#codewords in the list) × O(1)`,
  and `#codewords = #flat (k+1)-windows = C(n,k+1) ~ 2^{H(ρ)·n}` — the LIST SIZE above Johnson.

**So Surface 2 RE-COLLAPSES, not escapes:** the worst-monomial incidence is a *characteristic-zero
combinatorial* quantity (the above-Johnson list size `C(n,k+1)`), which the character-sum / large-
values machinery never sees.  The moment no-go is about the *global, `q`-dependent* sup-norm at
the sub-`n` BGK scale — a genuinely different object that is irrelevant to this incidence.  The
per-codeword O(1) escape is real, but summed over the exponential list it re-collapses to the
list-decoding count above Johnson (the project's open face 4 / B4 LD⇒MCA).

This file formalizes only the *structural* facts that make the count `q`-independent:

* `badScalars_card_le_windows` — the bad-scalar set is the SUPPORT (distinct-value image) of a
  finite collision family indexed by the `(k+1)`-windows, hence `≤ C(n,k+1)`, with NO field
  dependence (the character-sum sup-norm `B` never appears).
* `windows_le_support_mul_maxFibre` — the *no-escape mechanism*: shrinking the support below a
  target forces a large window-fibre, i.e. a scalar shared by many windows = high agreement =
  below Johnson.  So the support cannot be made small (`≤ n`) without leaving the prize window.

No theorem here claims the prize is solved; the equality with the saturated profile and the
worst-over-ALL-lines (non-monomial / complete-homogeneous, `_CompleteHomogeneousReadout.lean`)
question remain the open core.

Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.MonomialLineSpectrumNoEscape

/-- The **window-collision family** for a monomial line: each `(k+1)`-window of coordinates
`i ∈ windows` carries a bad-scalar value `γ i` (the divided-difference ratio `-D₀/D₁`) and a
predicate `live i` saying it actually contributes (`D₁ ≠ 0`).  The `mcaEvent` bad-scalar set of
a monomial line is the image of the live windows under `γ` (verified equal by the probes). -/
structure WindowCollision (ι Scalar : Type*) where
  /-- the (finite) index set of `(k+1)`-windows -/
  windows : Finset ι
  /-- the bad-scalar value carried by each window -/
  γ : ι → Scalar
  /-- whether a window contributes a bad scalar -/
  live : ι → Prop
  /-- decidability of `live` (so we can take the live subset) -/
  liveDec : DecidablePred live

attribute [instance] WindowCollision.liveDec

variable {ι Scalar : Type*} [DecidableEq Scalar]

/-- The live windows (those that contribute a bad scalar). -/
def liveWindows (W : WindowCollision ι Scalar) : Finset ι :=
  W.windows.filter W.live

/-- The **bad-scalar set**: the distinct `γ`-values over the live windows.  This is the in-tree
`mcaEvent` bad-scalar set for a monomial line. -/
def badScalars (W : WindowCollision ι Scalar) : Finset Scalar :=
  (liveWindows W).image W.γ

/-- The **window-fibre** of a scalar `c`: the live windows whose value is `c`. -/
def fibre (W : WindowCollision ι Scalar) (c : Scalar) : Finset ι :=
  (liveWindows W).filter (fun i => W.γ i = c)

/-- **The Surface-2 structural bound: the bad-scalar count is at most the number of windows,
with NO dependence on the field / character-sum sup-norm.**  The bad-scalar count of a monomial
line is the support size of the window-collision family, hence `≤ #windows = C(n,k+1)`.  This is
the field-independent (characteristic-zero, list-size) wall — the global character-sum sup-norm
`B` never enters this count. -/
theorem badScalars_card_le_windows (W : WindowCollision ι Scalar) :
    (badScalars W).card ≤ W.windows.card :=
  le_trans (Finset.card_image_le) (Finset.card_filter_le _ _)

/-- **No-escape mechanism (support–collision tension).**  The number of live windows is at most
the support size times the largest window-fibre.  Equivalently: to push the bad-scalar count
(the support) below a target, the live windows must collide heavily (a large fibre), i.e. one
scalar is shared by many `(k+1)`-windows — which is exactly a high-agreement event (below the
Johnson radius).  So one cannot have *both* a small support (`≤ n`) *and* a large window count
(`C(n,k+1)`) without a large fibre; in the prize window the fibre is bounded, so the support
stays large.  This is the structured analogue of the moment no-go. -/
theorem windows_le_support_mul_maxFibre (W : WindowCollision ι Scalar)
    (m : ℕ) (hfibre : ∀ c, (fibre W c).card ≤ m) :
    (liveWindows W).card ≤ (badScalars W).card * m := by
  classical
  -- partition the live windows over their γ-value in the support
  have hcover : liveWindows W
      = (badScalars W).biUnion (fun c => fibre W c) := by
    ext i
    simp only [Finset.mem_biUnion, badScalars, fibre, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hi
      exact ⟨W.γ i, ⟨i, hi, rfl⟩, hi, rfl⟩
    · rintro ⟨c, _, hi, _⟩
      exact hi
  calc (liveWindows W).card
      = ((badScalars W).biUnion (fun c => fibre W c)).card := by rw [hcover]
    _ ≤ ∑ c ∈ badScalars W, (fibre W c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ badScalars W, m := Finset.sum_le_sum (fun c _ => hfibre c)
    _ = (badScalars W).card * m := by rw [Finset.sum_const, smul_eq_mul]

/-- **Corollary (the wall, contrapositive form).**  If every window-fibre is small (`≤ m`, the
prize-window agreement cap) and there are many live windows (`≥ N`, the list size `C(n,k+1)`),
then the bad-scalar count is at least `N / m` — super-linear in `n` whenever `N = 2^{Θ(n)}` and
`m` is polynomial.  No field-size / character-sum input is used. -/
theorem badScalars_card_ge_of_many_windows (W : WindowCollision ι Scalar)
    (m N : ℕ) (hfibre : ∀ c, (fibre W c).card ≤ m)
    (hN : N ≤ (liveWindows W).card) :
    N ≤ (badScalars W).card * m :=
  le_trans hN (windows_le_support_mul_maxFibre W m hfibre)

end ProximityGap.Frontier.MonomialLineSpectrumNoEscape

-- Axiom audit (must be only `propext, Classical.choice, Quot.sound`):
#print axioms ProximityGap.Frontier.MonomialLineSpectrumNoEscape.badScalars_card_le_windows
#print axioms
  ProximityGap.Frontier.MonomialLineSpectrumNoEscape.windows_le_support_mul_maxFibre
#print axioms
  ProximityGap.Frontier.MonomialLineSpectrumNoEscape.badScalars_card_ge_of_many_windows
