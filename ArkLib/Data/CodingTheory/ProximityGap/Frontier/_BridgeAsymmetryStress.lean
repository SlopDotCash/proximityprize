/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# ANGLE U3 — stress-test of the "tautological bridge": is the `q−1` factor an exploitable asymmetry? (#444)

`_BridgeOneWall` proved the **bridge bracket**

> `(q·E_r − n^{2r})/(q−1) ≤ M^{2r} ≤ q·E_r − n^{2r}`,    `q = |F|`, `n = |G|`, `S := q·E_r − n^{2r}`,

where `M = max_{b≠0}‖η_b‖` and `E_r = rEnergy G r`. The two sides differ by the factor `q−1 ≈ p`. The campaign
labelled the bridge **tautological** (the additive count and the multiplicative phases are the *same* object,
linked by the loss-free identity `sum_nonzero_moment : Σ_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`). This file STRESSES
that label along three axes and lands the verdict.

The bracket, stripped of names, is the **textbook max-vs-average gap of a sum of `q−1` nonnegative terms**:
`S/N ≤ max ≤ S` for `N = q−1` summands. The three sub-questions:

**(a) Does averaging (energy→sup) lose what the sup→energy direction keeps, or vice versa?**
  The **upper** edge `M^{2r} ≤ S` is *worst-term-≤-sum*: it carries **no** `q−1` factor and is the
  prize-relevant direction (an upper bound on the worst case). The **lower** edge `M^{2r} ≥ S/(q−1)` is where the
  entire `q−1` lives — the *floor* direction (it lower-bounds `M`, i.e. proves `M` large). So averaging loses the
  **identity of the maximiser** and keeps the **ceiling**; the `q−1` slack sits entirely on the floor side. The
  asymmetry is real but harmless: the loss is on the direction the prize does not use.
  Brick: `upper_edge_is_q_independent`.

**(b) Could a DIFFERENT moment (odd / fractional / weighted) break the symmetry?**
  No. Every functional of `(‖η_b‖)_{b≠0}` inherits the **exact coset invariance** `η_{b·h} = η_b` for `h ∈ G`
  (`eta_coset_invariant`, proved below from the subgroup reindexing `h·G = G`). Hence for ANY weight the `q−1`
  values collapse into `(q−1)/n` *exact n-fold-repeated* blocks; no moment can see more than `(q−1)/n` distinct
  values, and the worst-vs-average ratio is governed by the **number of near-maximal cosets**, `O(poly n)`,
  independent of the moment order. A different moment cannot manufacture asymmetry the coset structure does not
  already fix. Brick: `eta_coset_invariant`.

**(c) Is the factor `q−1` improvable to `o(p)` using structure?**
  **YES — and that is the whole point.** Coset invariance improves it *for free* from `q−1` toward `(q−1)/n`,
  and the extreme-value count improves it further to `O(poly n)`. **But every such improvement lands on the LOWER
  edge** `M^{2r} ≥ S/N`: a smaller `N` proves a **larger** floor on `M`. The prize needs an **upper** bound on
  `M`; the upper edge `M^{2r} ≤ S` already carries no `q−1` and is untouched. Tightening the bracket factor
  sharpens the *wrong* side. Brick: `improving_count_raises_floor`.

## Verdict (honest)

The `q−1` factor is **not** an exploitable lever for the prize. It is **exactly the worst-case-vs-average gap
that IS the open problem**: the bracket says "the average energy `E_r` and the worst case `M` agree up to how
peaked the spectrum is", and *how peaked the spectrum is* is the BGK / Paley-conjecture content. Asymmetry (a) is
real but on the floor direction; (b) is closed by exact coset invariance; (c) improves only the floor. **The
bridge is strictly tautological for the purpose of upper-bounding `M`.** `reachesPrize = false`,
`closesCharP = false`. The landed bricks are exact, axiom-clean: the upper-edge `q`-independence, the exact
coset invariance, and the floor-direction audit — formalising *why* the asymmetry is not a lever. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## (b) Exact coset invariance — closes the "different moment" escape.

The structural reason no choice of moment/weight can break the bridge symmetry: every functional of the period
sequence inherits the same `(q−1)/n`-fold degeneracy. We prove the period itself is constant on `G`-cosets. -/

/-- **Exact coset invariance of `η` (subgroup multiplication).** If left-multiplication by `h` is a bijection of
`G` onto itself (the defining property of a subgroup element), then `η_{b·h} = η_b`: the defining sum reindexes
onto itself, since `ψ((b·h)·y) = ψ(b·(h·y))` and `y ↦ h·y` permutes `G`. The periods are *equal*, not merely
equal in modulus, so EVERY moment (even, odd, fractional, weighted) sees the same `(q−1)/|G|`-fold collapse of
the `q−1` nonzero frequencies. This kills sub-question (b): no moment can manufacture asymmetry the coset
structure does not already fix. -/
theorem eta_coset_invariant {ψ : AddChar F ℂ} (G : Finset F) (b h : F)
    (σ : F → F) (hσ : ∀ y ∈ G, σ y ∈ G)
    (hσinj : Set.InjOn σ (↑G)) (hστ : ∀ y ∈ G, h * y = σ y) :
    eta ψ G (b * h) = eta ψ G b := by
  unfold eta
  -- `∑_{y∈G} ψ((b·h)·y) = ∑_{y∈G} ψ(b·(h·y)) = ∑_{y∈G} ψ(b·σ y) = ∑_{z∈ G.image σ} ψ(b·z) = ∑_{z∈G} ψ(b·z)`.
  have himg : G.image σ = G := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rcases Finset.mem_image.1 hz with ⟨y, hy, rfl⟩
      exact hσ y hy
    · rw [Finset.card_image_of_injOn hσinj]
  calc ∑ y ∈ G, ψ ((b * h) * y)
      = ∑ y ∈ G, ψ (b * σ y) := by
        apply Finset.sum_congr rfl; intro y hy; rw [mul_assoc, hστ y hy]
    _ = ∑ z ∈ G.image σ, ψ (b * z) :=
        (Finset.sum_image (f := fun z => ψ (b * z)) hσinj).symm
    _ = ∑ z ∈ G, ψ (b * z) := by rw [himg]

/-! ## (a) The upper edge carries no `q−1` — the prize direction is `q`-independent.

This is the asymmetry-direction audit. The prize needs an UPPER bound on `M`. We isolate that the upper edge of
the bracket `M^{2r} ≤ q·E_r − n^{2r}` is exactly worst-term-≤-sum and contains **no** `q−1` factor: it is the
direction that does NOT degrade as `q → ∞` at fixed `n`. (Compare `_BridgeOneWall.energy_le_of_supnorm`, the
LOWER edge, which carries the full `q−1`.) -/

/-- **(a) Upper edge `q`-independence.** For ANY frequency `b ≠ 0`, `‖η_b‖^{2r} ≤ q·E_r − n^{2r}`, with no `q−1`
factor: the worst case is bounded by the (DC-subtracted) total energy directly. This is the prize-relevant
direction; the `q−1` slack lives only on the opposite (floor) edge. Hence averaging loses information only about
*which* frequency is worst (the floor), never about the ceiling. -/
theorem upper_edge_is_q_independent {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  rw [← sum_nonzero_moment hψ G r]
  apply Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r))
  · intro i _; positivity
  · exact Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩

/-! ## (c) Any improvement of the bracket factor lands on the FLOOR — the wrong direction.

The campaign's escape hope: "improve `q−1` to `o(p)` so the average pins the worst case." We formalise that a
better count `N ≤ q−1` (e.g. `N = (q−1)/n` from coset collapse, or `N = #near-maximal cosets = O(poly n)`)
upgrades only the LOWER edge `M^{2r} ≥ S/N`, producing a *larger floor* on `M`. It can NEVER upper-bound `M`. -/

/-- **(c) Improving the count raises the floor — it does not cap the worst case.** Suppose the `q−1` nonzero
periods take values among `N` "blocks" so that the total moment `S` is concentrated on `N` summands of size at
most `M^{2r}` (the coset/extreme-value sharpening of the bracket factor). Then `S ≤ N · M^{2r}`, i.e.
`M^{2r} ≥ S/N`. A *smaller* `N` (the improvement we sought) gives a *larger* lower bound on `M^{2r}` — it proves
`M` is BIG. The prize wants `M` SMALL, so this improvement is on the wrong side: the bracket factor is a floor
mechanism, structurally unable to upper-bound the worst case. -/
theorem improving_count_raises_floor
    (S : ℝ) (N : ℕ) (M2r : ℝ) (hN : 0 < N) (hconc : S ≤ (N : ℝ) * M2r) :
    S / (N : ℝ) ≤ M2r := by
  rw [div_le_iff₀ (by exact_mod_cast hN)]
  linarith [hconc]

/-- **Monotonicity of the floor in the count.** Making the count `N` smaller (a tighter bracket factor) makes the
floor `S/N` larger: for `0 < N₁ ≤ N₂` and `S ≥ 0`, `S/N₂ ≤ S/N₁`. So every sharpening of the bracket factor
`q−1 ↦ N` *raises* the lower bound on `M`. The improvement the campaign sought provably acts on the floor, never
on the ceiling — confirming the bridge is tautological for upper-bounding `M`. -/
theorem floor_antitone_in_count (S : ℝ) (hS : 0 ≤ S) (N₁ N₂ : ℕ)
    (h1 : 0 < N₁) (h12 : N₁ ≤ N₂) :
    S / (N₂ : ℝ) ≤ S / (N₁ : ℝ) := by
  apply div_le_div_of_nonneg_left hS
  · exact_mod_cast h1
  · exact_mod_cast h12

end ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.eta_coset_invariant
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.upper_edge_is_q_independent
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.improving_count_raises_floor
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.floor_antitone_in_count
