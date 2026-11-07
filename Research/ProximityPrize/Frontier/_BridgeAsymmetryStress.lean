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
  entire `q−1` lives — the *floor* direction (it lower-bounds `M`, i.e. proves `M` large). The bare upper edge
  `M^{2r} ≤ S` is not optimal, however: coset replication sharpens it by a factor `n` (see (c)).
  Brick: `upper_edge_is_q_independent`.

**(b) Could a DIFFERENT moment (odd / fractional / weighted) break the symmetry?**
  Every functional of `(‖η_b‖)_{b≠0}` inherits the **exact coset invariance** `η_{b·h} = η_b` for `h ∈ G`
  (`eta_coset_invariant`, proved below from the subgroup reindexing `h·G = G`), so the `q−1` nonzero periods
  take at most `(q−1)/n` distinct values, each on an exact `n`-fold block. This does NOT transfer to an arbitrary
  weighted moment: a weighting preserves the `n`-fold block structure only if the weights are themselves constant
  on `G`-cosets (and are normalised accordingly); that invariance/normalisation is a hypothesis, not proved here.
  No theorem in this file counts near-maximal cosets: an `O(poly n)` count of them is an unproved assertion.
  Brick: `eta_coset_invariant`.

**(c) Is the factor `q−1` improvable using structure?**
  Partly, and on BOTH edges once the normalisation is done correctly.
  * **Upper edge (correction of an earlier verdict).** If a nonzero frequency `b` attains `M`, then the `n`
    distinct nonzero frequencies `b·h` (`h ∈ G`) all attain the same value, so `S ≥ n · M^{2r}`, i.e.
    `M^{2r} ≤ S/n`. Coset replication therefore saves a genuine factor `n` on the UPPER edge, for free. Brick:
    `replicated_peak_upper_bound` / `replicated_peak_upper_bound_div` (requires `G` closed under multiplication
    and `0 ∉ G`). An earlier version of this file claimed the opposite (that every coset improvement lands only
    on the floor); that claim was wrong. The factor `n` is far from a prize-scale bound: it does not by itself
    prove any target bound on `M`.
  * **Lower edge.** Passing to the quotient with `N = (q−1)/n` coset blocks, the quotient moment sum is `S/n`,
    not `S`, so the quotient AVERAGE is `(S/n)/N = S/(q−1)`: the original floor is unchanged
    (`quotient_average_eq`). Pairing the reduced count `N` with the unnormalised full `S` double-counts every
    block. The division lemma `improving_count_raises_floor` is valid FROM an entered premise `S ≤ N·M^{2r}`, but
    this file does not establish that premise for the quotient count `N` with the full sum `S`.

## Verdict (corrected)

What the formalised inequalities establish: the upper edge `M^{2r} ≤ S` carries no `q−1` factor; coset
replication sharpens it to `M^{2r} ≤ S/n` under the subgroup hypotheses; correctly normalised quotient averages
leave the floor `S/(q−1)` unchanged; and a floor `S/N` is antitone in an entered count `N`. They do NOT show that
the `q−1` gap is unexploitable in general, that no weighted moment or structural argument can improve the upper
edge further, or that near-maximal cosets number `O(poly n)`. Turning the remaining worst-case-vs-average gap into
a prize bound is still the BGK / Paley-type open content. `reachesPrize = false`, `closesCharP = false`. Issue
#444.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## (b) Exact coset invariance of the periods.

Every unweighted functional of the period sequence inherits the same `(q−1)/n`-fold degeneracy. We prove the
period itself is constant on `G`-cosets. A weighted moment inherits it only when the weights are coset-invariant
(not assumed or proved here). -/

/-- **Exact coset invariance of `η` (subgroup multiplication).** If left-multiplication by `h` is a bijection of
`G` onto itself (the defining property of a subgroup element), then `η_{b·h} = η_b`: the defining sum reindexes
onto itself, since `ψ((b·h)·y) = ψ(b·(h·y))` and `y ↦ h·y` permutes `G`. The periods are *equal*, not merely
equal in modulus, so every unweighted moment (even, odd, fractional) sees the same `(q−1)/|G|`-fold collapse of
the `q−1` nonzero frequencies; a weighted moment sees it only for coset-invariant weights. The replication is
also what gives the upper-edge saving `replicated_peak_upper_bound` below. -/
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

/-! ## (c) Coset replication on both edges, with correct normalisation.

Upper edge: replication of a peak over the `n` distinct frequencies `b·h` gives `n · M^{2r} ≤ S`
(`replicated_peak_upper_bound`), a genuine factor-`n` improvement of the upper edge. Lower edge: the quotient
moment sum over `N = (q−1)/n` coset blocks is `S/n`, so its average equals the original `S/(q−1)`
(`quotient_average_eq`). The scalar lemmas `improving_count_raises_floor` / `floor_antitone_in_count` are valid
for an ENTERED premise `S ≤ N · M^{2r}`; this file does not prove that premise for a quotient count `N` paired
with the full, unnormalised sum `S`, nor any `O(poly n)` count of near-maximal cosets. -/

/-- **Replicated-peak upper bound.** Let `G` be closed under multiplication with `0 ∉ G` (e.g. a finite
multiplicative subgroup). For every nonzero frequency `b`, the `|G|` distinct nonzero frequencies `b·h`
(`h ∈ G`) all carry the same period `η_b` (`eta_coset_invariant`), so their total contribution
`|G| · ‖η_b‖^{2r}` is at most the full nonzero moment `S = q·E_r − n^{2r}`. This saves a factor `n = |G|` on the
UPPER edge relative to `upper_edge_is_q_independent`. -/
theorem replicated_peak_upper_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hmul : ∀ h ∈ G, ∀ y ∈ G, h * y ∈ G) (h0 : (0 : F) ∉ G) (r : ℕ) (b : F) (hb : b ≠ 0) :
    (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  rw [← sum_nonzero_moment hψ G r]
  have hinj : Set.InjOn (fun h => b * h) (↑G) := by
    intro x _ y _ hxy
    exact mul_left_cancel₀ hb hxy
  have hsub : G.image (fun h => b * h) ⊆ univ.erase (0 : F) := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨h, hh, rfl⟩
    have hh0 : h ≠ 0 := fun e => h0 (e ▸ hh)
    exact Finset.mem_erase.2 ⟨mul_ne_zero hb hh0, Finset.mem_univ _⟩
  have hrep : ∀ h ∈ G, eta ψ G (b * h) = eta ψ G b := by
    intro h hh
    have hh0 : h ≠ 0 := fun e => h0 (e ▸ hh)
    exact eta_coset_invariant (ψ := ψ) G b h (fun y => h * y) (fun y hy => hmul h hh y hy)
      (by intro x _ y _ hxy; exact mul_left_cancel₀ hh0 hxy) (fun y _ => rfl)
  have hconst : ∑ h ∈ G, ‖eta ψ G (b * h)‖ ^ (2 * r) = ∑ _h ∈ G, ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.sum_congr rfl (fun h hh => by rw [hrep h hh])
  calc (G.card : ℝ) * ‖eta ψ G b‖ ^ (2 * r)
      = ∑ h ∈ G, ‖eta ψ G (b * h)‖ ^ (2 * r) := by
        rw [hconst, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ z ∈ G.image (fun h => b * h), ‖eta ψ G z‖ ^ (2 * r) :=
        (Finset.sum_image (f := fun z => ‖eta ψ G z‖ ^ (2 * r)) hinj).symm
    _ ≤ ∑ z ∈ univ.erase (0 : F), ‖eta ψ G z‖ ^ (2 * r) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- **Replicated-peak upper bound, division form.** Under the hypotheses of `replicated_peak_upper_bound` with
`G` nonempty, `‖η_b‖^{2r} ≤ S / n` for every `b ≠ 0`: coset replication improves the upper edge `M^{2r} ≤ S` by
the factor `n`. -/
theorem replicated_peak_upper_bound_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hmul : ∀ h ∈ G, ∀ y ∈ G, h * y ∈ G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty) (r : ℕ) (b : F)
    (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) / (G.card : ℝ) := by
  have hpos : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hne.card_pos
  rw [le_div_iff₀ hpos, mul_comm]
  exact replicated_peak_upper_bound hψ G hmul h0 r b hb

/-- **Quotient averages are unchanged by correct normalisation.** If the `q−1` nonzero moment terms come in
exact `n`-fold blocks, the quotient sum over the `(q−1)/n` blocks is `S/n`, and its average is
`(S/n)/((q−1)/n) = S/(q−1)`: the original floor. Replacing the count by `(q−1)/n` while keeping the full `S`
would double-count every block. -/
theorem quotient_average_eq (S n q1 : ℝ) (hn : n ≠ 0) :
    (S / n) / (q1 / n) = S / q1 := by
  rw [div_div_div_cancel_right₀ hn]

/-- **Division lemma from an entered concentration premise.** IF `S ≤ N · M^{2r}` (entered as `hconc`), then
`S/N ≤ M^{2r}`. This is valid scalar arithmetic, but the premise is not established in this file for a quotient
count such as `N = (q−1)/n` paired with the full unnormalised sum `S` (the correctly normalised quotient sum is
`S/n`; see `quotient_average_eq`). In particular this lemma does not show that coset structure can only act on
the floor: `replicated_peak_upper_bound` gives an upper-edge saving. -/
theorem improving_count_raises_floor
    (S : ℝ) (N : ℕ) (M2r : ℝ) (hN : 0 < N) (hconc : S ≤ (N : ℝ) * M2r) :
    S / (N : ℝ) ≤ M2r := by
  rw [div_le_iff₀ (by exact_mod_cast hN)]
  linarith [hconc]

/-- **Monotonicity of the floor in the count.** For a FIXED sum `S ≥ 0` and `0 < N₁ ≤ N₂`, `S/N₂ ≤ S/N₁`. This
is scalar arithmetic only: it says nothing about whether a reduced count comes with a correspondingly reduced
(normalised) sum, and it does not show that structure acts only on the floor (see
`replicated_peak_upper_bound` for an upper-edge saving). -/
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
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.replicated_peak_upper_bound
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.replicated_peak_upper_bound_div
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.quotient_average_eq
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.improving_count_raises_floor
#print axioms ArkLib.ProximityGap.Frontier.BridgeAsymmetryStress.floor_antitone_in_count
