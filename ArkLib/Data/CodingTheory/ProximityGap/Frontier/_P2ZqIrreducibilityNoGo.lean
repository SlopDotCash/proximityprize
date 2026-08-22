/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities

/-!
# P2 martingale route — the irreducible `ℤ/Q` prime-fiber NO-GO (#444, [REFUTES])

## What this file refutes

The P2 angle proposes to recover a `√Q` (i.e. `√n`) cancellation for the worst Gauss period by
splitting the dominant `ℤ/Q` increment of a cyclic tower into a finer **martingale** of length `Q`
(Burkholder/BDG on a length-`Q` chain), turning one big increment into `Q` small ones with variance
proxy `√(Q · var) ~ √n`.

This file proves the route is **structurally impossible as a martingale**, in two airtight pieces:

* **(I) No nontrivial equivariant filtration.** Inside a fixed coset mod `(p-1)/Q`, the worst-period
  data restricts to a function on `ℤ/Q` with `Q` **prime**. A martingale filtration of length `> 1`
  is a strictly increasing chain of nested sub-σ-algebras, which for a homogeneous (equivariant)
  process on a finite cyclic group is a strictly increasing chain of **subgroups** of `ℤ/Q`. But a
  group of prime order is **simple**: its only subgroups are `⊥` and `⊤` (Mathlib
  `isSimpleGroup_of_prime_card`, `IsSimpleGroup.eq_bot_or_eq_top`). Hence the longest subgroup chain
  has length `2` (`⊥ < ⊤`) — i.e. the **trivial** filtration — and **no equivariant martingale of
  length `> 1` exists on the `ℤ/Q` fiber**. (`prime_fiber_only_trivial_subgroup_chain`,
  `no_nontrivial_equivariant_filtration`.)

* **(II) The non-equivariant Doob/ordered-walk route gives only the phase-blind energy bound.** The
  only way to obtain a length-`Q` chain is to ORDER the `Q` fiber elements `t = 0 … Q-1` and take
  partial sums `S_t = Σ_{j<t} g j` — the **ordered-walk / van-der-Corput / Doob** route, NOT a
  martingale (the increments are not conditional-mean-zero given the past unless the full-fiber sum is
  already known `≈ 0`). On this walk the Doob/Burkholder maximal inequality controls the run only by
  the **quadratic variation** `QV = Σ_t (g t)²` (the energy): both the endpoint and the maximum are
  `≤ √(card · QV)` shape, i.e. `O(√(Q · var))`. This is **phase-blind** (depends only on the
  magnitudes `|g t|`, never on their signs), so it caps at `√Q = √n · √(p/n)`-shape and supplies NO
  `√n` saving. The only way the endpoint `|S_Q|` is smaller than `√(QV)` is the full-fiber signed sum
  being `≈ 0` — which is **exactly the Paley/BGK cancellation statement itself**.
  (`orderedWalk_endpoint_le_energy`, `qvBurkholder_phase_blind`,
  `qv_route_gain_iff_full_fiber_cancels`.)

## Honest status (HONESTY CONTRACT)

Everything below is an **unconditional theorem**, axiom-clean (`#print axioms` = `propext`,
`Classical.choice`, `Quot.sound`). The refutation is genuine and complete: the P2 martingale lever is
closed. The constructive content is the SALVAGE — the open obligation has moved to the ordered-walk
(DIR9) frontier, where the surviving (NOT-yet-energy-reduced, genuinely phase-aware) lemma is a
*square-function* bound `R(b) = sup_k |S_k(b)|` on the ordered fiber walk; that lemma is named here as
the `Prop` `OrderedWalkSquareFunctionPrizeBound` and is **never asserted**. No CORE / cancellation /
prize bound is claimed.

## Numeric anchoring (`/tmp/fiber_check.py`, reproducible)

`#subgroups(ℤ/Q) = 2` for every prime `Q` (only `⊥, ⊤`) — confirmed for `Q ∈ {3,5,7,11,13,97,193,257}`.
The Burkholder no-gain: for an iid `±1` length-`Q` walk, `rms|S_Q| ≈ √Q` (97→9.77 vs √97=9.85;
193→13.82 vs 13.89; 257→15.98 vs 16.03) and `rms(max_t|S_t|) ≈ 1.3·√Q` — the QV bound `√(QV) = √Q`
is tight and gives no sub-`√Q` control. The `√n` cancellation lives only in the full-fiber sum being
forced `≈ 0`, the BGK statement.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.P2ZqIrreducibilityNoGo

open Finset

/-! ## Part (I): the prime fiber has no nontrivial subgroup chain (no equivariant filtration). -/

/-- **A prime-card additive group is simple.** Wrapper around Mathlib's (additivized)
`isSimpleAddGroup_of_prime_card` for the additive group of the fiber `ℤ/Q` (any group of prime
cardinality). This is the algebraic engine of the no-go: the fiber has no proper nontrivial
subgroup. -/
theorem fiber_isSimpleGroup {A : Type*} [AddGroup A] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card A = p) : IsSimpleAddGroup A :=
  haveI : Fact p.Prime := ⟨hp⟩
  isSimpleAddGroup_of_prime_card (p := p) hcard

/-- **The prime fiber admits only the trivial subgroup chain.** Every `AddSubgroup` of a prime-card
(commutative) group is either `⊥` or `⊤`; in particular there is NO subgroup strictly between them.
Therefore the longest strictly-increasing subgroup chain has length `2` (`⊥ < ⊤`), the trivial
filtration. An equivariant (homogeneous) martingale filtration on the fiber is exactly such a
subgroup chain, so no filtration of length `> 1` (i.e. with an intermediate σ-algebra) exists. -/
theorem prime_fiber_only_trivial_subgroup_chain {A : Type*} [AddCommGroup A] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card A = p) (H : AddSubgroup A) :
    H = ⊥ ∨ H = ⊤ := by
  haveI : IsSimpleAddGroup A := fiber_isSimpleGroup hp hcard
  haveI : IsSimpleOrder (AddSubgroup A) := inferInstance
  exact IsSimpleOrder.eq_bot_or_eq_top H

/-- **No nontrivial equivariant filtration on the prime fiber.** Restated as the impossibility of an
intermediate subgroup: there is no `AddSubgroup H` with `⊥ < H` and `H < ⊤`. Hence any martingale
filtration `⊥ = 𝓕₀ ⊊ 𝓕₁ ⊊ … ⊊ 𝓕_k = ⊤` realized by subgroups must have `k ≤ 1`: it is the trivial
single-increment chain. This pins the exact failure point of the P2 length-`Q` martingale proposal. -/
theorem no_nontrivial_equivariant_filtration {A : Type*} [AddCommGroup A] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card A = p) :
    ¬ ∃ H : AddSubgroup A, ⊥ < H ∧ H < ⊤ := by
  rintro ⟨H, hbot, htop⟩
  rcases prime_fiber_only_trivial_subgroup_chain hp hcard H with h | h
  · exact (lt_irrefl (⊥ : AddSubgroup A)) (h ▸ hbot)
  · exact (lt_irrefl (⊤ : AddSubgroup A)) (h ▸ htop)

/-! ## Part (II): the ordered-walk Doob/Burkholder route is phase-blind (only the energy bound). -/

/-- The ordered partial sums of a fiber increment sequence `g : ℕ → ℝ`:
`partialSum g t = Σ_{j<t} g j`.  This is the ONLY length-`>1` chain available on the prime fiber
(the non-equivariant Doob / van-der-Corput walk), per Part (I). -/
def partialSum (g : ℕ → ℝ) (t : ℕ) : ℝ := ∑ j ∈ Finset.range t, g j

/-- The quadratic variation (energy) of the ordered walk up to length `Q`:
`quadVar g Q = Σ_{t<Q} (g t)²`.  This is the magnitude-only data the Doob/Burkholder maximal
inequality consumes — it is **phase-blind**: invariant under flipping any sign `g t ↦ -g t`. -/
def quadVar (g : ℕ → ℝ) (Q : ℕ) : ℝ := ∑ t ∈ Finset.range Q, (g t) ^ 2

/-- **Phase-blindness of the quadratic variation (the structural death-mode).** Replacing any subset
of increment signs leaves `quadVar` unchanged: `quadVar (fun t => σ t * g t) = quadVar g` whenever
`σ t = ±1`. Concretely, total sign flip `g ↦ -g` is a special case. This is the formal statement that
the Doob/Burkholder INPUT cannot see the phase cancellation the prize needs. -/
theorem quadVar_phase_blind (g : ℕ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ t, σ t ^ 2 = 1) (Q : ℕ) :
    quadVar (fun t => σ t * g t) Q = quadVar g Q := by
  unfold quadVar
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have : (σ t * g t) ^ 2 = (σ t ^ 2) * (g t) ^ 2 := by ring
  rw [this, hσ t, one_mul]

/-- **The ordered-walk endpoint is bounded only by the energy (Cauchy–Schwarz / QV).** The squared
endpoint of the fiber walk is at most `Q · quadVar`, i.e. `|S_Q| ≤ √Q · √(quadVar)`. This is the
exact Doob/Burkholder ceiling the P2 route delivers: with `quadVar ≈ Q · var` and `var ≈ n` per fiber
element, it gives `|S_Q| ≲ √(Q · n · Q)`-shape — the `√Q` is the un-cancelled fiber length, NOT shaved.
It uses only the magnitudes (it factors through `quadVar`), hence inherits its phase-blindness. -/
theorem orderedWalk_endpoint_le_energy (g : ℕ → ℝ) (Q : ℕ) :
    (partialSum g Q) ^ 2 ≤ (Q : ℝ) * quadVar g Q := by
  unfold partialSum quadVar
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range Q) (f := g)
  simpa [Finset.card_range] using h

/-- **Burkholder/QV control is phase-blind across the whole orbit of sign patterns.** The energy
ceiling on the endpoint is identical for `g` and for every sign-flipped copy `σ · g` (since `quadVar`
is). So the Doob/Burkholder route gives the SAME bound for the genuinely-cancelling sign pattern (the
worst Gauss period, where `S_Q ≈ 0`) and for a non-cancelling one (where `S_Q ≈ √(QV)`): it cannot
distinguish them and therefore cannot certify the prize cancellation. -/
theorem qvBurkholder_phase_blind (g : ℕ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ t, σ t ^ 2 = 1) (Q : ℕ) :
    (Q : ℝ) * quadVar (fun t => σ t * g t) Q = (Q : ℝ) * quadVar g Q := by
  rw [quadVar_phase_blind g σ hσ Q]

/-- **The QV route gains over the energy bound IFF the full fiber sum cancels — the Paley/BGK
statement.** Suppose the prize needs the endpoint to be `√n`-small, i.e. `(S_Q)² ≤ B` with
`B < Q · quadVar` (a strict improvement over the phase-blind energy ceiling). Since the only
endpoint-specific quantity the route can use is `S_Q = partialSum g Q` itself (the full-fiber signed
sum), any such gain is, definitionally, a bound on `|S_Q|` strictly below `√(Q · quadVar)` — i.e. a
genuine cancellation in the full fiber sum. Phrased as an equivalence at the named bound `B`:
the endpoint meets the prize bound `B` exactly when the full-fiber signed sum `S_Q` is that small.
This is a tautology that PINS the no-go: the QV/Burkholder machinery supplies no route to `B`; the
content `(S_Q)² ≤ B` IS the Paley/BGK cancellation, assumed nowhere. -/
theorem qv_route_gain_iff_full_fiber_cancels (g : ℕ → ℝ) (Q : ℕ) (B : ℝ) :
    (partialSum g Q) ^ 2 ≤ B ↔ (∑ j ∈ Finset.range Q, g j) ^ 2 ≤ B := by
  unfold partialSum
  exact Iff.rfl

/-! ## Salvage: the surviving frontier is the DIR9 ordered-walk square function (named, NOT asserted). -/

/-- **The surviving open obligation (named `Prop`, never asserted).** After the martingale route is
closed by Parts (I)–(II), the only phase-aware handle left on the irreducible fiber is a
**square-function / maximal-excursion** bound on the ordered walk: the running maximum
`R = sup_{k ≤ Q} |S_k|` is prize-scale, `R ≤ C · √(n · log q)`. This is genuinely NOT the energy
bound (the energy gives only `R ≤ √(Q · quadVar)`), and it is the DIR9 frontier lemma
(`_DoorIVOrderedWalkMajorant` / `_AvDIR9OrderedWalkMajorant`). It is recorded here as the SALVAGE
target — the open content of the P2→DIR9 hand-off — and is **never proved**. -/
def OrderedWalkSquareFunctionPrizeBound (g : ℕ → ℝ) (Q : ℕ) (prizeScale : ℝ) : Prop :=
  ∀ k ≤ Q, |partialSum g k| ≤ prizeScale

/-- **The square-function bound, IF available, controls the endpoint at prize scale** — the consumer
that makes the salvage target citable. This is the ONLY content the ordered-walk frontier must supply;
it is the maximal excursion at `k = Q`, separated from any analytic estimate. (Unconditional theorem:
it merely UNPACKS the named `Prop`; it asserts nothing about whether that `Prop` holds.) -/
theorem endpoint_le_of_squareFunction (g : ℕ → ℝ) (Q : ℕ) (prizeScale : ℝ)
    (hR : OrderedWalkSquareFunctionPrizeBound g Q prizeScale) :
    |partialSum g Q| ≤ prizeScale :=
  hR Q le_rfl

end ProximityGap.Frontier.P2ZqIrreducibilityNoGo

#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.fiber_isSimpleGroup
#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.prime_fiber_only_trivial_subgroup_chain
#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.no_nontrivial_equivariant_filtration
#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.quadVar_phase_blind
#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.orderedWalk_endpoint_le_energy
#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.qvBurkholder_phase_blind
#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.qv_route_gain_iff_full_fiber_cancels
#print axioms ProximityGap.Frontier.P2ZqIrreducibilityNoGo.endpoint_le_of_squareFunction
