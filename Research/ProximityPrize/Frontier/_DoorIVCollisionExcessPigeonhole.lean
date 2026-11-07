/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Door IV: the pigeonhole floor on the subset-sum collision excess `Ψ_0 − Ψ_p`
# (A50 follow-on constraint lemma; one-way lower bound only)

This file records the axiom-clean arithmetic kernel behind the probes
`scripts/probes/probe_444_psi_collision_excess_scaling.py` (and its honesty follow-ups
`probe_psi3`, `probe_psi4`).

## Context

`Sweep_A50_SpectrumGeneratingFunction.lean` put the **char-0** subset-sum spectrum count
`Ψ_0(r) = N_r = #{ distinct ∑_{z∈S} z : S ⊆ μ_n, |S| = r }` in closed form, and named its
honest open core as the **`F_p` collision excess**:

  `Ψ_p(r) := #{ distinct (∑_{z∈S} z mod p) : S ⊆ μ_n, |S| = r }`,
  `defect(r) := Ψ_0(r) − Ψ_p(r) ≥ 0`   (reducing mod `p` can only merge classes).

The brief's door-(iv) hope was that this excess might carry exploitable arithmetic (multiplicative,
thin-subgroup) structure that a non-moment bound could grip.

## The probe observations (finite evidence only; corrected per audit R-304)

(probed cells: proper `μ_n < F_p^*`, `p ≡ 1 mod n`, `m` odd, `β ≈ 4`, never `n = q-1`)

* In the probed cells the measured `Ψ_p` tracked the random birthday prediction
  `p·(1 − (1 − 1/p)^{N_r})` to ~1–12%. This is a finite empirical observation; it does NOT show
  that `Ψ_p` is determined solely by the ratio `N_r / p`, and nothing in this file proves such a
  birthday law.
* An earlier version of this header claimed that for `N_r ≪ p` (`n = 16`, `β ≥ 4`) the reduction
  is **exactly** collision-free (`defect = 0`). **That claim is false.** `N_r < p` does not make
  reduction injective. Counterexample cell (repository audit 2026-10-28, findings T106/R-304;
  exponent sets `{0,1,2,4,8,13,14,15}` and `{0,1,3,6,7,9,10,12}` both evaluate to `1108`):
  `n = 16`, `p = 66449 > 16⁴` (odd quotient `4153`), root `12909`; the `12870` eight-subsets have
  `3281` distinct char-0 sums (coefficient vectors in the `Φ₁₆` basis) but only `3217` distinct
  values mod `p`, so `defect = 64 > 0` although `N_r / p < 1/20`. (A finite cell in the advertised
  regime, not a sponsor-prime counterexample.) Whether collisions occur below `p` is an
  arithmetic, per-prime question, not a cardinality one.
* At the crossover band `N_r / p ∈ [0.7, 1.3]`, the probed thin subgroup `μ_n` produced more
  collisions (fewer distinct sums) than a random set of the same cardinality (mu/birthday
  ≈ 0.93–1.01 vs random/birthday ≈ 1.08–1.12).

**Direction of the upper-bound question.** An earlier version argued that an *upper* bound on the
collision excess "cannot give an upper bound on `M`" because more collisions mean worse
cancellation. That inference has its direction backwards: if more collisions correlate with
larger `M`, then *preventing* large excess is exactly how an upper energy envelope could rule out
excessive concentration. What is genuinely missing is a **bridge** from the unweighted image
deficit `Ψ_0 − Ψ_p` to the weighted (multiplicity-counting) collision energy that controls `M`;
the image deficit alone need not determine that weighted energy. No such bridge is proved here,
and its absence is not a sign-based impossibility theorem. Nothing in this file excludes further
arithmetic lower or upper bounds on the collision count beyond the generic pigeonhole floor.

## The formalizable kernel (this file)

The one-way pigeonhole floor: `Ψ_p` is the cardinality of the **image**
of the sum-map on the `Ψ_0`-many char-0 classes into `F_p` (a fintype of size `p`). The image
of a finite set under any map into a `p`-element type has card `≤ min(source, p)`, hence:

* `Ψ_p ≤ Ψ_0`  (mod-`p` reduction only merges) — `image_card_le_source`;
* `Ψ_p ≤ p`    (only `p` residues exist)        — `image_card_le_codomain`;
* `Ψ_0 > p ⟹ defect = Ψ_0 − Ψ_p ≥ Ψ_0 − p > 0`  (pigeonhole FORCES collisions once `N_r`
  exceeds the field size) — `defect_ge_of_source_gt_card`.

This proves *nothing* about CORE and uses no moment/completion. It supplies only the generic
pigeonhole floor `defect ≥ N_r − p`, a quantity that involves the char-0 count and the field size
but not the thin-subgroup phase structure. The converse direction is NOT proved and is false in
general: `N_r ≤ p` does not imply injectivity (see the `n = 16`, `p = 66449` cell above), and the
actual image count is not a function of `N_r / p` alone. This file is not a no-go for a door-(iv)
upper-bound route: such a route would need an actual bridge from the image deficit to a weighted
collision energy, which is neither supplied nor refuted here.
-/

namespace ProximityGap.Frontier.DoorIVCollisionExcessPigeonhole

open Finset

variable {α : Type*}

/-- `Ψ_p` modelled abstractly: the number of distinct images of a finite source set `s` of char-0
classes under the reduction map `φ : α → β`. The image card never exceeds the source card —
reduction can only merge classes (`Ψ_p ≤ Ψ_0`). -/
theorem image_card_le_source {β : Type*} [DecidableEq β]
    (s : Finset α) (φ : α → β) :
    (s.image φ).card ≤ s.card :=
  Finset.card_image_le

/-- The image card never exceeds the size of the codomain fintype (only `p` residues exist):
`Ψ_p ≤ p`. -/
theorem image_card_le_codomain {β : Type*} [DecidableEq β] [Fintype β]
    (s : Finset α) (φ : α → β) :
    (s.image φ).card ≤ Fintype.card β := by
  calc (s.image φ).card ≤ (Finset.univ : Finset β).card := Finset.card_le_card (subset_univ _)
    _ = Fintype.card β := Finset.card_univ

/-- **The collision-excess pigeonhole bound.** Writing `Ψ_0 = s.card` (char-0 spectrum count) and
`Ψ_p = (s.image φ).card` (distinct mod-`p` count), the collision excess is bounded below by the
pure cardinality gap `N_r − p`:

  `s.card − Fintype.card β ≤ s.card − (s.image φ).card`   (= the defect `Ψ_0 − Ψ_p`).

The bound holds unconditionally (when `p ≥ N_r` the left side is `0`); its content is in the regime
`Fintype.card β < s.card`, where it forces `defect ≥ N_r − p > 0`. So the generic (map-independent)
forced lower bound is `N_r − p` (see `defect_pos_of_source_gt_card`); particular reduction maps can
have strictly larger defect, including positive defect when `N_r ≤ p`. -/
theorem defect_ge_of_source_gt_card {β : Type*} [DecidableEq β] [Fintype β]
    (s : Finset α) (φ : α → β) :
    s.card - Fintype.card β ≤ s.card - (s.image φ).card :=
  Nat.sub_le_sub_left (image_card_le_codomain s φ) s.card

/-- The forced defect is strictly positive once the spectrum exceeds the field size: a clean
statement that `N_r > p` makes the `F_p` count strictly collision-saturated (`Ψ_p < Ψ_0`). -/
theorem defect_pos_of_source_gt_card {β : Type*} [DecidableEq β] [Fintype β]
    (s : Finset α) (φ : α → β) (h : Fintype.card β < s.card) :
    (s.image φ).card < s.card := by
  exact lt_of_le_of_lt (image_card_le_codomain s φ) h

/-- Consumer form: the distinct mod-`p` count is bounded by the elementary collision ceiling
`min(Ψ_0, p)`. This is a ceiling only: the actual count can be strictly below `min(N_r, p)` (e.g.
`3217 < 3281 = min(N_r, p)` at `n = 16`, `p = 66449`). -/
theorem image_card_le_min {β : Type*} [DecidableEq β] [Fintype β]
    (s : Finset α) (φ : α → β) :
    (s.image φ).card ≤ min s.card (Fintype.card β) :=
  le_min (image_card_le_source s φ) (image_card_le_codomain s φ)

/-- Collision-free reduction is exactly injectivity of the reduction map on the char-0 classes.
Zero defect is precisely the elementary no-two-classes-merge condition; it is not implied by
`N_r ≪ p` and must be checked (or proved arithmetically) per prime. -/
theorem defect_eq_zero_iff_injOn {β : Type*} [DecidableEq β]
    (s : Finset α) (φ : α → β) :
    s.card - (s.image φ).card = 0 ↔ Set.InjOn φ s := by
  rw [Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    have hle : (s.image φ).card ≤ s.card := image_card_le_source s φ
    have heq : (s.image φ).card = s.card := le_antisymm hle h
    exact (Finset.card_image_iff).mp heq
  · intro h
    have heq : (s.image φ).card = s.card := Finset.card_image_of_injOn h
    rw [heq]

/-- Positive collision excess is exactly non-injectivity on the source classes. Thus the formal
content of `Ψ₀ - Ψ_p > 0` is a merge/collision witness, not an independent cancellation bound. -/
theorem defect_pos_iff_not_injOn {β : Type*} [DecidableEq β]
    (s : Finset α) (φ : α → β) :
    0 < s.card - (s.image φ).card ↔ ¬ Set.InjOn φ s := by
  rw [Nat.pos_iff_ne_zero]
  exact not_congr (defect_eq_zero_iff_injOn s φ)

#print axioms image_card_le_source
#print axioms image_card_le_codomain
#print axioms defect_ge_of_source_gt_card
#print axioms defect_pos_of_source_gt_card
#print axioms image_card_le_min
#print axioms defect_eq_zero_iff_injOn
#print axioms defect_pos_iff_not_injOn

end ProximityGap.Frontier.DoorIVCollisionExcessPigeonhole
