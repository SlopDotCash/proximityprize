/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Door IV: the subset-sum collision excess `Ψ_p − Ψ_0` is a pure pigeonhole quantity, not an
# exploitable arithmetic lever (A50 follow-on constraint lemma)

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

## The probe verdict

(reproducible; proper `μ_n < F_p^*`, `p ≡ 1 mod n`, `m` odd, `β ≈ 4`, never `n = q-1`)

The collision count is governed **purely by the cardinality ratio `N_r / p`**, i.e. by the generic
birthday/pigeonhole law:

* `N_r ≪ p` (n = 16, β ≥ 4 prize regime): `defect = 0` **exactly** — the `F_p` count is
  collision-FREE. So A50's "collision-saturated at binding depth" is *false in the dilute large-p
  regime*; saturation is a function of `N_r / p`, not of the binding depth `r = ρn` per se.
* The actual `Ψ_p` tracks the random birthday prediction `p·(1 − (1 − 1/p)^{N_r})` to ~1–12%.
* At the crossover band `N_r / p ∈ [0.7, 1.3]`, the thin subgroup `μ_n` produces **MORE** collisions
  (fewer distinct sums) than a random set of the same cardinality (mu/birthday ≈ 0.93–1.01 vs
  random/birthday ≈ 1.08–1.12). The excess **is** thinness-essential, but in the **WRONG
  DIRECTION**: more subset-sum collisions ⟺ less additive distinctness ⟺ the thin subgroup is
  *more* additively degenerate, which is exactly why `M(n)` is *large* (worse cancellation). An
  upper bound on the
  collision excess therefore cannot give an upper bound on `M`; the collision count is
  *anti*-correlated with cancellation. (Consistent with the mapped DISPROOF "thin `μ_n`
  concentrates WORSE than random", 2026-06-15 — this is its depth-resolved refinement.)

## The formalizable kernel (this file)

The reason the excess is a pure pigeonhole quantity: `Ψ_p` is the cardinality of the **image**
of the sum-map on the `Ψ_0`-many char-0 classes into `F_p` (a fintype of size `p`). The image
of a finite set under any map into a `p`-element type has card `≤ min(source, p)`, hence:

* `Ψ_p ≤ Ψ_0`  (mod-`p` reduction only merges) — `image_card_le_source`;
* `Ψ_p ≤ p`    (only `p` residues exist)        — `image_card_le_codomain`;
* `Ψ_0 > p ⟹ defect = Ψ_0 − Ψ_p ≥ Ψ_0 − p > 0`  (pigeonhole FORCES collisions once `N_r`
  exceeds the field size) — `defect_ge_of_source_gt_card`.

This proves *nothing* about CORE and uses no moment/completion. It pins the collision excess as a
cardinality (pigeonhole) phenomenon: its only forced lower bound is `N_r − p`, a quantity that
involves the char-0 count and the field size but **not** the thin-subgroup phase structure that the
prize cancellation lives in. Combined with the probe's wrong-direction sign, this is the no-go
for the "`Ψ_p − Ψ_0` is a live door-(iv) upper-bound lever" route.
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
`Fintype.card β < s.card`, where it forces `defect ≥ N_r − p > 0`. So the defect's only *forced*
lower bound is `N_r − p`, a pure cardinality quantity (see `defect_pos_of_source_gt_card`). -/
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
`min(Ψ_0, p)`. This is the exact `Ψ_p ≤ min(N_r, p)` ceiling the probe measured the actual count
tracking (to birthday accuracy). -/
theorem image_card_le_min {β : Type*} [DecidableEq β] [Fintype β]
    (s : Finset α) (φ : α → β) :
    (s.image φ).card ≤ min s.card (Fintype.card β) :=
  le_min (image_card_le_source s φ) (image_card_le_codomain s φ)

/-- Collision-free reduction is exactly injectivity of the reduction map on the char-0 classes.
This is the probe-facing form for the dilute `N_r ≪ p` regime: zero defect is not a phase
coherence estimate; it is precisely the elementary no-two-classes-merge condition. -/
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
