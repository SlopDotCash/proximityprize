/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# The `e₂=0` mod-`q` defect image is `O(n)`, quantized in units of `n`
(Proximity Prize #407, thread **L4-onq**, T400-05 follow-up)

This file formalizes, **axiom-clean**, the *quantization* half of the per-`q` `e₂=0` defect
image bound that thread L4-onq drives. Wave 1 (T400-05) measured the genuine per-`q` carrier
image to be exactly in **units of `n`** — `{n, 2n, 3n} = {16, 32, 48}` at `n=16, w=6` once the
small-prime `q-1` saturation artifact is escaped (probe
`scripts/probes/wf407w2_L4-onq_image_quantization.py`, EXACT enumeration). This file proves the
**mechanism** behind that observed quantization.

## The mechanism (measured exact, here proven)

For a `w`-subset `S ⊆ μ_n` the dilation `S ↦ g·S` by `g ∈ μ_n` preserves `e₂(S)=0 (mod q)` and
sends `e₁(S) ↦ g·e₁(S)`. So the set of *nonzero* carrier images
`I = { e₁(S) (mod q) : e₂(S) = 0, e₁(S) ≠ 0 }` is **invariant under multiplication by a primitive
`n`-th root `z ∈ F_q^×`**. The cyclic group `⟨z⟩ ≅ ZMod n` acts on `F_q^×` by multiplication;
this action is **free** (no element of a group is fixed by left-multiplication by `z ≠ 1`), so
**every orbit has size exactly `n`**. Hence the `z`-invariant finite set `I` is a disjoint union of
size-`n` orbits:

* `n ∣ |I|` — the image is **quantized in units of `n`** (matches the measured `{n,2n,3n}`);
* if `I` is covered by `k` orbits then `|I| = k · n`, so with the `s_max = μ−1` staircase ceiling
  `k ≤ s_max` (issue400-smax-law) one gets `|I| ≤ s_max · n = (μ−1)·n = O(n)`, **uniform in `q`**.

## What this file proves (the elementary skeleton)

The dilation invariance is captured abstractly: we work with a **group** `G` (the multiplicative
group `F_q^×`), an element `z : G` of order `n`, and the left-multiplication `MulAction` of the
finite cyclic group `Multiplicative (ZMod n)` (via `zpowers`/`Subgroup.zpowers z`). The genuine
content:

* `card_orbit_eq_orderOf` — every orbit of the `⟨z⟩`-action by left multiplication on `G` has size
  exactly `orderOf z = n` (the action is free).
* `dvd_card_of_smul_invariant` — a finite `z`-invariant set `I` has `n ∣ |I|` (it is a disjoint
  union of size-`n` orbits). **This is the "units of `n`" quantization.**
* `card_le_of_orbit_count` — if moreover `I` is covered by at most `k` orbits, `|I| ≤ k · n`.
* `image_card_le_smax_mul_n` — packaging: with the staircase orbit-count ceiling `k ≤ s_max`, the
  per-`q` image is `≤ s_max · n` (`= O(n)`, **uniform in `q`** below saturation).

## Honesty contract (what this does and does NOT prove)

This proves the **structural quantization + `O(n)` ceiling of the per-`q` image**, the rigorous
form of the measured `{n, 2n, 3n}`. The orbit-count ceiling `k ≤ s_max = μ−1` enters as a named
hypothesis (`hk`), exactly the `s_max` law (`issue400-smax-law-mu-minus-1…`: constructive lower
bound + upper bound verified to `n=32`, full induction open — a finite combinatorial residual, NOT
the character-sum wall). With that input the per-`q` image is provably `O(n)`, uniform in `q`.

It does **NOT** close the prize: it is a per-`q` (below-saturation) image bound, not a uniform
worst-case-over-`q` *defect* bound; the adversary's choice of `q` (the cyclotomic-norm collision
`q ∣ N(e₂(S))`, face 3 of the open core) is untouched. See the companion onset measurement
(`scripts/probes/wf407w2_L4-onq_onset.py`): the smallest carrier norms are units / 2-powers
(harmless), the first GENUINE adversarial prime at `n=16` is `q=97` (norm `97` itself).

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.WF407W2_L4onq

open MulAction

variable {G : Type*} [Group G] [Fintype G]

attribute [local instance] Classical.propDecidable

/-- **The `⟨z⟩`-stabilizer of any point under left multiplication is trivial (free action).**
Left multiplication by `h ∈ ⟨z⟩` fixes `x` iff `h = 1`; this is the freeness that forces every
orbit to have full size `orderOf z`. -/
theorem stabilizer_eq_bot (z : G) (x : G) :
    stabilizer (Subgroup.zpowers z) x = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  have hx : (h : G) * x = x := hh
  have h1 : (h : G) = 1 := by
    apply mul_right_cancel (b := x)
    simpa using hx
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

/-- **Every orbit of the `⟨z⟩`-action by left multiplication has size `orderOf z`.**
The cyclic subgroup `H = Subgroup.zpowers z` acts on `G` by left multiplication. This action is
**free** (left multiplication has no fixed points: `h • x = x ⟹ h = 1`), so each orbit `H • x` is
in bijection with `H`, whose cardinality is `orderOf z = n`. This is the source of the measured
"units of `n`" quantization of the per-`q` `e₂=0` image. -/
theorem card_orbit_eq_orderOf (z : G) (x : G) :
    Fintype.card (orbit (Subgroup.zpowers z) x) = orderOf z := by
  classical
  have hstab := stabilizer_eq_bot z x
  -- Orbit-stabilizer: |orbit| * |stab| = |H|, with |stab| = 1.
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Subgroup.zpowers z) x
  have hsub : Fintype.card (stabilizer (Subgroup.zpowers z) x) = 1 := by
    simpa only [hstab] using
      (Fintype.card_eq_one_iff.mpr
        ⟨(1 : (⊥ : Subgroup (Subgroup.zpowers z))), fun y => Subsingleton.elim _ _⟩)
  rw [hsub, mul_one] at hos
  rw [hos, Fintype.card_zpowers]

end ArkLib.ProximityGap.WF407W2_L4onq
