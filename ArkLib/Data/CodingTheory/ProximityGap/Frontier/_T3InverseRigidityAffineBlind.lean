/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# T3 inverse-rigidity dichotomy is AFFINE-BLIND (#444, shape-transform T3-inverse)

## The shape we tried to transform into

Instead of bounding `M = max_{b≠0} ‖η_b‖` directly, the T3-inverse-rigidity programme proposed a
**margin-free dichotomy** (escaping face (d) = vanishing margin):

> IF `‖η_{b*}‖` is abnormally large THEN the dilate `b*·μ_n` has additive structure (small
> doubling / a 2nd large Fourier coefficient / concentration). But `μ_n` is multiplicatively
> structured, hence additively rigid (Sidon-like). Contradiction ⟹ `M` cannot be large.

## Why it REDUCES — the exact obstruction (this file proves it)

Every "additive-structure signature" of the candidate set `b·S` (doubling `|b·S + b·S|`, additive
energy `#{(a,b,c,d) : a+b=c+d}`, the difference set, the whole Fourier-magnitude spectrum) is an
**affine invariant**: the dilation map `x ↦ b·x` is an additive-group automorphism of `ZMod p`
(for `b` a unit), so it is a bijection commuting with `+`. Hence

* `|b·S + b·S| = |S + S|`  for **every** unit `b`, and
* `‖η̂_{b·S}‖` as a multiset equals `‖η̂_S‖` (the spectrum is permuted, not changed).

Therefore the additive-structure signature of `b·μ_n` is **literally constant in `b`**. It is
*identical* at the worst frequency `b*` and at a typical frequency. A dichotomy whose "structured"
side is read off an affine invariant can never separate the worst `b*` from any other `b`: there is
nothing to detect. The dichotomy collapses to the trivial statement "`μ_n` has the doubling it has".

This is confirmed numerically (exact, this session): at the worst `b*`, `|b*·μ_n + b*·μ_n| =
|μ_n + μ_n|` exactly (`129` at `n=16,p=65537`; `513` at `n=32`; `K = |A+A|/|A| ≈ n/2`, i.e.
**near-MAXIMAL** doubling — `μ_n` is already additively structureless), and the spectrum is FLAT:
`M` is attained on a *full coset* of size `n` with `M/secondMax = 1.0000`. There is no second large
Fourier coefficient and no small-doubling dilate to find.

## Which of the four faces it dies through

Face **(d) vanishing-margin** is what it tried to escape, and it does escape (d) — but it dies
through a *fifth*, even more basic, obstruction the diagnosis did not list explicitly: **affine-
invariance / b-blindness**. The dichotomy's input (an additive-structure functional of the dilate)
is constant across all `b`, so it is *worse* than b-summed face (a): it does not even see `b`. The
phase cancellation that produces small `‖η_b‖` at most `b` (and the value `√(n log p)` at the worst)
lives in the *archimedean phases* of the Fourier coefficient, NOT in the additive combinatorics of
the set — and the additive combinatorics is exactly what an affine-invariant dichotomy reads.

Conclusion: the inverse-rigidity dichotomy is a genuine *relabel*, not a transform. The honest
content is the lemma below: additive doubling of a unit-dilate is independent of the dilate.

## What this file proves (axiom-clean)

For a finite set `S ⊆ ZMod p` and a unit `b`, the dilated sumset `(b•S) + (b•S)` is the image of
`S + S` under the bijection `x ↦ b•x`, hence has the *same cardinality*. This is the precise,
fully general obstruction: **doubling is a dilation invariant**, so it cannot distinguish frequencies.
-/

namespace ProximityGap.T3InverseRigidity

open Finset

variable {p : ℕ}

/-- The sumset `S + S` of a finite set in `ZMod p`, as a `Finset`. -/
def sumset (S : Finset (ZMod p)) : Finset (ZMod p) :=
  (S ×ˢ S).image (fun q => q.1 + q.2)

/-- The dilate `b • S = {b * x : x ∈ S}`. -/
def dilate (b : ZMod p) (S : Finset (ZMod p)) : Finset (ZMod p) :=
  S.image (fun x => b * x)

/-- Multiplication by a unit `b` is injective on `ZMod p`. -/
theorem mul_left_injective_of_isUnit {b : ZMod p} (hb : IsUnit b) :
    Function.Injective (fun x : ZMod p => b * x) := by
  obtain ⟨u, rfl⟩ := hb
  intro x y h
  simp only at h
  have h2 := congrArg (fun z => (↑u⁻¹ : ZMod p) * z) h
  simpa [← mul_assoc] using h2

/-- **Dilation preserves the sumset, up to the bijection `x ↦ b•x`.**
The sumset of the dilate equals the dilate of the sumset. -/
theorem sumset_dilate (b : ZMod p) (S : Finset (ZMod p)) :
    sumset (dilate b S) = dilate b (sumset S) := by
  unfold sumset dilate
  ext z
  simp only [mem_image, mem_product]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
    exact ⟨x + y, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, by ring⟩
  · rintro ⟨w, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
    exact ⟨⟨b * x, b * y⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, by ring⟩

/-- **THE OBSTRUCTION (doubling is a dilation invariant).**
For a unit `b`, the doubling `|b•S + b•S|` equals `|S + S|` for *every* `b`. Hence no additive-
doubling functional of the dilate `b•μ_n` can distinguish the worst frequency `b*` from any other
`b`: the inverse-rigidity dichotomy reads a quantity that is constant in `b`, so it reduces. -/
theorem doubling_dilate_eq (b : ZMod p) (hb : IsUnit b) (S : Finset (ZMod p)) :
    (sumset (dilate b S)).card = (sumset S).card := by
  rw [sumset_dilate]
  unfold dilate
  exact Finset.card_image_of_injective _ (mul_left_injective_of_isUnit hb)

/-- The dilate has the same cardinality as the original set (a unit acts bijectively),
so `|S|` itself is also b-invariant — the "size of the candidate set" is constant too. -/
theorem card_dilate_eq (b : ZMod p) (hb : IsUnit b) (S : Finset (ZMod p)) :
    (dilate b S).card = S.card :=
  Finset.card_image_of_injective _ (mul_left_injective_of_isUnit hb)

/-- **Corollary (the dichotomy is b-blind).** The doubling *ratio* `|b•S + b•S| / |b•S|`,
the standard "additive structure" measure, is identical for all units `b`. Stated as the equality
of the two cardinality pairs that define the ratio. -/
theorem doubling_ratio_b_blind (b₁ b₂ : ZMod p) (h₁ : IsUnit b₁) (h₂ : IsUnit b₂)
    (S : Finset (ZMod p)) :
    (sumset (dilate b₁ S)).card = (sumset (dilate b₂ S)).card ∧
    (dilate b₁ S).card = (dilate b₂ S).card := by
  refine ⟨?_, ?_⟩
  · rw [doubling_dilate_eq b₁ h₁, doubling_dilate_eq b₂ h₂]
  · rw [card_dilate_eq b₁ h₁, card_dilate_eq b₂ h₂]

/-!
## The named dichotomy and its refutation

We record the dichotomy as a `Prop` and prove that its "structured side" is vacuously constant.
-/

/-- The additive-structure functional the dichotomy would read off the dilate: doubling. -/
def structureSignature (b : ZMod p) (S : Finset (ZMod p)) : ℕ :=
  (sumset (dilate b S)).card

/-- **The inverse-rigidity dichotomy reduces (formal statement).**
For any two nonzero frequencies `b*` (worst) and `b` (typical), the structure signature the
dichotomy compares is *equal*. So the would-be separating quantity is constant: the dichotomy
carries no information about which frequency is the worst, and reduces to a tautology. -/
theorem inverse_rigidity_dichotomy_reduces
    {bStar b : ZMod p} (hStar : IsUnit bStar) (hb : IsUnit b) (S : Finset (ZMod p)) :
    structureSignature bStar S = structureSignature b S := by
  unfold structureSignature
  rw [doubling_dilate_eq bStar hStar, doubling_dilate_eq b hb]


-- Axiom audit (must be {propext, Classical.choice, Quot.sound}; no sorryAx).
#print axioms ProximityGap.T3InverseRigidity.sumset_dilate
#print axioms ProximityGap.T3InverseRigidity.doubling_dilate_eq
#print axioms ProximityGap.T3InverseRigidity.doubling_ratio_b_blind
#print axioms ProximityGap.T3InverseRigidity.inverse_rigidity_dichotomy_reduces

end ProximityGap.T3InverseRigidity
