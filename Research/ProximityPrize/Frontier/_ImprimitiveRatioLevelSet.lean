/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.GCD.Basic

/-!
# The imprimitive ratio-census level-set law (the inverse-Littlewood–Offord brick, #407 D3)

Companion / sharpening of `RatioLevelSet.lean` and `RatioCensusWeightIdentity.lean`.

`RatioCensusWeightIdentity.lean` lands the exact char-sum-free identity
`wt(s₀ + γ·s₁) = n − z₀ − ratioMult s₀ s₁ γ`, where
`ratioMult γ = #{i ∈ supp(s₁) : −s₀ᵢ/s₁ᵢ = γ}` is the multiplicity of `γ` in the ratio
sequence.  `RatioLevelSet.lean` lands the **generic** upper bound: for a GRS line the ratio is a
rational function so any level set is a root set, hence `ratioMult γ ≤ max (deg s₀) (deg s₁)`.

The D3 thread (issue #407 comment 199) pins that the *worst-case* far-line incidence is attained
on the **imprimitive** monomial directions `r(x) = −x^d` on the smooth subgroup `μ_n` (`n = 2^μ`),
where the per-value multiplicity *collapses* onto the Gauss period — the BGK object.  This file
isolates the elementary, char-free, **exact** (sharp both directions — the inverse-LO content) law
behind that collapse:

> **The ratio sequence of `r = −x^d` on the cyclic group `μ_n` is the power map `x ↦ x^d`, whose
> nonempty fibers are *exactly* the cosets of `ker = μ_{gcd(n,d)}`.** Hence every attained value has
> multiplicity **exactly** `gcd(n, d)` (not merely `≤`), and the number of attained values (the
> high-multiplicity level-set count, i.e. the inverse-LO concentration count) is **exactly**
> `n / gcd(n, d)`.

Stated for an abstract finite cyclic group `G` (the smooth subgroup `μ_n` is the running model):

* `imprimitive_fiber_card` — every nonempty fiber of `x ↦ x^d` has card `gcd(card G, d)`.
  This is the **sharp** `ratioMult`: the per-value multiplicity is forced to be exactly the gcd, so
  the imprimitive direction *cannot* spread its multiplicity below `gcd(n,d)` — anti-concentration
  is impossible, concentration is forced.  (The inverse-LO statement: high `ratioMult` is *not* a
  rare accident here, it is structural.)
* `imprimitive_image_card` — the number of distinct attained ratio values is
  `card G / gcd(card G, d)` (the count of high-multiplicity level sets).
* `imprimitive_highmult_levelset_card` — the clean inverse-LO level-set count: for any threshold
  `t ≤ gcd (card G) d`, the number of values with `ratioMult ≥ t` is exactly
  `card G / gcd(card G, d)`.

**Honest scope.**  This is the exact `STEP-2` algebraic input for the imprimitive sub-family that
the generic `RatioLevelSet.grs_line_incidence_le` over-estimates (`max deg = d` vs the true
`gcd(n,d)`), and it is the precise place where the ratio-census *re-encodes* the Gauss period:
`d = n/2` gives `gcd(n,d) = n/2`, the maximal collapse (`x^{n/2} = ±1` on `μ_n`).  It bounds the
**concentrated** part of the far-line incidence: numerically (exact list-decode, `n=16,k=4,r=10`,
worst monomial direction `(x^9, x^{15})`, `j=b−a=6`, `gcd(j,n)=2`), the high-multiplicity bad
scalars are **exactly a `μ_{n/gcd}=μ_8` coset of size `n/gcd=8`** (every concentrated `γ` verified
to satisfy `(γ/γ₀)^8 = 1`), matching `imprimitive_image_card`.  It is **NOT a closure**: the
binding far-line-to-*code* incidence at that direction is `88`, dominated by the **80
low-multiplicity generic ratios** (mult `≤ 2`, the Weil part = the `t=2` coincidence moment) — open
BGK/Paley face — which this law does not touch.  The brick caps the concentrated `μ_{n/gcd}`-coset
contribution at `n` (sharp), reducing the open residual to the generic-ratio coincidence moment.
See the #407 D3 thread (comment 199).

Char-free, no field-size hypothesis; pure finite cyclic-group theory built on Mathlib's
`IsCyclic.card_powMonoidHom_ker` / `card_powMonoidHom_range`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- issue #407, attack thread D3 (inverse-Littlewood–Offord ratio-census), comment 199.
-/

namespace ArkLib.ProximityGap.ImprimitiveRatio

open Finset

variable {G : Type*} [CommGroup G] [IsCyclic G] [Fintype G] [DecidableEq G]

/-- The **power map** `x ↦ x^d` on the cyclic group `G` — the ratio sequence of the imprimitive
monomial direction `r(x) = −x^d` (the `−` and the GRS sign are absorbed; what matters is the
fiber structure of `x ↦ x^d` on `μ_n`). -/
abbrev powHom (d : ℕ) : G →* G := powMonoidHom d

/-- **The sharp `ratioMult` for the imprimitive direction (the inverse-LO core).**
Every *nonempty* fiber of the power map `x ↦ x^d` on the cyclic group `G` has cardinality
**exactly** `gcd (card G) d`.  In ratio-census terms: the per-value multiplicity of the imprimitive
ratio `−x^d` is forced to be exactly the gcd — concentration is structural, not accidental. -/
theorem imprimitive_fiber_card (d : ℕ) {y : G} (hy : y ∈ Set.range (powHom (G := G) d)) :
    (univ.filter (fun x : G => x ^ d = y)).card = Nat.gcd (Fintype.card G) d := by
  classical
  -- the fiber over `1` is the kernel, of card `gcd (card G) d`
  have hker_mem : (1 : G) ∈ Set.range (powHom (G := G) d) := ⟨1, by simp [powHom]⟩
  -- all fibers over the range have equal card (Mathlib's `card_fiber_eq_of_mem_range`)
  have heq := MonoidHom.card_fiber_eq_of_mem_range (powHom (G := G) d) hy hker_mem
  -- the two filter predicates of `heq` are our `x ^ d = y` and `x ^ d = 1`
  have hlhs : (univ.filter (fun g : G => (powHom (G := G) d) g = y))
      = univ.filter (fun x : G => x ^ d = y) := by
    apply Finset.filter_congr; intro x _; simp [powHom, powMonoidHom]
  have hrhs : (univ.filter (fun g : G => (powHom (G := G) d) g = (1 : G)))
      = univ.filter (fun x : G => x ^ d = 1) := by
    apply Finset.filter_congr; intro x _; simp [powHom, powMonoidHom]
  rw [hlhs, hrhs] at heq
  rw [heq]
  -- the fiber over `1` IS the kernel as a subtype; its card is `gcd (card G) d`
  have hbij : (univ.filter (fun x : G => x ^ d = 1)).card
      = Fintype.card (powHom (G := G) d).ker := by
    rw [Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro x _
    simp [MonoidHom.mem_ker, powHom, powMonoidHom_apply]
  rw [hbij]
  have hnc := IsCyclic.card_powMonoidHom_ker G d
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hnc
  exact hnc

/-- **The number of distinct attained ratio values** (the count of high-multiplicity level sets):
the image of the power map `x ↦ x^d` on the cyclic group `G` has cardinality
`card G / gcd (card G) d`. -/
theorem imprimitive_image_card (d : ℕ) :
    (univ.image (fun x : G => x ^ d)).card = Fintype.card G / Nat.gcd (Fintype.card G) d := by
  classical
  -- the image is exactly the range subgroup as a subtype
  have hbij : (univ.image (fun x : G => x ^ d)).card
      = Fintype.card (powHom (G := G) d).range := by
    rw [Fintype.card_subtype]
    apply Finset.card_bij (fun y _ => y)
    · intro y hy
      rw [mem_image] at hy
      obtain ⟨x, _, rfl⟩ := hy
      simp only [mem_filter, mem_univ, true_and, MonoidHom.mem_range, powHom, powMonoidHom_apply]
      exact ⟨x, rfl⟩
    · intro a _ b _ h; exact h
    · intro y hy
      simp only [mem_filter, mem_univ, true_and, MonoidHom.mem_range, powHom,
        powMonoidHom_apply] at hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x ^ d, by rw [mem_image]; exact ⟨x, mem_univ _, rfl⟩, rfl⟩
  rw [hbij]
  have hnc := IsCyclic.card_powMonoidHom_range G d
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hnc
  exact hnc

/-- **The clean inverse-Littlewood–Offord level-set count for the imprimitive direction.**
For any threshold `t ≤ gcd (card G) d`, the number of ratio values whose multiplicity (fiber size)
is `≥ t` is **exactly** `card G / gcd (card G) d` — every attained value already has the full
multiplicity `gcd (card G) d ≥ t`.  This is the sharp inverse-LO statement: the high-multiplicity
level set is *all* of the image, of size `card G / gcd(card G,d)`.  (For `t > gcd (card G) d` the
count is `0` — no value can exceed its forced multiplicity.) -/
theorem imprimitive_highmult_levelset_card (d : ℕ) {t : ℕ} (_ht : 1 ≤ t)
    (htle : t ≤ Nat.gcd (Fintype.card G) d) :
    ((univ.image (fun x : G => x ^ d)).filter
        (fun y => t ≤ (univ.filter (fun x : G => x ^ d = y)).card)).card
      = Fintype.card G / Nat.gcd (Fintype.card G) d := by
  classical
  -- every value in the image attains multiplicity exactly `gcd`, hence `≥ t`
  have hfilter : (univ.image (fun x : G => x ^ d)).filter
      (fun y => t ≤ (univ.filter (fun x : G => x ^ d = y)).card)
      = univ.image (fun x : G => x ^ d) := by
    apply Finset.filter_true_of_mem
    intro y hy
    rw [mem_image] at hy
    obtain ⟨x, _, rfl⟩ := hy
    have hmem : x ^ d ∈ Set.range (powHom (G := G) d) := ⟨x, by simp [powHom, powMonoidHom]⟩
    rw [imprimitive_fiber_card d hmem]
    exact htle
  rw [hfilter, imprimitive_image_card]

/-- **Maximal collapse at the half-power (the Gauss-period re-encoding).**  When `d` divides
`card G` (the imprimitive 2-power-tower directions `d = n/2, n/4, …` on `μ_n`), every nonempty
fiber has card exactly `d`, and there are `card G / d` attained values.  At `d = n/2` this is the
maximal multiplicity `n/2` over `2` values (`x^{n/2} = ±1` on `μ_n`): the ratio-census collapses
onto the Gauss period, exactly the BGK object the D3 thread flags. -/
theorem imprimitive_fiber_card_of_dvd {d : ℕ} (hd : d ∣ Fintype.card G)
    {y : G} (hy : y ∈ Set.range (powHom (G := G) d)) :
    (univ.filter (fun x : G => x ^ d = y)).card = d := by
  rw [imprimitive_fiber_card d hy, Nat.gcd_eq_right hd]

end ArkLib.ProximityGap.ImprimitiveRatio

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.ImprimitiveRatio.imprimitive_fiber_card
#print axioms ArkLib.ProximityGap.ImprimitiveRatio.imprimitive_image_card
#print axioms ArkLib.ProximityGap.ImprimitiveRatio.imprimitive_highmult_levelset_card
#print axioms ArkLib.ProximityGap.ImprimitiveRatio.imprimitive_fiber_card_of_dvd
