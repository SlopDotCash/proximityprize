/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import ArkLib.Data.CodingTheory.ProximityGap.MultiplicativeRigidityZMod

/-!
# Conjecture 7.1 residual: the binomial strata **bad-scalar support count** (#444, #389)

## Context (the missing companion to the gcd dichotomy + window total)
Two facts about the thin-subgroup binomial-direction incidence are already in tree:
* `MultiplicativeRigidityZMod.pow_eq_card_eq_zero_or_gcd` — the **per-scalar dichotomy**: in a
  cyclic `G` of order `n`, `#{x : x^d = c}` is `0` or *exactly* `gcd(d, n)`.
* `C71BinomialWindowAverage.windowSum_…_eq_card` — the **window TOTAL**: `Σ_c #{x : x^d = c} = n`.

The dichotomy + total pin the *sum* and the *per-scalar value*, but NOT the **support size**: how
many dilation scalars `c` actually carry an incidence. This file supplies it: the number of `c` with
a *nonempty* fiber (equivalently, the number of distinct `d`-th powers `= #(image of x ↦ x^d)`) is

> `#{c : ∃ x ∈ μ_n, x^d = c} = n / gcd(d, n)`.

This is the **bad-scalar count** the soundness side wants: across the dilation window, the binomial
strata is bad at exactly `n/gcd(d,n)` scalars, each with incidence exactly `gcd(d,n)`, and
`(n/gcd) · gcd = n` recovers the window total. For `d` coprime to `n` (the primitive directions,
`~half` for `n = 2^a`) this is `n` bad scalars of incidence `1` each; for `gcd(d,n) ~ n/2` it is
`~2` bad scalars of incidence `~n/2` each — the *concentration* the per-direction worst-case bound
sees only one side of.

Probe `scripts/probes/probe_binomial_window_concentration.py` (EXACT, thin `μ_n` `n=2^a` (`a=2,3,4`),
`p ≡ 1 mod n`, `(p-1)/n ≥ 2`, multi-prime incl `p > n^3` + Fermat `257`, NEVER `n=q-1`): incidence
`∈ {0, gcd(d,n)}` and the support size `= n/gcd(d,n)` in **100%** of rows.

## Theorems
* `card_image_pow_eq` (HEADLINE, abstract) : in a finite cyclic `G` of order `n`, the number of
  distinct `d`-th powers — `#(univ.image (· ^ d))` — equals `n / gcd(d, n)`. (The bad-scalar /
  support count; via `IsCyclic.card_powMonoidHom_range`.)
* `card_distinct_pow_mul_gcd` : `(#image) · gcd(d,n) = n` exactly — support × per-scalar value =
  window total, recombining the dichotomy and the range-card.

These EXTEND the rigidity dichotomy (`pow_eq_card_eq_zero_or_gcd`) with the **support cardinality**;
pure cyclic-group structure, no character-sum / BGK content. NON-MOMENT, field-universal,
EXTEND-proven. The transport to the `F`-valued strata and the reduction of this concentration to a
soundness bound remain OPEN and are NOT claimed here.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.C71BinomialBadScalarCount

variable {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] [DecidableEq G]

/-- **The bad-scalar / support count (HEADLINE).** In a finite cyclic group `G` of order
`n = Fintype.card G`, the number of distinct `d`-th powers — i.e. the number of targets `c` carrying
a nonempty fiber `{x : x^d = c}` — is exactly `n / gcd(d, n)`. This is `#(image (· ^ d))`, the size
of the dilation-window support over which the binomial strata is bad. -/
theorem card_image_pow_eq (d : ℕ) :
    (univ.image (fun x : G => x ^ d)).card = Fintype.card G / Nat.gcd d (Fintype.card G) := by
  classical
  -- (univ.image f).card = Nat.card (Set.range f), and Set.range (powMonoidHom d) = ↑range
  have himg : (univ.image (fun x : G => x ^ d)).card
      = Nat.card (Set.range (fun x : G => x ^ d)) := by
    rw [← Set.toFinset_range, Set.toFinset_card, Nat.card_eq_fintype_card]
  have hrng : Set.range (fun x : G => x ^ d) = ((powMonoidHom d : G →* G).range : Set G) := by
    ext c; simp [MonoidHom.mem_range, powMonoidHom_apply]
  rw [himg, hrng]
  -- Nat.card ↑(range subgroup) = Nat.card ↥(range subgroup), then the cyclic range-card lemma
  have hbridge : Nat.card ((powMonoidHom d : G →* G).range : Set G)
      = Nat.card (powMonoidHom d : G →* G).range := by
    rw [← SetLike.coe_sort_coe]
  rw [hbridge, IsCyclic.card_powMonoidHom_range (G := G) d, Nat.card_eq_fintype_card, Nat.gcd_comm]

/-- **Primitive/coprime directions hit every scalar.** If the exponent gap `d` is coprime to the
cyclic-window size `n`, the power map `x ↦ x^d` is onto the whole dilation window: every scalar is
bad, and each bad scalar has incidence `1` by the gcd dichotomy. This is the support-side companion
to the coprime one-root incidence corollaries. -/
theorem card_image_pow_eq_card_of_coprime (d : ℕ)
    (hcop : Nat.Coprime d (Fintype.card G)) :
    (univ.image (fun x : G => x ^ d)).card = Fintype.card G := by
  rw [card_image_pow_eq (G := G) d, hcop.gcd_eq_one, Nat.div_one]

/-- **The zero-gap direction has one support scalar.** For `d = 0`, the power map is constant, so
only one dilation scalar carries the whole incidence mass. This is the opposite concentration edge
from the coprime-support theorem. -/
theorem card_image_pow_zero_eq_one :
    (univ.image (fun x : G => x ^ (0 : ℕ))).card = 1 := by
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  rw [card_image_pow_eq (G := G) 0, Nat.gcd_zero_left, Nat.div_self hpos]

/-- **Full-period gaps have one support scalar.** If the exponent gap is divisible by the cyclic
window size `n`, the power map is constant on the window (`x^d = 1` for all `x`), so exactly one
scalar carries the incidence mass. This extends the `d = 0` edge to every wrapped/divisible
binomial direction. -/
theorem card_image_pow_eq_one_of_card_dvd (d : ℕ)
    (hdvd : Fintype.card G ∣ d) :
    (univ.image (fun x : G => x ^ d)).card = 1 := by
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  rw [card_image_pow_eq (G := G) d, Nat.gcd_eq_right hdvd, Nat.div_self hpos]

/-- **Support × per-scalar value = window total.** The support count `n / gcd(d,n)` times the
per-scalar incidence `gcd(d,n)` (the nontrivial branch of the dichotomy) is exactly `n`. This
recombines `card_image_pow_eq` and the rigidity dichotomy into the window total `Σ_c fiber = n`,
exhibiting it as `(#bad scalars) · (incidence each)`. -/
theorem card_distinct_pow_mul_gcd (d : ℕ) :
    (univ.image (fun x : G => x ^ d)).card * Nat.gcd d (Fintype.card G) = Fintype.card G := by
  rw [card_image_pow_eq (G := G) d, Nat.div_mul_cancel]
  exact Nat.gcd_dvd_right d (Fintype.card G)

/-- **Exact divisor-window support count.** If the cyclic window has size `m*k`, then the
`k`-th power map has exactly `m` support scalars.  Equivalently, a direction whose exponent gap is
a divisor `k` of the window size concentrates the binomial-window support by precisely the quotient
`m = n/k`.  This is the caller-facing quotient form of the C71 support count. -/
theorem card_image_pow_divisor_window_eq (m k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card G = m * k) :
    (univ.image (fun x : G => x ^ k)).card = m := by
  rw [card_image_pow_eq (G := G) k, hcard]
  have hgcd : Nat.gcd k (m * k) = k := by
    exact Nat.gcd_eq_left ⟨m, by rw [mul_comm]⟩
  rw [hgcd, Nat.mul_div_left _ hk]

/-- **Half-period gaps have exactly two support scalars.** If the cyclic window has size `2k`, the
half-period power map `x ↦ x^k` concentrates the binomial-window support onto exactly two scalars,
each with fiber size `k` by the gcd dichotomy. This is the explicit cliff-at-`n/2` calibration for
the C71 binomial support count, not a CORE or capacity claim. -/
theorem card_image_pow_half_period_eq_two (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card G = 2 * k) :
    (univ.image (fun x : G => x ^ k)).card = 2 := by
  exact card_image_pow_divisor_window_eq (G := G) 2 k hk hcard

end ArkLib.ProximityGap.C71BinomialBadScalarCount

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.C71BinomialBadScalarCount.card_image_pow_eq
#print axioms ArkLib.ProximityGap.C71BinomialBadScalarCount.card_image_pow_eq_card_of_coprime
#print axioms ArkLib.ProximityGap.C71BinomialBadScalarCount.card_image_pow_zero_eq_one
#print axioms ArkLib.ProximityGap.C71BinomialBadScalarCount.card_image_pow_eq_one_of_card_dvd
#print axioms ArkLib.ProximityGap.C71BinomialBadScalarCount.card_distinct_pow_mul_gcd
#print axioms ArkLib.ProximityGap.C71BinomialBadScalarCount.card_image_pow_divisor_window_eq
#print axioms ArkLib.ProximityGap.C71BinomialBadScalarCount.card_image_pow_half_period_eq_two
