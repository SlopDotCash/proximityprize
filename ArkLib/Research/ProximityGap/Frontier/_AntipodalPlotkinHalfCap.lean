/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat

/-!
# Per-value antipode-freeness of odd agreement polynomials (half-cap on a single value) (#444 / #407)

> **DOCSTRING CORRECTED 2026-06-16 (audit `deltastar-444-audit-corrections-2026-06-16.md` §A0/§C/§IX).**
> The original headline -- "the antipodal/odd far-line route **caps at delta* >= 1/2**, lies strictly
> below the prize floor, and **isolates** the hard residual to asymmetric far-line words" -- was
> **RETRACTED**. That reading conflated two different objects. What is *actually true and proven below*
> is the strictly weaker, sound combinatorial fact stated next; the downstream "delta* cap / residual
> isolation" inference does NOT follow and is removed. The theorems themselves are correct and
> axiom-clean (they were never the bug -- only the docstring's interpretation was). See "What this does
> NOT prove" below.

## What IS proven (the sound fact: a single-value half-cap)

`_AntipodalAgreementScope` proved *when* the off-BGK antipodal tower applies: precisely to **even or
odd** agreement polynomials (whose root set is negation-closed). This file proves a **per-value
antipode-freeness ceiling** for the **odd** branch: for a fixed *nonzero* value `c`, the set of points
of a negation-closed `G` where an odd `P` equals `c` has cardinality `<= |G|/2`.

### Mechanism (char != 2)

An **odd** agreement polynomial `P` (`P(-X) = -P`, equivalently `P.eval (-z) = - P.eval z`) cannot
hit a fixed nonzero value `c` at both `z` and `-z`: if `P z = c` then `P (-z) = -c`, and `-c != c`
because `c != 0` and `2 != 0`. So the **single-value** agreement set `A_c = {z in G : P z = c}` is
**antipode-free**: it contains at most one of each antipodal pair `{z, -z}`. On a negation-closed `G`
carrying the fixed-point-free involution `z |-> -z`, an antipode-free subset has cardinality
`<= G.card / 2`. Hence `#A_c <= |G|/2`. (This is a Plotkin-type *single-value* half-cap; `agreeSet`,
`agreeSet_card_le_half`.)

Probe `scripts/probes/probe_antipodal_plotkin_cap.py` (PROPER thin mu_n, p >> n^3, p == 1 mod n, two
structured primes per n, never n = q-1, n = 8..64): **0 paired-violations**, single-value
multiplicity always `<= n/2` (columns: `odd_maxAgree(c!=0) = 2` and `signHalf <= n/2`). This matches
`agreeSet_card_le_half` exactly. The `rho = 1/4` worst word `x^a + x^b` (a, b both odd) is odd
(`AntipodalAgreementScope.twoMonomial_odd_of_both_odd`), so the single-value cap applies to it.

## What this does NOT prove (the retracted over-claim, with the CORRECT values)

The original docstring leapt from "`#A_c <= |G|/2` per single value `c`" to "the antipodal far-line
**route** caps at `delta* >= 1/2` and isolates the hard residual to asymmetric words." **Neither
follows**, for two distinct reasons, both established in the audit:

1. **`#A_c <= |G|/2` is a cap on a SINGLE codeword value, not the far-line `delta*`.** The far-line
   `delta*` is the *binding incidence* taken over all far directions / all attainable values, governed
   by the distinct-gamma union count -- a different object. Its exact value (audit §A0, full-direction
   `orbcount`; in-tree pin `DeltaStarSecondPin...`/`FarCosetExplosion`; probe
   `probe_plotkin_farline_johnson.py`, exact rational, n=8..2048) is the **Johnson-locked PROXY**
   > `delta*_farline = 1/2 + (1/(2 rho) - 1)/n`, and at `rho = 1/4` this is **`1/2 + 1/n -> 1/2`**:
   `n=16 -> 9/16`, `n=32 -> 17/32`, `n=64 -> 33/64`, ... -> `1/2` from ABOVE (with a small-`n`
   anomaly `n=8 -> 3/8 < 1/2`). So the far-line route does NOT sit at a fixed `>= 1/2` cap below the
   floor; it is a *proxy that tends to `1/2`* (`delta*_MCA <= delta*_farline -> 1/2`).

2. **The proxy does NOT isolate a residual.** Because `delta*_farline -> 1/2` for *all* branches
   (`m* = n/4 - 1` is LINEAR, `capacity - delta* = m*/n -> 1/4`), the even/asymmetric branches give the
   SAME `-> 1/2` proxy; capping the odd single-value multiplicity isolates nothing. The true
   beyond-Johnson worst-case MCA floor (`delta*_MCA >= Johnson`, the prize) is the **separate, harder
   BCHKS/BGK object** that the far-line proxy never reaches. There is no in-tree evidence that the
   worst-case MCA `delta*` climbs to capacity, and none that the odd half-cap brackets the open core.

## Honest scope

Char-free finite combinatorics over a field of char != 2; **field-universal**. The proven content is
exactly the per-value half-cap `agreeSet_card_le_half` (and its building blocks) -- a correct,
axiom-clean structural fact about odd polynomials. It is NOT a `delta*` cap, NOT a Plotkin ceiling on
the route, and does NOT isolate the prize residual. The prize core `M(mu_n) <= C sqrt(n log(p/n))`
(equivalently BCHKS 1.12, equivalently `delta*_MCA` in the window interior) stays **OPEN** and is
untouched by this file. (#407, #444.)
-/

open Polynomial

namespace ProximityGap.Frontier.AntipodalPlotkinHalfCap

open scoped Classical

variable {F : Type*} [Field F]

/-- **Odd polynomials negate their values** (the working hypothesis, matching
`_AntipodalAgreementScope.eval_neg_eq_neg_of_odd`): `P(-z) = -P(z)`. -/
def IsOddOn (P : F[X]) : Prop := ∀ z : F, P.eval (-z) = - P.eval z

/-- An odd polynomial cannot hit a **nonzero** value `c` at both `z` and `-z` (char != 2). -/
theorem not_both_of_odd {P : F[X]} (hodd : IsOddOn P) {c : F} (hc : c ≠ 0)
    (htwo : (2 : F) ≠ 0) {z : F} (hz : P.eval z = c) : P.eval (-z) ≠ c := by
  rw [hodd z, hz]
  intro h
  -- -c = c  =>  2 c = 0  =>  c = 0 (char != 2), contradiction
  apply hc
  have h2c : c + c = 0 := by
    have hcc : -c + c = c + c := by rw [h]
    rw [neg_add_cancel] at hcc
    exact hcc.symm
  have hmul : (2 : F) * c = 0 := by rw [two_mul]; exact h2c
  rcases mul_eq_zero.mp hmul with h2 | hc0
  · exact absurd h2 htwo
  · exact hc0

/-- The **agreement set** of `P` at value `c` over a negation-closed evaluation set `G`. -/
noncomputable def agreeSet (P : F[X]) (G : Finset F) (c : F) : Finset F :=
  G.filter (fun z => P.eval z = c)

/-- **Antipode-freeness of the agreement set** (char != 2): for a nonzero target `c` and an odd `P`,
if `z` is in the agreement set then `-z` is not. This is the structural core of the half-cap. -/
theorem agreeSet_antipode_free {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) {z : F} (hz : z ∈ agreeSet P G c) :
    (-z) ∉ agreeSet P G c := by
  simp only [agreeSet, Finset.mem_filter] at hz ⊢
  rintro ⟨_, hroot⟩
  exact not_both_of_odd hodd hc htwo hz.2 hroot

/-- The negation map is a **fixed-point-free involution** on a field of char != 2: `-z != z` for any
`z` such that ... ` -z = z` forces `z = 0`. We package the disjointness needed for the half-cap:
the agreement set and its pointwise negation are disjoint. -/
theorem agreeSet_disjoint_neg {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) :
    Disjoint (agreeSet P G c) ((agreeSet P G c).image (fun z => -z)) := by
  rw [Finset.disjoint_left]
  intro a ha hain
  rw [Finset.mem_image] at hain
  obtain ⟨b, hb, hba⟩ := hain
  -- a = -b, and both a, b in the agreement set; but -b not in it (antipode-free on b)
  have hnb : (-b) ∉ agreeSet P G c := agreeSet_antipode_free hodd hc htwo hb
  rw [hba] at hnb
  exact hnb ha

/-- **Plotkin half-cap (Finset form).** For an odd `P`, a nonzero target `c`, and char != 2, the
agreement set of `P` at `c` over `G` injects into a set disjoint from its own negation-image of
equal size, so `2 * #agreeSet <= #(agreeSet) + #(neg-image)`. We state the
clean consequence: `2 * (agreeSet P G c).card <= (G ∪ G.image Neg.neg).card`. When `G` is
negation-closed this is `<= G.card`, giving the half-cap. -/
theorem two_mul_agreeSet_card_le {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) :
    2 * (agreeSet P G c).card ≤ (G ∪ G.image (fun z => -z)).card := by
  set A := agreeSet P G c with hA
  have hneg_card : (A.image (fun z => -z)).card = A.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    simpa using hxy
  have hdisj := agreeSet_disjoint_neg hodd hc htwo (P := P) (G := G) (c := c)
  have hunion : (A ∪ A.image (fun z => -z)).card = A.card + A.card := by
    rw [Finset.card_union_of_disjoint hdisj, hneg_card]
  -- A ⊆ G and A.image Neg ⊆ G.image Neg, so the union ⊆ G ∪ G.image Neg
  have hAG : A ⊆ G := by
    intro x hx
    simp only [hA, agreeSet, Finset.mem_filter] at hx
    exact hx.1
  have hsub : A ∪ A.image (fun z => -z) ⊆ G ∪ G.image (fun z => -z) := by
    apply Finset.union_subset_union hAG
    exact Finset.image_subset_image hAG
  calc 2 * A.card = A.card + A.card := by ring
    _ = (A ∪ A.image (fun z => -z)).card := by rw [hunion]
    _ ≤ (G ∪ G.image (fun z => -z)).card := Finset.card_le_card hsub

/-- **Single-value half-cap on a negation-closed `G`.** If `G` is closed under negation
(`g ∈ G ⟹ -g ∈ G`), then `G.image Neg.neg ⊆ G`, so `G ∪ G.image Neg = G`, and the cap reads
`2 * #agreeSet <= #G`: the agreement of an odd `P` with any **single** nonzero value `c` is at most
half the subgroup. (Per-value antipode-freeness; NOT a `delta*` cap -- see file header §"What this
does NOT prove": the far-line `delta*` is the Johnson-locked proxy `1/2 + 1/n -> 1/2`, a different
object.) -/
theorem two_mul_agreeSet_card_le_of_neg_closed {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) (hG : ∀ g ∈ G, -g ∈ G) :
    2 * (agreeSet P G c).card ≤ G.card := by
  have himg : G.image (fun z => -z) ⊆ G := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨g, hg, hgx⟩ := hx
    rw [← hgx]; exact hG g hg
  have hunion : G ∪ G.image (fun z => -z) = G := Finset.union_eq_left.mpr himg
  have := two_mul_agreeSet_card_le hodd hc htwo (P := P) (G := G) (c := c)
  rwa [hunion] at this

/-- **The clean single-value half-cap.** On a negation-closed `G`, an odd polynomial `P` agrees with
any single nonzero value `c` on at most `#G / 2` points. This is the sound combinatorial content of
the file. ⚠️ It is NOT a `delta*` cap and does NOT isolate a prize residual: the far-line `delta*` is
the Johnson-locked proxy `delta*_farline = 1/2 + (1/(2ρ)-1)/n -> 1/2` (at ρ=1/4: `1/2 + 1/n`,
n=16→9/16, n=32→17/32, ...), a distinct object that tends to `1/2` for ALL branches; the true MCA
floor (`delta*_MCA >= Johnson`, the prize) is the separate, harder BCHKS/BGK object. See the file
header §"What this does NOT prove". -/
theorem agreeSet_card_le_half {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) (hG : ∀ g ∈ G, -g ∈ G) :
    (agreeSet P G c).card ≤ G.card / 2 := by
  have h := two_mul_agreeSet_card_le_of_neg_closed hodd hc htwo hG (P := P) (c := c)
  omega

end ProximityGap.Frontier.AntipodalPlotkinHalfCap

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AntipodalPlotkinHalfCap.not_both_of_odd
#print axioms ProximityGap.Frontier.AntipodalPlotkinHalfCap.two_mul_agreeSet_card_le_of_neg_closed
#print axioms ProximityGap.Frontier.AntipodalPlotkinHalfCap.agreeSet_card_le_half
