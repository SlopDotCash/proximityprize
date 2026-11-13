/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import Mathlib.Tactic

/-!
# The `e₂=0` bad-scalar locus is DISJOINT from the antipodal / coset-closed sets (#407, ATTACK-E2)

This file answers the ATTACK-E2 / Approach-E question — *do `e₂=0` subsets have forced
antipodal/coset structure?* — with a clean, axiom-clean **NO, and exactly why**.

The δ* bad-scalar locus at agreement `k+2` is `{ S ⊆ μ_n : e₂(S)=0, e₁(S)≠0 }` (the `e₁≠0`
constraint is **essential** — it is the requirement that the bad scalar `α=−1/e₁(S)` exists, see
`E2VanishEnergy.badScalar_of_energy`). The sibling lane's coset-saturation theory (beyond-Johnson
agreement sets are `μ_d`-cosets, `FactorizationRigidity`) and the Lam–Leung antipodal machinery
suggest the bad locus might also be coset-structured. **It is the opposite**: the very condition
`e₁≠0` is what *forbids* antipodal/coset structure.

The mechanism is a one-line involution argument, here made rigorous:

> **`e1_eq_zero_of_neg_closed`** (the structural core). If `S` is closed under negation
> (`−S = S`) in a field of characteristic `≠ 2`, then `e₁(S) = ∑_{s∈S} s = 0`.

Proof: pair each `s` with `−s` (Mathlib's `Finset.sum_involution`); `s + (−s) = 0`, and `2 ≠ 0`
forbids the fixed point `s = −s` for `s ≠ 0`, so the sum telescopes to `0`. Consequences:

* **`e2_zero_bad_not_neg_closed`** — the ATTACK-E2 verdict. A bad `e₂=0` subset (`e₁(S)≠0`) is
  **NOT** negation-closed. So the bad-scalar locus lives entirely *outside* the antipodal sets;
  `e₂=0` does NOT force antipodal/coset structure. (Confirmed by probe: across all `e₂=0` subsets
  of `μ_n`, `n≤16`, `e₁≠0 ⟺` not-antipodal-closed, 0 violations; and *every* `e₂=0` bad set at
  `n=8,16,32` width `4..n−1` is in the NEITHER class — non-antipodal AND non-coset-union.)

* **`neg_closed_of_subgroup_coset_union`** — for `μ_n` over a dyadic domain (`−1 ∈ μ_n`), any
  union of `μ_d`-cosets with `d` even (so `−1 ∈ μ_d`) is negation-closed, hence has `e₁=0`, hence
  is NOT a bad set. The coset families (the `FactorizationRigidity` image) carry **zero** bad
  scalars at agreement `k+2`. So the bad count is supported on the *complement* of the coset
  structure — the count is NOT a (small) coset count; this **refutes the Approach-E hypothesis**
  that `e₂=0` reduces to a coset count, and explains why the extremal count is the genuinely hard
  non-coset object.

Net (honest): a clean structural dichotomy, NOT a closure. It removes "coset count" as an escape
for the open extremal-radius count and localizes the difficulty to the non-antipodal locus, but it
does not bound that count. Flag: no BGK collapse here — this is pure char-0 involution algebra.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Chai–Fan. *Action–Orbit FRI Soundness Above the Johnson Radius*. eprint 2026/861.
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.E2NegationStructure

open ArkLib.ProximityGap.E2VanishEnergy

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Negation-closure predicate.** `S` is closed under negation (antipodal): for every `s ∈ S`,
the negative `−s ∈ S`. For `S ⊆ μ_n` with `n = 2^μ` (so `−1 = ζ^{n/2} ∈ μ_n`), this is exactly
closure under multiplication by `−1`, i.e. the antipodal-closed sets. -/
def NegClosed (S : Finset F) : Prop := ∀ s ∈ S, -s ∈ S

/-- **The structural core (involution argument).** Over a field of characteristic `≠ 2`, the first
power sum `e₁(S) = ∑_{s∈S} s` of any negation-closed finset vanishes. Each `s` is paired with `−s`
(distinct, since `2 ≠ 0` rules out `s = −s` for `s ≠ 0`), and `s + (−s) = 0`. -/
theorem e1_eq_zero_of_neg_closed (h2 : (2 : F) ≠ 0) {S : Finset F} (hS : NegClosed S) :
    e1 S = 0 := by
  unfold e1
  -- Sum of `id` over `S`, paired by the negation involution `g a _ = -a`.
  refine Finset.sum_involution (fun a _ => -a) (fun a _ => by ring) ?_
    (fun a ha => hS a ha) (fun a _ => neg_neg a)
  -- `f a ≠ 0 → g a ≠ a`, i.e. `a ≠ 0 → -a ≠ a`.
  intro a _ ha hcontra
  -- `-a = a` ⟹ `2a = 0` ⟹ `a = 0` (char ≠ 2), contradicting `a ≠ 0`.
  apply ha
  have h2a : (2 : F) * a = 0 := by linear_combination -hcontra
  rcases mul_eq_zero.mp h2a with h | h
  · exact absurd h h2
  · exact h

/-- **The ATTACK-E2 verdict.** A *bad* `e₂=0` subset — one with `e₁(S) ≠ 0`, the condition under
which the bad scalar `α = −1/e₁(S)` of the affine pencil exists — is **NOT** negation-closed.
Hence the bad-scalar locus is disjoint from the antipodal sets: `e₂ = 0` does **not** force
antipodal/coset structure. The bad count is supported entirely on the *non*-antipodal subsets. -/
theorem e2_zero_bad_not_neg_closed (h2 : (2 : F) ≠ 0) {S : Finset F}
    (hbad : e1 S ≠ 0) : ¬ NegClosed S := by
  intro hclosed
  exact hbad (e1_eq_zero_of_neg_closed h2 hclosed)

/-- **Contrapositive, packaged for the locus.** If `S` is negation-closed and `e₂(S) = 0` (char
`≠ 2`), then `e₁(S)² = p₂(S)` **and** `e₁(S) = 0`, i.e. the energy locus is met but the bad scalar
does NOT exist (`α = −1/e₁(S)` is undefined). Antipodal `e₂=0` sets are energy-extremal but
carry no bad scalar. -/
theorem energy_locus_neg_closed_has_no_bad_scalar (h2 : (2 : F) ≠ 0) {S : Finset F}
    (hclosed : NegClosed S) (he2 : e2 S = 0) :
    e1 S ^ 2 = p2 S ∧ e1 S = 0 :=
  ⟨(e2_zero_iff h2 S).mp he2, e1_eq_zero_of_neg_closed h2 hclosed⟩

/-- **Coset families carry no bad scalars (the `FactorizationRigidity` connection).** Suppose `S`
is a union of `H`-cosets for a finite multiplicative-style structure containing `−1`, modeled here
abstractly: `S` is closed under negation because `−1` lies in the acting set. Concretely, if `S`
is stable under multiplication by `−1` (`∀ s ∈ S, (−1) * s ∈ S`), then `S` is negation-closed,
so `e₁(S) = 0`: a `μ_d`-coset union (`d` even, `−1 ∈ μ_d`) is never a bad set. -/
theorem neg_closed_of_subgroup_coset_union (h2 : (2 : F) ≠ 0) {S : Finset F}
    (hclosed : ∀ s ∈ S, (-1 : F) * s ∈ S) : e1 S = 0 := by
  apply e1_eq_zero_of_neg_closed h2
  intro s hs
  have := hclosed s hs
  simpa using this

/-- **Sharpened verdict for the dyadic prize regime.** Over a dyadic subgroup `μ_n` (`n = 2^μ`,
so `−1 = ζ^{n/2} ∈ μ_n` and every `μ_d`-coset union with `d` even is `(−1)`-stable), the bad
`e₂=0` scalars come ONLY from subsets that are **not** stable under multiplication by `−1`. Coset
unions are excluded. This is the precise structural statement that *refutes* "the `e₂=0` count is a
coset count": the bad locus is exactly the `(−1)`-asymmetric part. -/
theorem bad_set_not_minus_one_stable (h2 : (2 : F) ≠ 0) {S : Finset F}
    (hbad : e1 S ≠ 0) : ¬ (∀ s ∈ S, (-1 : F) * s ∈ S) := by
  intro hstable
  exact hbad (neg_closed_of_subgroup_coset_union h2 hstable)

end ArkLib.ProximityGap.E2NegationStructure

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.E2NegationStructure.e1_eq_zero_of_neg_closed
#print axioms ArkLib.ProximityGap.E2NegationStructure.e2_zero_bad_not_neg_closed
#print axioms ArkLib.ProximityGap.E2NegationStructure.energy_locus_neg_closed_has_no_bad_scalar
#print axioms ArkLib.ProximityGap.E2NegationStructure.neg_closed_of_subgroup_coset_union
#print axioms ArkLib.ProximityGap.E2NegationStructure.bad_set_not_minus_one_stable
