/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.PrimeFin

/-!
# Lane A6 — feasibility verdict for the universal single-obstruction (Gate 3) route

## What this file is

The finite-obstruction good-prime selector
(`Frontier.FiniteObstructionGoodPrime.exists_not_mem_bad_of_bad_dvd_obstruction`) clears a
bad-prime set whenever a candidate prime window `P` beats `omega(D) = D.primeFactors.card`, where
`D` is a *single* nonzero integer obstruction whose prime factors cover every bad prime.  For a
*single modeled stack* this is a clean, true, and useful step.

The **universal route ("Gate 3")** would need ONE obstruction integer `D` that dominates **all**
stacks (cosets / Galois orbits) at once.  The only structural way to force every bad prime — across
every stack — to divide one integer is to take the product `D = ∏_i D_i` over the per-stack
obstructions `D_i`.  But `omega(∏_i D_i) = card (⋃_i (D_i).primeFactors)`, and when the stacks
contribute *distinct* primes this is exactly the number of stacks.

This file banks the **negative feasibility verdict** as an axiom-clean Lean lower bound:

* `omega_prod_distinct_primes_eq` : if `q : ι → ℕ` is an injective family of primes indexed by a
  finite stack set `I`, then `omega(∏_{i∈I} q i) = I.card`.  (The obstruction's prime-factor count
  is exactly the number of stacks.)
* `universal_window_must_exceed_stackCount` : consequently the good-prime selector requires a
  candidate prime window with `I.card < P.card`, i.e. the window must beat the **number of stacks**.
* `universal_obstruction_omega_ge_stackCount` : the lower bound `I.card ≤ omega(∏_{i∈I} q i)` even
  when the per-stack obstructions are general nonzero integers, provided each carries a private
  prime (one prime per stack that no other stack's obstruction uses).

### The verdict (read `scripts/probes/universal_obstruction_omega.py`)

In the prize regime the number of stacks is the **coset count** `~ q/n ~ 2^128` (or, on the most
route-favorable orbit model, still grows with `n`).  No Thorner–Zaman / Linnik PNT-in-AP window
supplies a candidate prime window of size `> 2^128`; the largest analytically reachable window is
`|P| ~ n^β` (polynomial), which is `2^120` even at the prize `n = 2^30`.  Hence the universal
single-obstruction route is **INFEASIBLE**: `omega(∏ D_i)` grows with the stack count, while the
clearable window does not.

The *sound* form is the already-banked **local-obstruction** selector
(`bad_filter_card_le_sum_primeFactors_card_of_local_obstructions`), which compares the window with
`∑_i omega(D_i)` — and that sum does **not** collapse to one small obstruction.

## Honesty caveat (OFF-WALL)

This is a route-closing **no-go for a proof *strategy***, not a math theorem about `δ*`.  It does
NOT pin the δ* / BGK / Paley threshold (the recognized-OPEN $1M core), and is necessary-not-
sufficient substrate hygiene: it tells future agents not to invest in the universal-obstruction
gate.  Nothing here closes the prize.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.UniversalObstructionOmegaBudget

open Finset

/-- `omega(n) := n.primeFactors.card`, the number of distinct prime factors. -/
abbrev omega (n : ℕ) : ℕ := n.primeFactors.card

/-- **Distinct-prime obstruction count.**  If each stack `i ∈ I` contributes a *distinct* prime
`q i` (the family is injective on `I` and every value is prime), then the universal obstruction
`D = ∏_{i∈I} q i` has `omega(D) = I.card`.

This is the exact accounting that kills the universal route: bundling one private prime per stack
into a single obstruction makes `omega` equal to the number of stacks. -/
theorem omega_prod_distinct_primes_eq
    {ι : Type} (I : Finset ι) (q : ι → ℕ)
    (hq : ∀ i ∈ I, (q i).Prime)
    (hinj : Set.InjOn q I) :
    omega (∏ i ∈ I, q i) = I.card := by
  classical
  -- Re-index the product over the image set of distinct primes.
  have hmap : (∏ i ∈ I, q i) = ∏ p ∈ I.image q, p := by
    rw [Finset.prod_image]
    intro a ha b hb hab
    exact hinj ha hb hab
  have himg_prime : ∀ p ∈ I.image q, p.Prime := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact hq i hi
  show (∏ i ∈ I, q i).primeFactors.card = I.card
  rw [hmap, Nat.primeFactors_prod himg_prime]
  exact Finset.card_image_of_injOn hinj

/-- **Universal-window lower requirement.**  Using one private prime per stack and bundling them
into the single universal obstruction `D = ∏_{i∈I} q i`, the good-prime selector requires the
candidate prime window `P` to strictly exceed the **number of stacks** `I.card`.

In other words: `omega(D)` is not some small fixed constant — it is the stack count itself.  This is
the Lean witness for the NEGATIVE feasibility verdict. -/
theorem universal_window_must_exceed_stackCount
    {ι : Type} (I : Finset ι) (q : ι → ℕ) (P : Finset ℕ)
    (hq : ∀ i ∈ I, (q i).Prime)
    (hinj : Set.InjOn q I)
    (hclears : omega (∏ i ∈ I, q i) < P.card) :
    I.card < P.card := by
  rwa [omega_prod_distinct_primes_eq I q hq hinj] at hclears

/-- **General lower bound: one private prime per stack ⇒ `omega(∏ Dᵢ) ≥ #stacks`.**

Even if the per-stack obstructions `D i` are arbitrary nonzero integers (not single primes), as
long as each stack carries a *private* prime `q i` — a prime dividing `D i` that no other stack's
prime equals — the universal obstruction's prime-factor count is at least the number of stacks.

This is the robust form of the no-go: you cannot escape the growth by making `D i` composite or
shared; one private prime per stack already forces `omega` up to `#stacks`. -/
theorem universal_obstruction_omega_ge_stackCount
    {ι : Type} (I : Finset ι) (D : ι → ℕ) (q : ι → ℕ)
    (hD : ∀ i ∈ I, D i ≠ 0)
    (hqprime : ∀ i ∈ I, (q i).Prime)
    (hqdvd : ∀ i ∈ I, q i ∣ D i)
    (hinj : Set.InjOn q I) :
    I.card ≤ omega (∏ i ∈ I, D i) := by
  classical
  -- The product of all `D i` is nonzero.
  have hProdNe : (∏ i ∈ I, D i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact hD
  -- Each private prime `q i` is a prime factor of the whole product.
  have hmem : ∀ i ∈ I, q i ∈ (∏ j ∈ I, D j).primeFactors := by
    intro i hi
    refine Nat.mem_primeFactors.mpr ⟨hqprime i hi, ?_, hProdNe⟩
    exact (hqdvd i hi).trans (Finset.dvd_prod_of_mem D hi)
  -- The image of `q` over `I` injects into the prime-factor set; hence the cardinality bound.
  have hsub : I.image q ⊆ (∏ j ∈ I, D j).primeFactors := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    exact hmem i hi
  calc I.card = (I.image q).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (∏ j ∈ I, D j).primeFactors.card := Finset.card_le_card hsub

/-- **Feasibility verdict, stated.**  Combining the lower bound with the selector requirement: if
the universal route is to clear *all* stacks at once with a single obstruction `∏ Dᵢ`, the candidate
prime window must strictly exceed the number of stacks (each carrying a private prime).

Since the stack count in the prize regime is the coset count `~ q/n ~ 2^128`, and no PNT-in-AP
window reaches that size, the hypothesis `I.card < P.card` is unsatisfiable by any
Thorner–Zaman/Linnik window — formalizing the route as INFEASIBLE. -/
theorem universal_route_needs_window_above_stackCount
    {ι : Type} (I : Finset ι) (D : ι → ℕ) (q : ι → ℕ) (P : Finset ℕ)
    (hD : ∀ i ∈ I, D i ≠ 0)
    (hqprime : ∀ i ∈ I, (q i).Prime)
    (hqdvd : ∀ i ∈ I, q i ∣ D i)
    (hinj : Set.InjOn q I)
    (hclears : omega (∏ i ∈ I, D i) < P.card) :
    I.card < P.card :=
  lt_of_le_of_lt (universal_obstruction_omega_ge_stackCount I D q hD hqprime hqdvd hinj) hclears

/-! ## Axiom audit -/
#print axioms omega_prod_distinct_primes_eq
#print axioms universal_window_must_exceed_stackCount
#print axioms universal_obstruction_omega_ge_stackCount
#print axioms universal_route_needs_window_above_stackCount

end ArkLib.ProximityGap.Frontier.UniversalObstructionOmegaBudget
