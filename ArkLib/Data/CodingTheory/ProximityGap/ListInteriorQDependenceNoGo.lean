/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorListCountBridge
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPigeonholeFiber
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorUnconditionalT1

/-!
# Round 6 (Issue #232, ABF26) — the `q`-independence question, and a VERIFIED NO-GO: the
# averaging/pigeonhole method inherently loses a factor of `q`.

The Proximity Prize counterexample needs a **`q`-independent** list lower bound: a list `Λ` with
`|Λ| > ε* · q` where `ε*` is a *fixed* (field-size-independent) constant. Every interior list lower
bound produced in Rounds 1–5 of this development carries a `1/q` factor:

* `Round5Unconditional.exists_interior_list_ge_unconditional`: `C(n,k+1) ≤ q · #(list)`, i.e. the
  list is only `≥ C(n,k+1)/q`.
* `Round4NewtonVietaUpper.max_fiber_interior_ge`: `C(n,k+t) ≤ q · N(k+t, target)` — the heavy
  subset-sum fiber is only `≥ C(n,k+t)/q`.

The **single** `q`-independent list bound in the whole development
(`ListCapacityFieldIndependent.list_card_ge_choose_at_capacity`, recorded elsewhere) gives the
field-independent `C(n,k)` — but **only at the excluded capacity endpoint `δ = 1 − ρ`**, never
strictly inside the gap. Round 6 asks: *can ANY interior lower bound be made `q`-independent?*

## The verdict (a structural NO-GO for the averaging method)

We prove that the `q`-independence the prize needs is **structurally impossible to obtain from the
averaging / pigeonhole method that drives every Round-1..5 interior bound.** The mechanism is the
exact conservation law `∑_{target} N(a, target) = C(n, a)` (`sum_subsetSumCount_eq_choose`,
Round 4): the subset-sum fibers tile the field-independent total `C(n,a)` across the `q = |F|`
targets, so the *average* fiber is exactly `C(n,a)/q`. Two sharp consequences:

1. **`uniform_subsetSumCount_lb_le_choose` — uniformity ⟹ the `1/q` factor.** If a lower bound `f`
   on the subset-sum count holds at *every* target (`∀ target, f ≤ N(a, target)` — the only kind a
   `q`-independent, construction-agnostic argument can give), then `q · f ≤ C(n, a)`: the bound is
   *forced* to be `≤ C(n,a)/q`, i.e. it carries the `1/q`. A uniform bound can never beat the
   average.

2. **`exists_target_subsetSumCount_le_average` — the dual (min-fiber) pigeonhole.** There is
   *always* a target whose fiber is `≤ C(n,a)/q` (`q · N(a, target) ≤ C(n,a)`). So a construction
   that does not get to *choose* the target (any `q`-independent / worst-case-target-blind argument)
   cannot guarantee a large list. The existential heavy-fiber bound `max_fiber_interior_ge` escapes
   this only by *picking* the `q`-dependent heavy target — and even then the guaranteed size is the
   average `C(n,a)/q`, still `q`-dependent.

3. **`qIndependent_count_lb_forces_concentration` — the EXACT escape condition.** A genuinely
   `q`-independent lower bound at a *single chosen* target `target₀`, of constant-fraction size
   `c · N(a, target₀) ≥ C(n, a)` with `c` fixed, is **equivalent** to the subset-sum count
   *concentrating* on `O(1)` targets: that one fiber must capture a `1/c` fraction of the *entire*
   total `∑_{target} N = C(n,a)`, i.e. exceed the average by the factor `q/c`
   (`single_fiber_excess_over_average`). Concentration on `O(1)` targets is a property the
   order-`≤ 4` Newton/Vieta symmetry group (Round 4) provably *cannot* deliver, and it is a
   fundamentally **non-averaging** input — exactly the missing ingredient.

4. **`uniform_interior_list_lb_carries_q` — the no-go lifted to the actual RS list.** Through the
   Round-5 conservation law on the index-fiber family (`sum_indexFamily_card_eq_choose`), any list
   lower bound obtained uniformly across the `q` window-sum targets is itself `≤ C(n,k+1)/q`. So the
   averaging route to the interior RS list **cannot** produce a `q`-independent list either.

## Honest scope

This is a **NO-GO**, not a counterexample and not a closure. It does not prove the prize is true or
false; it sharply explains *why the disproof is hard*: every averaging-based interior list bound in
this development carries an irreducible `1/q`, and removing it is **equivalent** to a subset-sum
concentration statement (`O(1)`-target domination of `C(n,a)`) that the available symmetric-function
structure cannot supply. The positive side — a `q`-independent interior bound — would require the
concentration input, which remains open and is *not* an averaging fact. The lone `q`-independent
bound we have sits at the *excluded* capacity endpoint, consistent with this no-go.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round6QIndependence

open ArkLib.ProximityGap.Round4NewtonVietaUpper

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. Uniformity ⟹ the `1/q` factor.

The single most important structural fact: a lower bound on the subset-sum count that holds at
*every* target — the only kind a construction-agnostic, `q`-independent argument can produce — is
forced to be at most the average `C(n,a)/q`. There is no way around the `1/q` if your bound is
uniform over targets. -/

/-- **Uniformity ⟹ the `1/q` factor (the core no-go).** Suppose `f` is a lower bound on the
subgroup subset-sum count that holds *uniformly* over all targets: `∀ target, f ≤ N(a, target)`.
Then `q · f ≤ C(n, a)`, i.e. `f ≤ C(n,a)/q`. The proof is the conservation law
`∑_{target} N(a, target) = C(n, a)` (`sum_subsetSumCount_eq_choose`) summed against the constant
lower bound: `q · f = ∑_{target} f ≤ ∑_{target} N(a, target) = C(n, a)`.

This is the precise sense in which the averaging method **inherently** loses a factor of `q`: any
bound it can certify at *every* target is capped by the average, which is `q` times smaller than the
field-independent total `C(n,a)`. A `q`-independent list lower bound (what the prize needs) cannot
be a uniform-over-targets bound. -/
theorem uniform_subsetSumCount_lb_le_choose [Fintype F] {G : Finset F} {n : ℕ}
    (hGcard : G.card = n) (a : ℕ) (f : ℕ)
    (huniform : ∀ target : F, f ≤ subsetSumCount G a target) :
    Fintype.card F * f ≤ n.choose a := by
  classical
  have hsum : ∑ target : F, subsetSumCount G a target = n.choose a :=
    sum_subsetSumCount_eq_choose hGcard a
  calc Fintype.card F * f
      = ∑ _target : F, f := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ target : F, subsetSumCount G a target :=
        Finset.sum_le_sum (fun target _ => huniform target)
    _ = n.choose a := hsum

/-! ## 2. The dual (min-fiber) pigeonhole: some target is always at most the average.

The mirror of Round 4's `max_fiber_interior_ge` (some target is `≥` average) is: some target is `≤`
average. So a construction that cannot *choose* the target cannot guarantee a large fiber. -/

/-- **The min-fiber pigeonhole.** There is *always* a target whose subset-sum fiber is at most the
average `C(n,a)/q`: `∃ target, q · N(a, target) ≤ C(n, a)`. (Dual to `max_fiber_interior_ge`.) The
fibers sum to `C(n,a)` over the `q` targets, so the minimum fiber is `≤ C(n,a)/q`.

Consequence for `q`-independence: a list construction whose received word does not *pin* the heavy
window-sum target — any argument blind to which target is heavy — lands on a fiber that may be only
`C(n,a)/q`. The existential heavy-fiber bound `max_fiber_interior_ge` evades this **only** by
selecting the `q`-dependent heavy target; the selection itself is `q`-dependent. -/
theorem exists_target_subsetSumCount_le_average [Fintype F] {G : Finset F} {n : ℕ}
    (hGcard : G.card = n) (a : ℕ) (hq : 0 < Fintype.card F) :
    ∃ target : F, Fintype.card F * subsetSumCount G a target ≤ n.choose a := by
  classical
  have hsum : ∑ target : F, subsetSumCount G a target = n.choose a :=
    sum_subsetSumCount_eq_choose hGcard a
  -- Compare the two constant-vs-fiber sums over `univ`: `∑ (q·N) = q·C(n,a) = ∑ C(n,a)`.
  have hle : ∑ target : F, Fintype.card F * subsetSumCount G a target
      ≤ ∑ _target : F, n.choose a := by
    rw [← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  obtain ⟨target, _, htarget⟩ :=
    Finset.exists_le_of_sum_le (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hq)) hle
  exact ⟨target, htarget⟩

/-! ## 3. The EXACT escape condition: a `q`-independent bound is equivalent to concentration.

A genuinely `q`-independent lower bound `c · N(a, target₀) ≥ C(n,a)` (factor `c` *fixed*, not `q`)
at a single chosen target is, by the conservation law, **equivalent** to that one fiber dominating a
`1/c` fraction of the *entire* total over all targets. That is the concentration statement: it
exceeds the average by the factor `q/c`. The averaging method only knows the average, so it cannot
produce concentration; concentration is a strictly stronger, non-averaging input. -/

/-- **A constant-factor (`q`-independent-shaped) fiber bound IS a concentration statement.** If a
single target `target₀` satisfies `c · N(a, target₀) ≥ C(n, a)` with `c` a fixed constant (the shape
of a `q`-independent lower bound — `c` does not grow with `q`), then that one fiber dominates the
**entire** total subset-sum count up to the factor `c`:

  `c · N(a, target₀)  ≥  ∑_{target} N(a, target)`.

In words: one fiber captures a `1/c` fraction of *all* `C(n,a)` size-`a` subsets. This is precisely
the `O(1)`-target concentration the averaging method cannot see — the average only certifies
`q · N(a, target₀) ≥ C(n,a)` for *some* target, a factor `q` weaker. So a `q`-independent bound is
*equivalent* (here: implies, and is implied by) such concentration. -/
theorem qIndependent_count_lb_forces_concentration [Fintype F] {G : Finset F} {n : ℕ}
    (hGcard : G.card = n) (a c : ℕ) (target₀ : F)
    (hqindep : n.choose a ≤ c * subsetSumCount G a target₀) :
    (∑ target : F, subsetSumCount G a target) ≤ c * subsetSumCount G a target₀ := by
  rw [sum_subsetSumCount_eq_choose hGcard a]
  exact hqindep

/-- **The single fiber exceeds the average by the factor `q/c`.** Quantitatively: a `q`-independent
fiber bound `c · N(a, target₀) ≥ C(n,a)` forces

  `q · N(a, target₀)  ≥  (q/c) · C(n,a)`  i.e.  `c · (q · N(a, target₀)) ≥ q · C(n,a)`,

so the chosen fiber is `q/c` times the average `C(n,a)/q`. For fixed `c` and `q → ∞` this is a
super-average concentration that the conservation law alone (which only pins the average) does not
provide — it is the extra, non-averaging hypothesis a `q`-independent counterexample needs. -/
theorem single_fiber_excess_over_average [Fintype F] {G : Finset F} {n : ℕ}
    (_hGcard : G.card = n) (a c : ℕ) (target₀ : F)
    (hqindep : n.choose a ≤ c * subsetSumCount G a target₀) :
    Fintype.card F * n.choose a
      ≤ c * (Fintype.card F * subsetSumCount G a target₀) := by
  calc Fintype.card F * n.choose a
      ≤ Fintype.card F * (c * subsetSumCount G a target₀) :=
        Nat.mul_le_mul_left _ hqindep
    _ = c * (Fintype.card F * subsetSumCount G a target₀) := by ring

/-! ## 4. The no-go lifted to the actual RS interior list (via the Round-5 index-fiber tiling).

The Round-5 unconditional bound is `C(n,k+1) ≤ q · #(list)`. We show the `1/q` there is the *same*
averaging artifact: any list lower bound holding uniformly across the `q` window-sum index targets
is itself `≤ C(n,k+1)/q`. So the averaging route to the interior RS list cannot be made
`q`-independent either. -/

open ArkLib.CodingTheory.Round5Unconditional in
/-- **Uniform interior-list lower bound ⟹ the `1/q` factor (RS list version).** The Round-5
index-fiber family tiles `C(n,k+1)` across the `q` window-sum targets
(`sum_indexFamily_card_eq_choose`). Hence if `f` lower-bounds the index-fiber size *uniformly* over
all targets (`∀ target, f ≤ |indexFamily D k target|` — the construction-agnostic regime), then
`q · f ≤ C(n,k+1)`. Since the index-fiber injects into the RS interior list
(`interior_list_card_ge_family`, used in `exists_interior_list_ge_unconditional`), the uniform
list lower bound the averaging method can certify is at most `C(n,k+1)/q` — it carries the `1/q`.
The Round-5 `exists_interior_list_ge_unconditional` escapes the *uniform* cap only by picking the
single heavy target (a `q`-dependent choice), and still delivers only the average `C(n,k+1)/q`. -/
theorem uniform_interior_list_lb_carries_q {ι : Type*} [Fintype ι] [Fintype F]
    (D : ι ↪ F) (k : ℕ) (f : ℕ)
    (huniform : ∀ target : F, f ≤ (indexFamily D k target).card) :
    Fintype.card F * f ≤ (Fintype.card ι).choose (k + 1) := by
  classical
  have hsum : ∑ target : F, (indexFamily D k target).card = (Fintype.card ι).choose (k + 1) :=
    sum_indexFamily_card_eq_choose D k
  calc Fintype.card F * f
      = ∑ _target : F, f := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ target : F, (indexFamily D k target).card :=
        Finset.sum_le_sum (fun target _ => huniform target)
    _ = (Fintype.card ι).choose (k + 1) := hsum

/-! ## 5. Non-vacuity: the no-go is about genuine interior counts, and the hypotheses are realized.

The uniformity premise is satisfiable (the trivial uniform bound `f = 0` makes the conclusion
`0 ≤ C(n,a)` a true, non-vacuous instance; and any nonzero uniform `f` is a real constraint). The
min-fiber pigeonhole is non-vacuous whenever `0 < q`. We also record that the no-go bites at the gap
*interior* (`a = k + t`, `t ≥ 1`), not merely at the capacity endpoint. -/

/-- **The min-fiber pigeonhole is non-vacuous, and bites at the gap interior.** At `a = k + t` with
`t ≥ 1` (strictly past the capacity endpoint), there is a target whose interior subset-sum fiber is
at most the average `C(n,k+t)/q`. So even *inside* the gap, a target-blind construction cannot
guarantee a heavy fiber — the no-go is an interior statement, not an endpoint artifact. -/
theorem exists_target_interior_le_average [Fintype F] {G : Finset F} {n : ℕ}
    (hGcard : G.card = n) (k t : ℕ) (ht : 1 ≤ t) (hq : 0 < Fintype.card F) :
    ∃ target : F, Fintype.card F * subsetSumCount G (k + t) target ≤ n.choose (k + t) := by
  have _ : 0 < t := ht
  exact exists_target_subsetSumCount_le_average hGcard (k + t) hq

/-- **The uniform no-go is non-vacuous.** The hypothesis `∀ target, f ≤ N(a,target)` is satisfiable
with `f = 0` (giving the true `0 ≤ C(n,a)`), and the conclusion `q · f ≤ C(n,a)` is a genuine
constraint for any `f ≥ 1`: it pins the maximal *uniform* lower bound to `⌊C(n,a)/q⌋`. We record the
satisfiable instance and that the conclusion forces `f ≤ C(n,a)` (so a uniform bound exceeding the
total is impossible — the averaging cap is real). -/
theorem uniform_no_go_satisfiable [Fintype F] {G : Finset F} {n : ℕ}
    (hGcard : G.card = n) (a : ℕ) (hq : 0 < Fintype.card F) :
    (∀ target : F, (0 : ℕ) ≤ subsetSumCount G a target) ∧
      (∀ f : ℕ, (∀ target : F, f ≤ subsetSumCount G a target) → f ≤ n.choose a) := by
  refine ⟨fun _ => Nat.zero_le _, fun f huniform => ?_⟩
  have h := uniform_subsetSumCount_lb_le_choose hGcard a f huniform
  calc f = 1 * f := (one_mul f).symm
    _ ≤ Fintype.card F * f := Nat.mul_le_mul_right _ hq
    _ ≤ n.choose a := h

/-- **Concrete non-vacuity of the concentration characterization.** A `q`-independent fiber bound of
shape `c · N ≥ C(n,a)` with `c = 4` (the order of the Newton/Vieta symmetry group) would force one
fiber to capture a `1/4` fraction of all `C(n,a)` subsets — concentration far beyond the average
`C(n,a)/q`. We record the implication shape at `c = 4` so the characterization is exhibited on the
exact constant the symmetry group provides. (That the order-`≤ 4` symmetry group *cannot* in fact
deliver this is the Round-4 `max_fiber_ge_total_div_card` no-go; here we pin the equivalence so it
is clear what a `q`-independent bound would have to assume.) -/
theorem concentration_at_symmetry_constant [Fintype F] {G : Finset F} {n : ℕ}
    (hGcard : G.card = n) (a : ℕ) (target₀ : F)
    (hqindep : n.choose a ≤ 4 * subsetSumCount G a target₀) :
    (∑ target : F, subsetSumCount G a target) ≤ 4 * subsetSumCount G a target₀ :=
  qIndependent_count_lb_forces_concentration hGcard a 4 target₀ hqindep

end ArkLib.CodingTheory.Round6QIndependence

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round6QIndependence.uniform_subsetSumCount_lb_le_choose
#print axioms ArkLib.CodingTheory.Round6QIndependence.exists_target_subsetSumCount_le_average
#print axioms ArkLib.CodingTheory.Round6QIndependence.qIndependent_count_lb_forces_concentration
#print axioms ArkLib.CodingTheory.Round6QIndependence.single_fiber_excess_over_average
#print axioms ArkLib.CodingTheory.Round6QIndependence.uniform_interior_list_lb_carries_q
#print axioms ArkLib.CodingTheory.Round6QIndependence.exists_target_interior_le_average
#print axioms ArkLib.CodingTheory.Round6QIndependence.uniform_no_go_satisfiable
#print axioms ArkLib.CodingTheory.Round6QIndependence.concentration_at_symmetry_constant
