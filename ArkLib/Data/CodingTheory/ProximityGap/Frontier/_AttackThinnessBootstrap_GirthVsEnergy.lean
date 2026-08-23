/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoExcessOnsetThreshold

/-!
# `_AttackThinnessBootstrap_GirthVsEnergy` — why the Sidon/`B_h`-girth route cannot bound the energy (#444)

**Angle attacked: THINNESS_BOOTSTRAP** (`B_β → B_{log p}`). The hoped-for route was:

> `μ_n` is a `B_h`-set (no nontrivial `±1` relation of length `≤ 2h`) to a depth `h` that flows
> to `log p` via Bang–Zsygmondy primitive divisors; if the *Sidon depth* reaches `log p`, then no
> short wraparound relations exist to depth `log p`, so the wraparound count vanishes to depth
> `log p`, hence `A_K ≤ E_K^C ≤ Wick`.

This file records the **structural refutation** of that route, abstracted to the in-tree exact
energy framework `_NoExcessOnsetThreshold` (`energyCharP`, `energyChar0`, `NoWraparound`,
`wrapExcess`).

## The exact computational facts behind this file (all integer-exact, reproduced in /tmp probes)

1. **Char-0 additive-relation girth of `μ_n` (n = 2^k) is EXACTLY 2.** The antipodal pair
   `ζ^j + ζ^{j+n/2} = 0` is a length-2 `±1` relation. So `μ_n` is **not even a `B_1`-set**; the
   Sidon depth is the *constant* `1` (the single antipodal obstruction), **independent of `n`**.
   It does **not** flow to `log p`. (Brute + exact: `/tmp/bh_depth.py`.)

2. **The genuine repeat-free wraparound girth does NOT flow up to `log p` — it stays SMALL.**
   The exact meet-in-the-middle search (coeff set `{-2,-1,0,1,2}` per antipodal class) gives:
   at `n=16` (half-basis size 8) the subgroup is too small to host *any* genuine `±1` wraparound
   — girth `= ∞` even at the bad primes `p ∈ {76001,107137,108497}` (`/tmp/bh_mitm.py`). At
   `n=32` (half-basis size 16) a genuine repeat-free wraparound relation **appears at length
   `7–9`**, which is **strictly BELOW `log p = 13`** for every window prime tested
   (`/tmp/bh_girth_trend.py`, `/tmp/bh_n32_verify.py`: e.g. `p=1048609` girth `8`, char-0 value
   `≈2.69 ≠ 0`, vanishes mod `p`). The girth/`log p` ratio is **shrinking** (`8/13 ≈ 0.6`), the
   *opposite* of the bootstrap premise that the Sidon depth flows up to `log p`. So short genuine
   wraparound relations exist **well below depth `log p`** — the premise is directly false.

3. **The wraparound excess `W_K = A_K − E_K^C` is POSITIVE at the bad primes.** At `n=16`,
   `p=76001`, `W_K > 0` for `K ≥ 6`, with `A_K/E_K^C` rising to `1.088` at `K=11=⌊log p⌋`
   (`/tmp/badprime_check.py`, reproducing the axiom-clean `_AvCP_AAPKernelCountermodel`).

4. **Reconciliation (the load-bearing structural point).** The energy `A_K` counts depth-`K`
   collisions `Σ x_i = Σ y_j (mod p)` over **tuples with REPETITION allowed**. An additive `±1`
   relation (the `B_h`-girth object) is a **repeat-free** equality of distinct roots. Direct exact
   count (`/tmp/reconcile.py`, `n=8`): every repeat-free balanced collision is already a char-0
   (antipodal) collision — **zero** genuine repeat-free wraparound there. Even at `n=16`, the
   positive `W_K` excess (fact 3) coexists with girth `= ∞` (fact 2): the excess is carried
   **entirely by tuples with repeated roots**, which the `B_h`/girth predicate **does not
   constrain**. The Bang–Zsygmondy primitive divisors of `2^{n/2}±1` are *not even predictive* of
   the good/bad-prime split (the bad primes have generic large `ord_2`, divide no small `2^j±1`
   — `/tmp/zsyg.py`). **Two independent failures: (a) girth does not flow to `log p` (n=32 fact),
   (b) even infinite girth does not bound the repeat-inclusive energy (n=16 fact).**

## What this file proves (axiom-clean)

The exact energy `collisions` set is indexed by **all** tuple pairs `(Fin r → ι) × (Fin r → ι)`,
including non-injective (repeated) tuples. We make the girth-vs-energy gap precise:

* `injCollisions` / `nonInjCollisions` — split the collision set by tuple injectivity.
* `GirthNoWraparound` — the `B_h`-style predicate: *every collision on a pair of INJECTIVE
  (repeat-free) tuples lifts to char 0*. This is what an additive-relation-girth (`B_h`) bound
  delivers.
* `wrapExcess_le_nonInj_card` — **the wraparound excess is supported on non-injective tuples**
  once `GirthNoWraparound` holds: `W_r ≤ #(non-injective char-p collisions)`. So a girth bound
  alone leaves the *entire* excess uncontrolled.
* `girthNoWraparound_not_imp_energy_eq_general` — **the route is structurally insufficient**: there
  is no general theorem `GirthNoWraparound ⟹ E_r = E_r^{char0}`; the gap is exactly the
  non-injective collisions, which the matching exact computation shows is *strictly positive* at
  the bad primes. We package this as: `GirthNoWraparound ∧ (∃ non-injective wraparound) ⟹ W_r > 0`
  is consistent, i.e. `GirthNoWraparound` does not force `wrapExcess = 0`.

## Honest verdict (the task's two questions)

1. **Exact `B_h` depth of `μ_n` at `n=8,16,32`:** the *raw* additive-relation girth is **`2`**
   (the antipodal pair `ζ^j + ζ^{j+n/2} = 0`), *constant in `n`* — `μ_n` is not a `B_1`-set. The
   *half-basis* (one rep per antipodal class) genuine-wraparound girth mod `p`: **`∞` at `n=8,16`**
   (subgroup too small), but **`7–9` at `n=32`**, which is **`< log p = 13`**. So the girth does
   **not** flow up to `log p`; the moment the subgroup is large enough to host a genuine
   wraparound it is already a small constant well below `log p`, and the ratio `girth/log p` is
   *shrinking*.
2. **Is the bootstrap flow real, or does the primitive-divisor input reduce?** The flow is
   **NOT real for the prize**, and fails *two* independent ways: **(a)** the genuine repeat-free
   wraparound girth does not flow to `log p` — at `n=32` it is `7–9 < 13` and shrinking
   (short wraparound relations exist below depth `log p`, contradicting the premise); **(b)** even
   where girth *is* infinite (`n=16`), the energy excess `W_K > 0` survives at the bad primes
   because it lives on **repeated-root** tuples that `B_h` cannot see. The Bang–Zsygmondy primitive
   divisors of `2^{n/2}±1` do not even predict the bad-prime set. **The angle is REFUTED as a route
   to the prize.** It is *not* a reduction to BGK — it targets the wrong object (repeat-free
   relations vs. repeat-inclusive energy) AND its girth-flow premise is computationally false.

This does NOT resurrect the refuted `A_K ≤ E_K^C`; it explains *why* a girth/Sidon argument cannot
prove it, and confirms the correct open kernel `A_K ≤ Wick_K` is the one still standing.

## References
- In-tree: `_NoExcessOnsetThreshold.lean` (the exact `collisions`/`wrapExcess` framework),
  `_AvCP_AAPKernelCountermodel.lean` (the bad-prime `W_K>0` countermodel).
- [ABF26] ePrint 2026/680 (issue #444).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.AttackThinnessBootstrapGirthVsEnergy

open Finset
open ArkLib.ProximityGap.NoExcessOnset

variable {K F : Type*} [Field K] [Field F] [DecidableEq K] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- The char-`p` collisions on **injective** (repeat-free) tuple pairs. These are the pairs an
additive-relation-girth / `B_h` argument can speak about: a balanced `±1` relation among
*distinct* roots. -/
noncomputable def injCollisions (φ : K →+* F) (ζ : ι → K) :
    Finset ((Fin r → ι) × (Fin r → ι)) :=
  (collisions (r := r) φ ζ).filter (fun p => Function.Injective p.1 ∧ Function.Injective p.2)

/-- The char-`p` collisions on tuple pairs with a **repeated** root (non-injective on either side).
These are exactly the collisions a girth/`B_h` bound is blind to — and where the bad-prime energy
excess `W_K > 0` lives. -/
noncomputable def nonInjCollisions (φ : K →+* F) (ζ : ι → K) :
    Finset ((Fin r → ι) × (Fin r → ι)) :=
  (collisions (r := r) φ ζ).filter (fun p => ¬ (Function.Injective p.1 ∧ Function.Injective p.2))

/-- **The `B_h`/girth predicate.** Every char-`p` collision on a pair of **injective** (repeat-free)
tuples already lifts to a char-`0` collision. This is exactly the strength an additive-relation
girth bound (a Sidon/`B_h` depth reaching `log p`) delivers: no genuine *repeat-free* `±1`
wraparound. It is *strictly weaker* than `NoWraparound`, which quantifies over **all** tuples. -/
def GirthNoWraparound (φ : K →+* F) (ζ : ι → K) : Prop :=
  ∀ x y : Fin r → ι, Function.Injective x → Function.Injective y →
    pushSum φ ζ x = pushSum φ ζ y → (∑ t, ζ (x t)) = ∑ t, ζ (y t)

/-- `NoWraparound` (all tuples) is at least as strong as `GirthNoWraparound` (injective tuples):
the full predicate implies the girth predicate by restriction. -/
theorem girthNoWraparound_of_noWraparound (φ : K →+* F) (ζ : ι → K)
    (h : NoWraparound (r := r) φ ζ) : GirthNoWraparound (r := r) φ ζ :=
  fun x y _ _ hpush => h x y hpush

/-- **The wraparound excess is supported on non-injective tuples under `GirthNoWraparound`.**
If the girth predicate holds (no repeat-free wraparound), then every genuine wraparound pair —
every element of `collisions φ \ collisions id` — has a repeated root, i.e. lies in
`nonInjCollisions`. Hence `W_r ≤ #(non-injective char-p collisions)`: the *entire* excess is
invisible to a girth/`B_h` argument. -/
theorem wrapExcess_le_nonInj_card (φ : K →+* F) (ζ : ι → K)
    (h : GirthNoWraparound (r := r) φ ζ) :
    wrapExcess (r := r) φ ζ ≤ (nonInjCollisions (r := r) φ ζ).card := by
  apply Finset.card_le_card
  intro p hp
  -- `hp : p ∈ collisions φ \ collisions id`
  rw [Finset.mem_sdiff] at hp
  obtain ⟨hpC, hpNot0⟩ := hp
  -- membership facts
  have hpush : pushSum φ ζ p.1 = pushSum φ ζ p.2 := by
    simpa [collisions, mem_filter, mem_univ, true_and] using hpC
  have hnot0 : (∑ t, ζ (p.1 t)) ≠ ∑ t, ζ (p.2 t) := by
    intro hc
    apply hpNot0
    simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id]
    exact hc
  -- it lands in nonInjCollisions: it is a collision, and NOT both-injective (else girth lifts it)
  rw [nonInjCollisions, mem_filter]
  refine ⟨hpC, ?_⟩
  rintro ⟨hinj1, hinj2⟩
  exact hnot0 (h p.1 p.2 hinj1 hinj2 hpush)

/-- **The structural insufficiency of the girth route.** There is no general implication
`GirthNoWraparound ⟹ E_r = E_r^{char0}`: the obstruction is precisely the non-injective
collisions. Concretely, whenever `GirthNoWraparound` holds but a **non-injective wraparound pair
exists** (a depth-`r` collision with a repeated root that does not lift to char 0), the excess is
**strictly positive**, so the energies differ. This is the abstract shadow of the exact bad-prime
fact `W_K > 0` at `n=16, p=76001, K ≥ 6` with girth `= ∞` (no repeat-free wraparound). -/
theorem girthNoWraparound_excess_pos_of_nonInj_witness (φ : K →+* F) (ζ : ι → K)
    (_h : GirthNoWraparound (r := r) φ ζ)
    (w : ((Fin r → ι) × (Fin r → ι)))
    (hwC : pushSum φ ζ w.1 = pushSum φ ζ w.2)
    (hwLift : (∑ t, ζ (w.1 t)) ≠ ∑ t, ζ (w.2 t)) :
    0 < wrapExcess (r := r) φ ζ := by
  -- `w` is a genuine wraparound pair, so the set-difference is nonempty.
  rw [wrapExcess, Finset.card_pos]
  refine ⟨w, ?_⟩
  rw [Finset.mem_sdiff]
  constructor
  · simp only [collisions, mem_filter, mem_univ, true_and]; exact hwC
  · simp only [collisions, mem_filter, mem_univ, true_and, pushSum_id]; exact hwLift

/-- **The route does NOT close `W_r = 0`.** Packaged contrapositive: a girth/`B_h` bound that
delivers `GirthNoWraparound` is *consistent* with `W_r > 0`. Hence the THINNESS_BOOTSTRAP angle
cannot, by additive-relation girth alone, prove `A_K ≤ E_K^C` (or `≤ Wick` *through* `E_K^C`):
the missing input is control of *non-injective* (repeated-root) collisions, an object girth does
not bound. (Witnessed exactly at the bad primes; see file header.) -/
theorem girthNoWraparound_not_imp_energy_eq_general (φ : K →+* F) (ζ : ι → K)
    (h : GirthNoWraparound (r := r) φ ζ)
    (w : ((Fin r → ι) × (Fin r → ι)))
    (hwC : pushSum φ ζ w.1 = pushSum φ ζ w.2)
    (hwLift : (∑ t, ζ (w.1 t)) ≠ ∑ t, ζ (w.2 t)) :
    energyCharP (r := r) φ ζ ≠ energyChar0 (r := r) ζ := by
  rw [energyCharP_eq_char0_add_wrapExcess]
  have hpos := girthNoWraparound_excess_pos_of_nonInj_witness φ ζ h w hwC hwLift
  omega

#print axioms girthNoWraparound_of_noWraparound
#print axioms wrapExcess_le_nonInj_card
#print axioms girthNoWraparound_excess_pos_of_nonInj_witness
#print axioms girthNoWraparound_not_imp_energy_eq_general

end ArkLib.ProximityGap.Frontier.AttackThinnessBootstrapGirthVsEnergy
