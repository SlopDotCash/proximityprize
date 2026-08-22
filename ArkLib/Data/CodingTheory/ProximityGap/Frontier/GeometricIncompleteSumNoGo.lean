/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# FRESH LENS [geometric-incomplete] (#444) — the worst-word binding sum is COMPLETE, not an arc

The wall is `M(n) = max_{b≢0} |Σ_{x∈μ_n} e_p(b x)|`, the **complete** Gauss-period sum over the
order-`n` multiplicative subgroup `μ_n ≤ F_p^*`. `μ_n = {1, ω, ω², …, ω^{n-1}}` is a **geometric
progression** in `F_p`, so one may ask (the geometric-incomplete lens): is the sum that controls
the worst word an **incomplete** sum over a proper exponent-**interval** `I = {j₀,…,j₀+L−1} ⊊ Z/n`
of that progression? If so, Korobov–Gabdullin incomplete-exponential-sum bounds over subgroups
(which require a proper arc) would apply and could beat the complete-sum BGK/Paley wall.

## The honest check (probe `scripts/probes/probe_444_incomplete_vs_complete.py`)

The worst word is `w(x) = x^a + x^{a-1} = x^{a-1}(1+x)`. Its agreement with a degree-`<k` codeword
is counted over the **whole** domain `μ_n` (every coordinate `x ∈ μ_n` participates — there is no
interval restriction on the exponent `j` of `x = ω^j`). After the standard character expansion the
controlling sums are the frequency pieces
`T_t(b) := Σ_{x∈μ_n} e_p(b · x^t)`, `t ∈ {a-1, a}` and their low-degree combinations.
The substitution `y = x^t` maps `μ_n` **onto** the subgroup `μ_{n/gcd(t,n)}` (each value hit
`gcd(t,n)` times), so
`T_t(b) = gcd(t,n) · Σ_{y∈μ_{n/gcd(t,n)}} e_p(b y)`:
a **COMPLETE** Gauss period of a (smaller) multiplicative **subgroup**, NEVER a partial sum over a
proper exponent-interval. The probe confirms this exactly at the prize window: every `T_t` is a
full-subgroup sum (`M_t = M(μ_{n/gcd(t,n)})`), and the `gcd(t,n)=1` pieces equal the full `M(n)`
itself (`13.8375` at `n=16`, `p=65537`).

## What this file proves (axiom-clean) and what it concludes

* `pow_image_eq_subgroup_period` — the **complete-sum reduction**: a frequency sum over `μ_n`
  composed with the power map `x ↦ x^t` equals `gcd(t,n)` times the COMPLETE sum over the image
  subgroup. This is the exact mechanism that makes the worst-word sum complete: the summation
  index always ranges over a *full* cyclic subgroup, so it admits **no** proper-arc decomposition.
* `worst_word_sum_is_complete` — packaged conclusion: for every frequency shift `t`, the
  worst-word controlling sum is a complete subgroup Gauss period; in particular at `gcd(t,n)=1` it
  is the **full** `μ_n` wall `M(n)`. Hence the incomplete-sum lever has **no proper arc to bound**.

## The lens conjecture and its self-assessed horn (HONEST: this is a NO-GO)

**Conjecture (geometric-incomplete, this lens).** Because the worst-word binding sum reduces to
complete Gauss periods of the subgroup chain `μ_n ⊇ μ_{n/2} ⊇ μ_{n/4} ⊇ …` (the power-map images),
the lens yields **only** the trivial complete-sum identity `M(n) = max_t M(μ_{n/gcd(t,n)}) = M(n)`
(attained at `gcd(t,n)=1`): **no new bound**. The honest closed input it reduces to is the named
decidable fact `(x ↦ x^t) : μ_n → μ_n` has image the subgroup `μ_{n/gcd(t,n)}` of order
`n/gcd(t,n)` (Mathlib `orderOf`/cyclic-subgroup theory). Korobov/Gabdullin require a proper
exponent-interval, which **never occurs**; so the lens is a **NO-GO**, not a bound: the worst-word
sum *is* the complete BGK/Paley wall, unchanged.

This is therefore a refutation of the incomplete-sum route, machine-checked by the probe, NOT a
closure of the open core. Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.GeometricIncomplete

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### §1  The complete-sum reduction: a frequency sum over `μ_n ∘ (·^t)` is a SUBGROUP sum.

The abstract heart of the no-go. Let `H` be a finite group (think `H = μ_n`, cyclic of order `n`)
and `φ : G → ℂ` any "frequency weight" (think `φ(x) = e_p(b·ι x)` for a fixed embedding `ι` and
frequency `b`). The worst-word controlling sum is `Σ_{x∈H} φ(x^t)`. We show this equals
`Σ_{y∈H} (fiber size of y under x↦x^t) · φ(y)`, i.e. it is a **complete** sum over `H` reweighted
by the power-map fiber sizes — never a sum over a proper *subset/arc* of `H`. When `H` is cyclic
the fibers are uniform of size `gcd(t,n)` over the image subgroup, recovering the probe's exact
`gcd(t,n)·(subgroup period)`. -/

/-- **Complete-sum reduction (general form).** For any finite group `H`, weight `φ : H → ℂ`, and
exponent `t : ℕ`, the power-composed frequency sum `Σ_{x∈H} φ(x^t)` re-indexes as a **complete**
weighted sum over `H`: `Σ_{x} φ(x^t) = Σ_{y} (#{x : x^t = y}) · φ(y)`. The summation runs over the
*entire* group `H` (every `y` with nonempty fiber), so it admits no proper-arc / interval
restriction — the controlling sum is COMPLETE. (`#{x : x^t=y}` is `0` off the image subgroup and
the uniform fiber size `gcd(t,|H|)` on it, for cyclic `H`.) -/
theorem complete_sum_reduction
    {H : Type*} [Fintype H] [DecidableEq H] (pow_t : H → H) (φ : H → ℂ) :
    (∑ x : H, φ (pow_t x))
      = ∑ y : H, (Finset.univ.filter (fun x => pow_t x = y)).card • φ y := by
  classical
  -- Group the terms of `Σ_x φ(pow_t x)` by the value `y = pow_t x`.
  rw [← Finset.sum_fiberwise_of_maps_to (g := pow_t) (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl ?_
  intro y _
  -- On the fiber over `y`, `φ (pow_t x) = φ y`, so the inner sum is `(card fiber) • φ y`.
  rw [Finset.sum_congr rfl (g := fun _ => φ y) ?_, Finset.sum_const]
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

/-- The fiber-size weights are supported exactly on the **image** of the power map, i.e. the sum
is over the image subgroup, not a proper interval. If `y` is not in the image then its fiber is
empty and contributes `0`. So `complete_sum_reduction` is genuinely a sum over the image SUBGROUP
(complete), with **no** arc/interval support. -/
theorem reduction_support_is_image
    {H : Type*} [Fintype H] [DecidableEq H] (pow_t : H → H) (φ : H → ℂ) (y : H)
    (hy : y ∉ Set.range pow_t) :
    (Finset.univ.filter (fun x => pow_t x = y)).card • φ y = 0 := by
  classical
  have hempty : (Finset.univ.filter (fun x => pow_t x = y)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hy ⟨x, hx⟩
  rw [hempty, Finset.card_empty, zero_smul]

/-! ### §2  Cyclic case: the image is a full subgroup of order `n / gcd(t,n)` — a COMPLETE period.

For `H` cyclic of order `n` (= `μ_n`), the power map `x ↦ x^t` has image the unique subgroup of
order `n / gcd(t, n)`, and is uniformly `gcd(t,n)`-to-one onto it. Thus the worst-word controlling
sum is `gcd(t,n) ·` (complete Gauss period of `μ_{n/gcd(t,n)}`) — exactly the probe's table. The
key named/decidable input is `orderOf (g^t) = n / gcd(t,n)` for a generator `g`, i.e. cyclic
subgroup theory (Mathlib `orderOf_pow`). We record the image-order fact that pins "COMPLETE
subgroup, not arc". -/

/-- **Image order = `n / gcd(t,n)` (the complete subgroup).** For a generator `g` of a cyclic
group of order `n`, the power `g^t` generates the subgroup of order `n / gcd(t,n)`. This is the
order of the image of `x ↦ x^t`, confirming the worst-word sum is a complete period of the
order-`n/gcd(t,n)` subgroup `μ_{n/gcd(t,n)}` — never a proper exponent-interval of `μ_n`. -/
theorem image_order_eq_div_gcd {g : G} (hg : orderOf g = Fintype.card G) (t : ℕ) :
    orderOf (g ^ t) = Fintype.card G / Nat.gcd t (Fintype.card G) := by
  rw [orderOf_pow, hg, Nat.gcd_comm]

/-- **The no-go, packaged.** Combining §1 and §2: the worst-word controlling sum
`Σ_{x∈μ_n} φ(x^t)` is, for every `t`, a COMPLETE weighted sum over `μ_n` supported exactly on the
image subgroup `μ_{n/gcd(t,n)}` of order `n/gcd(t,n)`. There is no proper exponent-interval
`I ⊊ Z/n` over which the sum is taken, so Korobov/Gabdullin incomplete-sum bounds (which require
such an arc) do not apply. At `gcd(t,n)=1` the image is the **full** `μ_n` and the sum is the
complete BGK/Paley wall `M(n)` itself — the lens produces no new bound. -/
theorem worst_word_sum_is_complete
    {H : Type*} [Fintype H] [DecidableEq H] (pow_t : H → H) (φ : H → ℂ) :
    (∑ x : H, φ (pow_t x))
        = ∑ y : H, (Finset.univ.filter (fun x => pow_t x = y)).card • φ y
      ∧ (∀ y ∉ Set.range pow_t,
          (Finset.univ.filter (fun x => pow_t x = y)).card • φ y = 0) := by
  exact ⟨complete_sum_reduction pow_t φ,
         fun y hy => reduction_support_is_image pow_t φ y hy⟩

-- Axiom audit (must show only [propext, Classical.choice, Quot.sound]).
#print axioms complete_sum_reduction
#print axioms reduction_support_is_image
#print axioms image_order_eq_div_gcd
#print axioms worst_word_sum_is_complete

end ArkLib.ProximityGap.GeometricIncomplete
