/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Partition substrate for the BCIKS20 Appendix A.4 β-recursion (brick L1)

This file provides the **partition / well-founded-recursion substrate** required to give a
`termination_by` definition of the BCIKS20 (eprint 2020/654) Appendix-A.4 Hensel-lift numerator
recursion (A.1)

```
β_0 = T  (mod H̃)
β_t = Σ_{i₁; λ ∈ P(t−i₁), λ ≠ λ^(t)}  W^{i₁+δ−1} · ξ^{2i₁+Σλ−2} · B_{i₁,λ} · ∏_l β_l^{λ_l}
```

where `P(m)` is the set of partitions `λ = (λ_l)_{l≥1}` of `m` (i.e. `Σ_l l·λ_l = m`), `λ^(t)` is
the *trivial* partition `λ_t = 1` (a single part of size `t`), and `Σλ = Σ_l λ_l` is the total
number of parts.

## Representation

We reuse Mathlib's `Nat.Partition n`, a structure carrying a `Multiset ℕ` of strictly-positive parts
that **sum to `n`**. The dictionary to the BCIKS20 notation is:

| BCIKS20 | Mathlib `p : Nat.Partition n` |
|---|---|
| `Σ_l l·λ_l = n` (the partition constraint) | `p.parts_sum : p.parts.sum = n` (built in) |
| `λ_l` (multiplicity of part `l`) | `p.parts.count l` |
| `Σλ = Σ_l λ_l` (number of parts) | `Multiset.card p.parts` |
| `λ^(t)` (trivial partition, single part `t`) | `Nat.Partition.indiscrete t` |
| "`l` in support of `λ`" (a part `l`) | `l ∈ p.parts` |

Finiteness of `P(n)` is `Nat.Partition`'s `Fintype` instance, so
`Finset.univ : Finset (Partition n)` is the finite index set the outer sum of (A.1) ranges
over.

## The key export (what L7's `termination_by` needs)

`§6` of the dependency DAG (Risks / notes for implementers) states the exact decreasing measure:

> the recursion `β_t` references `β_l` for `l ≤ t` but in any `λ ≠ λ^(t)` every `l` with `λ_l>0`
> has `l < t` (only `λ^(t)` hits `l=t`, and it is excluded). Encode this as the decreasing measure;
> L1 must export exactly this lemma.

That lemma is `parts_lt_of_ne_indiscrete` below. Combined with the `i₁ > 0` case
(`parts_lt_of_pos_sub`, where every part of a partition of `t - i₁ < t` is automatically `< t`),
`recursionStep_parts_lt` packages the full strict-decrease fact that every recursive call `β_l`
appearing in the `(t+1)`-step of (A.1) satisfies `l < t+1`, which is exactly the obligation a
`termination_by … => t` / `decreasing_by` discharges.

## Main results

* `Nat.Partition.indiscrete` is the trivial partition `λ^(t)`; characterised by `indiscrete_parts`,
  `card_parts_indiscrete = 1`, `mem_parts_indiscrete`.
* `parts_lt_of_ne_indiscrete` — **THE decreasing-measure lemma L7 needs** (`i₁ = 0` case):
  for `p : Partition t`, `p ≠ indiscrete t`, every part is `< t`.
* `parts_lt_of_pos_sub` — the `i₁ > 0` case: every part of a `Partition (t - i₁)` with `0 < i₁` is
  `< t`.
* `recursionStep_parts_lt` — the combined strict-decrease lemma covering every recursive call of the
  `(A.1)` step, ready to feed a `termination_by`/`decreasing_by`.
* `two_le_card_parts_of_ne_indiscrete` — the `Σλ ≥ 2` lemma (non-trivial case), used by L8 for the
  `ξ`-exponent `2i₁ + Σλ − 2 ≥ 0` regularity when `i₁ = 0`.
* `recursionWF` — a `WellFoundedRelation ℕ` (`<` on `ℕ`) witnessing termination, plus
  `recursionStep_rel` restating the strict decrease in that relation.
-/

set_option linter.style.longLine false

namespace ArkLib

open Nat

namespace Nat.Partition

variable {t : ℕ}

/-! ### Basic facts about the trivial partition `λ^(t) = indiscrete t` -/

/-- The trivial partition `λ^(t)` (`indiscrete t`) has exactly one part. (`Σλ = 1`.) -/
@[simp] theorem card_parts_indiscrete (hn : t ≠ 0) :
    Multiset.card (Nat.Partition.indiscrete t).parts = 1 := by
  rw [Nat.Partition.indiscrete_parts hn]; rfl

/-- The single part of `λ^(t)` is `t` itself. -/
theorem mem_parts_indiscrete (hn : t ≠ 0) :
    ∀ m ∈ (Nat.Partition.indiscrete t).parts, m = t := by
  intro m hm
  rw [Nat.Partition.indiscrete_parts hn] at hm
  simpa using hm

/-! ### The non-trivial case: a partition equals `indiscrete` iff it has a part equal to `t` -/

/-- A partition of `t` whose multiset of parts contains `t` is the trivial partition `λ^(t)`.
This is the structural fact behind the decreasing measure: only `λ^(t)` uses the part `t`. -/
theorem eq_indiscrete_of_mem_self (ht : 0 < t) {p : Nat.Partition t} (hm : t ∈ p.parts) :
    p = Nat.Partition.indiscrete t := by
  -- `t` is a part and the parts sum to `t`, so all other parts have total sum `0`, hence none.
  have hsum : p.parts.sum = t := p.parts_sum
  have hcons : t ::ₘ (p.parts.erase t) = p.parts := Multiset.cons_erase hm
  have hsplit : t + (p.parts.erase t).sum = t := by
    rw [← Multiset.sum_cons, hcons, hsum]
  have herase0 : (p.parts.erase t).sum = 0 := by omega
  have herase_empty : p.parts.erase t = 0 := by
    rw [Multiset.sum_eq_zero_iff] at herase0
    by_contra hne
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    have hxpos : 0 < x := p.parts_pos (Multiset.mem_of_mem_erase hx)
    have := herase0 x hx
    omega
  have hpe : p.parts = {t} := by rw [← hcons, herase_empty]; rfl
  apply Nat.Partition.ext
  rw [hpe, Nat.Partition.indiscrete_parts ht.ne']

/-- A partition of `t > 0` contains the part `t` **iff** it is the trivial partition `λ^(t)`.
The packaged biconditional of `eq_indiscrete_of_mem_self` (forward) and the singleton membership of
`indiscrete` (reverse). With `notMem_parts_of_lt` this fully resolves the BCIKS20 A.4 exclusion
`(t+1) ∉ λ.parts`: for a partition of total `t+1`, the only excluded term is `λ = indiscrete (t+1)`
(the single part `[t+1]`); for any smaller total the exclusion is vacuous. -/
theorem mem_self_iff_eq_indiscrete (ht : 0 < t) {p : Nat.Partition t} :
    t ∈ p.parts ↔ p = Nat.Partition.indiscrete t := by
  refine ⟨eq_indiscrete_of_mem_self ht, fun h => ?_⟩
  rw [h, Nat.Partition.indiscrete_parts ht.ne']
  exact Multiset.mem_singleton.mpr rfl

/-! ### The zero-total partition is a singleton -/

/-- A partition of `0` has no parts.  This is the zero-total companion to the positive-total
`indiscrete` characterisation above, and is useful when the BCIKS20 recursion reaches the
`λ : Partition 0` branch. -/
theorem parts_eq_zero_of_zero (p : Nat.Partition 0) : p.parts = 0 := by
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  have hpos := p.parts_pos ha
  have hle : a ≤ p.parts.sum := Multiset.le_sum_of_mem ha
  rw [p.parts_sum] at hle
  omega

/-- Every partition of `0` is the empty/indiscrete partition. -/
theorem eq_indiscrete_zero (p : Nat.Partition 0) :
    p = Nat.Partition.indiscrete 0 := by
  apply Nat.Partition.ext
  rw [parts_eq_zero_of_zero p]
  simp

/-- The finite type of partitions of `0` is the singleton `{indiscrete 0}`. -/
theorem univ_eq_singleton_indiscrete_zero :
    (Finset.univ : Finset (Nat.Partition 0)) = {Nat.Partition.indiscrete 0} := by
  ext p
  constructor
  · intro _
    exact Finset.mem_singleton.mpr (eq_indiscrete_zero p)
  · intro _
    exact Finset.mem_univ p

/-- A partition of `0` contains no part. -/
theorem notMem_parts_of_zero (p : Nat.Partition 0) (m : ℕ) : m ∉ p.parts := by
  rw [parts_eq_zero_of_zero p]
  simp

/-- Filtering partitions of `0` by exclusion of any part leaves the singleton empty partition. -/
theorem univ_filter_notMem_zero_eq_singleton_indiscrete (m : ℕ) :
    ((Finset.univ : Finset (Nat.Partition 0)).filter (fun lam => m ∉ lam.parts)) =
      {Nat.Partition.indiscrete 0} := by
  classical
  rw [univ_eq_singleton_indiscrete_zero]
  simp

/-! ### The one-total partition and the excluded singleton branch -/

/-- Every partition of `1` contains the part `1`. -/
theorem one_mem_parts_of_one (p : Nat.Partition 1) : 1 ∈ p.parts := by
  by_contra hnot
  have hzero : p.parts = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    have hpos := p.parts_pos ha
    have hle : a ≤ p.parts.sum := Multiset.le_sum_of_mem ha
    rw [p.parts_sum] at hle
    have ha1 : a = 1 := by omega
    exact hnot (ha1 ▸ ha)
  have hsum0 : p.parts.sum = 0 := by
    rw [hzero]
    rfl
  have hsum1 : p.parts.sum = 1 := p.parts_sum
  omega

/-- Every partition of `1` is the one-part/indiscrete partition. -/
theorem eq_indiscrete_one (p : Nat.Partition 1) :
    p = Nat.Partition.indiscrete 1 :=
  eq_indiscrete_of_mem_self (by omega) (one_mem_parts_of_one p)

/-- The finite type of partitions of `1` is the singleton `{indiscrete 1}`. -/
theorem univ_eq_singleton_indiscrete_one :
    (Finset.univ : Finset (Nat.Partition 1)) = {Nat.Partition.indiscrete 1} := by
  ext p
  constructor
  · intro _
    exact Finset.mem_singleton.mpr (eq_indiscrete_one p)
  · intro _
    exact Finset.mem_univ p

/-- Filtering partitions of `1` by exclusion of the part `1` leaves the empty finset. -/
theorem univ_filter_notMem_one_eq_empty :
    ((Finset.univ : Finset (Nat.Partition 1)).filter (fun lam => 1 ∉ lam.parts)) = ∅ := by
  classical
  rw [univ_eq_singleton_indiscrete_one]
  ext p
  simp

/-- Adding an arbitrary part-count upper bound to the partition-of-`1` exclusion filter still
leaves the empty finset. -/
theorem univ_filter_card_le_and_notMem_one_eq_empty (i : ℕ) :
    ((Finset.univ : Finset (Nat.Partition 1)).filter
        (fun lam => lam.parts.card ≤ i ∧ 1 ∉ lam.parts)) = ∅ := by
  classical
  apply Finset.filter_false_of_mem
  intro lam _
  exact fun h => h.2 (one_mem_parts_of_one lam)

/-- The P2-style filter on partitions of `0` is the singleton empty partition. -/
theorem univ_zero_filter_card_le_and_notMem_one_eq_singleton (i : ℕ) :
    ((Finset.univ : Finset (Nat.Partition 0)).filter
        (fun lam => lam.parts.card ≤ i ∧ 1 ∉ lam.parts)) = {Nat.Partition.indiscrete 0} := by
  classical
  rw [univ_eq_singleton_indiscrete_zero]
  ext p
  simp

/-! ### THE decreasing-measure lemma (the `i₁ = 0` case; what §6 of the DAG specifies) -/

/-- **The key export for L7's well-founded recursion (`i₁ = 0` case).**

For a partition `p` of `t` that is *not* the trivial partition `λ^(t)` (`indiscrete t`), every part
`m ∈ p.parts` satisfies `m < t` strictly. This is precisely the BCIKS20 App-A.4 fact that the
recursion `β_t = Σ_{λ ≠ λ^(t)} … ∏_l β_l^{λ_l}` only refers to `β_l` with `l < t`, so the recursion
on (A.1) is well-founded. (DAG §6: "in any `λ ≠ λ^(t)` every `l` with `λ_l>0` has `l < t`".) -/
theorem parts_lt_of_ne_indiscrete (p : Nat.Partition t)
    (h : p ≠ Nat.Partition.indiscrete t) :
    ∀ m ∈ p.parts, m < t := by
  intro m hm
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp at hm
  · have hle : m ≤ t := Nat.Partition.le_of_mem_parts hm
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd (eq_indiscrete_of_mem_self ht (heq ▸ hm)) h

/-! ### The `i₁ > 0` case: a partition of `t - i₁` has all parts `< t` -/

/-- The `i₁ > 0` branch of the recursion strict-decrease: every part of a partition of `t - i₁`
(with `0 < i₁ ≤ t`) is `< t`, automatically — no exclusion of `λ^(t)` is needed because the parts
already sum to `t - i₁ < t`. -/
theorem parts_lt_of_pos_sub {i₁ : ℕ} (hi₁ : 0 < i₁) (hit : i₁ ≤ t)
    (p : Nat.Partition (t - i₁)) :
    ∀ m ∈ p.parts, m < t := by
  intro m hm
  have hle : m ≤ t - i₁ := Nat.Partition.le_of_mem_parts hm
  omega

/-! ### The `Σλ ≥ 2` lemma (non-trivial case) used for `ξ`-exponent regularity (L8) -/

/-- **The `Σλ ≥ 2` export (non-trivial case).** A partition of `t > 0` that is not `λ^(t)` has at
least two parts (`Σλ = Multiset.card p.parts ≥ 2`). Used by L8 to show `2i₁ + Σλ − 2 ≥ 0` (so the
`ξ`-exponent of every term of (A.1) is non-negative; the only delicate case is `i₁ = 0`). -/
theorem two_le_card_parts_of_ne_indiscrete (ht : 0 < t) {p : Nat.Partition t}
    (h : p ≠ Nat.Partition.indiscrete t) :
    2 ≤ Multiset.card p.parts := by
  -- card ≠ 0 (parts nonempty since sum = t > 0) and card ≠ 1 (else it is the single-part
  -- partition).
  rcases Nat.lt_or_ge (Multiset.card p.parts) 2 with hlt | hge
  · exfalso
    interval_cases hc : Multiset.card p.parts
    · -- card = 0 ⟹ parts empty ⟹ sum 0 ≠ t
      rw [Multiset.card_eq_zero] at hc
      have : p.parts.sum = t := p.parts_sum
      rw [hc] at this; simp at this; omega
    · -- card = 1 ⟹ parts = {a}, sum = a = t ⟹ p = indiscrete t
      rw [Multiset.card_eq_one] at hc
      obtain ⟨a, ha⟩ := hc
      apply h
      have hsum : p.parts.sum = t := p.parts_sum
      rw [ha] at hsum
      simp only [Multiset.sum_singleton] at hsum
      have hmem : t ∈ p.parts := by rw [ha, ← hsum]; simp
      exact eq_indiscrete_of_mem_self ht hmem
  · exact hge

/-! ### Packaging the combined strict decrease for L7's `termination_by` -/

/-- **The combined strict-decrease lemma for the `(A.1)` recursion step.**

In the `β_{t+1}` step the outer sum ranges over `(i₁, λ)` with `i₁ ≤ t+1`, `λ : Partition (t+1−i₁)`,
excluding only the trivial pair `(0, λ^(t+1))`; the recursive calls are `β_l` for `l ∈ λ.parts`.
This lemma certifies every such `l` satisfies `l < t + 1`, which is exactly the obligation
discharged by `termination_by β_rec t => t` / `decreasing_by`.

The hypothesis `hexcl` excludes precisely the single forbidden term `(i₁ = 0, λ = λ^(t+1))`,
expressed type-safely via the parts multiset (`λ^(t+1)` is the unique partition with
`parts = {t+1}`). -/
theorem recursionStep_parts_lt {i₁ : ℕ} (hi : i₁ ≤ t + 1)
    (p : Nat.Partition (t + 1 - i₁))
    (hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ))) :
    ∀ l ∈ p.parts, l < t + 1 := by
  rcases Nat.eq_zero_or_pos i₁ with hi0 | hipos
  · -- i₁ = 0: p : Partition (t+1), and p ≠ indiscrete (t+1) (from hexcl)
    subst hi0
    simp only [Nat.sub_zero] at p hexcl ⊢
    have hne : p ≠ Nat.Partition.indiscrete (t + 1) := by
      intro hp
      apply hexcl
      refine ⟨trivial, ?_⟩
      rw [hp]
      exact Nat.Partition.indiscrete_parts (Nat.succ_ne_zero t)
    exact parts_lt_of_ne_indiscrete p hne
  · -- i₁ > 0: every part ≤ (t+1) - i₁ < t+1
    exact parts_lt_of_pos_sub hipos hi p

/-! ### A `WellFoundedRelation` witness (`<` on `ℕ`) -/

/-- The well-founded relation underlying the `β`-recursion: ordinary `<` on `ℕ`, applied to the
recursion index `t`. Provided so callers can write a `WellFoundedRelation`-based definition; the
strict decrease of each recursive call is `recursionStep_rel`. -/
@[reducible] def recursionWF : WellFoundedRelation ℕ := ⟨(· < ·), Nat.lt_wfRel.wf⟩

/-- Restatement of the combined strict decrease in terms of `recursionWF`: every recursive index `l`
of the `β_{t+1}` step is related to `t + 1` by `recursionWF.rel` (i.e. `l < t + 1`). -/
theorem recursionStep_rel {i₁ : ℕ} (hi : i₁ ≤ t + 1)
    (p : Nat.Partition (t + 1 - i₁))
    (hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)))
    {l : ℕ} (hl : l ∈ p.parts) :
    recursionWF.rel l (t + 1) :=
  recursionStep_parts_lt hi p hexcl l hl

/-- A partition of `n` contains no part `k` strictly larger than `n`: every part is at most
`p.parts.sum = n < k`. In the BCIKS20 A.4 recursion this discharges the `(t+1) ∉ λ.parts`
exclusion automatically for every block whose partitioned total is `≤ t` (e.g. `λ` partitioning
`t+1-i₁` with `i₁ ≥ 1`), so the exclusion is only nontrivial for the `i₁ = 0` outer block. -/
theorem notMem_parts_of_lt {n k : ℕ} (p : Nat.Partition n) (h : n < k) :
    k ∉ p.parts := by
  intro hk
  have hle : k ≤ p.parts.sum := Multiset.le_sum_of_mem hk
  rw [p.parts_sum] at hle
  omega

end Nat.Partition

end ArkLib

#print axioms ArkLib.Nat.Partition.parts_lt_of_ne_indiscrete
#print axioms ArkLib.Nat.Partition.parts_lt_of_pos_sub
#print axioms ArkLib.Nat.Partition.recursionStep_parts_lt
#print axioms ArkLib.Nat.Partition.two_le_card_parts_of_ne_indiscrete
#print axioms ArkLib.Nat.Partition.eq_indiscrete_of_mem_self
#print axioms ArkLib.Nat.Partition.parts_eq_zero_of_zero
#print axioms ArkLib.Nat.Partition.eq_indiscrete_zero
#print axioms ArkLib.Nat.Partition.univ_eq_singleton_indiscrete_zero
#print axioms ArkLib.Nat.Partition.notMem_parts_of_zero
#print axioms ArkLib.Nat.Partition.univ_filter_notMem_zero_eq_singleton_indiscrete
#print axioms ArkLib.Nat.Partition.one_mem_parts_of_one
#print axioms ArkLib.Nat.Partition.eq_indiscrete_one
#print axioms ArkLib.Nat.Partition.univ_eq_singleton_indiscrete_one
#print axioms ArkLib.Nat.Partition.univ_filter_notMem_one_eq_empty
#print axioms ArkLib.Nat.Partition.univ_filter_card_le_and_notMem_one_eq_empty
#print axioms ArkLib.Nat.Partition.univ_zero_filter_card_le_and_notMem_one_eq_singleton
#print axioms ArkLib.Nat.Partition.card_parts_indiscrete
#print axioms ArkLib.Nat.Partition.recursionStep_rel
#print axioms ArkLib.Nat.Partition.notMem_parts_of_lt
#print axioms ArkLib.Nat.Partition.mem_self_iff_eq_indiscrete
