/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Polynomial.Basic

/-!
# Power-series composition coefficients (BCIKS20 App. A.4 — WAVE 3 foundation)
-/

namespace ArkLib.PowerSeriesComposition

open Finset BigOperators PowerSeries

section Combinatorics

variable {M : Type*} [CommMonoid M]

/-- The **multiset of values** of a weak composition `l` over the index set `s`. -/
def valueMultiset {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) : Multiset ℕ :=
  s.val.map (fun i => l i)

@[simp]
theorem valueMultiset_card {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) :
    (valueMultiset s l).card = s.card := by
  rw [valueMultiset, Multiset.card_map, Finset.card_def]

theorem valueMultiset_sum {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) :
    (valueMultiset s l).sum = ∑ i ∈ s, l i := by
  rw [valueMultiset, Finset.sum]

/-- **Index-set → value-multiset.**  The product `∏_{i∈s} b (l i)` of a family `b : ℕ → M`
evaluated at the *values* `l i` equals the product over the **multiset of values**
`valueMultiset s l` after applying `b`.  This is the rewriting that turns an index-keyed
product into a value-keyed one, so that two compositions sharing the same bag of values
produce the same product — the prerequisite for the multiplicity grouping below. -/
theorem prod_eq_multiset_value_prod {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) (b : ℕ → M) :
    ∏ i ∈ s, b (l i) = ((valueMultiset s l).map b).prod := by
  rw [valueMultiset, Multiset.map_map, Finset.prod]
  rfl

/-- **L4 — FOUNDATIONAL: the multiplicity-grouping identity.**

The order-`t` weak-composition sum
`∑_{l ∈ finsuppAntidiag s t} ∏_{i∈s} b (l i)` — exactly the shape produced by mathlib's
`PowerSeries.coeff_pow` / `coeff_prod` — regroups, *by the multiset of part-values*, into a
sum indexed by the distinct value-multisets `m` (each a `Multiset ℕ` of `card = #s`,
`sum = t`, realized by some composition), weighted by the number of compositions realizing
`m`:

`∑_{l} ∏_{i∈s} b (l i) = ∑_{m ∈ image valueMultiset} (#fiber of m) • ((m.map b).prod)`.

This is the multivariate-Faà-di-Bruno combinatorial core (BCIKS20 A.4): the fiber
cardinality `#{l | valueMultiset s l = m}` is the multinomial counting how many weak
compositions share the bag `m`, and `(m.map b).prod = ∏_l (b l)^{count l m}` is the
partition-product `∏ β^λ`.  The products run in the multiplicative monoid of `R` while the
outer sum / `•` run in its additive monoid (so the natural home is a `CommSemiring`, which
is also where `coeff_pow` lives).  It is pure semiring combinatorics — no dependence on
`𝕃`/`R`/`H` — so it compiles fast and (witnessed by `compositionSum_example`) cannot be
vacuous.  Everything downstream (`coeff_pow_eq_valueMultisetSum`, and the staged
`compositionSum_eq_partitionSum`) reuses it. -/
theorem compositionSum_eq_valueMultisetSum {ι : Type*} [DecidableEq ι]
    {R : Type*} [CommSemiring R] (s : Finset ι) (t : ℕ) (b : ℕ → R) :
    ∑ l ∈ finsuppAntidiag s t, ∏ i ∈ s, b (l i)
      = ∑ m ∈ (finsuppAntidiag s t).image (valueMultiset s),
          (#{l ∈ finsuppAntidiag s t | valueMultiset s l = m}) • ((m.map b).prod) := by
  classical
  -- Each summand depends on `l` only through `valueMultiset s l`, so this is exactly the
  -- fiber-cardinality grouping `Finset.sum_comp`.
  have hsummand : ∀ l : ι →₀ ℕ, (∏ i ∈ s, b (l i)) = ((valueMultiset s l).map b).prod :=
    fun l => prod_eq_multiset_value_prod s l b
  simp_rw [hsummand]
  exact Finset.sum_comp (fun m => (m.map b).prod) (valueMultiset s)

/-- The concrete family `b n := 2 ^ n : ℕ → ℕ` used to witness non-vacuity of L4. -/
private def bWitness : ℕ → ℕ := fun n => 2 ^ n

/-- **Non-vacuity witness for L4 (composition side).**  At `s = range 2`, `t = 2`, with
`b n := 2 ^ n`, the three weak compositions `(2,0),(0,2),(1,1)` each contribute
`2^{l₀}·2^{l₁} = 2^2 = 4`, so the left-hand (ungrouped) sum is `4 + 4 + 4 = 12 ≠ 0`. -/
example : (∑ l ∈ finsuppAntidiag (range 2) 2, ∏ i ∈ range 2, bWitness (l i)) = 12 := by decide

/-- **Non-vacuity witness for L4 (grouped side).**  The same data, grouped by value-multiset:
`{2,0}` has fiber size `2` and product `2^2·2^0 = 4` (contributing `2 • 4 = 8`); `{1,1}` has
fiber size `1` and product `2^1·2^1 = 4` (contributing `1 • 4 = 4`); total `12`.  So the
grouping genuinely splits into two distinct multisets with *different* multinomial weights —
neither an empty sum nor a degenerate `0 = 0`. -/
example :
    (∑ m ∈ (finsuppAntidiag (range 2) 2).image (valueMultiset (range 2)),
        (#{l ∈ finsuppAntidiag (range 2) 2 | valueMultiset (range 2) l = m})
          • ((m.map bWitness).prod)) = 12 := by decide

/-- The two sides of L4 visibly agree, and both equal the nonzero value `12`, at the concrete
instance `s = range 2`, `t = 2`, `b n = 2^n`: a self-check that
`compositionSum_eq_valueMultisetSum` is not vacuous. -/
theorem compositionSum_example :
    (∑ l ∈ finsuppAntidiag (range 2) 2, ∏ i ∈ range 2, bWitness (l i))
      = ∑ m ∈ (finsuppAntidiag (range 2) 2).image (valueMultiset (range 2)),
          (#{l ∈ finsuppAntidiag (range 2) 2 | valueMultiset (range 2) l = m})
            • ((m.map bWitness).prod) :=
  compositionSum_eq_valueMultisetSum (range 2) 2 bWitness

end Combinatorics

section PowerSeries

open scoped Classical in
/-- **L1 — substitution coefficient as a Finset sum.**  Packages mathlib's
`PowerSeries.coeff_subst'` (a `finsum` over `d : ℕ`) as a genuine `Finset.sum` over the
finite support guaranteed by `coeff_subst_finite'`.  This is the form the keystone needs:
the `e`-coefficient of `subst b f` is the finite sum `∑_d (coeff_d f) • coeff_e (b^d)`.

Pure mathlib repackaging (no new math), but reusable: it removes the `finsum` boilerplate at
every downstream use. -/
theorem coeff_subst_eq_finset_sum
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {b : S⟦X⟧} (hb : PowerSeries.HasSubst b) (f : R⟦X⟧) (e : ℕ) :
    coeff e (f.subst b)
      = ∑ d ∈ (PowerSeries.coeff_subst_finite' hb f e).toFinset,
          coeff d f • PowerSeries.coeff e (b ^ d) := by
  rw [PowerSeries.coeff_subst' hb f e]
  exact finsum_eq_sum _ (PowerSeries.coeff_subst_finite' hb f e)

/-- **L2 — power coefficient as a weak-composition sum.**  A thin restatement (definitional
alias) of `PowerSeries.coeff_pow`: the `n`-th coefficient of `φ ^ k` is the sum over weak
compositions `l ∈ finsuppAntidiag (range k) n` of `∏_{i<k} coeff_{l i} φ`.  This is the exact
antidiagonal form that `compositionSum_eq_valueMultisetSum` (L4) then regroups. -/
theorem coeff_pow_eq_compositionSum {R : Type*} [CommSemiring R] (k n : ℕ) (φ : R⟦X⟧) :
    coeff n (φ ^ k)
      = ∑ l ∈ finsuppAntidiag (range k) n, ∏ i ∈ range k, coeff (l i) φ :=
  PowerSeries.coeff_pow k n φ

/-- **L5-precursor — `coeff_pow` already in grouped (value-multiset) form.**  Combining L2
(`coeff_pow_eq_compositionSum`) with L4 (`compositionSum_eq_valueMultisetSum`) lands the
`n`-th coefficient of `φ^k` directly on the multiplicity-grouped sum: over the distinct
value-multisets `m` of weak compositions of `n` into `k` parts, weighted by the number of
compositions realizing `m`, of `∏_l (coeff_l φ)^{count l m}`.

This is the structural shape the keystone's order-`t` coefficient must reproduce (with
`φ = γ`, `k = i` the `Y`-degree); the only remaining gap to the in-tree
`partitionProd`/`prefactor` form is the zero-part / `Nat.Partition` reconciliation staged in
`compositionSum_eq_partitionSum` below. -/
theorem coeff_pow_eq_valueMultisetSum {R : Type*} [CommSemiring R] (k n : ℕ) (φ : R⟦X⟧) :
    coeff n (φ ^ k)
      = ∑ m ∈ (finsuppAntidiag (range k) n).image (valueMultiset (range k)),
          (#{l ∈ finsuppAntidiag (range k) n | valueMultiset (range k) l = m})
            • ((m.map (fun j => coeff j φ)).prod) := by
  rw [coeff_pow_eq_compositionSum k n φ]
  exact compositionSum_eq_valueMultisetSum (range k) n (fun j => coeff j φ)

end PowerSeries

section FiberCard

/-! ## The fiber-cardinality identity — fiber count `=` multinomial of multiplicities

The value-multiset index `m` of `compositionSum_eq_valueMultisetSum` is a `Multiset ℕ` of
cardinality `#s` summing to `t`; it carries the `#s − (number of positive parts)` **zero**
parts of a *weak* composition.  This section identifies the fiber cardinality
`#{l | valueMultiset s l = m}` with `Multiset.countPerms m` — the number of distinct orderings
of the bag `m` over the `#s` ordered slots (zeros included), i.e. the `Nat.multinomial` of `m`'s
part-multiplicities.  This is the load-bearing combinatorial identity that turns the fiber-card
weight of `compositionSum_eq_valueMultisetSum` into the `prefactor`/`multinomial` of `(A.1)`.

The proof is by induction on the index finset `s` (peeling one index `a`, summing over the value
`l a = v`), matched against the value-erasure recursion `countPerms_eq_sum_erase` of `countPerms`.
The latter is derived from the per-value identity
`count v m * countPerms m = card m * countPerms (m.erase v)` (a clean factorial cancellation off
`Nat.multinomial_spec`), avoiding any zero-part `Nat.Partition` reconciliation. -/

open scoped Nat

/-- `valueMultiset` on `insert a s` (for `a ∉ s`) prepends the value `l a` to the
`valueMultiset` over `s` — the recursion that drives the induction on the index set. -/
theorem valueMultiset_insert {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι) (h : a ∉ s)
    (l : ι →₀ ℕ) : valueMultiset (insert a s) l = (l a) ::ₘ valueMultiset s l := by
  unfold valueMultiset
  rw [Finset.insert_val, Multiset.ndinsert_of_notMem h, Multiset.map_cons]

/-- `valueMultiset s` depends only on the values at indices of `s`, so erasing an index `a ∉ s`
from the finsupp leaves it unchanged. -/
theorem valueMultiset_erase_notMem {ι : Type*} (a : ι) (s : Finset ι) (h : a ∉ s)
    (l : ι →₀ ℕ) : valueMultiset s (Finsupp.erase a l) = valueMultiset s l := by
  unfold valueMultiset
  refine Multiset.map_congr rfl (fun i hi => ?_)
  rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hi h)]

/-- `countPerms m` as a `Nat.multinomial` over the support `m.toFinset` of `m`'s
count function. -/
theorem countPerms_eq_multinomial (m : Multiset ℕ) :
    m.countPerms = Nat.multinomial m.toFinset (fun v => m.count v) := by
  rw [Multiset.countPerms,
    ← Finsupp.multinomial_of_support_subset (s := m.toFinset) (d := m.toFinsupp)
        (by rw [Multiset.toFinsupp_support])]
  rfl

/-- `countPerms (m.erase v)` as a `Nat.multinomial` over the **larger** finset `m.toFinset`
(any index dropped by the erasure contributes a `0! = 1` factor). -/
theorem countPerms_erase_eq_multinomial (m : Multiset ℕ) (v : ℕ) :
    (m.erase v).countPerms = Nat.multinomial m.toFinset (fun w => (m.erase v).count w) := by
  rw [countPerms_eq_multinomial]
  apply Nat.multinomial_congr_of_sdiff (s := (m.erase v).toFinset) (t := m.toFinset)
  · exact Multiset.toFinset_subset.mpr (Multiset.erase_subset _ _)
  · intro w hw
    rw [Finset.mem_sdiff, Multiset.mem_toFinset, Multiset.mem_toFinset] at hw
    rw [Multiset.count_eq_zero]; exact hw.2
  · intro w _; rfl

/-- `∑_{w ∈ m.toFinset} count w m = card m`. -/
theorem sum_count_self (m : Multiset ℕ) :
    ∑ w ∈ m.toFinset, m.count w = m.card := Multiset.toFinset_sum_count_eq m

/-- `∑_{w ∈ m.toFinset} count w (m.erase v) = card (m.erase v)` (summed over the *larger*
finset `m.toFinset`; the extra index contributes count `0`). -/
theorem sum_count_erase (m : Multiset ℕ) (v : ℕ) :
    ∑ w ∈ m.toFinset, (m.erase v).count w = (m.erase v).card := by
  rw [← Multiset.toFinset_sum_count_eq (m.erase v)]
  refine (Finset.sum_subset (Multiset.toFinset_subset.mpr (Multiset.erase_subset _ _)) ?_).symm
  intro w _ hw
  rw [Multiset.mem_toFinset] at hw
  rw [Multiset.count_eq_zero]; exact hw

/-- **Per-value cancellation:** `count v m * countPerms m = card m * countPerms (m.erase v)`
for `v ∈ m`.  Proved by clearing both `Nat.multinomial_spec` denominators over the common
finset `m.toFinset` (the products differ only at `v`, by one factorial step). -/
theorem count_mul_countPerms (m : Multiset ℕ) (v : ℕ) (hv : v ∈ m) :
    m.count v * m.countPerms = m.card * (m.erase v).countPerms := by
  have hvf : v ∈ m.toFinset := Multiset.mem_toFinset.mpr hv
  set P : ℕ := ∏ w ∈ (m.toFinset).erase v, (m.count w)! with hP
  have hprodm : ∏ w ∈ m.toFinset, (m.count w)! = (m.count v)! * P :=
    (Finset.mul_prod_erase m.toFinset (fun w => (m.count w)!) hvf).symm
  have hprode : ∏ w ∈ m.toFinset, ((m.erase v).count w)! = ((m.count v) - 1)! * P := by
    rw [← Finset.mul_prod_erase m.toFinset (fun w => ((m.erase v).count w)!) hvf,
        Multiset.count_erase_self]
    congr 1
    refine Finset.prod_congr rfl (fun w hw => ?_)
    rw [Finset.mem_erase] at hw
    rw [Multiset.count_erase_of_ne hw.1]
  have specm := Nat.multinomial_spec m.toFinset (fun w => m.count w)
  have spece := Nat.multinomial_spec m.toFinset (fun w => (m.erase v).count w)
  rw [sum_count_self, hprodm, ← countPerms_eq_multinomial] at specm
  rw [sum_count_erase, hprode, ← countPerms_erase_eq_multinomial] at spece
  have hc : 1 ≤ m.count v := Multiset.one_le_count_iff_mem.mpr hv
  have hcard : (m.erase v).card + 1 = m.card := Multiset.card_erase_add_one hv
  have hfv : (m.count v)! = m.count v * ((m.count v) - 1)! :=
    (Nat.mul_factorial_pred (Nat.one_le_iff_ne_zero.mp hc)).symm
  have hfcard : (m.card)! = m.card * ((m.erase v).card)! := by
    rw [← hcard, Nat.factorial_succ]
  have hPpos : 0 < ((m.count v) - 1)! * P := by positivity
  apply Nat.eq_of_mul_eq_mul_left hPpos
  calc ((m.count v - 1)! * P) * (m.count v * m.countPerms)
      = (m.count v * (m.count v - 1)! * P) * m.countPerms := by ring
    _ = ((m.count v)! * P) * m.countPerms := by rw [hfv]
    _ = (m.card)! := specm
    _ = m.card * ((m.erase v).card)! := hfcard
    _ = m.card * (((m.count v) - 1)! * P * (m.erase v).countPerms) := by rw [spece]
    _ = ((m.count v - 1)! * P) * (m.card * (m.erase v).countPerms) := by ring

/-- **Value-erasure recursion for `countPerms`:** for `m ≠ 0`,
`countPerms m = ∑_{v ∈ m.toFinset} countPerms (m.erase v)`.  This mirrors the position-peeling
recursion of the fiber count.  Obtained by summing `count_mul_countPerms` over `m.toFinset` and
cancelling `card m > 0`. -/
theorem countPerms_eq_sum_erase (m : Multiset ℕ) (hm : m ≠ 0) :
    m.countPerms = ∑ v ∈ m.toFinset, (m.erase v).countPerms := by
  have hcard : 0 < m.card := Multiset.card_pos.mpr hm
  apply Nat.eq_of_mul_eq_mul_left hcard
  rw [Finset.mul_sum]
  calc m.card * m.countPerms
      = (∑ v ∈ m.toFinset, m.count v) * m.countPerms := by rw [sum_count_self]
    _ = ∑ v ∈ m.toFinset, m.count v * m.countPerms := by rw [Finset.sum_mul]
    _ = ∑ v ∈ m.toFinset, m.card * (m.erase v).countPerms :=
          Finset.sum_congr rfl
            (fun v hv => count_mul_countPerms m v (Multiset.mem_toFinset.mp hv))

/-- **General fiber-cardinality identity (over an arbitrary index finset `s`).**
The number of weak compositions `l : ι →₀ ℕ` supported on `s` and summing to `m.sum` whose
*value-multiset* over `s` equals a fixed bag `m` (of cardinality `#s`) equals
`Multiset.countPerms m`.

Proof: induction on `s`.  The empty case forces `m = 0` (so `countPerms = 1`).  For
`insert a s`, partition the fiber by the value `l a = v` (`Finset.card_eq_sum_card_fiberwise`):
each block bijects (`Finset.card_bij'` via `Finsupp.erase a` / `Finsupp.update · a v`) with the
fiber of `m.erase v` over `s`, matching `countPerms_eq_sum_erase` term-by-term. -/
theorem fiberCard_eq_countPerms_gen {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ (m : Multiset ℕ), m.card = s.card →
      (#{l ∈ finsuppAntidiag s m.sum | valueMultiset s l = m}) = Multiset.countPerms m := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro m hm
    rw [Finset.card_empty, Multiset.card_eq_zero] at hm
    subst hm
    simp [valueMultiset, Multiset.countPerms_zero]
  | insert a s ha ih =>
    intro m hm
    have hmne : m ≠ 0 := by
      rw [Ne, ← Multiset.card_eq_zero, hm, Finset.card_insert_of_notMem ha]; omega
    have hmaps : ((↑{l ∈ finsuppAntidiag (insert a s) m.sum | valueMultiset (insert a s) l = m} :
        Finset (ι →₀ ℕ)) : Set (ι →₀ ℕ)).MapsTo (fun l => l a) ↑m.toFinset := by
      intro l hl
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
        Multiset.mem_toFinset] at hl ⊢
      obtain ⟨_, hvm⟩ := hl
      rw [valueMultiset_insert a s ha] at hvm
      have : l a ∈ (l a) ::ₘ valueMultiset s l := Multiset.mem_cons_self _ _
      rwa [hvm] at this
    rw [Finset.card_eq_sum_card_fiberwise hmaps, countPerms_eq_sum_erase m hmne]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [Multiset.mem_toFinset] at hv
    have herasecard : (m.erase v).card = s.card := by
      rw [Multiset.card_erase_of_mem hv, hm, Finset.card_insert_of_notMem ha]; simp
    rw [← ih (m.erase v) herasecard]
    apply Finset.card_bij'
      (i := fun l _ => Finsupp.erase a l)
      (j := fun l' _ => Finsupp.update l' a v)
    · -- `Finsupp.erase a l` lands in the `m.erase v` fiber over `s`
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hl
      obtain ⟨⟨⟨_, hsupp⟩, hvm⟩, hla⟩ := hl
      rw [valueMultiset_insert a s ha, hla] at hvm
      have hvms : valueMultiset s l = m.erase v := by
        rw [← hvm, Multiset.erase_cons_head]
      simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← valueMultiset_sum s (Finsupp.erase a l), valueMultiset_erase_notMem a s ha, hvms]
      · rw [Finsupp.support_erase]
        exact (Finset.erase_subset_erase a hsupp).trans (by rw [Finset.erase_insert ha])
      · rw [valueMultiset_erase_notMem a s ha, hvms]
    · -- `Finsupp.update l' a v` lands back in the `l a = v` block over `insert a s`
      intro l' hl'
      simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hl'
      obtain ⟨⟨_, hsupp⟩, hvm⟩ := hl'
      have hvms_s : valueMultiset s (l'.update a v) = valueMultiset s l' := by
        unfold valueMultiset
        refine Multiset.map_congr rfl (fun i hi => ?_)
        rw [Finsupp.update_apply, if_neg (ne_of_mem_of_not_mem hi ha)]
      have hvm_full : valueMultiset (insert a s) (l'.update a v) = m := by
        rw [valueMultiset_insert a s ha, Finsupp.update_apply, if_pos rfl, hvms_s, hvm,
            Multiset.cons_erase hv]
      simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag]
      refine ⟨⟨⟨?_, ?_⟩, hvm_full⟩, ?_⟩
      · rw [← valueMultiset_sum (insert a s) (l'.update a v), hvm_full]
      · exact (Finsupp.support_update_subset _ _).trans (Finset.insert_subset_insert a hsupp)
      · rw [Finsupp.update_apply, if_pos rfl]
    · -- left inverse: `update (erase a l) a v = l` (using `l a = v`)
      intro l hl
      simp only [Finset.mem_filter] at hl
      ext i
      rw [Finsupp.update_apply]
      by_cases h : i = a
      · subst h; rw [if_pos rfl, hl.2]
      · rw [if_neg h, Finsupp.erase_ne h]
    · -- right inverse: `erase a (update l' a v) = l'` (using `l' a = 0`)
      intro l' hl'
      simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hl'
      obtain ⟨⟨_, hsupp⟩, _⟩ := hl'
      have hl'a : l' a = 0 := Finsupp.notMem_support_iff.mp (fun hc => ha (hsupp hc))
      ext i
      rw [Finsupp.erase_apply]
      by_cases h : i = a
      · subst h; rw [if_pos rfl, hl'a]
      · rw [if_neg h, Finsupp.update_apply, if_neg h]

/-- **Fiber-cardinality = multinomial of multiplicities (PROVEN).**

The number of weak compositions `l : range k →₀ ℕ` with `∑ l = t` realizing a fixed
value-multiset `m` (so `m` has `card = k`, `sum = t`) equals `Multiset.countPerms m`, the
number of distinct orderings of the bag `m` over the `k` ordered slots (zeros included) —
i.e. the `Nat.multinomial` of `m`'s multiplicities.  This is the load-bearing combinatorial
identity that turns the fiber-card weight of `compositionSum_eq_valueMultisetSum` into the
`prefactor`/`multinomial` of `(A.1)`.  Specialization of `fiberCard_eq_countPerms_gen` to
`s = range k` (using `#(range k) = k`). -/
theorem fiberCard_eq_countPerms {k t : ℕ} (m : Multiset ℕ)
    (hcard : m.card = k) (hsum : m.sum = t) :
    (#{l ∈ finsuppAntidiag (range k) t | valueMultiset (range k) l = m})
      = Multiset.countPerms m := by
  subst hsum
  exact fiberCard_eq_countPerms_gen (range k) m (by rw [hcard, Finset.card_range])

/-- Compatibility alias for the formerly-staged name (now **proven**, no `sorry`):
identical statement to `fiberCard_eq_countPerms`.  Kept so downstream references to the
original staged identifier continue to resolve. -/
theorem fiberCard_eq_countPerms_staged {k t : ℕ} (m : Multiset ℕ)
    (hcard : m.card = k) (hsum : m.sum = t) :
    (#{l ∈ finsuppAntidiag (range k) t | valueMultiset (range k) l = m})
      = Multiset.countPerms m :=
  fiberCard_eq_countPerms m hcard hsum

/-- **L5 — `compositionSum` in `Nat.multinomial`/`countPerms` (partition) form.**

The full regrouping promised by the staged residual: feeding the now-proven fiber-cardinality
identity `fiberCard_eq_countPerms_gen` into `compositionSum_eq_valueMultisetSum` (L4) replaces
the *opaque* fiber-cardinality weight `#{l | valueMultiset s l = m}` by the explicit
`Multiset.countPerms m` (the `Nat.multinomial` of `m`'s multiplicities).  The order-`t`
weak-composition sum thus equals the sum, over the distinct value-multisets `m`, of
`countPerms m • (m.map b).prod` — i.e. `∑_m (mult. of m) · ∏ β^λ`, the partition/`(A.1)` form. -/
theorem compositionSum_eq_partitionSum {ι : Type*} [DecidableEq ι]
    {R : Type*} [CommSemiring R] (s : Finset ι) (t : ℕ) (b : ℕ → R) :
    ∑ l ∈ finsuppAntidiag s t, ∏ i ∈ s, b (l i)
      = ∑ m ∈ (finsuppAntidiag s t).image (valueMultiset s),
          (Multiset.countPerms m) • ((m.map b).prod) := by
  rw [compositionSum_eq_valueMultisetSum s t b]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_image] at hm
  obtain ⟨l, hl, rfl⟩ := hm
  rw [Finset.mem_finsuppAntidiag] at hl
  have hsum : (valueMultiset s l).sum = t := by rw [valueMultiset_sum]; exact hl.1
  rw [← hsum, fiberCard_eq_countPerms_gen s (valueMultiset s l) (by rw [valueMultiset_card])]

/-- **Coefficient of `φ^k` in `countPerms`/partition form.**  The `coeff_pow` corollary of
`compositionSum_eq_partitionSum` with `b j := coeff j φ`, `s = range k`: the `n`-th coefficient
of `φ^k` equals `∑_m countPerms m • (m.map (coeff · φ)).prod` over the distinct value-multisets
`m` of weak compositions of `n` into `k` parts.  This is `coeff_pow_eq_valueMultisetSum` with the
opaque fiber weight replaced by the explicit multinomial `countPerms m`. -/
theorem coeff_pow_eq_partitionSum {R : Type*} [CommSemiring R] (k n : ℕ) (φ : R⟦X⟧) :
    coeff n (φ ^ k)
      = ∑ m ∈ (finsuppAntidiag (range k) n).image (valueMultiset (range k)),
          (Multiset.countPerms m) • ((m.map (fun j => coeff j φ)).prod) := by
  rw [coeff_pow_eq_compositionSum k n φ]
  exact compositionSum_eq_partitionSum (range k) n (fun j => coeff j φ)

end FiberCard

/-! ## Axiom audit (recorded 2026-06-05; refreshed after fiber-card closure)

This file is now **fully `sorry`-free**.  In-file `#print axioms` confirmed every declaration
(`valueMultiset_card`, `valueMultiset_sum`, `prod_eq_multiset_value_prod`,
`compositionSum_eq_valueMultisetSum`, `compositionSum_example`, `coeff_subst_eq_finset_sum`,
`coeff_pow_eq_compositionSum`, `coeff_pow_eq_valueMultisetSum`, and the FiberCard block:
`valueMultiset_insert`, `valueMultiset_erase_notMem`, `countPerms_eq_multinomial`,
`countPerms_erase_eq_multinomial`, `sum_count_self`, `sum_count_erase`, `count_mul_countPerms`,
`countPerms_eq_sum_erase`, `fiberCard_eq_countPerms_gen`, `fiberCard_eq_countPerms`,
`compositionSum_eq_partitionSum`, `coeff_pow_eq_partitionSum`) depends only on
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool`
(the `decide` witnesses are kernel-checked, not native).  The formerly-staged
`fiberCard_eq_countPerms_staged` is now proven (renamed `fiberCard_eq_countPerms`). -/

end ArkLib.PowerSeriesComposition

-- Axiom audit: every claimed-done declaration rests only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.PowerSeriesComposition.coeff_subst_eq_finset_sum
#print axioms ArkLib.PowerSeriesComposition.coeff_pow_eq_compositionSum
#print axioms ArkLib.PowerSeriesComposition.coeff_pow_eq_valueMultisetSum
#print axioms ArkLib.PowerSeriesComposition.fiberCard_eq_countPerms
#print axioms ArkLib.PowerSeriesComposition.coeff_pow_eq_partitionSum
