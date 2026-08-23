/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031DilationOrbitReduction

/-!
# I031 — the global orbit-count: `Fₚ*` partitions into exactly `(q−1)/n` `μ_n`-orbits (#444)

The dilation-orbit reduction (`I031DilationOrbitReduction.lean`) proves the per-coset facts the
metric-entropy collapse needs:

* each `μ_n`-coset `b•μ_n` has **size exactly `n`** (`coset_card_eq_n`),
* the action is **free** on `Fₚ*` (`dilation_free`),
* distinct cosets are **disjoint** (`coset_disjoint_of_ratio_notMem`).

What was *asserted but never landed* is the **global capstone**: that these size-`n` orbits
genuinely tile the `q−1` nonzero frequencies into **exactly `(q−1)/n` blocks**. The
`PeriodOrbitQuotientReduction` consumer explicitly says *"the relevant index set has size `(q−1)/|G|`
**once a transversal is supplied**"* — but the transversal-cardinality fact itself was open.

This file lands it. The mechanism is pure partition combinatorics: if a `Finset` `S` is the disjoint
union of the blocks of a partition family and **every block has the same card `n`**, then the number
of blocks is `S.card / n`. Instantiated at `S = Fₚ*` (the `q−1` nonzero frequencies) and the
`μ_n`-cosets (all of card `n`, by `coset_card_eq_n`), this gives the **exact `(q−1)/n` orbit count**
the I031 chaining route consumes — the machine-checked statement of the `log p → log(p/n)`
metric-entropy collapse at the level of the index-set cardinality.

**Probe (validated before formalizing).** `scripts/probes/probe_i031_orbit_count_partition.py`:
for `μ_n = ⟨g^{(p−1)/n}⟩ ⊆ Fₚ*` at prize-regime primes (`n = 2^a`, `n ∣ p−1`, `p ≫ n³`, n=4..64), the
`μ_n`-orbits of `Fₚ*` number **exactly `(p−1)/n`**, all of size `n`, free, disjoint, and covering —
verified exhaustively (e.g. `n=64, p=262337`: `4099 = (p−1)/64` orbits, all size 64). NEVER `n=q−1`.

**Honesty (rules 3, 6).** This is the EXACT structural orbit-count of the prize index set; it is NOT a
CORE closure and NOT thinness-essential (a free action of an order-`n` group on a set of size `q−1`
always has `(q−1)/n` orbits, independent of thickness). Its VALUE is frontier-movement: it lands the
named-open transversal-cardinality capstone of the I031 reduction, completing the
`log p → log(p/n)` index collapse at the cardinality level. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.I031DilationOrbitReduction

/-! ### Generic partition-cardinality lemma (constant block size ⟹ `card / n` blocks)

The combinatorial heart, stated abstractly so it is reusable: a partition of `S` into the fibers of a
"block-label" map `f : F → ι`, all of constant card `n`, has exactly `S.card / n` distinct labels. -/

/-- **Constant-fiber partition count.** If `S : Finset F` is partitioned by a label map `f : F → ι`
into fibers (the sets `{x ∈ S | f x = i}` for `i ∈ S.image f`) and **every nonempty fiber has card
`n`** with `0 < n`, then the number of distinct labels is `S.card / n`. This is the abstract
orbit-count: `#orbits = |S| / (orbit size)`. -/
theorem image_card_eq_card_div {F ι : Type*} [DecidableEq F] [DecidableEq ι]
    {S : Finset F} {f : F → ι} {n : ℕ} (hn : 0 < n)
    (hfiber : ∀ i ∈ S.image f, (S.filter (fun x => f x = i)).card = n) :
    (S.image f).card = S.card / n := by
  -- `|S| = Σ_{i ∈ image f} |fiber i| = Σ_{i} n = |image f| * n`.
  have hsum : S.card = (S.image f).card * n := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S.image f)
        (fun x hx => Finset.mem_image_of_mem f hx)]
    rw [Finset.sum_congr rfl (fun i hi => hfiber i hi)]
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- divide.
  rw [hsum, Nat.mul_div_cancel _ hn]

/-! ### Instantiation: the `μ_n`-cosets of `Fₚ*`

We label each nonzero `b` by its coset `b•μ_n` (as a `Finset F`); the fibers are exactly the cosets,
each of card `n` by `coset_card_eq_n`. So the number of distinct cosets is `(q−1)/n`. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonzero frequencies `Fₚ* = univ \ {0}`. -/
def nonzeroFreqs (F : Type*) [Fintype F] [DecidableEq F] [Zero F] : Finset F :=
  (Finset.univ : Finset F).erase 0

@[simp] theorem mem_nonzeroFreqs {b : F} : b ∈ nonzeroFreqs F ↔ b ≠ 0 := by
  simp [nonzeroFreqs]

/-- The card of `Fₚ*` is `q − 1`. -/
theorem nonzeroFreqs_card : (nonzeroFreqs F).card = Fintype.card F - 1 := by
  rw [nonzeroFreqs, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]

/-- **The coset label of a nonzero frequency.** `cosetLabel n b := b • μ_n` (the left coset as a
`Finset F`). Two nonzero frequencies share a label iff they lie in the same `μ_n`-orbit. -/
noncomputable def cosetLabel (n : ℕ) (b : F) : Finset F := dilate b (nthRootsFinset n (1 : F))

/-- **Membership in one's own coset.** `b ∈ b•μ_n` (since `1 ∈ μ_n`), provided `0 < n`. -/
theorem self_mem_cosetLabel {n : ℕ} (hn : 0 < n) (b : F) : b ∈ cosetLabel n b := by
  rw [cosetLabel, dilate, Finset.mem_image]
  refine ⟨1, ?_, by rw [mul_one]⟩
  rw [mem_nthRootsFinset hn, one_pow]

/-- **Same coset ⟺ same label.** For `b₁ b₂ ≠ 0`, `cosetLabel n b₁ = cosetLabel n b₂` exactly when
they lie in a common `μ_n`-orbit (`b₂ b₁⁻¹ ∈ μ_n`). The contrapositive of
`coset_disjoint_of_ratio_notMem` packaged with self-membership: if the labels are equal then
`b₂ ∈ b₁•μ_n`. -/
theorem ratio_mem_of_cosetLabel_eq {n : ℕ} (hn : 0 < n) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (h : cosetLabel n b₁ = cosetLabel n b₂) : b₂ * b₁⁻¹ ∈ nthRootsFinset n (1 : F) := by
  by_contra hnot
  have hdisj := coset_disjoint_of_ratio_notMem (F := F) hb₁ hb₂ hn hnot
  -- `b₂` lies in both cosets (its own, and `b₁`'s via `h`), contradicting disjointness.
  have h2 : b₂ ∈ cosetLabel n b₂ := self_mem_cosetLabel hn b₂
  have h1 : b₂ ∈ cosetLabel n b₁ := h ▸ h2
  exact (Finset.disjoint_left.mp hdisj h1) h2

/-- **Each coset-fiber of `Fₚ*` has card `n`** (under a primitive `n`-th root). The fiber of the
label map at a label `cosetLabel n b` (for `b ≠ 0`) is exactly the coset `b•μ_n ⊆ Fₚ*`, of card `n`
by `coset_card_eq_n`. -/
theorem coset_fiber_card {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {b : F} (hb : b ≠ 0) :
    ((nonzeroFreqs F).filter (fun x => cosetLabel n x = cosetLabel n b)).card = n := by
  -- the fiber equals the coset `b•μ_n`, then apply `coset_card_eq_n`.
  have hcoset_sub : cosetLabel n b ⊆ nonzeroFreqs F := by
    intro y hy
    rw [cosetLabel, dilate, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_nonzeroFreqs]
    have hxne : x ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hx
    exact mul_ne_zero hb hxne
  have hfilter_eq : (nonzeroFreqs F).filter (fun x => cosetLabel n x = cosetLabel n b)
      = cosetLabel n b := by
    apply Finset.ext
    intro y
    rw [Finset.mem_filter, mem_nonzeroFreqs]
    constructor
    · rintro ⟨hy0, hlabel⟩
      -- `cosetLabel y = cosetLabel b` ⇒ `y ∈ cosetLabel b` via self-membership.
      have : y ∈ cosetLabel n y := self_mem_cosetLabel hn y
      rwa [hlabel] at this
    · intro hy
      have hy0 : y ≠ 0 := by
        have := hcoset_sub hy; rwa [mem_nonzeroFreqs] at this
      refine ⟨hy0, ?_⟩
      -- `y ∈ b•μ_n` ⇒ `y = b * x` with `x ∈ μ_n` ⇒ `y•μ_n = b•μ_n`.
      rw [cosetLabel, dilate, Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      -- `cosetLabel n (b*x) = cosetLabel n b`: dilate by `x ∈ μ_n` absorbs.
      rw [cosetLabel, cosetLabel]
      -- `dilate (b*x) μ_n = dilate b (dilate x μ_n) = dilate b μ_n`.
      have hxμ : dilate x (nthRootsFinset n (1 : F)) = nthRootsFinset n (1 : F) :=
        dilate_self_eq hx
      rw [show dilate (b * x) (nthRootsFinset n (1 : F))
            = dilate b (dilate x (nthRootsFinset n (1 : F))) from ?_, hxμ]
      · -- dilate composition: dilate (b*x) S = dilate b (dilate x S)
        ext z
        simp only [dilate, Finset.mem_image]
        constructor
        · rintro ⟨w, hw, rfl⟩; exact ⟨x * w, ⟨w, hw, rfl⟩, by ring⟩
        · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, by ring⟩
  rw [hfilter_eq, cosetLabel, coset_card_eq_n hζprim hb]

/-- **The global orbit count: `Fₚ*` partitions into exactly `(q−1)/n` `μ_n`-orbits.** Under a
primitive `n`-th root of unity (so `|μ_n| = n`), the number of distinct `μ_n`-cosets among the `q−1`
nonzero frequencies is **exactly `(Fintype.card F − 1)/n`**. This is the I031 metric-entropy
collapse at the index-set cardinality level: the sup over `q−1` frequencies reduces to a sup over
`(q−1)/n` orbit representatives. (`PeriodOrbitQuotientReduction`'s "transversal of size
`(q−1)/|G|`" is now a proven cardinality, not an assumed one.) -/
theorem orbit_count {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) :
    ((nonzeroFreqs F).image (cosetLabel n)).card = (Fintype.card F - 1) / n := by
  rw [← nonzeroFreqs_card]
  apply image_card_eq_card_div hn
  intro i hi
  -- `i = cosetLabel n b` for some `b ∈ Fₚ*`; the fiber card is `n` by `coset_fiber_card`.
  rw [Finset.mem_image] at hi
  obtain ⟨b, hb, rfl⟩ := hi
  rw [mem_nonzeroFreqs] at hb
  exact coset_fiber_card hζprim hn hb

end ArkLib.ProximityGap.I031DilationOrbitReduction
