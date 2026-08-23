/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal

/-!
# Issue #407 (T3) — the odd-moment law: no odd-length all-positive vanishing sum of `2^k`-th roots

**Target.** In characteristic zero, **every vanishing multiset of `2^k`-th roots of unity has
even cardinality**. Equivalently: there is *no odd-length all-positive (multiplicity-one
weighted) vanishing sum of `2^μ`-th roots of unity*.

**Why this is the T3 core.** The worst incomplete Gauss sum / additive-energy programme studies
the period power sums `T_{2k+1} = Σ_{b≠0} S_b^{2k+1}`. Expanding `S_b^{2k+1}` over the dyadic
subgroup `μ_n` (`n = 2^μ`) collects, at each `b`, the count of `(2k+1)`-tuples of `μ_n`-elements
summing to zero — an **odd-length all-positive vanishing sum**. The structure theorem of
Lam–Leung at the prime 2 says every vanishing sum of `2^μ`-th roots is a `ℕ`-combination of the
two-term antipodal relations `x + (-x) = 0`
(`LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`: `count z = count (-z)`).
Antipodal pairing forces **even** length, since `-z ≠ z` for any root of
unity of order `> 1`. Hence `T_{2k+1} = 0` has no genuine (multiplicity-positive) contributors of
odd length, which is the char-0 input to the odd-moment law `Σ_i η_i^{2k+1} = -n^{2k}`.

**This brick is character-sum-free and combinatorial** — it does NOT touch the BGK worst-incomplete
-Gauss-sum wall (that wall is about the *even* moments `E_r` / `T_{2r}` at depth `r ≈ log q`). The
odd-moment vanishing is an exact structural identity provable from the Lam–Leung antipodal pairing.

## Main results

* `even_sum_of_fpf_involution` — durable combinatorial lemma: a `ℕ`-valued sum over a finset
  closed under a fixed-point-free involution `g` with `f ∘ g = f` is even.
* `neg_ne_self_of_pow_two_pow_eq_one` — for a `2^k`-th root of unity `z` in a `CharZero` field,
  `-z ≠ z`.
* `even_card_of_vanishing_dyadic_multiset` — **the T3 core**: a multiset of `2^k`-th roots of
  unity with `M.sum = 0` has `Even M.card`.
* `no_odd_length_allpositive_vanishing_sum` — the contrapositive packaging: an **odd**-cardinality
  multiset of `2^k`-th roots of unity cannot have vanishing sum.
-/

namespace DyadicOddMomentVanishing

open Finset

/-- **Durable combinatorial lemma.** A `ℕ`-valued sum over a finset `s` closed under a
fixed-point-free involution `g`, with `f` invariant under `g`, is even: the finset partitions into
two-element orbits `{x, g x}`, each contributing `2 · f x`. -/
theorem even_sum_of_fpf_involution {α : Type*}
    (s : Finset α) (g : α → α)
    (hg : ∀ x ∈ s, g x ∈ s) (hgg : ∀ x ∈ s, g (g x) = x)
    (hfix : ∀ x ∈ s, g x ≠ x) (f : α → ℕ) (hf : ∀ x ∈ s, f (g x) = f x) :
    Even (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · have hga : g a ∈ s := hg a ha
      have hne : g a ≠ a := hfix a ha
      set t := (s.erase a).erase (g a) with ht
      have hgamem : g a ∈ s.erase a := Finset.mem_erase.mpr ⟨hne, hga⟩
      have ha_not_t : a ∉ t := by
        rw [ht]; exact fun h => (notMem_erase a s) (Finset.mem_of_mem_erase h)
      have hga_not_t : g a ∉ t := by rw [ht]; exact notMem_erase _ _
      have hsub : t ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have htss : t ⊂ s := ⟨hsub, fun hcon => ha_not_t (hcon ha)⟩
      have hdecomp : s = insert a (insert (g a) t) := by
        rw [ht, Finset.insert_erase hgamem, Finset.insert_erase ha]
      have hmem_t : ∀ x ∈ t, x ∈ s := fun x hx => hsub hx
      have hxne : ∀ x ∈ t, x ≠ a ∧ x ≠ g a := by
        intro x hx
        rw [ht] at hx
        exact ⟨(Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1,
               (Finset.mem_erase.mp hx).1⟩
      have hg_t : ∀ x ∈ t, g x ∈ t := by
        intro x hx
        have hxs := hmem_t x hx
        have hgx_s := hg x hxs
        rw [ht]
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hgx_s⟩⟩
        · intro h
          have hxa : x = a := by
            have := congrArg g h; rwa [hgg x hxs, hgg a ha] at this
          exact (hxne x hx).1 hxa
        · intro h
          have hxga : x = g a := by
            have := congrArg g h; rwa [hgg x hxs] at this
          exact (hxne x hx).2 hxga
      have hIH : Even (∑ x ∈ t, f x) :=
        ih t htss hg_t (fun x hx => hgg x (hmem_t x hx))
          (fun x hx => hfix x (hmem_t x hx)) (fun x hx => hf x (hmem_t x hx))
      rw [hdecomp, Finset.sum_insert (by
            rw [Finset.mem_insert]; exact not_or.mpr ⟨hne.symm, ha_not_t⟩),
          Finset.sum_insert hga_not_t]
      have hfa : f (g a) = f a := hf a ha
      rw [hfa]
      have hrw : f a + (f a + ∑ x ∈ t, f x) = 2 * f a + ∑ x ∈ t, f x := by ring
      rw [hrw]
      exact (Even.add (even_two_mul (f a)) hIH)

variable {L : Type*} [Field L] [CharZero L]

/-- For a `2^k`-th root of unity `z` in a characteristic-zero field, the negation map is
fixed-point-free: `-z ≠ z`. (If `-z = z` then `2z = 0`, but `2 ≠ 0` in `CharZero` and `z ≠ 0`
as a root of unity.) -/
theorem neg_ne_self_of_pow_two_pow_eq_one {z : L} {k : ℕ} (hz : z ^ (2 ^ k) = 1) :
    -z ≠ z := by
  intro h
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, zero_pow (by positivity)] at hz; exact zero_ne_one hz
  have h2z : (2 : L) * z = 0 := by linear_combination -h
  have h2 : (2 : L) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h2z with h2' | hz'
  · exact h2 h2'
  · exact hz0 hz'

/-- **The T3 core (odd-moment vanishing).** In characteristic zero, every multiset of `2^k`-th
roots of unity whose sum vanishes has **even** cardinality.

The negation map `z ↦ -z` is a fixed-point-free involution on `M.toFinset` (membership balance is
`LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`; fixed-point-freeness is
`neg_ne_self_of_pow_two_pow_eq_one`), and `M.count` is constant on each orbit `{z, -z}` (the same
antipodal-balance identity). Hence `M.card = ∑_{z ∈ M.toFinset} M.count z` is even by
`even_sum_of_fpf_involution`. -/
theorem even_card_of_vanishing_dyadic_multiset {k : ℕ} {M : Multiset L}
    (hM : ∀ z ∈ M, z ^ (2 ^ k) = 1) (hsum : M.sum = 0) :
    Even (Multiset.card M) := by
  classical
  -- antipodal count-balance from Lam–Leung at the prime 2
  have hbal : ∀ z : L, M.count z = M.count (-z) :=
    LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero hM hsum
  -- card = ∑_{z ∈ toFinset} count z
  have hcard : Multiset.card M = ∑ z ∈ M.toFinset, M.count z :=
    (Multiset.toFinset_sum_count_eq M).symm
  rw [hcard]
  refine even_sum_of_fpf_involution M.toFinset (fun z => -z) ?_ ?_ ?_ M.count ?_
  · -- toFinset closed under negation
    intro z hz
    rw [Multiset.mem_toFinset, ← Multiset.count_pos] at hz ⊢
    rwa [← hbal z]
  · -- involution
    intro z _; simp
  · -- fixed-point-free
    intro z hz
    rw [Multiset.mem_toFinset] at hz
    exact neg_ne_self_of_pow_two_pow_eq_one (hM z hz)
  · -- count invariant: count (-z) = count z
    intro z _; exact (hbal z).symm

/-- **No odd-length all-positive vanishing sum of `2^k`-th roots of unity** (the contrapositive
packaging of `even_card_of_vanishing_dyadic_multiset`). An odd-cardinality multiset of `2^k`-th
roots of unity cannot have a vanishing sum. This is exactly the statement that the odd-period
power sums `T_{2k+1}` collect no genuine (multiplicity-positive) odd-length contributors — the
char-0 input to the odd-moment law `Σ_i η_i^{2k+1} = -n^{2k}`. -/
theorem no_odd_length_allpositive_vanishing_sum {k : ℕ} {M : Multiset L}
    (hM : ∀ z ∈ M, z ^ (2 ^ k) = 1) (hodd : Odd (Multiset.card M)) :
    M.sum ≠ 0 := by
  intro hsum
  exact (Nat.not_even_iff_odd.mpr hodd) (even_card_of_vanishing_dyadic_multiset hM hsum)

/-- **Length-1 base case of the odd-moment ledger.** A single `2^k`-th root of unity has nonzero
sum: a multiset of `2^k`-th roots of unity with cardinality one cannot vanish. This is the
base case (`card = 1`, odd) of `no_odd_length_allpositive_vanishing_sum`. -/
theorem ne_zero_of_card_one_dyadic {k : ℕ} {M : Multiset L}
    (hM : ∀ z ∈ M, z ^ (2 ^ k) = 1) (hcard : Multiset.card M = 1) :
    M.sum ≠ 0 :=
  no_odd_length_allpositive_vanishing_sum hM (hcard ▸ odd_one)


/-- **Minimal vanishing relation at cardinality two.** A two-element multiset of `2^k`-th roots
of unity whose sum vanishes is an antipodal pair `{z, -z}`. This is the base case of the
Lam–Leung antipodal structure theorem in the dyadic context: the only way two roots of unity can
cancel is `z + (-z) = 0`. -/
theorem card_two_vanishing_antipodal {k : ℕ} {M : Multiset L}
    (hM : ∀ z ∈ M, z ^ (2 ^ k) = 1) (hcard : Multiset.card M = 2) (hsum : M.sum = 0) :
    ∃ z : L, M = {z, -z} := by
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨x, ?_⟩
  have hs : x + y = 0 := by simpa using hsum
  have hy : y = -x := eq_neg_of_add_eq_zero_right hs
  rw [hy]


/-- **Minimal-relation length floor.** A nonzero multiset of `2^k`-th roots of unity whose sum
vanishes has cardinality at least two. This sharpens the even-card law
(`even_card_of_vanishing_dyadic_multiset`, which gives `card = 2c`) by ruling out the empty
case: a genuine (nonempty) vanishing relation among dyadic roots of unity needs at least the
antipodal pair `{z, -z}`. There is no length-1 cancellation (a single root is nonzero), so the
shortest vanishing relation has length exactly two. -/
theorem two_le_card_of_vanishing_dyadic {k : ℕ} {M : Multiset L}
    (hM : ∀ z ∈ M, z ^ (2 ^ k) = 1) (hsum : M.sum = 0) (hne : M ≠ 0) :
    2 ≤ Multiset.card M := by
  have hpos : 0 < Multiset.card M := Multiset.card_pos.mpr hne
  obtain ⟨c, hc⟩ := even_card_of_vanishing_dyadic_multiset hM hsum
  omega


end DyadicOddMomentVanishing
#print axioms DyadicOddMomentVanishing.ne_zero_of_card_one_dyadic
#print axioms DyadicOddMomentVanishing.card_two_vanishing_antipodal
#print axioms DyadicOddMomentVanishing.two_le_card_of_vanishing_dyadic
