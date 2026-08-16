/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# The antipodal-pairing uniqueness ENGINE on the distinct-class locus (#407 lower companion)

The char-0 energy LOWER bound `E_r(μ_n) ≥ (2r−1)‼·(n/2)_r·2^r` is the dual of the proven UPPER
bound `zeroSumCount_le_pairings` (which uses `Finset.card_biUnion_le`, the SUB-additive cover).
The lower direction needs the GENUINE `Finset.card_biUnion` (the additive, disjoint version), which
requires the per-pairing antipodal-consistent image sets to be PAIRWISE DISJOINT across distinct
pairings `σ`. The reports (czlower `19d3fb231`, persigma `d4659db2f`) isolated this disjointness as
the remaining brick but neither landed it, it was probe-verified only.

This file lands the **combinatorial engine** of that disjointness, axiom-clean and field-general:
on the *distinct-class generic locus*, where the negative `−c i` of each coordinate is attained at
a UNIQUE index, the antipodal pairing `σ` (a fixed-point-free involution with `c (σ i) = −c i`) is
**uniquely determined by `c`**. Hence two pairings that both antipodally pair the same generic `c`
are equal, which is exactly the per-`σ` image disjointness:

> `antipodalPairing_forced` :  on the unique-negative locus, `c (σ i) = −c i` forces `σ i` = the
>   unique index `j` with `c j = −c i`;
> `antipodalPairing_unique_of_uniqueNeg` :  two fixed-point-free involutions `σ, τ` that both
>   antipodally pair a unique-negative-locus tuple `c` are EQUAL (`σ = τ`);
> `genericAntipodal_pairwiseDisjoint` :  the per-`σ` antipodal-consistent sets, restricted to the
>   unique-negative (generic) locus, are PAIRWISE DISJOINT across distinct pairings `σ`, the exact
>   `Finset.card_biUnion` disjointness hypothesis for the lower-bound assembly.

**Mechanism.** `c (σ i) = −c i` says `σ i` is *an* index whose `c`-value equals `−c i`. On the
generic locus that index is UNIQUE, so `σ i` is forced to equal it. Thus `σ` is a function of `c`
alone (independent of which involution you started with), giving uniqueness, hence disjointness.

**Probe.** `scripts/probes/probe_sigma_unique_distinct_class.py`, for every distinct-class
antipodally-paired tuple (`n ∈ {4,8}`, `r ∈ {1,2,3}`, all pairings), the pairing `σ` is UNIQUE
(2880 tuples checked at `(n,r)=(8,3)`).

**Honest scope (rules 1, 3, 6).** This is the disjointness ENGINE, the unique-`σ` forcing and the
`PairwiseDisjoint` consequence, formalized from the explicit generic (unique-negative) hypothesis.
It is the precise `card_biUnion` disjointness brick the lower-bound assembly needs; it does NOT by
itself assemble the full `(2r−1)‼·(n/2)_r·2^r` count (that still needs the per-`σ` generic count
`(n/2)_r·2^r` welded in via `card_biUnion`, and the verification that `μ_{2^k}` realizes the
unique-negative locus on the generic stratum). Negation-closed / no-2-torsion combinatorics, NOT
thinness-essential, does NOT close CORE. Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.AntipodalSigmaUnique

open ArkLib.ProximityGap.NegationClosedWalk

variable {F : Type*} [Field F] [DecidableEq F]

/-- The **unique-negative (generic) locus** predicate for a tuple `c : Fin (2r) → F`: for every
coordinate `i`, the value `−c i` is attained at a UNIQUE index. This is the field-general form of
the "distinct antipodal class" condition (each antipodal class `{g, −g}` of a generic `μ_{2^k}`
tuple is used exactly once as `+` and once as `−`, so `−c i` has a unique witness). -/
def UniqueNeg {r : ℕ} (c : Fin (2 * r) → F) : Prop :=
  ∀ i, ∃! j, c j = - c i

omit [DecidableEq F] in
/-- **The forcing lemma.** On the unique-negative locus, an antipodal involution `σ` (satisfying
`c (σ i) = −c i`) sends `i` to THE unique index `j` with `c j = −c i`. Hence `σ i` is a function of
`c` alone, independent of which `σ` you started with. -/
theorem antipodalPairing_forced {r : ℕ} {c : Fin (2 * r) → F} (hc : UniqueNeg c)
    {σ : Equiv.Perm (Fin (2 * r))} (hσ : ∀ i, c (σ i) = - c i) (i : Fin (2 * r)) :
    σ i = (hc i).choose := by
  -- `(hc i).choose` is the unique index with `c · = −c i`; `σ i` also satisfies that equation,
  -- so by the uniqueness clause of `∃!` they coincide.
  exact (hc i).choose_spec.2 (σ i) (hσ i)

omit [DecidableEq F] in
/-- **The pairing is uniquely determined.** Two permutations `σ, τ` that both antipodally pair the
same unique-negative-locus tuple `c` agree as functions, hence are equal. (No involution or
fixed-point-free hypothesis is needed, the unique-negative locus alone forces the value.) -/
theorem antipodalPairing_unique_of_uniqueNeg {r : ℕ} {c : Fin (2 * r) → F} (hc : UniqueNeg c)
    {σ τ : Equiv.Perm (Fin (2 * r))}
    (hσ : ∀ i, c (σ i) = - c i) (hτ : ∀ i, c (τ i) = - c i) : σ = τ := by
  apply Equiv.Perm.ext
  intro i
  rw [antipodalPairing_forced hc hσ i, antipodalPairing_forced hc hτ i]

/-- The antipodal-consistent set for a fixed pairing `σ`, restricted to the generic
(unique-negative) locus: tuples in `G^{2r}` that are antipodally `σ`-paired AND lie on the
unique-negative locus. -/
noncomputable def genericAntipodalSet {r : ℕ} (G : Finset F) (σ : Equiv.Perm (Fin (2 * r))) :
    Finset (Fin (2 * r) → F) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter
    (fun c => (∀ i, c (σ i) = - c i) ∧ UniqueNeg c)

/-- A tuple lies in two distinct pairings' generic antipodal sets only if the pairings are equal,
so on the generic locus the per-`σ` sets do not share any tuple unless `σ = τ`. -/
theorem genericAntipodalSet_inter_eq {r : ℕ} (G : Finset F)
    {σ τ : Equiv.Perm (Fin (2 * r))}
    {c : Fin (2 * r) → F} (hcσ : c ∈ genericAntipodalSet G σ) (hcτ : c ∈ genericAntipodalSet G τ) :
    σ = τ := by
  simp only [genericAntipodalSet, Finset.mem_filter] at hcσ hcτ
  exact antipodalPairing_unique_of_uniqueNeg hcσ.2.2 hcσ.2.1 hcτ.2.1

/-- **The `card_biUnion` disjointness brick.** Over any finite index set `Pairs` of permutations,
the per-`σ` generic antipodal sets are PAIRWISE DISJOINT (distinct `σ` ⟹ disjoint generic sets).
This is exactly the hypothesis `Finset.card_biUnion` needs to turn the SUB-additive cover bound
(used in the proven UPPER `zeroSumCount_le_pairings`) into the EXACT additive sum required by the
LOWER bound `E_r ≥ Σ_σ (n/2)_r·2^r = (2r−1)‼·(n/2)_r·2^r`. -/
theorem genericAntipodal_pairwiseDisjoint {r : ℕ} (G : Finset F)
    (Pairs : Finset (Equiv.Perm (Fin (2 * r)))) :
    (Pairs : Set (Equiv.Perm (Fin (2 * r)))).PairwiseDisjoint (genericAntipodalSet G) := by
  intro σ _ τ _ hστ
  rw [Function.onFun, Finset.disjoint_left]
  intro c hcσ hcτ
  exact hστ (genericAntipodalSet_inter_eq G hcσ hcτ)

/-- **The exact lower assembly skeleton.** Given a constant per-`σ` generic count `m` (i.e. each
generic antipodal set over a pairing in `Pairs` has card exactly `m`), the union over `Pairs` has
card EXACTLY `(#Pairs)·m`, by `Finset.card_biUnion` with the disjointness brick. With
`Pairs = {fixed-point-free involutions}` (count `(2r−1)‼` by `pairings_card_eq_doubleFactorial`)
and `m = (n/2)_r·2^r` this is the full super-diagonal lower count. -/
theorem genericBiUnion_card_eq {r : ℕ} (G : Finset F)
    (Pairs : Finset (Equiv.Perm (Fin (2 * r)))) (m : ℕ)
    (hm : ∀ σ ∈ Pairs, (genericAntipodalSet G σ).card = m) :
    (Pairs.biUnion (genericAntipodalSet G)).card = Pairs.card * m := by
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl hm, Finset.sum_const, smul_eq_mul]
  · intro σ hσ τ hτ hστ
    exact genericAntipodal_pairwiseDisjoint G Pairs hσ hτ hστ

/-- **Lower bound on the zero-sum count from the generic stratum.** The zero-sum count of `2r`-tuples
of `G` is at least the cardinality of the generic-antipodal union over any set of pairings whose
generic antipodal sets are zero-sum (antipodally paired ⟹ each pair `(i, σ i)` cancels). Concretely,
if every generic antipodal tuple over `Pairs` is zero-sum, the union (card `(#Pairs)·m` by
`genericBiUnion_card_eq`) injects into the zero-sum set, giving `(#Pairs)·m ≤ Z_{2r}(G)`. -/
theorem genericBiUnion_card_le_zeroSumCount {r : ℕ} (G : Finset F)
    (Pairs : Finset (Equiv.Perm (Fin (2 * r))))
    (hpair : ∀ σ ∈ Pairs, IsPairing σ) :
    (Pairs.biUnion (genericAntipodalSet G)).card ≤ zeroSumCount G (2 * r) := by
  classical
  unfold zeroSumCount
  refine Finset.card_le_card ?_
  intro c hc
  rw [Finset.mem_biUnion] at hc
  obtain ⟨σ, hσP, hcσ⟩ := hc
  simp only [genericAntipodalSet, Finset.mem_filter] at hcσ
  obtain ⟨hcmem, hcanti, _⟩ := hcσ
  rw [Finset.mem_filter]
  refine ⟨hcmem, ?_⟩
  -- antipodally `σ`-paired ⟹ zero sum: pair each `i` with `σ i`, the two cancel
  have hσ : IsPairing σ := hpair σ hσP
  -- reindex the sum by the involution-pairing; each lower slot + its partner = c i + (−c i) = 0
  have hinv : Function.Involutive σ := hσ.1
  -- ∑ c = ∑_{i} c i; split via the σ-orbit pairing using the existing transversal machinery
  -- Use: ∑ over univ = ∑ over lowerHalf of (c i + c (σ i)) = ∑ over lowerHalf of 0
  set L := lowerHalf σ with hL
  set U := Finset.univ.filter (fun i => σ i < i) with hU
  have hmaps : ∀ i ∈ L, σ i ∈ U := by
    intro i hi
    simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hinv i]; exact hi
  have hinjOn : Set.InjOn σ L := fun a _ b _ h => σ.injective h
  have himg : L.image σ = U := by
    apply Finset.Subset.antisymm
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact hmaps i hi
    · intro j hj
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine Finset.mem_image.mpr ⟨σ j, ?_, hinv j⟩
      simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hinv j]; exact hj
  have hdisj : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro i hiL hiU
    simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hiL
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hiU
    exact absurd hiL (not_lt.mpr (le_of_lt hiU))
  have hunion : L ∪ U = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    rw [Finset.mem_union]
    rcases lt_trichotomy i (σ i) with h | h | h
    · left; simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    · exact absurd h.symm (hσ.2 i)
    · right; simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
  -- ∑_univ c = ∑_L c + ∑_U c = ∑_L c + ∑_L c∘σ = ∑_L (c i + c (σ i)) = ∑_L 0 = 0
  have hsplit : ∑ i, c i = (∑ i ∈ L, c i) + ∑ i ∈ U, c i := by
    rw [← Finset.sum_union hdisj, hunion]
  have hUsum : ∑ i ∈ U, c i = ∑ i ∈ L, c (σ i) := by
    rw [← himg, Finset.sum_image hinjOn]
  rw [hsplit, hUsum, ← Finset.sum_add_distrib]
  have hzero : ∀ i ∈ L, c i + c (σ i) = 0 := by
    intro i _
    rw [hcanti i]; ring
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]

end ProximityGap.Frontier.AntipodalSigmaUnique

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AntipodalSigmaUnique.antipodalPairing_unique_of_uniqueNeg
#print axioms ProximityGap.Frontier.AntipodalSigmaUnique.genericAntipodal_pairwiseDisjoint
#print axioms ProximityGap.Frontier.AntipodalSigmaUnique.genericBiUnion_card_eq
#print axioms ProximityGap.Frontier.AntipodalSigmaUnique.genericBiUnion_card_le_zeroSumCount
