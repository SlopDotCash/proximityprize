/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupQuadraticHalving

/-!
# The pencil spike law over smooth subgroups (#357 N3, elementary half)

The M3 probe campaign (`scripts/probes/moments/RESULTS-M3.md`) discovered that the first
agreement-spectrum moment that *sees* the evaluation domain is M3, and that what it measures
is the **pencil census**: for each Möbius involution `x ~ y ⟺ xy − a(x+y) + b = 0`, the
number `t₂` of its 2-element orbits inside the domain. For smooth subgroup domains the probes
found (exactly, at `(q,n) = (41,10), (113,16), (257,16)`):

* a **spike band**: the torus-normalizer pencils `x ↦ c/x` (`c ∈ H`) and `x ↦ −x` sit at
  `t₂ ∈ {(n−2)/2, n/2}`;
* a **noise band**: every other pencil has tiny `t₂` (conjecturally `O(n²/q + 1)`, a
  Weil-type statement);
* a **spectral gap** between the bands that random domains fill in.

This file proves the **elementary half** unconditionally, in ordered-pair form
(`orderedPairCount = 2·t₂`):

* `card_sq_eq_in_subgroup` — over `μ_{2m}` the equation `x² = c` has exactly 2 solutions if
  `c ∈ μ_m` and 0 otherwise (consumer of the round-9 halving keystone
  `sum_comp_sq_eq_two_smul`);
* `inversionPairCount_eq` — **the spike law**: the pencil `x ↦ c/x`, `c ∈ μ_{2m}`, has
  ordered off-diagonal count *exactly* `2m − 2` (`c ∈ μ_m`, i.e. `c` a square in the
  subgroup) or `2m` (non-square) — the probes' `t₂ ∈ {(n−2)/2, n/2}` verbatim;
* `inversionPairCount_eq_zero_of_notMem` — pencils `xy = c` with `c ∉ μ_n` are empty;
* `negationPairCount_eq` — the pencil `x ↦ −x` sits at exactly `2m` ordered pairs;
* `moebius_pair_count_le` — **the universal cap**: every nondegenerate Möbius pencil has
  ordered count `≤ |D|` over any domain. The normalizer spikes therefore sit at (or one
  orbit below) the absolute extremum: the spike band is *extremal*, not merely large.

The **noise half** — non-normalizer pencils are `O(n²/q + 1)` — is genuinely Weil-tier
(character sums of rational functions against subgroup cosets; not in Mathlib): recorded as
the named open surface `PencilNoiseBand`, with the gap statement
`spectral_gap_of_noiseBand` as its wired consumer. The additive pencils `x + y = c`
(`c ≠ 0`) inside that surface are exactly the `|μ_n ∩ (c − μ_n)|` additive-energy quantity
of the #232 open core — the pencil noise band *is* the same open mathematics, reached from
the M3 moments channel.

Everything outside `PencilNoiseBand` is axiom-clean; no `sorry`.

## References

- `scripts/probes/moments/RESULTS-M3.md` (probe verdicts H1/H2/H5/A5, the spectral gap).
- Issue #357 (N3 in the campaign dossier).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial BigOperators

namespace ProximityGap.PencilNormalizerBand

open ArkLib.ProximityGap.Round9SubgroupQuadraticHalving

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ordered off-diagonal solution count of the pencil `x·y = c` inside `μ_n`:
`#{(x,y) ∈ μ_n² : xy = c, x ≠ y}` — equal to `2·t₂` of the involution `x ↦ c/x`. -/
noncomputable def inversionPairCount (n : ℕ) (c : F) : ℕ :=
  (((nthRootsFinset n (1 : F)) ×ˢ (nthRootsFinset n (1 : F))).filter
    fun p => p.1 * p.2 = c ∧ p.1 ≠ p.2).card

/-- The ordered off-diagonal solution count of the negation pencil `x + y = 0` inside
`μ_n` — equal to `2·t₂` of the involution `x ↦ −x`. -/
noncomputable def negationPairCount (K : Type*) [Field K] [DecidableEq K] (n : ℕ) : ℕ :=
  (((nthRootsFinset n (1 : K)) ×ˢ (nthRootsFinset n (1 : K))).filter
    fun p => p.1 + p.2 = 0 ∧ p.1 ≠ p.2).card

/-- Elements of `μ_n` are nonzero. -/
theorem ne_zero_of_mem_nthRoots {n : ℕ} (hn : 0 < n) {x : F}
    (hx : x ∈ nthRootsFinset n (1 : F)) : x ≠ 0 := by
  intro h0
  have hxn : x ^ n = 1 := (mem_nthRootsFinset hn (1 : F)).mp hx
  rw [h0, zero_pow (by omega : n ≠ 0)] at hxn
  exact one_ne_zero hxn.symm

/-- **Square-equation count over the smooth even subgroup.** Over `μ_{2m}` the fiber of
squaring above `c` has exactly two points if `c ∈ μ_m` and is empty otherwise. Direct
consumer of the round-9 halving keystone. -/
theorem card_sq_eq_in_subgroup {m : ℕ} (hm : 0 < m) (h2 : (2 : F) ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 * m)) (c : F) :
    ((nthRootsFinset (2 * m) (1 : F)).filter fun x => x ^ 2 = c).card
      = if c ∈ nthRootsFinset m (1 : F) then 2 else 0 := by
  have h := sum_comp_sq_eq_two_smul hm h2 hζ (fun u => if u = c then (1 : ℕ) else 0)
  rw [Finset.sum_ite_eq' (nthRootsFinset m (1 : F)) c (fun _ => (1 : ℕ))] at h
  rw [← Finset.card_filter] at h
  rw [h]
  by_cases hc : c ∈ nthRootsFinset m (1 : F) <;> simp [hc]

/-- The off-diagonal solutions of `x·y = c` biject (via the first coordinate) with the
subgroup elements that are *not* square roots of `c`. -/
theorem inversionPairCount_eq_card_nonroots {n : ℕ} (hn : 0 < n) {c : F}
    (hc : c ∈ nthRootsFinset n (1 : F)) :
    inversionPairCount n c
      = ((nthRootsFinset n (1 : F)).filter fun x => ¬ x ^ 2 = c).card := by
  classical
  unfold inversionPairCount
  set G := nthRootsFinset n (1 : F) with hG
  have hcn : c ^ n = 1 := (mem_nthRootsFinset hn (1 : F)).mp hc
  apply Finset.card_bij (fun p _ => p.1)
  · -- maps into the non-root filter
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    refine ⟨hp.1.1, fun hsq => ?_⟩
    -- a diagonal-forcing square root contradicts `p.1 ≠ p.2`
    have hp1 : p.1 ≠ 0 := ne_zero_of_mem_nthRoots hn hp.1.1
    apply hp.2.2
    have : p.1 * p.2 = p.1 * p.1 := by
      rw [hp.2.1, ← hsq, pow_two]
    exact (mul_left_cancel₀ hp1 this).symm
  · -- injective: the first coordinate determines the second
    intro p hp q hq hpq
    have hpq' : p.1 = q.1 := hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hp hq
    have hp1 : p.1 ≠ 0 := ne_zero_of_mem_nthRoots hn hp.1.1
    have h1 : p.1 * p.2 = c := hp.2.1
    have h2' : q.1 * q.2 = c := hq.2.1
    rw [← hpq'] at h2'
    exact Prod.ext hpq' (mul_left_cancel₀ hp1 (h1.trans h2'.symm))
  · -- surjective: `x ↦ (x, c·x⁻¹)`
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    have hx0 : x ≠ 0 := ne_zero_of_mem_nthRoots hn hx.1
    have hxn : x ^ n = 1 := (mem_nthRootsFinset hn (1 : F)).mp hx.1
    refine ⟨(x, c * x⁻¹), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hx.1, ?_⟩, ?_, ?_⟩
    · rw [hG, mem_nthRootsFinset hn (1 : F), mul_pow, inv_pow, hcn, hxn, inv_one, mul_one]
    · field_simp
    · intro hdiag
      apply hx.2
      have : x * x = x * (c * x⁻¹) := by rw [← hdiag]
      rw [show x * (c * x⁻¹) = c by field_simp] at this
      rw [pow_two]
      exact this

/-- **The inversion-pencil spike law (ordered form).** For `c ∈ μ_{2m}` the pencil
`x ↦ c/x` over `μ_{2m}` has ordered off-diagonal count exactly `2m − 2` if `c` is a square
in the subgroup (`c ∈ μ_m`) and exactly `2m` otherwise — the probes' normalizer band
`t₂ ∈ {(n−2)/2, n/2}`, now a theorem. -/
theorem inversionPairCount_eq {m : ℕ} (hm : 0 < m) (h2 : (2 : F) ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {c : F} (hc : c ∈ nthRootsFinset (2 * m) (1 : F)) :
    inversionPairCount (2 * m) c
      = if c ∈ nthRootsFinset m (1 : F) then 2 * m - 2 else 2 * m := by
  classical
  have h2m : 0 < 2 * m := by omega
  rw [inversionPairCount_eq_card_nonroots h2m hc]
  have hadd := Finset.card_filter_add_card_filter_not
    (s := nthRootsFinset (2 * m) (1 : F)) (fun x => x ^ 2 = c)
  have hsq := card_sq_eq_in_subgroup hm h2 hζ c
  have hcard := hζ.card_nthRootsFinset
  by_cases hcm : c ∈ nthRootsFinset m (1 : F) <;> simp only [hcm, if_true, if_false] at hsq <;>
    simp only [hcm, if_true, if_false] <;> omega

/-- Pencils `x·y = c` with `c` outside the subgroup are empty: the subgroup is
multiplicatively closed. -/
theorem inversionPairCount_eq_zero_of_notMem {n : ℕ} (hn : 0 < n) {c : F}
    (hc : c ∉ nthRootsFinset n (1 : F)) :
    inversionPairCount n c = 0 := by
  unfold inversionPairCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y⟩ hxy ⟨hmul, -⟩
  simp only [Finset.mem_product] at hxy
  apply hc
  rw [← hmul, mem_nthRootsFinset hn (1 : F), mul_pow,
    (mem_nthRootsFinset hn (1 : F)).mp hxy.1, (mem_nthRootsFinset hn (1 : F)).mp hxy.2,
    mul_one]

/-- **The negation-pencil spike.** Over `μ_{2m}` (char ≠ 2) the pencil `x ↦ −x` has
ordered off-diagonal count exactly `2m` — the second normalizer spike, at the universal
cap (the involution is fixed-point-free). -/
theorem negationPairCount_eq {m : ℕ} (hm : 0 < m) (h2 : (2 : F) ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 * m)) :
    negationPairCount F (2 * m) = 2 * m := by
  classical
  unfold negationPairCount
  have h2m : 0 < 2 * m := by omega
  conv_rhs => rw [← hζ.card_nthRootsFinset]
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  · intro p hp q hq hpq
    have hpq' : p.1 = q.1 := hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hp hq
    refine Prod.ext hpq' ?_
    have h1 : p.2 = -p.1 := by linear_combination hp.2.1
    have h2' : q.2 = -q.1 := by linear_combination hq.2.1
    rw [h1, h2', hpq']
  · intro x hx
    simp only [Finset.mem_coe] at hx
    have hxn : x ^ (2 * m) = 1 := (mem_nthRootsFinset h2m (1 : F)).mp hx
    have hx0 : x ≠ 0 := ne_zero_of_mem_nthRoots h2m hx
    have hneg : -x ∈ nthRootsFinset (2 * m) (1 : F) := by
      rw [mem_nthRootsFinset h2m (1 : F), Even.neg_pow (even_two_mul m), hxn]
    refine ⟨(x, -x), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hx, hneg⟩, by ring, ?_⟩
    intro hcontra
    apply hx0
    have h2x : (2 : F) * x = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2x with h | h
    · exact absurd h h2
    · exact h

/-- **The universal Möbius cap.** Every nondegenerate Möbius pencil
`xy − a(x+y) + b = 0` (`a² ≠ b`) has ordered solution count at most `|D|` over *any*
finite domain: the first coordinate determines the second, and `x = a` is excluded. The
normalizer spikes therefore sit at (or one orbit below) the absolute extremum. -/
theorem moebius_pair_count_le (a b : F) (hab : a ^ 2 ≠ b) (D : Finset F) :
    ((D ×ˢ D).filter fun p => p.1 * p.2 - a * (p.1 + p.2) + b = 0 ∧ p.1 ≠ p.2).card
      ≤ D.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p => p.1)
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
    exact hp.1.1
  · intro p hp q hq hpq
    have hpq' : p.1 = q.1 := hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp hq
    have ha : p.1 ≠ a := by
      intro h
      apply hab
      have heq := hp.2.1
      rw [h] at heq
      linear_combination -heq
    have hkey : p.2 = q.2 := by
      have h1 := hp.2.1
      have h2' := hq.2.1
      rw [← hpq'] at h2'
      have hfac : (p.2 - q.2) * (p.1 - a) = 0 := by linear_combination h1 - h2'
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (by linear_combination h : p.1 = a) ha
    exact Prod.ext hpq' hkey

/-! ## The open noise surface (Weil tier) -/

/-- **The pencil noise band (named open surface, Weil tier).** The conjecture that over the
smooth subgroup `μ_n ⊆ F_q` every *non-normalizer* pencil sits in a noise band of width
`B`: Möbius pencils with `a ≠ 0`, and additive pencils `x + y = c` with `c ≠ 0`. The probes
measure `B = O(n²/q + 1)` (spectral gap at `n = 16`: nothing at `t₂ ∈ {4,5,6}`); a proof
needs Weil-type bounds for character sums of rational functions against subgroup cosets
(not in Mathlib). The additive case is exactly the `|μ_n ∩ (c − μ_n)|` additive-energy
quantity of the #232 open core. -/
def PencilNoiseBand (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (B : ℕ) : Prop :=
  (∀ a b : F, a ≠ 0 → a ^ 2 ≠ b →
    (((nthRootsFinset n (1 : F)) ×ˢ (nthRootsFinset n (1 : F))).filter
      fun p => p.1 * p.2 - a * (p.1 + p.2) + b = 0 ∧ p.1 ≠ p.2).card ≤ B) ∧
  (∀ c : F, c ≠ 0 →
    (((nthRootsFinset n (1 : F)) ×ˢ (nthRootsFinset n (1 : F))).filter
      fun p => p.1 + p.2 = c ∧ p.1 ≠ p.2).card ≤ B)

/-- **The spectral gap, conditionally on the noise band.** If the noise band holds, the
pencil spectrum over `μ_{2m}` is *gapped*: every non-normalizer pencil count is `≤ B`
(noise) while every inversion pencil with `c` in the subgroup sits exactly in
`{2m − 2, 2m}` (the normalizer spikes) — no pencil lands strictly between when
`B < 2m − 2`. The probes' measured gap, formal modulo the named Weil surface. -/
theorem spectral_gap_of_noiseBand {m : ℕ} (hm : 0 < m) (h2 : (2 : F) ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {B : ℕ}
    (hband : PencilNoiseBand F (2 * m) B) :
    (∀ a b : F, a ≠ 0 → a ^ 2 ≠ b →
      (((nthRootsFinset (2 * m) (1 : F)) ×ˢ (nthRootsFinset (2 * m) (1 : F))).filter
        fun p => p.1 * p.2 - a * (p.1 + p.2) + b = 0 ∧ p.1 ≠ p.2).card ≤ B) ∧
    (∀ c : F, c ∈ nthRootsFinset (2 * m) (1 : F) →
      inversionPairCount (2 * m) c = 2 * m - 2 ∨
        inversionPairCount (2 * m) c = 2 * m) := by
  refine ⟨hband.1, fun c hc => ?_⟩
  rw [inversionPairCount_eq hm h2 hζ hc]
  by_cases hcm : c ∈ nthRootsFinset m (1 : F)
  · left; simp [hcm]
  · right; simp [hcm]

/-! ## Source audit -/

#print axioms card_sq_eq_in_subgroup
#print axioms inversionPairCount_eq_card_nonroots
#print axioms inversionPairCount_eq
#print axioms inversionPairCount_eq_zero_of_notMem
#print axioms negationPairCount_eq
#print axioms moebius_pair_count_le
#print axioms spectral_gap_of_noiseBand

end ProximityGap.PencilNormalizerBand
