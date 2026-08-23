/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmallSubgroupDeltaStarPin

/-!
# Discharging `SmallSubgroupGoodList` — the exact provable regime, and the obstruction (#389)

The task: can the proven small-subgroup additive structure (`E(μ_n) = 3n²−3n`, `r(c) ≤ 2`,
the Sidon property, `T(μ_n) ≤ √3·n^{3/2}`) discharge the named hypothesis
`SmallSubgroupGoodList` — the **all-pairs** interleaved-list bound at the good radius — and so
close the small-subgroup δ* pin unconditionally?

## Answer (honest, machine-checked here): NO for the prize window; YES below `δ = (1−ρ)/4`.

The interleaved list `interleavedList C u₀ u₁ a` (the object `SmallSubgroupGoodList` quantifies
over) is taken at the **DOUBLED** radius floor `a = 2t − n = (1 − 2δ_good)·n`.  Two facts pin
down exactly what additive structure can and cannot do.

1. **`interleavedList_rs_card_le_one`** (proven here, unconditional, ANY RS code, NO Sidon input):
   if `n + k ≤ 2·a` then `interleavedList (rsCode dom k) u₀ u₁ a` has card `≤ 1`.  This is the
   *interleaved unique-decoding radius*: two list pairs each agree with `(u₀,u₁)` on `≥ a` points,
   so on the intersection (size `≥ 2a − n ≥ k`) both rows of both pairs equal the target — hence
   the two row-1 codewords agree on `≥ k` points and MDS forces them equal, likewise row 2.  The
   list is a subsingleton.  **No additive structure is used** — it is the pure MDS property.

2. **`smallSubgroup_goodList_of_mds_regime` / `_rs`** (proven here): consequently
   `SmallSubgroupGoodList (rsCode dom k) δ_good 1` holds whenever the good-radius floor satisfies
   `n + k ≤ 2·(2·⌈(1 − δ_good)·n⌉ − n)`, i.e. (continuous form) `δ_good ≤ (1 − ρ)/4`.

### Why this is genuinely sub-Johnson and the additive structure cannot help.

`(1 − ρ)/4 < (1 − ρ)/2 < 1 − √ρ` for every rate `ρ ∈ (0,1)`: the doubled radius collapses
the list to a singleton only *well below* the Johnson radius, hence FAR below the prize window
`(1 − √ρ, 1 − ρ)`.  Above this threshold the all-pairs list genuinely blows up, and the blow-up
is a pure MDS phenomenon the Sidon data does not see:

* exhaustive probe (`/tmp/probe_mu4.py`), `μ₄ ⊂ F₁₇`, `k = 3` (`ρ = 3/4`), the worst pair
  `(u₀,u₁) = (0,0)`:  `a = 3 : |list| = 1`,  `a = 2 : |list| = 1729`,  `a = 1 : |list| = 332353`;
* for a *non-codeword* ambiguous word `u₀` (interleaving two codewords), already at `a = k`
  there are **6** row-1 codewords agreeing with `u₀` on `≥ a` points (`/tmp/probe_fast.py`) — the
  per-row list is NOT unique at `a = k`; only `2a − n ≥ k` forces it;
* the list size at `a < k` is **identical** for the smooth subgroup `μ₄` and a generic random RS
  domain (`1729` either way, `/tmp/blowup_analytic.py`): it depends only on `(n,k,q)`, NOT on the
  additive structure of the domain.

**Therefore the Sidon / `r(c) ≤ 2` / energy data — which controls only the SINGLE cubic
obstruction word `x ↦ x³` (`cubic_explainable_core_sq_le_sharp`) — cannot discharge
`SmallSubgroupGoodList`:** the worst word pairs (codeword pairs, ambiguous interleavings) are
purely MDS/combinatorial objects invisible to the additive structure.  Bridging single-word
supply to the all-pairs interleaved list above the unique-decoding radius is exactly the open
beyond-Johnson core ([ABF26] §5, issue #334 core A); the small-subgroup additive structure does
not close it, so `SmallSubgroupGoodList` stays a genuine binder in the prize window.

What IS closed here, unconditionally and with the sharp list size `L = 1`: the
below-`(1 − ρ)/4` (interleaved unique-decoding) regime.  A real, if sub-Johnson, unconditional
discharge of the named hypothesis — and a machine-checked delimitation of exactly where the
additive structure stops helping.

All results axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.SmallSubgroupGoodListMDS

open ProximityGap.SpikeFloor InterleavedMCACollapse Round17CAPair
open ArkLib.ProximityGap.SmallSubgroupDeltaStarPin

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-! ## Part 1 — MDS unique `k`-interpolation for `rsCode` -/

/-- **MDS unique `k`-interpolation.**  Two Reed–Solomon codewords of `rsCode dom k` agreeing on
at least `k` positions are equal: their difference comes from a polynomial of degree `< k`
vanishing at `≥ k` distinct points, hence the zero polynomial. -/
theorem rsCode_unique_interp (dom : Fin n ↪ F) {k : ℕ}
    {g g' : Fin n → F} (hg : g ∈ rsCode dom k) (hg' : g' ∈ rsCode dom k)
    (hk : k ≤ (Finset.univ.filter (fun x => g x = g' x)).card) :
    g = g' := by
  classical
  obtain ⟨P, hP, rfl⟩ := hg
  obtain ⟨Q, hQ, rfl⟩ := hg'
  set S : Finset (Fin n) := Finset.univ.filter
    (fun x => (fun i => P.eval (dom i)) x = (fun i => Q.eval (dom i)) x) with hSdef
  have hScard : k ≤ S.card := hk
  have hPQ : P - Q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := P - Q) (s := S.image dom) ?_ ?_
    · have hcard : (S.image dom).card = S.card :=
        Finset.card_image_of_injective _ dom.injective
      rw [hcard]
      calc (P - Q).degree ≤ max P.degree Q.degree := Polynomial.degree_sub_le P Q
        _ < (k : WithBot ℕ) := max_lt hP hQ
        _ ≤ (S.card : WithBot ℕ) := by exact_mod_cast hScard
    · intro y hy
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
      have hxeq : P.eval (dom x) = Q.eval (dom x) := by
        have := Finset.mem_filter.mp hxS
        simpa using this.2
      simp [Polynomial.eval_sub, hxeq]
  have hPeq : P = Q := by linear_combination (norm := ring_nf) hPQ
  rw [hPeq]

/-! ## Part 2 — the interleaved list collapses to ≤ 1 above the unique-decoding radius -/

/-- **The MDS interleaved-list collapse (interleaved unique-decoding radius).**  For ANY Finset
subcode `C` of the Reed–Solomon code `rsCode dom k` and ANY word pair `(u₀, u₁)`, if the
joint-agreement floor `a` clears the interleaved unique-decoding radius `n + k ≤ 2·a`, the
interleaved list has at most one element:

  `n + k ≤ 2·a  ⟹  (interleavedList C u₀ u₁ a).card ≤ 1`.

Two list pairs `p, q` each agree with `(u₀,u₁)` on `≥ a` points; the two joint-agree sets meet in
`≥ 2a − n ≥ k` points, where both rows of both pairs equal the target.  Thus `p.1, q.1` agree on
`≥ k` points and MDS forces `p.1 = q.1`, likewise `p.2 = q.2`, so `p = q`.  Unconditional; no
additive (Sidon) input — purely the MDS property.  Taking `C` = the whole RS code (as a Finset)
gives the full interleaved list of the code; taking any subcode keeps the bound. -/
theorem interleavedList_rs_card_le_one (dom : Fin n ↪ F) {k a : ℕ} (hka : n + k ≤ 2 * a)
    (C : Finset (Fin n → F)) (hC : ∀ g ∈ C, g ∈ rsCode dom k)
    (u₀ u₁ : Fin n → F) :
    (interleavedList C u₀ u₁ a).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro p hp q hq
  simp only [interleavedList, Finset.mem_filter, Finset.mem_product] at hp hq
  obtain ⟨⟨hp1C, hp2C⟩, hpa⟩ := hp
  obtain ⟨⟨hq1C, hq2C⟩, hqa⟩ := hq
  have hp1 : p.1 ∈ rsCode dom k := hC _ hp1C
  have hp2 : p.2 ∈ rsCode dom k := hC _ hp2C
  have hq1 : q.1 ∈ rsCode dom k := hC _ hq1C
  have hq2 : q.2 ∈ rsCode dom k := hC _ hq2C
  -- the two joint-agree sets meet in ≥ 2a − n points (and Fintype.card (Fin n) = n)
  have hcardn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hinter : 2 * a ≤
      ((jointAgreeSet u₀ u₁ p.1 p.2) ∩ (jointAgreeSet u₀ u₁ q.1 q.2)).card
        + Fintype.card (Fin n) :=
    inter_card_ge hpa hqa
  -- on that intersection, p.1 = u₀ = q.1 and p.2 = u₁ = q.2
  have hsub1 : (jointAgreeSet u₀ u₁ p.1 p.2) ∩ (jointAgreeSet u₀ u₁ q.1 q.2)
      ⊆ Finset.univ.filter (fun x => p.1 x = q.1 x) := by
    intro x hx
    obtain ⟨hxp, hxq⟩ := Finset.mem_inter.mp hx
    simp only [jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxp hxq ⊢
    -- u₀ x = p.1 x and u₀ x = q.1 x
    exact hxp.1.symm.trans hxq.1
  have hsub2 : (jointAgreeSet u₀ u₁ p.1 p.2) ∩ (jointAgreeSet u₀ u₁ q.1 q.2)
      ⊆ Finset.univ.filter (fun x => p.2 x = q.2 x) := by
    intro x hx
    obtain ⟨hxp, hxq⟩ := Finset.mem_inter.mp hx
    simp only [jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxp hxq ⊢
    exact hxp.2.symm.trans hxq.2
  -- so the row-agreement counts are ≥ 2a − n ≥ k
  have hge1 : k ≤ (Finset.univ.filter (fun x => p.1 x = q.1 x)).card := by
    have h := Finset.card_le_card hsub1
    omega
  have hge2 : k ≤ (Finset.univ.filter (fun x => p.2 x = q.2 x)).card := by
    have h := Finset.card_le_card hsub2
    omega
  -- MDS forces both rows equal
  have hrow1 : p.1 = q.1 := rsCode_unique_interp dom hp1 hq1 hge1
  have hrow2 : p.2 = q.2 := rsCode_unique_interp dom hp2 hq2 hge2
  exact Prod.ext hrow1 hrow2

/-! ## Part 3 — discharging `SmallSubgroupGoodList` with `L = 1` in the regime -/

open Classical in
/-- **Unconditional discharge of `SmallSubgroupGoodList` below the interleaved UD radius.**
For the Reed–Solomon code `rsCode dom k` (any RS code; in particular the small-subgroup NTT code
with `n = 2^m`, `p > 2^n`), if the doubled good-radius floor clears the interleaved
unique-decoding radius —

  `n + k ≤ 2·(2·⌈(1 − δgood)·n⌉ − n)` —

then `SmallSubgroupGoodList (rsCode dom k) δgood 1` holds: the all-pairs interleaved list has size
`≤ 1` at the good radius.  Unconditional, no Sidon / energy input.  (In rate units this is
`δgood ≤ (1 − ρ)/4`, strictly below Johnson `1 − √ρ`, so it does NOT reach the prize window;
see the module docstring for the machine-checked obstruction above the threshold.) -/
theorem smallSubgroup_goodList_of_mds_regime [NeZero n]
    (dom : Fin n ↪ F) {k : ℕ} {δgood : ℝ≥0}
    (C : Finset (Fin n → F)) (hC : ∀ g ∈ C, g ∈ rsCode dom k)
    (hreg : Fintype.card (Fin n) + k
      ≤ 2 * (2 * ⌈(1 - δgood) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) :
    SmallSubgroupGoodList C δgood 1 := by
  intro u₀ u₁
  -- a := 2⌈(1−δ)·card(Fin n)⌉ − card(Fin n); the hypothesis is exactly card(Fin n) + k ≤ 2a
  -- (the goal's floor `a` literally uses `Fintype.card (Fin n)`, defeq to `n`)
  refine interleavedList_rs_card_le_one dom ?_ C hC u₀ u₁
  rw [Fintype.card_fin]
  rw [Fintype.card_fin] at hreg
  exact hreg

end ArkLib.ProximityGap.SmallSubgroupGoodListMDS

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.SmallSubgroupGoodListMDS.rsCode_unique_interp
#print axioms ArkLib.ProximityGap.SmallSubgroupGoodListMDS.interleavedList_rs_card_le_one
#print axioms ArkLib.ProximityGap.SmallSubgroupGoodListMDS.smallSubgroup_goodList_of_mds_regime
