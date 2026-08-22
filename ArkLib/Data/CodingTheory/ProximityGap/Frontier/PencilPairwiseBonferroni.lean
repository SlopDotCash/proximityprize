/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._KelleyOwenDilationPencil

/-!
# LEVER K, general pairwise: the Bonferroni dilation-pencil count (NO common core) (#407/#444)

`_PencilSunflowerCore.pencil_sunflower_core` proves the **sunflower** rung of the dilation-pencil
degradation: when the `r` blocks pairwise meet in a *single common* core `T` of size `M`, then
`r·(r−M) + M ≤ |G|`. Its honest scope note flags the strictly harder target it does NOT cover:

> "The general pairwise-`≤ M` core (`r² ≲ M·N` by a Cauchy–Schwarz/Fisher double-count, with **no
> common `T`**) is the harder honest target and stays a **separate brick**."

This is exactly the hypothesis `PencilAutocorrelation.pencil_overlap_le_of_autocorr` actually
delivers from a bounded multiplicative autocorrelation: every *distinct* pencil pair overlaps in
`≤ M`, but the intersections can be **different per pair** (no common `T`). This file supplies that
separate brick — the **second Bonferroni inequality** for the pencil, with no sunflower hypothesis.

## The combinatorial heart (`biUnion_card_ge_sub_pairwise`)

For ANY family `C : Fin r → Finset G` (not necessarily blocks),
  `Σᵢ |Cᵢ| − Σ_{i<j} |Cᵢ ∩ Cⱼ| ≤ |⋃ᵢ Cᵢ|`.
This is the second Bonferroni / inclusion–exclusion lower bound, proved fiberwise: over the union
`U = ⋃ Cᵢ`, with the multiplicity `d(x) = #{i : x ∈ Cᵢ}`,
  `Σᵢ|Cᵢ| = Σ_{x∈U} d(x)`,  `Σ_{i<j}|Cᵢ∩Cⱼ| = Σ_{x∈U} C(d(x),2)`,
and the pointwise inequality `d − C(d,2) ≤ 1` (true for every `d : ℕ`: `d=0,1` give `≤1`; `d=2`
gives `2−1=1`; `d≥3` gives a value `≤ 0`) sums to `Σ_x (d − C(d,2)) ≤ |U|`.

## The pencil headline (`pencil_pairwise_bonferroni`)

Specialized to the dilation pencil: `r` blocks `Bᵢ`, each size `r`, common point `p`, with the
punctured blocks `Cᵢ = Bᵢ \ {p}` (size `r−1`) pairwise overlapping in `≤ M`. Then
  `r·(r−1) ≤ C(r,2)·M + (|G|−1)`,
i.e. (since `C(r,2)·M = r(r−1)M/2`) `r(r−1)(1 − M/2) ≤ |G|−1`. For the prize-relevant `M ≍ n/2`
this is **vacuous** (RHS dominates), exactly recovering the Johnson-scale degradation: the pairwise
double-count, like the sunflower count, only reaches Johnson, never sub-Johnson. At `M = 0`
(disjoint punctured blocks, the `t=3` extreme) it recovers `r·(r−1) ≤ |G|−1` = `pencil_card_core`.

## Honest scope (rules 1,3,6)

This is **NOT** a closure of the prize and is **field-universal** (no thinness): it is a pure
double-count valid for any set family, so by rule 3 it CANNOT prove CORE (which is FALSE in the
thick window). It is the missing general-pairwise rung of the LEVER-K degradation that the sunflower
brick explicitly deferred — and it confirms, honestly, that the pairwise-bounded-overlap route
collapses to Johnson at the prize core size `M ≍ n/2`. The prize CORE `M(μ_n) ≤ C·√(n·log(p/n))`
stays **OPEN**. ASYMPTOTIC-CLAIM GUARD: a set-family counting object, not a `δ*`/incidence object;
the cliff-at-n/2 is untouched and no capacity/beyond-Johnson claim is made (the bound is Johnson at
`M ≍ n/2`, the correct side of the cliff). Probe-verified on genuine thin-`μ_n` dilation pencils
(`scripts/probes/probe_pencil_pairwise_bonferroni.py`): 0 violations / 55 instances incl. the prize
worst case `S = (coset of size n/2) ∪ {straggler}`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.PencilPairwiseBonferroni

variable {G : Type*} [DecidableEq G]

/-- **Strict-pair count = `C(card, 2)`.** For a finset `s` in a linear order, the number of strictly
increasing pairs `{(i,j) : i,j ∈ s, i < j}` is `C(|s|, 2)`. Proved by splitting `s.offDiag`
(`{(i,j) : i ≠ j}`, card `|s|² − |s|`) into the `<` and `>` halves, equinumerous via `Prod.swap`. -/
theorem filter_lt_offDiag_card {ι : Type*} [LinearOrder ι] [DecidableEq ι] (s : Finset ι) :
    (s.offDiag.filter (fun q => q.1 < q.2)).card = s.card.choose 2 := by
  classical
  -- The `>` half is the swap-image of the `<` half, so they have equal card.
  set L : Finset (ι × ι) := s.offDiag.filter (fun q => q.1 < q.2) with hL
  set Gt : Finset (ι × ι) := s.offDiag.filter (fun q => q.2 < q.1) with hGt
  have hswap : Gt = L.image Prod.swap := by
    apply Finset.ext
    rintro ⟨a, b⟩
    simp only [hGt, hL, Finset.mem_filter, Finset.mem_image, Finset.mem_offDiag, Prod.exists]
    constructor
    · rintro ⟨⟨ha, hb, hne⟩, hlt⟩
      exact ⟨b, a, ⟨⟨hb, ha, fun h => hne h.symm⟩, hlt⟩, rfl⟩
    · rintro ⟨c, d, ⟨⟨hc, hd, hne⟩, hlt⟩, heq⟩
      rw [Prod.swap, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨⟨hd, hc, fun h => hne h.symm⟩, hlt⟩
  have hGtcard : Gt.card = L.card := by
    rw [hswap, Finset.card_image_of_injective _ Prod.swap_injective]
  -- offDiag = L ⊔ Gt (disjoint: i<j vs i>j).
  have hdisj : Disjoint L Gt := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ haL haGt
    simp only [hL, hGt, Finset.mem_filter] at haL haGt
    exact absurd haL.2 (not_lt.mpr (le_of_lt haGt.2))
  have hunion : s.offDiag = L ∪ Gt := by
    apply Finset.ext
    rintro ⟨a, b⟩
    simp only [hL, hGt, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨ha, hb, hne⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨⟨ha, hb, hne⟩, hlt⟩
      · exact Or.inr ⟨⟨ha, hb, hne⟩, hgt⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hoff : s.offDiag.card = L.card + Gt.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  rw [Finset.offDiag_card, hGtcard] at hoff
  -- |s|² − |s| = 2 * L.card, and C(|s|,2) = |s|(|s|-1)/2.
  rw [Nat.choose_two_right]
  -- s.card * s.card - s.card = s.card * (s.card - 1)
  have hsc : s.card * s.card - s.card = s.card * (s.card - 1) := by
    cases s.card with
    | zero => simp
    | succ m => rw [Nat.succ_sub_one]; ring_nf; omega
  rw [hsc] at hoff
  omega

/-- The multiplicity of `x` in a finite family `C : Fin r → Finset G`: the number of indices `i`
with `x ∈ C i`. -/
def mult (r : ℕ) (C : Fin r → Finset G) (x : G) : ℕ :=
  (Finset.univ.filter (fun i => x ∈ C i)).card

/-- `Σᵢ |Cᵢ| = Σ_{x ∈ U} mult x`, where `U = ⋃ᵢ Cᵢ`. Pair-counting `{(x,i) : x ∈ Cᵢ}` two ways. -/
theorem sum_card_eq_sum_mult (r : ℕ) (C : Fin r → Finset G) :
    (∑ i, (C i).card) = ∑ x ∈ Finset.univ.biUnion C, mult r C x := by
  classical
  -- Count the set of pairs `{(i, x) : x ∈ C i}` over `Fin r × U`.
  set U : Finset G := Finset.univ.biUnion C with hU
  -- For each `i`, `C i ⊆ U`, so `(C i).card = (U.filter (· ∈ C i)).card`.
  have hCi : ∀ i, (C i).card = (U.filter (fun x => x ∈ C i)).card := by
    intro i
    congr 1
    apply Finset.ext
    intro x
    rw [Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩, hx⟩
    · intro hx; exact hx.2
  calc (∑ i, (C i).card)
      = ∑ i, (U.filter (fun x => x ∈ C i)).card := by
        exact Finset.sum_congr rfl (fun i _ => hCi i)
    _ = ∑ i, ∑ x ∈ U, (if x ∈ C i then 1 else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.card_filter]
    _ = ∑ x ∈ U, ∑ i, (if x ∈ C i then 1 else 0) := Finset.sum_comm
    _ = ∑ x ∈ U, mult r C x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [mult, Finset.card_filter]

/-- `Σ_{i<j} |Cᵢ ∩ Cⱼ| = Σ_{x ∈ U} C(mult x, 2)`. Pair-counting unordered index pairs sharing `x`.
We phrase the LHS over the `offDiag`-style sum `Σ_{(i,j), i<j}`, here as the sum over the
`Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2)`. -/
theorem sum_inter_eq_sum_choose_two (r : ℕ) (C : Fin r → Finset G) :
    (∑ p ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
        (C p.1 ∩ C p.2).card)
      = ∑ x ∈ Finset.univ.biUnion C, (mult r C x).choose 2 := by
  classical
  set U : Finset G := Finset.univ.biUnion C with hU
  -- Each |Cᵢ ∩ Cⱼ| = Σ_{x∈U} [x ∈ Cᵢ ∧ x ∈ Cⱼ].
  have hinter : ∀ i j : Fin r, (C i ∩ C j).card
      = ∑ x ∈ U, (if x ∈ C i ∧ x ∈ C j then 1 else 0) := by
    intro i j
    rw [← Finset.card_filter]
    congr 1
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · intro hx
      exact ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx.1⟩, hx⟩
    · intro hx; exact hx.2
  -- Swap sums: Σ_{i<j} Σ_x [..] = Σ_x Σ_{i<j} [..] = Σ_x C(mult x, 2).
  calc (∑ p ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
            (C p.1 ∩ C p.2).card)
      = ∑ p ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
          ∑ x ∈ U, (if x ∈ C p.1 ∧ x ∈ C p.2 then 1 else 0) := by
        exact Finset.sum_congr rfl (fun p _ => hinter p.1 p.2)
    _ = ∑ x ∈ U, ∑ p ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
          (if x ∈ C p.1 ∧ x ∈ C p.2 then 1 else 0) := Finset.sum_comm
    _ = ∑ x ∈ U, (mult r C x).choose 2 := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        -- The inner sum counts ordered pairs (i,j) with i<j and x ∈ Cᵢ, x ∈ Cⱼ:
        -- = C(#{i : x ∈ Cᵢ}, 2) = C(mult x, 2).
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
        -- The filtered set is {(i,j) : i<j ∧ x ∈ Cᵢ ∧ x ∈ Cⱼ}; its card = C(s.card, 2)
        -- where s = univ.filter (x ∈ C ·).
        set s : Finset (Fin r) := Finset.univ.filter (fun i => x ∈ C i) with hs
        have hcard : ((Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2)).filter
            (fun p => x ∈ C p.1 ∧ x ∈ C p.2) = (s.offDiag).filter (fun p => p.1 < p.2) := by
          apply Finset.ext
          intro p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag, hs]
          constructor
          · rintro ⟨hlt, h1, h2⟩
            exact ⟨⟨h1, h2, by exact (ne_of_lt hlt)⟩, hlt⟩
          · rintro ⟨⟨h1, h2, _⟩, hlt⟩
            exact ⟨hlt, h1, h2⟩
        rw [hcard]
        rw [mult, ← hs]
        -- |{(i,j) ∈ s.offDiag : i < j}| = C(|s|, 2)
        exact filter_lt_offDiag_card s

/-- The pointwise Bonferroni inequality on multiplicities: `d − C(d,2) ≤ 1` for every `d : ℕ`.
(`d=0,1`: `≤1`; `d=2`: `2−1=1`; `d≥3`: the choose dominates so the difference is `≤0`.) -/
theorem mult_sub_choose_two_le_one (d : ℕ) : d - d.choose 2 ≤ 1 := by
  rcases d with _ | _ | _ | d
  · simp
  · simp
  · decide
  · -- d ≥ 3: C(d+3, 2) = (d+3)(d+2)/2 ≥ d+3, so (d+3) - C(d+3,2) = 0 in ℕ subtraction.
    have h : (d + 1 + 1 + 1) ≤ (d + 1 + 1 + 1).choose 2 := by
      rw [Nat.choose_two_right]
      -- (d+3) ≤ (d+3)(d+2)/2 ⟺ (d+3)*2 ≤ (d+3)(d+2)
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      apply Nat.mul_le_mul_left; omega
    omega

/-- **THE COMBINATORIAL HEART (second Bonferroni inequality).** For ANY finite family
`C : Fin r → Finset G`,
  `Σᵢ |Cᵢ| ≤ Σ_{i<j} |Cᵢ ∩ Cⱼ| + |⋃ᵢ Cᵢ|`.
The lower bound on the union size by single minus pairwise overlaps. -/
theorem biUnion_card_ge_sub_pairwise (r : ℕ) (C : Fin r → Finset G) :
    (∑ i, (C i).card) ≤
      (∑ p ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
          (C p.1 ∩ C p.2).card)
        + (Finset.univ.biUnion C).card := by
  classical
  set U : Finset G := Finset.univ.biUnion C with hU
  rw [sum_card_eq_sum_mult r C, sum_inter_eq_sum_choose_two r C]
  -- Now: Σ_{x∈U} mult x ≤ Σ_{x∈U} C(mult x, 2) + |U|.
  -- Pointwise: mult x ≤ C(mult x, 2) + 1, summed; and |U| = Σ_{x∈U} 1.
  have hU_card : U.card = ∑ _x ∈ U, 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  rw [hU_card, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have := mult_sub_choose_two_le_one (mult r C x)
  omega

/-- **THE PENCIL HEADLINE (general pairwise, NO common core).** Suppose `univ : Finset G` carries a
family of `r` blocks `B : Fin r → Finset G`, each of size `r`, all containing a common point `p`,
with the **punctured** blocks pairwise overlapping in `≤ M`: for `i ≠ j`,
`|(B i).erase p ∩ (B j).erase p| ≤ M`. Then
  `r·(r−1) ≤ C(r,2)·M + (|univ| − 1)`.

No sunflower hypothesis (intersections may differ per pair) — this is the general-pairwise rung the
sunflower brick deferred. At `M = 0` it gives `r·(r−1) ≤ |univ|−1` (= `pencil_card_core`); at the
prize core `M ≍ n/2` the RHS dominates (Johnson, not sub-Johnson). -/
theorem pencil_pairwise_bonferroni (univ : Finset G)
    (r M : ℕ) (hr : 1 ≤ r) (B : Fin r → Finset G) (p : G)
    (hsub : ∀ i, B i ⊆ univ)
    (hsize : ∀ i, (B i).card = r)
    (hp : ∀ i, p ∈ B i)
    (hpair : ∀ i j, i ≠ j → ((B i).erase p ∩ (B j).erase p).card ≤ M) :
    r * (r - 1) ≤ (r.choose 2) * M + (univ.card - 1) := by
  classical
  have hrpos : 0 < r := hr
  set C : Fin r → Finset G := fun i => (B i).erase p with hC
  -- Each |C i| = r - 1.
  have hCcard : ∀ i, (C i).card = r - 1 := by
    intro i; rw [hC, Finset.card_erase_of_mem (hp i), hsize i]
  -- Σ |C i| = r * (r-1).
  have hsumC : (∑ i, (C i).card) = r * (r - 1) := by
    rw [Finset.sum_congr rfl (fun i _ => hCcard i)]
    simp [Finset.sum_const, Finset.card_univ]
  -- p ∉ any C i, so p ∉ U := ⋃ C i ⊆ univ; hence |U| ≤ |univ| - 1.
  have hpnotC : ∀ i, p ∉ C i := by intro i; rw [hC]; exact Finset.notMem_erase p _
  set U : Finset G := Finset.univ.biUnion C with hU
  have hpnotU : p ∉ U := by
    rw [hU, Finset.mem_biUnion]; rintro ⟨i, _, hi⟩; exact hpnotC i hi
  have hUsub : U ⊆ univ := by
    intro x hx
    rw [hU, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    rw [hC, Finset.mem_erase] at hxi
    exact hsub i hxi.2
  -- p ∈ univ (it's in B 0 ⊆ univ).
  have hpuniv : p ∈ univ := hsub ⟨0, hrpos⟩ (hp _)
  have hUcard_le : U.card ≤ univ.card - 1 := by
    have hins : insert p U ⊆ univ := Finset.insert_subset hpuniv hUsub
    have := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hpnotU] at this
    omega
  -- Bonferroni: Σ|C i| ≤ Σ_{i<j}|Ci ∩ Cj| + |U|.
  have hbonf := biUnion_card_ge_sub_pairwise r C
  rw [hsumC] at hbonf
  -- Bound the pairwise sum by C(r,2) * M.
  have hpairsum : (∑ q ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2),
      (C q.1 ∩ C q.2).card) ≤ (r.choose 2) * M := by
    have hle : ∀ q ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2),
        (C q.1 ∩ C q.2).card ≤ M := by
      intro q hq
      rw [Finset.mem_filter] at hq
      have hne : q.1 ≠ q.2 := ne_of_lt hq.2
      rw [hC]; exact hpair q.1 q.2 hne
    calc (∑ q ∈ _, (C q.1 ∩ C q.2).card)
        ≤ ∑ _q ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2), M :=
          Finset.sum_le_sum hle
      _ = ((Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2)).card * M := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (r.choose 2) * M := by
          congr 1
          -- |{(i,j) ∈ univ : i < j}| over Fin r = C(r, 2)
          have huniv : ((Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2))
              = ((Finset.univ : Finset (Fin r)).offDiag.filter (fun q => q.1 < q.2)) := by
            apply Finset.ext
            rintro ⟨a, b⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
            constructor
            · intro h
              exact ⟨ne_of_lt h, h⟩
            · intro h
              exact h.2
          rw [huniv, filter_lt_offDiag_card]
          simp [Finset.card_univ]
  calc r * (r - 1) ≤ _ + U.card := hbonf
    _ ≤ (r.choose 2) * M + (univ.card - 1) := by
        have := hUcard_le
        omega

/-- **Disjoint extreme (`M = 0`) recovers `pencil_card_core`'s numbers.** With pairwise-disjoint
punctured blocks (`M = 0`), the headline collapses to `r·(r−1) ≤ |univ| − 1`, i.e.
`r·(r−1) + 1 ≤ |univ|`, the Stepanov `√N` count. -/
theorem pencil_pairwise_bonferroni_disjoint (univ : Finset G)
    (r : ℕ) (hr : 1 ≤ r) (B : Fin r → Finset G) (p : G)
    (hsub : ∀ i, B i ⊆ univ)
    (hsize : ∀ i, (B i).card = r)
    (hp : ∀ i, p ∈ B i)
    (hpair : ∀ i j, i ≠ j → ((B i).erase p ∩ (B j).erase p).card ≤ 0) :
    r * (r - 1) + 1 ≤ univ.card := by
  have hpuniv : p ∈ univ := hsub ⟨0, hr⟩ (hp _)
  have h0 : 1 ≤ univ.card := Finset.card_pos.mpr ⟨p, hpuniv⟩
  have := pencil_pairwise_bonferroni univ r 0 hr B p hsub hsize hp hpair
  simp only [Nat.mul_zero] at this
  omega

/-! ## The `√` extractions and the `M ≥ 2` Johnson-collapse threshold

The headline `r·(r−1) ≤ C(r,2)·M + (n−1)` extracts a `√`-type root bound only while the pairwise
overlap `M ≤ 1`; at `M ≥ 2` the `C(r,2)·M` term alone already dominates `r·(r−1)`, so the bound is
VACUOUS — the exact point at which the dilation-pencil double-count stops bounding the root count.
This machine-checks the prose Johnson-collapse threshold of `_KelleyOwenDilationPencil` /
`_PencilSunflowerCore`. -/

/-- **Disjoint (`M = 0`) `√N` extraction.** `r·(r−1) ≤ n−1 ⟹ (r−1)² < n`, i.e. `r < 1 + √n`
(Stepanov / Kelley–Owen `√N`). -/
theorem sqrt_extract_disjoint {r n : ℕ} (h : r * (r - 1) ≤ n - 1) (hn : 1 ≤ n) :
    (r - 1) * (r - 1) < n := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0; simpa using hn
  · have : (r - 1) * (r - 1) ≤ r * (r - 1) := by
      apply Nat.mul_le_mul_right; omega
    omega

/-- **Autocorrelation-route (`M = 1`) `√(2N)` extraction.** With pairwise overlap `M = 1`,
`r·(r−1) ≤ C(r,2) + (n−1) = r·(r−1)/2 + (n−1)`, so `r·(r−1) ≤ 2·(n−1)`, giving `(r−1)² < 2·n`,
i.e. `r < 1 + √(2n)`. The genuine Kelley-3.2 root count when the multiplicative autocorrelation is
exactly `1` — still `√N` scale (Johnson), the honest ceiling of the pairwise route. -/
theorem sqrt_extract_autocorr_one {r n : ℕ} (h : r * (r - 1) ≤ r.choose 2 * 1 + (n - 1))
    (hn : 1 ≤ n) :
    (r - 1) * (r - 1) < 2 * n := by
  rw [Nat.choose_two_right, mul_one] at h
  -- r*(r-1)/2 ≤ r*(r-1) so from h: r*(r-1) ≤ r*(r-1)/2 + (n-1) ⟹ r*(r-1) ≤ 2*(n-1).
  have hhalf : r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
  have hkey : r * (r - 1) ≤ 2 * (n - 1) := by
    -- 2*(r*(r-1)) ≤ 2*(r*(r-1)/2) + 2*(n-1) ≤ r*(r-1) + 2*(n-1)
    have hdouble : 2 * (r * (r - 1) / 2) ≤ r * (r - 1) := by
      have := Nat.div_mul_le_self (r * (r - 1)) 2
      omega
    omega
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0; simpa using (by omega : (0:ℕ) < 2 * n)
  · have hsq : (r - 1) * (r - 1) ≤ r * (r - 1) := by
      apply Nat.mul_le_mul_right; omega
    omega

/-- **The `M ≥ 2` Johnson-collapse threshold (machine-checked).** For `M ≥ 2` the headline term
`C(r,2)·M` already dominates `r·(r−1)` (since `C(r,2)·2 = r·(r−1)`), so `r·(r−1) ≤ C(r,2)·M` holds
UNCONDITIONALLY — the pencil headline `r·(r−1) ≤ C(r,2)·M + (n−1)` carries NO information about `r`
once two distinct pencil blocks can share `≥ 2` punctured roots. This is the exact point where the
dilation-pencil double-count collapses to Johnson (it cannot beat `√N`), formalizing the prose
degradation of `_KelleyOwenDilationPencil` and the prize obstruction `M(S) ≥ n/2`. -/
theorem headline_vacuous_of_two_le (r M : ℕ) (hM : 2 ≤ M) :
    r * (r - 1) ≤ r.choose 2 * M := by
  rw [Nat.choose_two_right]
  -- r*(r-1)/2 * M ≥ r*(r-1)/2 * 2 = r*(r-1); the half is exact.
  have heven : 2 ∣ r * (r - 1) := Nat.even_mul_pred_self r |>.two_dvd
  obtain ⟨t, ht⟩ := heven
  rw [ht]
  -- 2*t/2 = t, goal: 2*t ≤ t*M, with M ≥ 2.
  rw [Nat.mul_div_cancel_left t (by norm_num)]
  calc 2 * t = t * 2 := by ring
    _ ≤ t * M := by apply Nat.mul_le_mul_left; omega

/-- **Consumer form of the `M ≥ 2` vacuity.** The actual pairwise-Bonferroni headline has the
extra nonnegative budget term `(n-1)`. Once `M ≥ 2`, even the overlap term alone dominates
`r·(r-1)`, so the full headline inequality is automatic for every `n`.  This is the exact
formal guard against reading a root-count bound out of the pencil inequality in the Johnson-collapse
regime. -/
theorem headline_with_budget_vacuous_of_two_le (r n M : ℕ) (hM : 2 ≤ M) :
    r * (r - 1) ≤ r.choose 2 * M + (n - 1) := by
  exact le_trans (headline_vacuous_of_two_le r M hM) (Nat.le_add_right _ _)

end ProximityGap.Frontier.PencilPairwiseBonferroni

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.PencilPairwiseBonferroni.biUnion_card_ge_sub_pairwise
#print axioms ProximityGap.Frontier.PencilPairwiseBonferroni.sqrt_extract_disjoint
#print axioms ProximityGap.Frontier.PencilPairwiseBonferroni.sqrt_extract_autocorr_one
#print axioms ProximityGap.Frontier.PencilPairwiseBonferroni.headline_vacuous_of_two_le
#print axioms ProximityGap.Frontier.PencilPairwiseBonferroni.headline_with_budget_vacuous_of_two_le
#print axioms ProximityGap.Frontier.PencilPairwiseBonferroni.pencil_pairwise_bonferroni
#print axioms ProximityGap.Frontier.PencilPairwiseBonferroni.pencil_pairwise_bonferroni_disjoint
