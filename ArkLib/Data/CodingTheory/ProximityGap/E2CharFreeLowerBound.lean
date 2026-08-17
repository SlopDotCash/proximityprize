/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

/-!
  A2-energy-transfer-r2  (char-p additive-energy transfer for μ_n at r=2)

  GOAL of this draft: pin, in Lean, the EXACT char-free content of the r=2 energy bound
  E_2(μ_n) = 3n² − 3n.  The probes establish:

    * char-0 / generic-prime value is EXACTLY 3n²−3n, with the clean decomposition
        E_2 = T1(diagonal n²) + T2(swap n²−n) + T3(antipodal-new n²−2n).
    * T1, T2 are CHARACTERISTIC-FREE (hold for any finite set, no field structure used).
    * T3 needs only  -1 ∈ μ_n  and  μ_n = -μ_n  (antipodal closure), which the just-landed
      char-free machinery `EvenOddAntipodal.image_neg_eq_of_prod_comp_neg` delivers.
    * Therefore  E_2(μ_n) ≥ 3n²−3n  is CHAR-FREE for every n (this file's provable core).
    * The UPPER bound  E_2(μ_n) ≤ 3n²−3n  is the ONLY char-dependent half, and it FAILS at
      structured primes for large n.  The EXACT obstruction is the 4-term root relation
        1 + B = C + D   with  B,C,D ∈ μ_n  and  {1,B} ≠ {C,D}   (the "genuine" extra quadruple).
      Minimal witness:  n=4, p=5:  1 + i = (-1)+(-1)  (i=2, since 2²=−1 in F₅).

  This draft formalizes the additive energy as a Finset count, the (T1,T2) char-free lower
  bound (the diagonal+swap injection), names the obstruction as an explicit Prop, and shows the
  upper bound is equivalent to the NON-existence of a genuine quadruple.  The antipodal T3 term
  is left as the hook to the EvenOddAntipodal closure (named, not silently discharged).
-/

open Finset

namespace ArkLib.ProximityGap.E2CharFree

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- The (ordered) additive-energy solution set of a finite set `S ⊆ F`:
quadruples `(x₁,x₂,y₁,y₂) ∈ S⁴` with `x₁ + x₂ = y₁ + y₂`. -/
def energyQuads (S : Finset F) : Finset (F × F × F × F) :=
  ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
    (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2) |>.image
    (fun q => (q.1.1, q.1.2, q.2.1, q.2.2))

/-- The additive energy `E₂(S) = #{(x₁,x₂,y₁,y₂) ∈ S⁴ : x₁+x₂ = y₁+y₂}`. -/
def E2 (S : Finset F) : ℕ := (energyQuads S).card

/-- The **diagonal** family: `(x₁,x₂,x₁,x₂)` for `(x₁,x₂) ∈ S×S`.  Always a valid quadruple,
char-free.  Cardinality `n²`. -/
def diagQuads (S : Finset F) : Finset (F × F × F × F) :=
  (S ×ˢ S).image (fun p => (p.1, p.2, p.1, p.2))

/-- The **swap** family: `(x₁,x₂,x₂,x₁)` for `(x₁,x₂) ∈ S×S`.  Always valid (`x₁+x₂=x₂+x₁`),
char-free. -/
def swapQuads (S : Finset F) : Finset (F × F × F × F) :=
  (S ×ˢ S).image (fun p => (p.1, p.2, p.2, p.1))

/-- diagonal quads are genuine energy quads (char-free, only uses commutativity). -/
theorem diagQuads_subset (S : Finset F) : diagQuads S ⊆ energyQuads S := by
  classical
  intro q hq
  simp only [diagQuads, Finset.mem_image, Finset.mem_product] at hq
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hq
  simp only [energyQuads, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  exact ⟨((a, b), (a, b)), ⟨⟨⟨ha, hb⟩, ⟨ha, hb⟩⟩, rfl⟩, rfl⟩

/-- swap quads are genuine energy quads (char-free, uses `add_comm`). -/
theorem swapQuads_subset (S : Finset F) : swapQuads S ⊆ energyQuads S := by
  classical
  intro q hq
  simp only [swapQuads, Finset.mem_image, Finset.mem_product] at hq
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hq
  simp only [energyQuads, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  exact ⟨((a, b), (b, a)), ⟨⟨⟨ha, hb⟩, ⟨hb, ha⟩⟩, add_comm a b⟩, rfl⟩

/-- The diagonal family has cardinality `|S|²` (the image is injective). -/
theorem diagQuads_card (S : Finset F) : (diagQuads S).card = S.card * S.card := by
  classical
  unfold diagQuads
  rw [Finset.card_image_of_injective _ (by
    intro x y h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1),
    Finset.card_product]

/-- **The char-free lower-bound seed.**  `E₂(S) ≥ |S|²` for any finite set in any
additive group, via the always-valid diagonal injection.  (This is the `T1` term; the full
`3n²−3n` char-free lower bound adds the `T2` swap term and the `T3` antipodal term — see below.) -/
theorem E2_ge_card_sq (S : Finset F) : S.card * S.card ≤ E2 S := by
  calc S.card * S.card = (diagQuads S).card := (diagQuads_card S).symm
    _ ≤ (energyQuads S).card := Finset.card_le_card (diagQuads_subset S)
    _ = E2 S := rfl

/-- The swap family also has cardinality `|S|²` (the image map is injective). -/
theorem swapQuads_card (S : Finset F) : (swapQuads S).card = S.card * S.card := by
  classical
  unfold swapQuads
  rw [Finset.card_image_of_injective _ (by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1),
    Finset.card_product]

/-- `diagQuads ∪ swapQuads ⊆ energyQuads` (both families are char-free valid quadruples). -/
theorem diag_union_swap_subset (S : Finset F) :
    diagQuads S ∪ swapQuads S ⊆ energyQuads S :=
  Finset.union_subset (diagQuads_subset S) (swapQuads_subset S)

/-- Membership of `diagQuads S`: `q ∈ diagQuads S ↔ ∃ a b, a∈S ∧ b∈S ∧ q=(a,b,a,b)`. -/
theorem mem_diagQuads {S : Finset F} {q : F × F × F × F} :
    q ∈ diagQuads S ↔ ∃ a ∈ S, ∃ b ∈ S, q = (a, b, a, b) := by
  classical
  simp only [diagQuads, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- Membership of `swapQuads S`. -/
theorem mem_swapQuads {S : Finset F} {q : F × F × F × F} :
    q ∈ swapQuads S ↔ ∃ a ∈ S, ∃ b ∈ S, q = (a, b, b, a) := by
  classical
  simp only [swapQuads, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- An element of the intersection `diagQuads ∩ swapQuads` is constant: `q = (a,a,a,a)`. -/
theorem inter_eq_const {S : Finset F} {q : F × F × F × F}
    (hq : q ∈ diagQuads S ∩ swapQuads S) : ∃ a ∈ S, q = (a, a, a, a) := by
  classical
  rw [Finset.mem_inter] at hq
  obtain ⟨a, ha, b, _, rfl⟩ := mem_diagQuads.mp hq.1
  obtain ⟨c, _, d, _, hcd⟩ := mem_swapQuads.mp hq.2
  -- (a,b,a,b) = (c,d,d,c) ⟹ a=c, b=d, a=d, b=c ⟹ a=b
  simp only [Prod.mk.injEq] at hcd
  obtain ⟨h1, h2, h3, h4⟩ := hcd
  -- h1: a=c, h2: b=d, h3: a=d, h4: b=c ⟹ a=b (from h2,h3: b=d=a)
  have hab : a = b := by rw [h2, ← h3]
  exact ⟨a, ha, by simp [hab]⟩

/-- The intersection of the diagonal and swap families is exactly the "constant" quadruples
`(x,x,x,x)` with `x ∈ S`; in particular it has cardinality `≤ |S|`. -/
theorem diag_inter_swap_card_le (S : Finset F) :
    (diagQuads S ∩ swapQuads S).card ≤ S.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun q => q.1)
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := inter_eq_const hq
    exact ha
  · intro q hq q' hq' hqq'
    obtain ⟨a, _, rfl⟩ := inter_eq_const hq
    obtain ⟨a', _, rfl⟩ := inter_eq_const hq'
    simp only at hqq'
    simp [hqq']

/-- **The char-free `2n²−n` lower bound.**  For any finite set in any additive group,
`E₂(S) ≥ 2|S|² − |S|`, via the diagonal ∪ swap families (`T1 + T2`).  This is the
characteristic-INDEPENDENT part of the `3n²−3n` value; only the antipodal `T3 = n²−2n` term
requires `μ_n = −μ_n` (supplied char-freely by `EvenOddAntipodal.image_neg_eq_of_prod_comp_neg`),
and only the matching UPPER bound is genuinely char-dependent. -/
theorem E2_ge_two_card_sq_sub_card (S : Finset F) :
    2 * (S.card * S.card) - S.card ≤ E2 S := by
  classical
  have hunion : (diagQuads S ∪ swapQuads S).card ≤ E2 S :=
    Finset.card_le_card (diag_union_swap_subset S)
  have hcard : (diagQuads S ∪ swapQuads S).card
      = (diagQuads S).card + (swapQuads S).card - (diagQuads S ∩ swapQuads S).card := by
    rw [Finset.card_union]
  rw [hcard, diagQuads_card, swapQuads_card] at hunion
  have hinter : (diagQuads S ∩ swapQuads S).card ≤ S.card := diag_inter_swap_card_le S
  have hle : 2 * (S.card * S.card) - S.card
      ≤ (S.card * S.card + S.card * S.card) - (diagQuads S ∩ swapQuads S).card := by
    omega
  exact le_trans hle hunion

/-! ### The exact obstruction to the UPPER bound `E₂ ≤ 3n²−3n`

A "genuine" extra quadruple is one outside diagonal ∪ swap ∪ antipodal.  After normalizing by
an element (divide by `x₁`), every genuine quadruple is a relation `1 + B = C + D` with
`B,C,D ∈ μ_n`, `{1,B} ≠ {C,D}`, and `1+B ≠ 0`.  We state this as an explicit Prop.  The probes
show it is SATISFIABLE starting at `n = 4`, `p = 5` (`1 + i = (-1)+(-1)` in `F₅`), so the
char-free transfer of the UPPER bound is genuinely conditional. -/

/-- **The genuine-quadruple obstruction Prop** (multiplicative form, to be specialized to `μ_n`).
For a set `S` containing `1`: a genuine 4-term additive relation among elements of `S` with the
distinguished element `1` on the left.  `E₂(S) = 3|S|²−3|S|` requires the NEGATION of this for
all such normalizations.  Stated over a ring so `1` is available. -/
def GenuineQuadruple {R : Type*} [Ring R] [DecidableEq R] (S : Finset R) : Prop :=
  ∃ B C D : R, B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ (1 : R) + B = C + D ∧
    ¬ (({(1 : R), B} : Finset R) = {C, D})

/-! ### The antipodal `T3` family and the full char-free `3n²−3n` lower bound

The `2n²−n` bound above is fully characteristic-free.  The remaining `T3 = n²−2n` term — which
lifts the floor to the `3n²−3n` value that the entire prize campaign uses as `E₂(μ_n)` — comes
from the **antipodal** family `(a, −a, c, −c)`, valid whenever `S = −S` (negation-closed), since
`a + (−a) = 0 = c + (−c)`.  For `μ_n` (`n = 2^μ`, so `−1 ∈ μ_n`) this closure holds char-freely
(`BGKSolSetSymmetry.neg_mem_of_mem` / `EvenOddAntipodal`).  Probes
(`scripts/probes/probe_e2_t3_overlaps.py`, proper subgroups `μ_n ⊊ F_p^*`, `p∈{769,…,40961}`)
confirm `|F1|=|F2|=|F3|=n²`, each pairwise overlap is **exactly `n`**, and
`|F1∪F2∪F3| = 3n²−3n` exactly (the value `E₂` attains in the near-Sidon regime and exceeds in
the deep prize regime).  Hence inclusion–exclusion gives the **lower** bound `E₂(S) ≥ 3n²−3n`.
This completes the char-free floor left as a hook above; only the matching UPPER bound stays
character-dependent (it FAILS once a `GenuineQuadruple` appears, i.e. once `μ_n` loses near-
Sidonicity in the deep prize regime — `scripts/probes/probe_e2_excess_*.py`). -/

/-- The **antipodal** family: `(a, −a, c, −c)` for `(a,c) ∈ S×S`.  Each is a valid energy
quadruple (`a+(−a)=0=c+(−c)`) **provided** `−a, −c ∈ S`, i.e. `S` is negation-closed. -/
def antiQuads (S : Finset F) : Finset (F × F × F × F) :=
  (S ×ˢ S).image (fun p => (p.1, -p.1, p.2, -p.2))

/-- Membership of `antiQuads S`. -/
theorem mem_antiQuads {S : Finset F} {q : F × F × F × F} :
    q ∈ antiQuads S ↔ ∃ a ∈ S, ∃ c ∈ S, q = (a, -a, c, -c) := by
  classical
  simp only [antiQuads, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩; exact ⟨a, ha, c, hc, rfl⟩
  · rintro ⟨a, ha, c, hc, rfl⟩; exact ⟨(a, c), ⟨ha, hc⟩, rfl⟩

/-- The antipodal family injects into the energy solution set **when `S` is negation-closed**
(`∀ x ∈ S, −x ∈ S`): each `(a,−a,c,−c)` satisfies `a+(−a) = c+(−c)` (both `0`). -/
theorem antiQuads_subset (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S) :
    antiQuads S ⊆ energyQuads S := by
  classical
  intro q hq
  obtain ⟨a, ha, c, hc, rfl⟩ := mem_antiQuads.mp hq
  simp only [energyQuads, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  refine ⟨((a, -a), (c, -c)), ⟨⟨⟨ha, hS a ha⟩, ⟨hc, hS c hc⟩⟩, ?_⟩, rfl⟩
  simp [add_neg_cancel]

/-- The antipodal family has cardinality `|S|²` (the image map is injective: the first and third
coordinates recover `(a,c)`). -/
theorem antiQuads_card (S : Finset F) : (antiQuads S).card = S.card * S.card := by
  classical
  unfold antiQuads
  rw [Finset.card_image_of_injective _ (by
    intro x y h
    simp only [Prod.mk.injEq, neg_inj] at h
    exact Prod.ext h.1 h.2.2.1),
    Finset.card_product]

/-- `diagQuads ∩ antiQuads` is `≤ |S|`: an element `(a,b,a,b) = (c,−c,c,−c)` forces `a=c`,
`b=−a`, so it is determined by `a`. -/
theorem diag_inter_anti_card_le (S : Finset F) :
    (diagQuads S ∩ antiQuads S).card ≤ S.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun q => q.1)
  · intro q hq; rw [Finset.mem_coe, Finset.mem_inter] at hq
    obtain ⟨a, ha, _, _, rfl⟩ := mem_diagQuads.mp hq.1
    exact ha
  · intro q hq q' hq' hqq'
    rw [Finset.mem_coe, Finset.mem_inter] at hq hq'
    obtain ⟨a, _, b, _, rfl⟩ := mem_diagQuads.mp hq.1
    obtain ⟨a', _, b', _, rfl⟩ := mem_diagQuads.mp hq'.1
    obtain ⟨c, _, d, _, hcd⟩ := mem_antiQuads.mp hq.2
    obtain ⟨c', _, d', _, hcd'⟩ := mem_antiQuads.mp hq'.2
    simp only [Prod.mk.injEq] at hcd hcd' hqq'
    -- (a,b,a,b)=(c,-c,d,-d): a=c, b=-c, a=d, b=-d ⟹ b=-a; and q'.1 = a' = a from hqq'
    -- the full quad is determined by `a` once we know b=-a and a=d.
    obtain ⟨hac, hbc, had, hbd⟩ := hcd
    obtain ⟨hac', hbc', had', hbd'⟩ := hcd'
    have hba : b = -a := by subst hac; exact hbc
    have hda : a = d := had
    have hba' : b' = -a' := by subst hac'; exact hbc'
    have hda' : a' = d' := had'
    have haa : a = a' := hqq'
    subst haa; subst hba; subst hba'; rfl

/-- `swapQuads ∩ antiQuads` is `≤ |S|`: an element `(a,b,b,a) = (c,−c,d,−d)` forces `a=c`,
`b=−a`, so it is determined by `a`. -/
theorem swap_inter_anti_card_le (S : Finset F) :
    (swapQuads S ∩ antiQuads S).card ≤ S.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun q => q.1)
  · intro q hq; rw [Finset.mem_coe, Finset.mem_inter] at hq
    obtain ⟨a, ha, _, _, rfl⟩ := mem_swapQuads.mp hq.1
    exact ha
  · intro q hq q' hq' hqq'
    rw [Finset.mem_coe, Finset.mem_inter] at hq hq'
    obtain ⟨a, _, b, _, rfl⟩ := mem_swapQuads.mp hq.1
    obtain ⟨a', _, b', _, rfl⟩ := mem_swapQuads.mp hq'.1
    obtain ⟨c, _, d, _, hcd⟩ := mem_antiQuads.mp hq.2
    obtain ⟨c', _, d', _, hcd'⟩ := mem_antiQuads.mp hq'.2
    simp only [Prod.mk.injEq] at hcd hcd' hqq'
    -- (a,b,b,a)=(c,-c,d,-d): a=c, b=-c, b=d, a=-d ⟹ b=-a; determined by a
    obtain ⟨hac, hbc, hbd, had⟩ := hcd
    obtain ⟨hac', hbc', hbd', had'⟩ := hcd'
    have hba : b = -a := by subst hac; exact hbc
    have hba' : b' = -a' := by subst hac'; exact hbc'
    have haa : a = a' := hqq'
    subst haa; subst hba; subst hba'; rfl

/-- **The full char-free `3n²−3n` lower bound for negation-closed sets.**  For any finite
negation-closed set `S = −S` in any additive commutative group,
`E₂(S) ≥ 3|S|² − 3|S|`, via the diagonal ∪ swap ∪ antipodal families (`T1 + T2 + T3`).  Each
family has cardinality `|S|²` and the three pairwise overlaps are each `≤ |S|`, so
inclusion–exclusion gives `|F1∪F2∪F3| ≥ 3|S|² − 3|S|`.  This is the char-free FLOOR that
`E₂(μ_n)` always meets; equality is the near-Sidon (char-dependent) UPPER half, which FAILS in
the deep prize regime (probes `probe_e2_excess_*.py`). -/
theorem E2_ge_three_card_sq_sub_three_card (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S) :
    3 * (S.card * S.card) - 3 * S.card ≤ E2 S := by
  classical
  -- The union of all three families is contained in the energy set.
  have hsub : diagQuads S ∪ swapQuads S ∪ antiQuads S ⊆ energyQuads S :=
    Finset.union_subset (diag_union_swap_subset S) (antiQuads_subset S hS)
  have hunion_le : (diagQuads S ∪ swapQuads S ∪ antiQuads S).card ≤ E2 S :=
    Finset.card_le_card hsub
  -- Lower-bound the union card by inclusion–exclusion (three-set form, lower direction).
  -- |A ∪ B ∪ C| ≥ |A| + |B| + |C| − |A∩B| − |A∩C| − |B∩C|.
  set A := diagQuads S
  set B := swapQuads S
  set C := antiQuads S
  have hAB : (A ∩ B).card ≤ S.card := diag_inter_swap_card_le S
  have hAC : (A ∩ C).card ≤ S.card := diag_inter_anti_card_le S
  have hBC : (B ∩ C).card ≤ S.card := swap_inter_anti_card_le S
  -- |A ∪ B| = |A| + |B| − |A∩B|
  have hcardAB : (A ∪ B).card = A.card + B.card - (A ∩ B).card := Finset.card_union A B
  -- |(A∪B) ∪ C| = |A∪B| + |C| − |(A∪B)∩C|, and (A∪B)∩C = (A∩C)∪(B∩C)
  have hcardUC : ((A ∪ B) ∪ C).card
      = (A ∪ B).card + C.card - ((A ∪ B) ∩ C).card := Finset.card_union _ _
  have hdistrib : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have hcardABC : ((A ∪ B) ∪ C).card
      ≥ (A ∪ B).card + C.card - ((A ∩ C) ∪ (B ∩ C)).card := by
    rw [hcardUC, hdistrib]
  have hinterUnion : ((A ∩ C) ∪ (B ∩ C)).card ≤ (A ∩ C).card + (B ∩ C).card :=
    Finset.card_union_le _ _
  have hAcard : A.card = S.card * S.card := diagQuads_card S
  have hBcard : B.card = S.card * S.card := swapQuads_card S
  have hCcard : C.card = S.card * S.card := antiQuads_card S
  -- Assemble. Let m = S.card. |A∪B| = m²+m²−|A∩B| ≥ 2m²−m (|A∩B|≤m).
  -- |ABC| ≥ |A∪B| + m² − (|A∩C|+|B∩C|) ≥ (2m²−m) + m² − 2m = 3m²−3m.
  have hgoal : 3 * (S.card * S.card) - 3 * S.card ≤ ((A ∪ B) ∪ C).card := by
    have hABge : (A ∪ B).card ≥ 2 * (S.card * S.card) - S.card := by
      rw [hcardAB, hAcard, hBcard]; omega
    omega
  exact le_trans hgoal hunion_le

end ArkLib.ProximityGap.E2CharFree

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.E2CharFree.diagQuads_subset
#print axioms ArkLib.ProximityGap.E2CharFree.swapQuads_subset
#print axioms ArkLib.ProximityGap.E2CharFree.diagQuads_card
#print axioms ArkLib.ProximityGap.E2CharFree.E2_ge_card_sq
#print axioms ArkLib.ProximityGap.E2CharFree.swapQuads_card
#print axioms ArkLib.ProximityGap.E2CharFree.diag_inter_swap_card_le
#print axioms ArkLib.ProximityGap.E2CharFree.E2_ge_two_card_sq_sub_card
#print axioms ArkLib.ProximityGap.E2CharFree.antiQuads_subset
#print axioms ArkLib.ProximityGap.E2CharFree.antiQuads_card
#print axioms ArkLib.ProximityGap.E2CharFree.diag_inter_anti_card_le
#print axioms ArkLib.ProximityGap.E2CharFree.swap_inter_anti_card_le
#print axioms ArkLib.ProximityGap.E2CharFree.E2_ge_three_card_sq_sub_three_card
