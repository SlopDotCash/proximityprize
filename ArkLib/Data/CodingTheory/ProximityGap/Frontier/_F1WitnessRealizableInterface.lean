/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._F1PolytopeMiddleCountermodel
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ47GeometricBalance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ50WitnessRealizability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ59EmptyMiddle

/-!
# F1 — the `WitnessRealizable` interface: binding the middle-band residual to real polynomials

## Where this sits

PR #528 (`_F1PolytopeMiddleCountermodel.lean`, merged at `5e1a2667e`) refuted the numeric statement

`SYZ50.Realizable a b c t k → ¬ SYZ59.middleBand a b c δ₁`

by the infinite family `(a,b,c,t,k,δ₁) = (d,d,d,d−2,2d−1,d+1)`, `d ≥ 6`: in that implication `δ₁`
does not occur in the antecedent, so the polytope predicate alone cannot carry the F1 middle
exclusion.  The independent review of #528 identified the missing object: a predicate binding the
numeric Venn profile to an **actual** rate-`1/2` band witness — a field, a `μ_{2k}` evaluation
domain, disjoint overlap regions, their vanishing polynomials `(W_AB, W_AC, W_BC)`, and the
**minimal product-degree `δ₁` of their syzygy module** (SYZ47 slot convention).  This file defines
that predicate (`WitnessRealizable`), proves the interface theorems that certify it is the right
strengthening, and restates the open F1 middle exclusion over it (`MiddleExclusion`), with the
PR #528 family as the canonical test corpus.

## What is proved here (all axiom-clean)

1. **Vanishing-polynomial toolkit** (§1): `vanishing S = ∏ (X − C s)` is monic of degree
   `S.card`, and disjoint regions give coprime vanishing polynomials.
2. **The numeric shadow** (§3, `realizable_of_witnessRealizable`): `WitnessRealizable` implies
   `SYZ50.Realizable`.  The domain-disjointness face `a+b+c+t ≤ 2k` is **derived** from the
   `μ_{2k}` domain by counting (`venn_card_face`), not assumed — only the SYZ37 budget cap and
   G172 interior slack are carried as band-stack constraints.
3. **The SYZ47 floor comes for free** (§4, `floor_of_witnessRealizable`):
   `max(a,b,c) ≤ δ₁` — the band constraints force the triangle inequalities
   (`SYZ47.band_forces_triangle`), disjointness forces pairwise coprimality, and
   `SYZ47.syzygy_product_degree_ge_max` applies to the minimal witness syzygy.  So the
   `hfloor` hypothesis of `SYZ69.two_class_law` / `classification_of_hilbert` is a **theorem**
   of this predicate, not an extra assumption.
4. **The pair-sum ceiling** (§4, `min_syzygy_le_pair_sums`): `δ₁ ≤ min(a+b, a+c, b+c)`, by the
   three trivial pair syzygies — the predicate can never hold with `δ₁` floating above the
   syzygy module it names.  Together with (3) this pins `δ₁` to the honest window
   `max(a,b,c) ≤ δ₁ ≤ min pair sums`.
5. **Two-class wiring** (§5, `two_class_of_witnessRealizable`): given SYZ44's Hilbert–Burch
   inputs (`RankNullity`, `TwoRamp`) and the middle exclusion for the profile, every
   witness-realizable triple is floor-attained or near-balance — the SYZ69 classification with
   its `hfloor` slot discharged by the polynomial data.
6. **The restated residual and its test corpus** (§6): `MiddleExclusion K` is the F1 open
   geometric residual over this predicate.  `middleExclusion_kills_family` /
   `family_witness_refutes_middleExclusion`: any discharge of `MiddleExclusion` must prove the
   PR #528 numeric family carries **no** polynomial witness at `δ₁ = d+1`, and conversely a
   single such witness refutes it.  `family_within_interface_window` records in checkable form
   that the interface theorems (3)–(4) do **not** decide the family: the exclusion is genuinely
   open at this interface.

## Scope honesty

* `MiddleExclusion` is **NOT proved** here, for any field.  It is the SYZ45 geometric residual
  ("no realizable low-degree non-constant dependence"), which SYZ45 proved is not an algebraic
  identity and SYZ49 identified with the BGK additive-log-phase level-set wall.  Nothing here
  touches that wall.
* Non-vacuity of `WitnessRealizable` at the polynomial level is the SYZ50 Question-C empirical
  fact (357 constant-syzygy witnesses on `μ₁₄ ⊂ 𝔽₂₉`); it is **not** formalized here.  This
  file is statement-interface plus elementary polynomial theory; it constructs no witnesses.
* The predicate models the rate-`1/2` reduced band triple exactly as the lane does: reduced
  degrees = region cardinalities (the triple region `T` is factored out of the reduced
  polynomials), SYZ37 `t`-loaded budget, G172 interior slack, SYZ47 slot product-degree.
* δ* is untouched; the three-face open surface (F1/F2/F3) is unchanged.  **CORE remains
  OPEN / ON-BGK.**
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.F1WitnessRealizable

open Polynomial

variable {K : Type*} [Field K]

/-! ## 1. Vanishing polynomials of Venn regions -/

/-- The **vanishing polynomial** of a region `S ⊆ K`: `∏ s ∈ S, (X − C s)`.  In the lane's
reduced-triple convention, `W_AB = vanishing S_AB` etc., so the reduced degree of each band
polynomial is the cardinality of its pairwise-exclusive overlap region. -/
noncomputable def vanishing (S : Finset K) : K[X] := ∏ s ∈ S, (X - C s)

/-- `vanishing S` is monic. -/
theorem vanishing_monic (S : Finset K) : (vanishing S).Monic :=
  monic_prod_of_monic S _ fun s _ => monic_X_sub_C s

/-- `vanishing S` is nonzero. -/
theorem vanishing_ne_zero (S : Finset K) : vanishing S ≠ 0 :=
  (vanishing_monic S).ne_zero

/-- The reduced degree of a region's vanishing polynomial is the region's cardinality. -/
theorem vanishing_natDegree (S : Finset K) : (vanishing S).natDegree = S.card := by
  unfold vanishing
  rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_sub_C s]
  simp

/-- **Disjoint regions have coprime vanishing polynomials.**  Root-disjointness is exactly
pairwise coprimality of the linear factors, which lifts through the products.  This is the
hypothesis SYZ47's floor machinery consumes. -/
theorem vanishing_isCoprime {S₁ S₂ : Finset K} (h : Disjoint S₁ S₂) :
    IsCoprime (vanishing S₁) (vanishing S₂) := by
  unfold vanishing
  refine IsCoprime.prod_left fun s hs => IsCoprime.prod_right fun r hr => ?_
  have hne : s ≠ r := fun hsr => Finset.disjoint_left.mp h hs (hsr ▸ hr)
  exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-! ## 2. The syzygy-module minimal product-degree, and the predicate -/

/-- **A syzygy of slot product-degree `≤ δ`** (SYZ47 slot convention): a nonzero cofactor triple
`(s_AB, s_AC, s_BC)` with `W_AB s_AB + W_AC s_AC + W_BC s_BC = 0` and every slot product-degree
`deg(W_slot · s_slot) ≤ δ`. -/
def SyzygyOfDegreeLe (WAB WAC WBC : K[X]) (δ : ℕ) : Prop :=
  ∃ sAB sAC sBC : K[X],
    WAB * sAB + WAC * sAC + WBC * sBC = 0 ∧
    ¬ (sAB = 0 ∧ sAC = 0 ∧ sBC = 0) ∧
    (WAB * sAB).natDegree ≤ δ ∧ (WAC * sAC).natDegree ≤ δ ∧ (WBC * sBC).natDegree ≤ δ

/-- **The minimal syzygy product-degree is exactly `δ₁`**: a syzygy of product-degree `≤ δ₁`
exists, and no syzygy has product-degree `< δ₁`.  (The witness syzygy then has product-degree
exactly `δ₁`.)  This is the datum the refuted PR #528 antecedent left floating free. -/
def MinimalSyzygyDegree (WAB WAC WBC : K[X]) (δ₁ : ℕ) : Prop :=
  SyzygyOfDegreeLe WAB WAC WBC δ₁ ∧
  ∀ δ : ℕ, SyzygyOfDegreeLe WAB WAC WBC δ → δ₁ ≤ δ

/-- **The Venn-region data of a rate-`1/2` band witness.**  A `μ_{2k}` evaluation domain `Ω`
(every point a `2k`-th root of unity, exactly `2k` of them) hosting the three pairwise-exclusive
overlap regions and the triple region as pairwise-disjoint subsets of the prescribed sizes. -/
def VennRegions (Ω SAB SAC SBC T : Finset K) (a b c t k : ℕ) : Prop :=
  (∀ x ∈ Ω, x ^ (2 * k) = 1) ∧ Ω.card = 2 * k ∧
  SAB ⊆ Ω ∧ SAC ⊆ Ω ∧ SBC ⊆ Ω ∧ T ⊆ Ω ∧
  Disjoint SAB SAC ∧ Disjoint SAB SBC ∧ Disjoint SAB T ∧
  Disjoint SAC SBC ∧ Disjoint SAC T ∧ Disjoint SBC T ∧
  SAB.card = a ∧ SAC.card = b ∧ SBC.card = c ∧ T.card = t

/-- **The band-stack constraints** carried as numeric hypotheses: nonempty overlap regions, the
SYZ37 `t`-loaded budget cap, and the G172 interior slack.  These encode that the regions arise
from an over-budget band stack; they are exactly `SYZ50.Realizable` **minus** its
domain-disjointness face, which `venn_card_face` derives from the domain instead. -/
def BandStack (a b c t k : ℕ) : Prop :=
  1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
  max a (max b c) + 1 + t ≤ k ∧
  2 * k + 1 ≤ a + b + c + 2 * t

/-- **The missing predicate (PR #528 review, §5).**  `WitnessRealizable K a b c t k δ₁`: there is
an actual rate-`1/2` band witness over `K` — a `μ_{2k}` domain, disjoint Venn regions of sizes
`(a,b,c,t)` satisfying the band-stack constraints — whose reduced vanishing triple
`(W_AB, W_AC, W_BC)` has syzygy-module minimal product-degree **exactly** `δ₁`.  Unlike
`SYZ50.Realizable`, the parameter `δ₁` is bound to the polynomial data. -/
def WitnessRealizable (K : Type*) [Field K] (a b c t k δ₁ : ℕ) : Prop :=
  ∃ Ω SAB SAC SBC T : Finset K,
    VennRegions Ω SAB SAC SBC T a b c t k ∧
    BandStack a b c t k ∧
    MinimalSyzygyDegree (vanishing SAB) (vanishing SAC) (vanishing SBC) δ₁

/-! ## 3. The numeric shadow: `WitnessRealizable → SYZ50.Realizable` -/

/-- **The domain-disjointness face is a theorem of the domain.**  Four pairwise-disjoint regions
inside a `2k`-point domain have total cardinality `≤ 2k`.  This is the face of the SYZ50
polytope that the polynomial model *derives* rather than assumes. -/
theorem venn_card_face {Ω SAB SAC SBC T : Finset K} {a b c t k : ℕ}
    (hV : VennRegions Ω SAB SAC SBC T a b c t k) :
    a + b + c + t ≤ 2 * k := by
  classical
  obtain ⟨-, hΩcard, hsAB, hsAC, hsBC, hsT, h12, h13, h1T, h23, h2T, h3T, ha, hb, hc, ht⟩ := hV
  have hd1 : Disjoint (SAB ∪ SAC) SBC := Finset.disjoint_union_left.mpr ⟨h13, h23⟩
  have hd2 : Disjoint (SAB ∪ SAC ∪ SBC) T :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h1T, h2T⟩, h3T⟩
  have hcards : (SAB ∪ SAC ∪ SBC ∪ T).card = a + b + c + t := by
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint h12, ha, hb, hc, ht]
  have hsub : SAB ∪ SAC ∪ SBC ∪ T ⊆ Ω :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset hsAB hsAC) hsBC) hsT
  calc a + b + c + t = (SAB ∪ SAC ∪ SBC ∪ T).card := hcards.symm
    _ ≤ Ω.card := Finset.card_le_card hsub
    _ = 2 * k := hΩcard

/-- **The numeric shadow.**  Every witness-realizable profile is polytope-realizable: the
band-stack constraints supply five of the six `SYZ50.Realizable` conjuncts, and the
domain-disjointness face is derived by `venn_card_face`.  So `WitnessRealizable` genuinely
strengthens the antecedent PR #528 refuted. -/
theorem realizable_of_witnessRealizable {a b c t k δ₁ : ℕ}
    (hW : WitnessRealizable K a b c t k δ₁) : SYZ50.Realizable a b c t k := by
  obtain ⟨Ω, SAB, SAC, SBC, T, hV, ⟨ha1, hb1, hc1, hbud, hslack⟩, -⟩ := hW
  exact ⟨ha1, hb1, hc1, venn_card_face hV, hbud, hslack⟩

/-- **The overlap regions never exhaust the domain** (numeric form).  The slack forces `t ≥ 1`
(`SYZ50.realizable_forces_triple`), so `a + b + c < 2k`: no witness-realizable profile fills the
whole `μ_{2k}` with its three pairwise regions.  This is the polynomial-level record of the
SYZ50 Question-B verdict (the whole-subgroup SYZ49 `μ₁₂` witness is one domain point short). -/
theorem regions_proper_of_witnessRealizable {a b c t k δ₁ : ℕ}
    (hW : WitnessRealizable K a b c t k δ₁) : a + b + c < 2 * k := by
  have h := realizable_of_witnessRealizable hW
  have ht := SYZ50.realizable_forces_triple h
  obtain ⟨-, -, -, hface, -, -⟩ := h
  omega

/-- **Balanced witness-realizable profiles need `n ≥ 3d + 1`** — SYZ50's domain lower bound,
transported through the shadow. -/
theorem balanced_needs_domain_of_witnessRealizable {d t k δ₁ : ℕ}
    (hW : WitnessRealizable K d d d t k δ₁) : 3 * d + 1 ≤ 2 * k :=
  SYZ50.balanced_profile_needs_domain (realizable_of_witnessRealizable hW)

/-! ## 4. The interface window: the SYZ47 floor and the pair-sum ceiling -/

/-- **The SYZ47 floor holds automatically.**  For a witness-realizable profile,
`max(a,b,c) ≤ δ₁`: the band-stack constraints force the triangle inequalities
(`SYZ47.band_forces_triangle` at budget `k − 1 − t`), region disjointness forces pairwise
coprimality of the vanishing triple, and `SYZ47.syzygy_product_degree_ge_max` applied to the
minimal witness syzygy yields the floor.  Consequence: the `hfloor` hypothesis of
`SYZ69.two_class_law` is discharged by the polynomial data — it is not an extra assumption on
this predicate. -/
theorem floor_of_witnessRealizable {a b c t k δ₁ : ℕ}
    (hW : WitnessRealizable K a b c t k δ₁) : max a (max b c) ≤ δ₁ := by
  obtain ⟨Ω, SAB, SAC, SBC, T, hV, ⟨ha1, hb1, hc1, hbud, hslack⟩, hmin⟩ := hW
  obtain ⟨-, -, -, -, -, -, h12, h13, -, h23, -, -, ha, hb, hc, -⟩ := hV
  obtain ⟨⟨sAB, sAC, sBC, hsyz, hnz, hAB, hAC, hBC⟩, -⟩ := hmin
  have hdegAB : (vanishing SAB).natDegree = a := by rw [vanishing_natDegree, ha]
  have hdegAC : (vanishing SAC).natDegree = b := by rw [vanishing_natDegree, hb]
  have hdegBC : (vanishing SBC).natDegree = c := by rw [vanishing_natDegree, hc]
  have htri := SYZ47.band_forces_triangle a b c (k - 1 - t)
    (by omega) (by omega) (by omega) (by omega)
  have hfloor := SYZ47.syzygy_product_degree_ge_max
    (vanishing SAB) (vanishing SAC) (vanishing SBC) sAB sAC sBC δ₁
    (vanishing_isCoprime h12) (vanishing_isCoprime h13) (vanishing_isCoprime h23)
    (vanishing_ne_zero _) (vanishing_ne_zero _) (vanishing_ne_zero _)
    (by rw [hdegAB, hdegAC, hdegBC]; omega)
    (by rw [hdegAB, hdegAC, hdegBC]; omega)
    (by rw [hdegAB, hdegAC, hdegBC]; omega)
    hsyz hnz hAB hAC hBC
  rw [hdegAB, hdegAC, hdegBC] at hfloor
  exact hfloor

/-- **The pair-sum ceiling.**  The three trivial pair syzygies — e.g.
`W_AB · W_AC + W_AC · (−W_AB) + W_BC · 0 = 0` of product-degree `a + b` — witness
`SyzygyOfDegreeLe` at each pairwise degree sum, so minimality forces
`δ₁ ≤ a+b`, `δ₁ ≤ a+c`, and `δ₁ ≤ b+c`.  The predicate can never hold with `δ₁` floating above
the syzygy module it names; together with the floor this pins `δ₁` to the honest window
`max(a,b,c) ≤ δ₁ ≤ min(a+b, a+c, b+c)`. -/
theorem min_syzygy_le_pair_sums {a b c t k δ₁ : ℕ}
    (hW : WitnessRealizable K a b c t k δ₁) :
    δ₁ ≤ a + b ∧ δ₁ ≤ a + c ∧ δ₁ ≤ b + c := by
  obtain ⟨Ω, SAB, SAC, SBC, T, hV, -, hmin⟩ := hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ha, hb, hc, -⟩ := hV
  obtain ⟨-, hlow⟩ := hmin
  have hdegAB : (vanishing SAB).natDegree = a := by rw [vanishing_natDegree, ha]
  have hdegAC : (vanishing SAC).natDegree = b := by rw [vanishing_natDegree, hb]
  have hdegBC : (vanishing SBC).natDegree = c := by rw [vanishing_natDegree, hc]
  refine ⟨hlow _ ?_, hlow _ ?_, hlow _ ?_⟩
  · -- pair (AB, AC): cofactors (W_AC, −W_AB, 0), product-degree a + b
    refine ⟨vanishing SAC, -(vanishing SAB), 0, by ring,
      fun h => vanishing_ne_zero SAC h.1, ?_, ?_, by simp⟩
    · rw [natDegree_mul (vanishing_ne_zero _) (vanishing_ne_zero _), hdegAB, hdegAC]
    · rw [mul_neg, natDegree_neg,
        natDegree_mul (vanishing_ne_zero _) (vanishing_ne_zero _), hdegAC, hdegAB]
      omega
  · -- pair (AB, BC): cofactors (W_BC, 0, −W_AB), product-degree a + c
    refine ⟨vanishing SBC, 0, -(vanishing SAB), by ring,
      fun h => vanishing_ne_zero SBC h.1, ?_, by simp, ?_⟩
    · rw [natDegree_mul (vanishing_ne_zero _) (vanishing_ne_zero _), hdegAB, hdegBC]
    · rw [mul_neg, natDegree_neg,
        natDegree_mul (vanishing_ne_zero _) (vanishing_ne_zero _), hdegBC, hdegAB]
      omega
  · -- pair (AC, BC): cofactors (0, W_BC, −W_AC), product-degree b + c
    refine ⟨0, vanishing SBC, -(vanishing SAC), by ring,
      fun h => vanishing_ne_zero SBC h.2.1, by simp, ?_, ?_⟩
    · rw [natDegree_mul (vanishing_ne_zero _) (vanishing_ne_zero _), hdegAC, hdegBC]
    · rw [mul_neg, natDegree_neg,
        natDegree_mul (vanishing_ne_zero _) (vanishing_ne_zero _), hdegBC, hdegAC]
      omega

/-! ## 5. Two-class wiring: the SYZ69 classification with `hfloor` discharged -/

/-- **The two-class law for witness-realizable profiles.**  Given SYZ44's Hilbert–Burch inputs
(`RankNullity`, `TwoRamp` — the degree-sum law engine) and the middle exclusion for this
profile, every witness-realizable triple is floor-attained or near-balance.  This is
`SYZ69.classification_of_hilbert` with its bare `hfloor` hypothesis **discharged** by
`floor_of_witnessRealizable`: the polynomial data carries the floor. -/
theorem two_class_of_witnessRealizable
    (hilb : ℕ → ℕ) {a b c t k δ₁ : ℕ} (δ₂ D₀ : ℕ)
    (hW : WitnessRealizable K a b c t k δ₁)
    (hRankNull : SYZ44.RankNullity hilb a b c D₀)
    (hTwoRamp : SYZ44.TwoRamp hilb δ₁ δ₂)
    (hle : δ₁ ≤ δ₂)
    (hno_middle : ¬ SYZ59.middleBand a b c δ₁) :
    (δ₁ = max a (max b c)) ∨ SYZ45.imbalance a b c δ₁ ≤ 1 := by
  have hsum : δ₁ + δ₂ = a + b + c :=
    SYZ44.degree_sum_of_hilbert hilb a b c δ₁ δ₂ D₀ hRankNull hTwoRamp
  exact SYZ59.empty_middle_dichotomy a b c δ₁ δ₂ hsum hle
    (floor_of_witnessRealizable hW) hno_middle

/-! ## 6. The restated open residual, and the PR #528 test corpus -/

/-- **The F1 middle exclusion over the witness predicate (OPEN — this file does not prove it).**
No witness-realizable profile over `K` sits in the middle band.  Unlike the numeric statement
PR #528 refuted, `δ₁` here is bound to the minimal syzygy product-degree of actual band witness
polynomials: this is the genuine SYZ45 geometric residual ("no realizable low-degree
non-constant dependence"), which SYZ49 identifies with the BGK level-set wall. -/
def MiddleExclusion (K : Type*) [Field K] : Prop :=
  ∀ a b c t k δ₁ : ℕ, WitnessRealizable K a b c t k δ₁ → ¬ SYZ59.middleBand a b c δ₁

/-- **A discharge must kill the PR #528 corpus.**  If `MiddleExclusion K` holds, then no member
of the PR #528 countermodel family `(d,d,d,d−2,2d−1)` carries a polynomial witness with minimal
syzygy product-degree `d+1`: the family's numeric middle-band membership is consumed directly
from the merged countermodel file (`F1PolytopeMiddleCountermodel.middleBand_family`). -/
theorem middleExclusion_kills_family (hEx : MiddleExclusion K) {d : ℕ} (hd : 6 ≤ d) :
    ¬ WitnessRealizable K d d d (d - 2) (2 * d - 1) (d + 1) := fun hW =>
  hEx d d d (d - 2) (2 * d - 1) (d + 1) hW
    (F1PolytopeMiddleCountermodel.middleBand_family d hd)

/-- **A single family witness refutes the exclusion.**  Conversely, exhibiting actual band
witness polynomials realizing any family profile at `δ₁ = d + 1` refutes `MiddleExclusion K`.
The PR #528 family is therefore the canonical first test corpus for any proposed discharge, in
both directions. -/
theorem family_witness_refutes_middleExclusion {d : ℕ} (hd : 6 ≤ d)
    (hW : WitnessRealizable K d d d (d - 2) (2 * d - 1) (d + 1)) :
    ¬ MiddleExclusion K :=
  fun hEx => middleExclusion_kills_family hEx hd hW

/-- **The interface window does not decide the corpus (honesty record).**  For the family
profile `(d,d,d)` at `δ₁ = d+1`, the §4 floor allows it (`max = d ≤ d+1`) and the pair-sum
ceiling allows it (`d+1 ≤ 2d` for `d ≥ 1`): the theorems of this file leave the middle
exclusion genuinely open on the corpus, as they must — nothing here touches the BGK wall. -/
theorem family_within_interface_window {d : ℕ} (hd : 6 ≤ d) :
    max d (max d d) ≤ d + 1 ∧ d + 1 ≤ d + d := by
  omega

end ArkLib.ProximityGap.F1WitnessRealizable

-- Honesty audit:
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.vanishing_monic
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.vanishing_ne_zero
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.vanishing_natDegree
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.vanishing_isCoprime
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.venn_card_face
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.realizable_of_witnessRealizable
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.regions_proper_of_witnessRealizable
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.balanced_needs_domain_of_witnessRealizable
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.floor_of_witnessRealizable
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.min_syzygy_le_pair_sums
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.two_class_of_witnessRealizable
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.middleExclusion_kills_family
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.family_witness_refutes_middleExclusion
#print axioms ArkLib.ProximityGap.F1WitnessRealizable.family_within_interface_window
