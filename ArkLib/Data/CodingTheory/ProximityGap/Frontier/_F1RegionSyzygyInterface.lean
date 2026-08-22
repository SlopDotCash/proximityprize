/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._F1PolytopeMiddleCountermodel
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ47GeometricBalance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ50WitnessRealizability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ59EmptyMiddle

/-!
# F1 — the region-syzygy realizability interface for the middle-band residual

## Where this sits

PR #528 (`_F1PolytopeMiddleCountermodel.lean`, merged at `5e1a2667e`) refuted the numeric statement

`SYZ50.Realizable a b c t k → ¬ SYZ59.middleBand a b c δ₁`

by the infinite family `(a,b,c,t,k,δ₁) = (d,d,d,d−2,2d−1,d+1)`, `d ≥ 6`: in that implication `δ₁`
does not occur in the antecedent, so the polytope predicate alone cannot carry the F1 middle
exclusion.  This file adds the next layer: a predicate (`RegionSyzygyRealizable`) binding the
numeric Venn profile to on-domain region data — a `μ_{2k}` evaluation domain, disjoint overlap
regions, their vanishing polynomials `(W_AB, W_AC, W_BC)` — and the **minimal product-degree `δ₁`
of the vanishing triple's syzygy module** (SYZ47 slot convention), together with the interface
theorems certifying the binding.

## What the predicate is NOT (scope fixed by the independent review of #529)

`RegionSyzygyRealizable` contains region and syzygy data **only**.  It has no stack `u`, no
codeword witnesses, no condition that the regions are the agreement/Venn regions of such
witnesses, and no bridge to `mcaEvent`, the G87 syndrome configuration, or SYZ42 realizability.
Its `BandStack` conjuncts are **necessary arithmetic faces** of an over-budget band stack, not a
stack-realization certificate.  Any synthetic on-domain Venn partition whose vanishing triple has
the requested minimal syzygy degree satisfies the predicate.  Whether such region/syzygy data
arises from a genuine over-budget stack is the unchanged open **SYZ42/SYZ28 lift gate**
(`_SYZ50WitnessRealizability.lean`, Question D).  The three layers, ordered by information
content, with each inclusion possibly strict:

* numeric polytope profiles (`SYZ50.Realizable`) — weakest;
* on-domain region/syzygy configurations (**this file**, `RegionSyzygyRealizable`);
* genuine stack-induced witnesses — **not formalized anywhere in-tree yet**; reaching them from
  this layer is the lift gate.

Consequently `RegionMiddleExclusion` is a **sufficient-side conjecture**, not a restatement of
the genuine F1 residual: it quantifies over a potentially strict superset of genuine F1
witnesses, and it could fail on a synthetic region triple even if the genuine F1 statement
holds.  `middleExclusion_transport` records the usable direction — for any future
genuine-witness predicate that factors through this layer, discharging `RegionMiddleExclusion`
discharges the genuine middle exclusion.  The converse direction needs the lift gate and is
**not** claimed.

## What is proved here (all axiom-clean)

1. **Vanishing-polynomial toolkit** (§1): `vanishing S = ∏ (X − C s)` is monic of degree
   `S.card`, and disjoint regions give coprime vanishing polynomials.
2. **The numeric shadow** (§3, `realizable_of_regionSyzygyRealizable`): `RegionSyzygyRealizable`
   implies `SYZ50.Realizable`.  The domain-disjointness face `a+b+c+t ≤ 2k` is **derived** from
   the `μ_{2k}` domain by counting (`venn_card_face`), not assumed — only the SYZ37 budget cap
   and G172 interior slack are carried as band-stack constraints.
3. **The SYZ47 floor comes for free** (§4, `floor_of_regionSyzygyRealizable`):
   `max(a,b,c) ≤ δ₁` — the band constraints force the triangle inequalities
   (`SYZ47.band_forces_triangle`), disjointness forces pairwise coprimality, and
   `SYZ47.syzygy_product_degree_ge_max` applies to the minimal syzygy.  So the `hfloor`
   hypothesis of `SYZ69.two_class_law` / `classification_of_hilbert` is a **theorem** of this
   predicate, not an extra assumption.
4. **The pair-sum ceiling** (§4, `min_syzygy_le_pair_sums`): `δ₁ ≤ min(a+b, a+c, b+c)`, by the
   three trivial pair syzygies — the predicate can never hold with `δ₁` floating above the
   syzygy module it names.  Together with (3) this pins `δ₁` to the honest window
   `max(a,b,c) ≤ δ₁ ≤ min pair sums`.
5. **Two-class wiring** (§5, `two_class_of_regionSyzygyRealizable`): given SYZ44's Hilbert–Burch
   inputs (`RankNullity`, `TwoRamp`) and the middle exclusion for the profile, every
   region-syzygy-realizable triple is floor-attained or near-balance — the SYZ69 classification
   with its `hfloor` slot discharged by the polynomial data.
6. **The sufficient-side conjecture and its test corpus** (§6): `RegionMiddleExclusion K` is the
   middle exclusion over this layer — sufficient for, possibly strictly stronger than, the
   genuine F1 residual (`middleExclusion_transport` is the precise transport statement).
   `regionMiddleExclusion_kills_family` / `family_witness_refutes_regionMiddleExclusion`: any
   discharge must prove the PR #528 numeric family carries **no** region/syzygy configuration at
   `δ₁ = d+1`, and conversely a single such configuration refutes it.
   `family_within_interface_window` records in checkable form that the interface theorems
   (3)–(4) do **not** decide the family: the exclusion is genuinely open at this interface.

## Scope honesty

* **The stack layer is absent by design.**  Nothing here certifies that region/syzygy data comes
  from an actual over-budget band stack; that bridge is the open SYZ42/SYZ28 lift gate, and this
  file does not attack it.  `regionMiddleExclusion_kills_family` excludes region/syzygy
  configurations for the family profiles; it does **not** show the family cannot arise from an
  actual over-budget witness stack.
* `RegionMiddleExclusion` is **NOT proved** here, for any field.  On the region-syzygy layer it
  is the SYZ45-shaped geometric obstruction ("no realizable low-degree non-constant
  dependence"), which SYZ49 identifies with the BGK additive-log-phase level-set wall.  Nothing
  here touches that wall.
* Non-vacuity of `RegionSyzygyRealizable` at the polynomial level is the SYZ50 Question-C
  empirical fact (357 constant-syzygy witnesses on `μ₁₄ ⊂ 𝔽₂₉`); it is **not** formalized here.
  This file is statement-interface plus elementary polynomial theory; it constructs no
  witnesses.
* The predicate models the rate-`1/2` reduced band triple **shape** exactly as the lane does:
  reduced degrees = region cardinalities (the triple region `T` is factored out of the reduced
  polynomials), SYZ37 `t`-loaded budget, G172 interior slack, SYZ47 slot product-degree.
* δ* is untouched; the three-face open surface (F1/F2/F3) is unchanged.  **CORE remains
  OPEN / ON-BGK.**
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.F1RegionSyzygy

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
exists, and no syzygy has product-degree `< δ₁`.  (The minimal syzygy then has product-degree
exactly `δ₁`.)  This is the datum the refuted PR #528 antecedent left floating free. -/
def MinimalSyzygyDegree (WAB WAC WBC : K[X]) (δ₁ : ℕ) : Prop :=
  SyzygyOfDegreeLe WAB WAC WBC δ₁ ∧
  ∀ δ : ℕ, SyzygyOfDegreeLe WAB WAC WBC δ → δ₁ ≤ δ

/-- **The Venn-region shape at a numeric profile.**  A `μ_{2k}` evaluation domain `Ω` (every
point a `2k`-th root of unity, exactly `2k` of them) hosting three pairwise-exclusive overlap
regions and a triple region as pairwise-disjoint subsets of the prescribed sizes.  This is the
*shape* of a band witness's agreement regions; nothing here ties the regions to any actual
witness stack. -/
def VennRegions (Ω SAB SAC SBC T : Finset K) (a b c t k : ℕ) : Prop :=
  (∀ x ∈ Ω, x ^ (2 * k) = 1) ∧ Ω.card = 2 * k ∧
  SAB ⊆ Ω ∧ SAC ⊆ Ω ∧ SBC ⊆ Ω ∧ T ⊆ Ω ∧
  Disjoint SAB SAC ∧ Disjoint SAB SBC ∧ Disjoint SAB T ∧
  Disjoint SAC SBC ∧ Disjoint SAC T ∧ Disjoint SBC T ∧
  SAB.card = a ∧ SAC.card = b ∧ SBC.card = c ∧ T.card = t

/-- **The band-stack numeric faces**: nonempty overlap regions, the SYZ37 `t`-loaded budget cap,
and the G172 interior slack.  These are **necessary arithmetic faces** of an over-budget band
stack — NOT a stack-realization certificate (that bridge is the open SYZ42/SYZ28 lift gate).
They are exactly `SYZ50.Realizable` **minus** its domain-disjointness face, which
`venn_card_face` derives from the domain instead. -/
def BandStack (a b c t k : ℕ) : Prop :=
  1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
  max a (max b c) + 1 + t ≤ k ∧
  2 * k + 1 ≤ a + b + c + 2 * t

/-- **The region-syzygy realizability layer** (scope fixed by the independent review of #529).
`RegionSyzygyRealizable K a b c t k δ₁`: over `K` there is an on-domain region/syzygy
configuration — a `μ_{2k}` domain and disjoint Venn regions of sizes `(a,b,c,t)` satisfying the
band-stack numeric faces — whose vanishing triple `(W_AB, W_AC, W_BC)` has syzygy-module minimal
product-degree **exactly** `δ₁`.  Unlike `SYZ50.Realizable`, the parameter `δ₁` is bound to
polynomial data; unlike a genuine witness predicate, no stack, codewords, or agreement condition
appears — see the module docstring for the three-layer map. -/
def RegionSyzygyRealizable (K : Type*) [Field K] (a b c t k δ₁ : ℕ) : Prop :=
  ∃ Ω SAB SAC SBC T : Finset K,
    VennRegions Ω SAB SAC SBC T a b c t k ∧
    BandStack a b c t k ∧
    MinimalSyzygyDegree (vanishing SAB) (vanishing SAC) (vanishing SBC) δ₁

/-! ## 3. The numeric shadow: `RegionSyzygyRealizable → SYZ50.Realizable` -/

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

/-- **The numeric shadow.**  Every region-syzygy-realizable profile is polytope-realizable: the
band-stack faces supply five of the six `SYZ50.Realizable` conjuncts, and the
domain-disjointness face is derived by `venn_card_face`.  So `RegionSyzygyRealizable` genuinely
strengthens the antecedent PR #528 refuted. -/
theorem realizable_of_regionSyzygyRealizable {a b c t k δ₁ : ℕ}
    (hW : RegionSyzygyRealizable K a b c t k δ₁) : SYZ50.Realizable a b c t k := by
  obtain ⟨Ω, SAB, SAC, SBC, T, hV, ⟨ha1, hb1, hc1, hbud, hslack⟩, -⟩ := hW
  exact ⟨ha1, hb1, hc1, venn_card_face hV, hbud, hslack⟩

/-- **The overlap regions never exhaust the domain** (numeric form).  The slack forces `t ≥ 1`
(`SYZ50.realizable_forces_triple`), so `a + b + c < 2k`: no region-syzygy-realizable profile
fills the whole `μ_{2k}` with its three pairwise regions.  This is the polynomial-level record
of the SYZ50 Question-B verdict (the whole-subgroup SYZ49 `μ₁₂` witness is one domain point
short). -/
theorem regions_proper_of_regionSyzygyRealizable {a b c t k δ₁ : ℕ}
    (hW : RegionSyzygyRealizable K a b c t k δ₁) : a + b + c < 2 * k := by
  have h := realizable_of_regionSyzygyRealizable hW
  have ht := SYZ50.realizable_forces_triple h
  obtain ⟨-, -, -, hface, -, -⟩ := h
  omega

/-- **Balanced region-syzygy-realizable profiles need `n ≥ 3d + 1`** — SYZ50's domain lower
bound, transported through the shadow. -/
theorem balanced_needs_domain_of_regionSyzygyRealizable {d t k δ₁ : ℕ}
    (hW : RegionSyzygyRealizable K d d d t k δ₁) : 3 * d + 1 ≤ 2 * k :=
  SYZ50.balanced_profile_needs_domain (realizable_of_regionSyzygyRealizable hW)

/-! ## 4. The interface window: the SYZ47 floor and the pair-sum ceiling -/

/-- **The SYZ47 floor holds automatically.**  For a region-syzygy-realizable profile,
`max(a,b,c) ≤ δ₁`: the band-stack faces force the triangle inequalities
(`SYZ47.band_forces_triangle` at budget `k − 1 − t`), region disjointness forces pairwise
coprimality of the vanishing triple, and `SYZ47.syzygy_product_degree_ge_max` applied to the
minimal syzygy yields the floor.  Consequence: the `hfloor` hypothesis of
`SYZ69.two_class_law` is discharged by the polynomial data — it is not an extra assumption on
this predicate. -/
theorem floor_of_regionSyzygyRealizable {a b c t k δ₁ : ℕ}
    (hW : RegionSyzygyRealizable K a b c t k δ₁) : max a (max b c) ≤ δ₁ := by
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
    (hW : RegionSyzygyRealizable K a b c t k δ₁) :
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

/-- **The two-class law for region-syzygy-realizable profiles.**  Given SYZ44's Hilbert–Burch
inputs (`RankNullity`, `TwoRamp` — the degree-sum law engine) and the middle exclusion for this
profile, every region-syzygy-realizable triple is floor-attained or near-balance.  This is
`SYZ69.classification_of_hilbert` with its bare `hfloor` hypothesis **discharged** by
`floor_of_regionSyzygyRealizable`: the polynomial data carries the floor. -/
theorem two_class_of_regionSyzygyRealizable
    (hilb : ℕ → ℕ) {a b c t k δ₁ : ℕ} (δ₂ D₀ : ℕ)
    (hW : RegionSyzygyRealizable K a b c t k δ₁)
    (hRankNull : SYZ44.RankNullity hilb a b c D₀)
    (hTwoRamp : SYZ44.TwoRamp hilb δ₁ δ₂)
    (hle : δ₁ ≤ δ₂)
    (hno_middle : ¬ SYZ59.middleBand a b c δ₁) :
    (δ₁ = max a (max b c)) ∨ SYZ45.imbalance a b c δ₁ ≤ 1 := by
  have hsum : δ₁ + δ₂ = a + b + c :=
    SYZ44.degree_sum_of_hilbert hilb a b c δ₁ δ₂ D₀ hRankNull hTwoRamp
  exact SYZ59.empty_middle_dichotomy a b c δ₁ δ₂ hsum hle
    (floor_of_regionSyzygyRealizable hW) hno_middle

/-! ## 6. The sufficient-side conjecture, its transport, and the PR #528 test corpus -/

/-- **The middle exclusion over the region-syzygy layer (OPEN — this file does not prove it).**
No region-syzygy-realizable profile over `K` sits in the middle band.  Unlike the numeric
statement PR #528 refuted, `δ₁` here is bound to the minimal syzygy product-degree of the
regions' vanishing triple.  **Scope**: this quantifies over a potentially strict superset of
genuine F1 witnesses (no stack data is required), so it is a *sufficient-side conjecture* for
the genuine F1 residual — see `middleExclusion_transport` — and possibly strictly stronger than
it.  On this layer it is the SYZ45-shaped geometric obstruction, which SYZ49 identifies with
the BGK level-set wall. -/
def RegionMiddleExclusion (K : Type*) [Field K] : Prop :=
  ∀ a b c t k δ₁ : ℕ, RegionSyzygyRealizable K a b c t k δ₁ → ¬ SYZ59.middleBand a b c δ₁

/-- **Sufficiency transport.**  For ANY notion of genuine stack-induced witness that factors
through the region-syzygy layer — i.e. every genuine witness induces a region/syzygy
configuration at its own profile — `RegionMiddleExclusion` implies the middle exclusion for
genuine witnesses.  This is the precise sense in which the conjecture stated here is
*sufficient* for the genuine F1 residual.  The hypothesis `hfactor` is exactly the open
SYZ42/SYZ28 lift-gate content (in the harmless direction); no instance of it is provided
in-tree, and none is claimed. -/
theorem middleExclusion_transport
    (Genuine : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (hfactor : ∀ a b c t k δ₁, Genuine a b c t k δ₁ → RegionSyzygyRealizable K a b c t k δ₁)
    (hEx : RegionMiddleExclusion K) :
    ∀ a b c t k δ₁, Genuine a b c t k δ₁ → ¬ SYZ59.middleBand a b c δ₁ :=
  fun a b c t k δ₁ hG => hEx a b c t k δ₁ (hfactor a b c t k δ₁ hG)

/-- **A discharge must kill the PR #528 corpus (region form).**  If `RegionMiddleExclusion K`
holds, then no member of the PR #528 countermodel family `(d,d,d,d−2,2d−1)` carries a
region/syzygy configuration with minimal syzygy product-degree `d+1`: the family's numeric
middle-band membership is consumed directly from the merged countermodel file
(`F1PolytopeMiddleCountermodel.middleBand_family`).  **Scope**: this excludes region/syzygy
configurations only; it does not show the family cannot arise from an actual over-budget
witness stack. -/
theorem regionMiddleExclusion_kills_family (hEx : RegionMiddleExclusion K) {d : ℕ} (hd : 6 ≤ d) :
    ¬ RegionSyzygyRealizable K d d d (d - 2) (2 * d - 1) (d + 1) := fun hW =>
  hEx d d d (d - 2) (2 * d - 1) (d + 1) hW
    (F1PolytopeMiddleCountermodel.middleBand_family d hd)

/-- **A single family configuration refutes the exclusion.**  Conversely, exhibiting an
on-domain region/syzygy configuration realizing any family profile at `δ₁ = d + 1` refutes
`RegionMiddleExclusion K`.  The PR #528 family is therefore the canonical first test corpus for
any proposed discharge of the region-layer conjecture, in both directions. -/
theorem family_witness_refutes_regionMiddleExclusion {d : ℕ} (hd : 6 ≤ d)
    (hW : RegionSyzygyRealizable K d d d (d - 2) (2 * d - 1) (d + 1)) :
    ¬ RegionMiddleExclusion K :=
  fun hEx => regionMiddleExclusion_kills_family hEx hd hW

/-- **The interface window does not decide the corpus (honesty record).**  For the family
profile `(d,d,d)` at `δ₁ = d+1`, the §4 floor allows it (`max = d ≤ d+1`) and the pair-sum
ceiling allows it (`d+1 ≤ 2d` for `d ≥ 1`): the theorems of this file leave the middle
exclusion genuinely open on the corpus, as they must — nothing here touches the BGK wall. -/
theorem family_within_interface_window {d : ℕ} (hd : 6 ≤ d) :
    max d (max d d) ≤ d + 1 ∧ d + 1 ≤ d + d := by
  omega

end ArkLib.ProximityGap.F1RegionSyzygy

-- Honesty audit:
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.vanishing_monic
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.vanishing_ne_zero
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.vanishing_natDegree
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.vanishing_isCoprime
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.venn_card_face
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.realizable_of_regionSyzygyRealizable
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.regions_proper_of_regionSyzygyRealizable
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.balanced_needs_domain_of_regionSyzygyRealizable
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.floor_of_regionSyzygyRealizable
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.min_syzygy_le_pair_sums
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.two_class_of_regionSyzygyRealizable
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.middleExclusion_transport
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.regionMiddleExclusion_kills_family
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.family_witness_refutes_regionMiddleExclusion
#print axioms ArkLib.ProximityGap.F1RegionSyzygy.family_within_interface_window
