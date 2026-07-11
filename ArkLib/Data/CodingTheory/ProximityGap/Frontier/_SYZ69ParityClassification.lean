/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ44MuBasisDegreeSum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ45ImbalanceBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ59EmptyMiddle
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ68GeneratorGapParity

/-!
# SYZ69 — the **parity-corrected two-class classification** of the μ-basis generator gap

## Context: four unconditional inputs, one crisp classification

The μ-basis lane has, as of SYZ68, four ingredients that together pin the shape of the generator
gap `g = δ₂ − δ₁` on a realizable interior band triple `(W_AB, W_AC, W_BC)` over `μ_n`:

* **degree-sum law** (SYZ44 `degree_sum_of_hilbert`, made *unconditional* by SYZ61→SYZ65):
  `δ₁ + δ₂ = a + b + c =: S`;
* **the floor** (SYZ47 `syzygy_product_degree_ge_max`): `δ₁ ≥ max(a,b,c)`;
* **parity** (SYZ68 `gap_parity`): `g ≡ S (mod 2)` — zero field content, forced by the degree-sum;
* **the empty-middle census** (SYZ55 cofactor census / SYZ59 product-convention dichotomy): every
  *realizable* witness sits **outside** the middle band `max(a,b,c) < δ₁ ≤ ⌊S/2⌋ − 2`.

This file assembles them into the single **two-class law**, in the honest conditionality each piece
supports:

> **Two-class law (conditional on the empty-middle census `¬ middleBand`).**  Every realizable
> interior band triple is *either*
> * **near-balance** — `ι ≤ 1` (SYZ45 imbalance ≤ 1), equivalently, per SYZ68 parity: even `S ⇒
>   g ≤ 2`, odd `S ⇒ g ∈ {1,3}`; *or*
> * **floor-attained** — `δ₁ = max(a,b,c)`, the **constant-syzygy family**, with `g = S − 2·max`
>   (balanced `a=b=c=d ⇒ g = d`).

The **two-class law itself is a theorem** (given the census input `¬ middleBand`); this file proves
it (`two_class_law`, `two_class_law_gap`) and packages it end-to-end from SYZ44's Hilbert–Burch
structural inputs (`classification_of_hilbert`).

What is **OPEN** is the *exclusion of the middle band* — the pure geometric statement that
`middleBand` is empty on realizable triples (SYZ45 showed this is not an algebraic identity; it needs
band realizability).  This file restates that residual **minimally and in parity-corrected gap
language** (`middleBand_iff_imbalance_ge_two`, `middle_gap_ge_four`, `middle_gap_parity`,
`open_exclusion_gap_form`): the middle is exactly the parity-allowed gaps
`{ g : 4 ≤ g ≤ S − 2·max, g ≡ S (mod 2) }` (even `S`: `g ∈ {4,6,…}`; odd `S`: `g ∈ {5,7,…}`), i.e.
the open geometric claim is precisely *"no realizable interior triple has `ι ≥ 2` strictly above the
floor"*.

## The parity correction and why it matters

SYZ54 handed downstream the **false class target** `g ≤ 1` for the whole balanced coprime class;
SYZ68 refuted it (even-`S` gap = 2 witnesses, `ι = 1`).  The corrected, class-true near-balance
target is `ι ≤ 1`, whose gap reading is *parity-dependent*: SYZ68 collapses the parity-free
`g ≤ 3` (SYZ53) to `g ≤ 2` on the even-`S` class, but at odd `S` the near-balance class still admits
`g = 3` (`ι = 1`).  So the honest **uniform** near-balance invariant is `ι ≤ 1`; the crisp gap
statement is the per-parity `g ≤ 2` (even) — recorded here as the corrected classification boundary.

## Scope honesty

Combinatorial classification only.  All theorems here are pure `ℕ` / `decide`, axiom-clean, and
consume only the (now-unconditional) degree-sum law, the SYZ47 floor hypothesis, SYZ68 parity, and
the SYZ59 empty-middle census input.  The file does **not** prove that a realizable triple actually
lands outside the middle band (that is the open geometric residual, restated minimally).  `ι ≤ 1`
closes SYZ44 `uniformSylvester` only at rate `1/2`; production δ* still needs SYZ18 supports,
`hrank` realizability, strip-radius transport, and the MCAThresholdLedger BGK lower bound.  **CORE
remains OPEN / ON-BGK; the BGK wall is untouched.**
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ69

open ArkLib.ProximityGap

/-! ## 1. The floor-attained class: gap `= S − 2·max`, the constant-syzygy family -/

/-- **Floor-attained gap.**  When the SYZ47 floor is *tight* (`δ₁ = max(a,b,c)`, the constant-syzygy
witness in the product convention), the generator gap is `g = δ₂ − δ₁ = S − 2·max(a,b,c)`.  This is
the second class of the two-class law: the level-set / constant-syzygy family. -/
theorem floor_attained_gap
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hattain : δ₁ = max a (max b c)) :
    δ₂ - δ₁ = (a + b + c) - 2 * max a (max b c) := by
  omega

/-- **Balanced floor-attained gap = `d`.**  For a balanced triple `a = b = c = d`, the floor-attained
(constant-syzygy) class has gap exactly `d`: `S = 3d`, `max = d`, `g = 3d − 2d = d`.  This is the
SYZ45 `(4,4,4)` witness read in the gap language (`g = 4`, `ι = ⌊4/2⌋ = 2`). -/
theorem balanced_floor_attained_gap
    (d δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = d + d + d) (hattain : δ₁ = d) :
    δ₂ - δ₁ = d := by
  omega

/-! ## 2. The two-class law (conditional on the empty-middle census `¬ middleBand`) -/

/-- **The two-class law (imbalance form).**  Under the degree-sum law, `δ₁ ≤ δ₂`, the SYZ47 floor,
and the empty-middle census input `¬ middleBand` (SYZ55/SYZ59), every realizable interior band triple
is **either** floor-attained (`δ₁ = max`, constant-syzygy family) **or** near-balance
(`ι ≤ 1`).  This is exactly SYZ59's `empty_middle_dichotomy`, recorded here as the top-level
classification. -/
theorem two_class_law
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁)
    (hno_middle : ¬ SYZ59.middleBand a b c δ₁) :
    (δ₁ = max a (max b c)) ∨ SYZ45.imbalance a b c δ₁ ≤ 1 :=
  SYZ59.empty_middle_dichotomy a b c δ₁ δ₂ hsum hle hfloor hno_middle

/-- **The two-class law (gap form).**  Same hypotheses, stated in the gap language: every realizable
interior band triple has *either* floor-attained gap `g = S − 2·max` (constant-syzygy family) *or*
near-balance gap `g ≤ 3` (`ι ≤ 1`).  Parity (SYZ68) refines the near-balance branch per class:
even `S ⇒ g ≤ 2`, odd `S ⇒ g ∈ {1,3}` — see `two_class_law_gap_even`. -/
theorem two_class_law_gap
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁)
    (hno_middle : ¬ SYZ59.middleBand a b c δ₁) :
    (δ₂ - δ₁ = (a + b + c) - 2 * max a (max b c)) ∨ (δ₂ - δ₁ ≤ 3) := by
  rcases two_class_law a b c δ₁ δ₂ hsum hle hfloor hno_middle with hattain | himb
  · exact Or.inl (floor_attained_gap a b c δ₁ δ₂ hsum hattain)
  · refine Or.inr ?_
    unfold SYZ45.imbalance at himb
    omega

/-- **The two-class law at even total degree (parity-corrected gap form).**  On the even-`S` class
the parity law (SYZ68) collapses the near-balance branch's `g ≤ 3` to the sharp `g ≤ 2`: every
realizable interior band triple is *either* floor-attained (`g = S − 2·max`) *or* near-balance with
`g ≤ 2`.  This is the crisp class-true statement that replaces SYZ54's refuted `g ≤ 1`. -/
theorem two_class_law_gap_even
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁)
    (heven : (a + b + c) % 2 = 0)
    (hno_middle : ¬ SYZ59.middleBand a b c δ₁) :
    (δ₂ - δ₁ = (a + b + c) - 2 * max a (max b c)) ∨ (δ₂ - δ₁ ≤ 2) := by
  rcases two_class_law a b c δ₁ δ₂ hsum hle hfloor hno_middle with hattain | himb
  · exact Or.inl (floor_attained_gap a b c δ₁ δ₂ hsum hattain)
  · refine Or.inr ?_
    have := (SYZ68.imbalance_le_one_iff_gap_le_two_of_even a b c δ₁ δ₂ hsum hle heven).1 himb
    exact this

/-! ## 3. The near-balance class: the parity-corrected boundary -/

/-- **Near-balance ⇒ `g ≤ 2` at even `S` (SYZ68 correction).**  The class-true near-balance gap
bound: on the even-`S` class, `ι ≤ 1` is equivalent to `g ≤ 2`.  This is one unit tighter than the
parity-free `g ≤ 3` and is the sharp replacement for SYZ54's false `g ≤ 1`. -/
theorem near_balance_gap_le_two_of_even
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (heven : (a + b + c) % 2 = 0)
    (himb : SYZ45.imbalance a b c δ₁ ≤ 1) :
    δ₂ - δ₁ ≤ 2 :=
  (SYZ68.imbalance_le_one_iff_gap_le_two_of_even a b c δ₁ δ₂ hsum hle heven).1 himb

/-- **Near-balance at odd `S` still admits `g = 3`.**  On the odd-`S` class, `ι ≤ 1` forces odd gap
(SYZ68 parity), so `g ∈ {1, 3}`; the value `g = 3` (with `ι = 1`) is *not* excluded.  This certifies
that the uniform near-balance invariant is `ι ≤ 1` (equivalently `g ≤ 3`), **not** the even-`S`
`g ≤ 2`: the gap statement is genuinely parity-dependent. -/
theorem near_balance_gap_odd_admits_three
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hodd : (a + b + c) % 2 = 1)
    (himb : SYZ45.imbalance a b c δ₁ ≤ 1) :
    δ₂ - δ₁ = 1 ∨ δ₂ - δ₁ = 3 := by
  unfold SYZ45.imbalance at himb
  omega

/-! ## 4. The open residual, restated minimally in parity-corrected gap language -/

/-- **The middle band is exactly `δ₁` above the floor with `ι ≥ 2`.**  Under the degree-sum law and
`δ₁ ≤ δ₂`, `middleBand` holds iff the floor is *strictly* exceeded (`max < δ₁`) **and** the imbalance
is `≥ 2`.  This rephrases SYZ59's `middleBand` in the invariant `ι`, isolating the open geometric
claim as *"no realizable interior triple has `ι ≥ 2` strictly above the floor"*. -/
theorem middleBand_iff_imbalance_ge_two
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    SYZ59.middleBand a b c δ₁ ↔
      (max a (max b c) < δ₁ ∧ 2 ≤ SYZ45.imbalance a b c δ₁) := by
  unfold SYZ59.middleBand SYZ45.imbalance
  omega

/-- **Middle gaps are `≥ 4`.**  A middle-band triple has generator gap `g ≥ 4` (equivalently
`ι ≥ 2`).  Together with parity (`middle_gap_parity`) this pins the middle to the parity-allowed
gaps `{4,6,…}` (even `S`) / `{5,7,…}` (odd `S`): the minimal excluded gap is `4` at even `S`, `5` at
odd `S`. -/
theorem middle_gap_ge_four
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hmid : SYZ59.middleBand a b c δ₁) :
    4 ≤ δ₂ - δ₁ := by
  unfold SYZ59.middleBand at hmid
  omega

/-- **Middle gaps share the total-degree parity.**  A middle-band triple's gap obeys the SYZ68 parity
law `g ≡ S (mod 2)`.  Hence the middle band, in gap language, is exactly
`{ g : 4 ≤ g, g ≡ S (mod 2), g ≤ S − 2·max }`. -/
theorem middle_gap_parity
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    (δ₂ - δ₁) % 2 = (a + b + c) % 2 :=
  SYZ68.gap_parity a b c δ₁ δ₂ hsum hle

/-- **The open exclusion, minimal gap form.**  The two-class law holds for a triple *exactly when*
it avoids every parity-allowed middle gap, i.e. when it is **not** the case that
`4 ≤ g ∧ g ≡ S (mod 2) ∧ δ₁ > max`.  This is the single open geometric obligation, restated with the
SYZ68 parity built in: an interior triple is either floor-attained or near-balance **unless** it
carries a parity-consistent gap `≥ 4` above the floor — the case the empty-middle census asserts is
unrealizable. -/
theorem open_exclusion_gap_form
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁)
    (hexcl : ¬ (max a (max b c) < δ₁ ∧ 4 ≤ δ₂ - δ₁)) :
    (δ₂ - δ₁ = (a + b + c) - 2 * max a (max b c)) ∨ (δ₂ - δ₁ ≤ 3) := by
  refine two_class_law_gap a b c δ₁ δ₂ hsum hle hfloor ?_
  rw [middleBand_iff_imbalance_ge_two a b c δ₁ δ₂ hsum hle]
  intro ⟨hlt, hge⟩
  exact hexcl ⟨hlt, by unfold SYZ45.imbalance at hge; omega⟩

/-! ## 5. Packaged end-to-end from SYZ44's Hilbert–Burch structural inputs -/

/-- **Packaged two-class classification (from Hilbert inputs).**  From SYZ44's two structural inputs
(`RankNullity`, `TwoRamp`) — both now *unconditional* via SYZ61→SYZ65 — plus `δ₁ ≤ δ₂`, the SYZ47
floor, and the empty-middle census `¬ middleBand`, conclude the two-class law: every realizable
interior band triple is floor-attained or near-balance.  End-to-end from Hilbert–Burch structure to
the parity-corrected classification. -/
theorem classification_of_hilbert
    (hilb : ℕ → ℕ) (a b c δ₁ δ₂ D₀ : ℕ)
    (hRankNull : SYZ44.RankNullity hilb a b c D₀)
    (hTwoRamp : SYZ44.TwoRamp hilb δ₁ δ₂)
    (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁)
    (hno_middle : ¬ SYZ59.middleBand a b c δ₁) :
    (δ₁ = max a (max b c)) ∨ SYZ45.imbalance a b c δ₁ ≤ 1 := by
  have hsum : δ₁ + δ₂ = a + b + c :=
    SYZ44.degree_sum_of_hilbert hilb a b c δ₁ δ₂ D₀ hRankNull hTwoRamp
  exact two_class_law a b c δ₁ δ₂ hsum hle hfloor hno_middle

/-! ## 6. Finite census: the two-class law holds on the SYZ59 realizable witnesses -/

/-- **Every realizable census witness is in the floor-attained class with gap `= d`.**  On the SYZ59
`productCensus` (balanced interior witnesses `d ∈ {3,4,5}`), every entry is floor-attained
(`δ₁ = max`) and hence in the constant-syzygy class with gap `= S − 2·max = d` — the second class of
the two-class law, non-vacuously realized.  (No census witness is near-balance: the realizable
balanced interior is *entirely* the floor-attained class.) -/
theorem census_two_class :
    ∀ e ∈ SYZ59.productCensus,
      e.2.2.2 = max e.1 (max e.2.1 e.2.2.1) ∧
      ¬ SYZ59.middleBand e.1 e.2.1 e.2.2.1 e.2.2.2 := by
  intro e he
  exact ⟨SYZ59.realizable_floor_attained e he, SYZ59.realizable_no_middle e he⟩

end ArkLib.ProximityGap.SYZ69

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ69.floor_attained_gap
#print axioms ArkLib.ProximityGap.SYZ69.balanced_floor_attained_gap
#print axioms ArkLib.ProximityGap.SYZ69.two_class_law
#print axioms ArkLib.ProximityGap.SYZ69.two_class_law_gap
#print axioms ArkLib.ProximityGap.SYZ69.two_class_law_gap_even
#print axioms ArkLib.ProximityGap.SYZ69.near_balance_gap_le_two_of_even
#print axioms ArkLib.ProximityGap.SYZ69.near_balance_gap_odd_admits_three
#print axioms ArkLib.ProximityGap.SYZ69.middleBand_iff_imbalance_ge_two
#print axioms ArkLib.ProximityGap.SYZ69.middle_gap_ge_four
#print axioms ArkLib.ProximityGap.SYZ69.middle_gap_parity
#print axioms ArkLib.ProximityGap.SYZ69.open_exclusion_gap_form
#print axioms ArkLib.ProximityGap.SYZ69.classification_of_hilbert
#print axioms ArkLib.ProximityGap.SYZ69.census_two_class
