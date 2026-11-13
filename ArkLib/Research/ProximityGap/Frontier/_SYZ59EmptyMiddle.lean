/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Research.ProximityGap.Frontier._SYZ45ImbalanceBound
import ArkLib.Research.ProximityGap.Frontier._SYZ47GeometricBalance
import ArkLib.Research.ProximityGap.Frontier._SYZ55GeneratorGap

/-!
# SYZ59 — the **empty middle**, with the SYZ55⇄SYZ47 convention reconciled

## The convention mismatch this file settles first

Two degree conventions co-exist in the μ-basis lane and, read naively, look contradictory:

* **PRODUCT-degree convention** (SYZ44 `min_syzygy_out_of_budget`, SYZ45 `imbalance`, SYZ47
  `syzygy_product_degree_ge_max`).  `δᵢ` is the *max slot product-degree*
  `max_slot deg(W_slot · s_slot)`.  The two minimal generators satisfy `δ₁ + δ₂ = a+b+c =: S`
  (SYZ44 degree-sum law) and the SYZ47 **floor** `δ₁ ≥ max(a,b,c)`.

* **COFACTOR-degree convention** (SYZ55 *prose*).  `δᵢ` is the degree of the *cofactor vector*
  `s`.  There SYZ55 writes "a constant syzygy is a degree-`0` module element, so `δ₁ = 0`,
  maximal gap `S`".

A **constant** syzygy `c₀W_AB + c₁W_AC + c₂W_BC = 0` of a *balanced* triple `a=b=c=d` has

* cofactor degree `0`  (the cofactors are the field constants `C cᵢ`), and
* **product-degree `d = max(a,b,c)`**  (a nonzero scalar does not change a polynomial's degree).

So the SYZ55 "`δ₁ = 0`" and the SYZ47 floor "`δ₁ ≥ max`" are **not** in conflict: they are the
*same* witness in two conventions, related by the bridge

`product_δ₁ = cofactor_δ₁ + max(a,b,c)`  (§1).

On a constant-syzygy witness `product_δ₁ = max(a,b,c)`: the SYZ47 floor is **attained / tight**, not
violated.  The SYZ45 `(4,4,4)⇒ι=2` "refutation" is exactly this attainment (`δ₁ = 4 = max`,
`ι = ⌊12/2⌋ − 4 = 2`).  The probe `probe_syz59_empty_middle.py` verifies both readings by exact
linear algebra on explicit `𝔽₁₃/𝔽₁₀₁` witnesses (`product_δ₁ = 4`, `cofactor_δ₁ = 0`).

## The cleaned empty-middle target (product convention)

Restated in the product convention, the SYZ55 census "every realizable witness has `δ₁ = 0`
(cofactor)" becomes **"every realizable witness has `δ₁ = max(a,b,c)` (product) — the floor is
attained"**.  The *empty middle* is then the pure statement:

> **No realizable band-interior triple has `max(a,b,c) < δ₁ ≤ ⌊S/2⌋ − 2`.**

i.e. a realizable syzygy is either the floor-tight constant one (`δ₁ = max`) or near-balance
(`δ₁ ≥ ⌊S/2⌋ − 1`, `ι ≤ 1`); nothing sits strictly between the floor and near-balance.

**Status of this target: contradicted at `n = 20` (probe evidence).**  SYZ71
(`_SYZ71LinearMiddleSlot.lean`, probe `probe_syz71_linear_middle_slot.py`) exhibits a
band-realizable (`Realizable 6 6 6 2 10`) witness over `μ₂₀ ⊂ 𝔽₄₁` with the linear-cofactor
syzygy `P = (29+10X)·W_AC + (30+X)·W_BC` of degree `7`, vanishing on `S_AB` and nonzero on the
leftover region `T = {20, 32}`; `rank(W_AB, W_AC, W_BC) = 3`, so there is no constant syzygy and
`δ₁ = 7`, i.e. `middleBand 6 6 6 7` is occupied.  So the empty middle is **false** as a statement
about band-realizable triples on `μ_n`, `n ≤ 20` (the finite-field arithmetic is not replayed in
Lean).  The SYZ59 dichotomy below remains a correct *conditional* (`¬ middleBand ⟹ …`), but its
hypothesis is not available in general.

## What is proved here (axiom-clean)

1. **Convention bridge** (§1): the polynomial fact that a nonzero constant syzygy has product-degree
   `= max` and cofactor-degree `0` (`const_syzygy_product_degree_eq_max`,
   `const_syzygy_cofactor_degree_zero`).  The relation `product = cofactor + max` is the
   convention's definition on balanced triples, recorded in prose only (a former Lean
   `convention_bridge` was the identity `h ↦ h` and was removed).
2. **The empty-middle dichotomy** (§2), pure `ℕ`: under the SYZ47 floor, "not in the middle" is
   *exactly* the dichotomy `δ₁ = max ∨ δ₁ ≥ ⌊S/2⌋ − 1` (`no_middle_iff_dichotomy`), and the
   near-balance branch feeds `ι ≤ 1` (SYZ45).
3. **Hand-entered constant-syzygy examples** (§3): three balanced rows `(d,d,d,δ₁ = d)`,
   `d ∈ {3,4,5}`, typed with `δ₁ = max` — so the `decide` checks
   (`constSyzygyExamples_floor_attained`, `constSyzygyExamples_no_middle`) are true by construction
   and are NOT a census of realizable triples.  The row `(3,3,3)` is not even balanced-interior.

## Honest residual

The **general** empty-middle statement remains OPEN — it is the SYZ45 geometric residual
"no realizable low-degree *non-constant* dependence", which SYZ45 showed is *not* an algebraic
identity (needs band realizability) — and, per SYZ71's `n = 20` occupant above, it is FALSE without further
hypotheses.  §4 records the conditional interface.  (A Wronskian / μ-basis-exchange attack was
considered and does not close it; the former `wronskian_no_jump` "skeleton" had hypotheses forcing
`dᵢ = dⱼ = max` and was removed.)  The convention bridge is the landable content;
**CORE remains OPEN / ON-BGK.**
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ59

open Polynomial
open ArkLib.ProximityGap

/-! ## 1. The convention bridge: constant syzygy has product-degree `max`, cofactor-degree `0` -/

/-- **Constant cofactors are degree `0`.**  In a constant syzygy the cofactor vector is
`(C c₀, C c₁, C c₂)`; each entry has `natDegree 0`, so the *cofactor* degree of the syzygy is `0`.
This is the SYZ55-prose reading "`δ₁ = 0`". -/
theorem const_syzygy_cofactor_degree_zero
    {K : Type*} [Field K] (c₀ c₁ c₂ : K) :
    max (C c₀).natDegree (max (C c₁).natDegree (C c₂).natDegree) = 0 := by
  simp

/-- **A nonzero scalar preserves the leading slot's degree.**  For the slot carrying a nonzero
scalar `c ≠ 0`, the product-degree `deg (C c · f)` equals `deg f`.  Hence on a balanced triple the
constant syzygy's product-degree *attains* `max(a,b,c)`. -/
theorem const_slot_product_degree_eq
    {K : Type*} [Field K] {c : K} (hc : c ≠ 0) (f : K[X]) :
    (C c * f).natDegree = f.natDegree :=
  natDegree_C_mul hc

/-- **Bridge (product = max on a constant syzygy of a balanced triple).**  Let
`c₀W_AB + c₁W_AC + c₂W_BC = 0` be a constant syzygy of a triple whose reduced degrees are all `d`
(`W_AB.natDegree = W_AC.natDegree = W_BC.natDegree = d`), and suppose the leading scalar `c₀ ≠ 0`.
Then the `AB` slot alone already has product-degree `d = max(a,b,c)`, and every slot's product-degree
is `≤ d` (`const_cofactor_natDegree_le`).  So the syzygy's product-degree is exactly `max(a,b,c) = d`
— the SYZ47 floor is **attained**, matching the cofactor reading `δ₁ = 0` via
`product = cofactor + max = 0 + d`. -/
theorem const_syzygy_product_degree_eq_max
    {K : Type*} [Field K] {WAB WAC WBC : K[X]} {c₀ c₁ c₂ : K} {d : ℕ}
    (hc₀ : c₀ ≠ 0)
    (hAB : WAB.natDegree = d) (hAC : WAC.natDegree = d) (hBC : WBC.natDegree = d) :
    (C c₀ * WAB).natDegree = d ∧
    (C c₁ * WAC).natDegree ≤ d ∧ (C c₂ * WBC).natDegree ≤ d := by
  refine ⟨?_, ?_, ?_⟩
  · rw [const_slot_product_degree_eq hc₀]; exact hAB
  · exact le_trans (SYZ45.const_cofactor_natDegree_le c₁ WAC) (by rw [hAC])
  · exact le_trans (SYZ45.const_cofactor_natDegree_le c₂ WBC) (by rw [hBC])

/-! ## 2. The empty-middle dichotomy (pure `ℕ`, axiom-clean) -/

/-- The **middle band** (product convention): a syzygy whose product-degree is *strictly above* the
floor `max(a,b,c)` yet still low enough (`≤ ⌊S/2⌋ − 2`) to force imbalance `ι ≥ 2`.  It is NOT
empty on realizable triples in general: SYZ71's `μ₂₀ ⊂ 𝔽₄₁` probe witness occupies
`middleBand 6 6 6 7` (module docstring). -/
def middleBand (a b c δ₁ : ℕ) : Prop :=
  max a (max b c) < δ₁ ∧ δ₁ ≤ (a + b + c) / 2 - 2

/-- **No-middle is exactly the floor/near-balance dichotomy.**  Under the SYZ47 floor
`max(a,b,c) ≤ δ₁` and the degree-sum law with `δ₁ ≤ δ₂`, *not* being in the middle band is
equivalent to: the floor is attained (`δ₁ = max`) **or** the syzygy is near-balance
(`δ₁ ≥ ⌊S/2⌋ − 1`, i.e. `ι ≤ 1`). -/
theorem no_middle_iff_dichotomy
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁) :
    ¬ middleBand a b c δ₁ ↔
      (δ₁ = max a (max b c) ∨ (a + b + c) / 2 - 1 ≤ δ₁) := by
  unfold middleBand
  omega

/-- **Near-balance branch of the dichotomy ⟹ `ι ≤ 1`.**  If the second (near-balance) alternative
holds, `δ₁ ≥ ⌊S/2⌋ − 1`, then the SYZ45 imbalance is `≤ 1` — the spread route closes at rate ½. -/
theorem near_balance_imbalance_le_one
    (a b c δ₁ : ℕ) (hnb : (a + b + c) / 2 - 1 ≤ δ₁) :
    SYZ45.imbalance a b c δ₁ ≤ 1 := by
  unfold SYZ45.imbalance; omega

/-- **Floor-attained branch = the constant-syzygy witness.**  If the first alternative holds,
`δ₁ = max(a,b,c)`, then (SYZ55 reading, product convention) the triple is a constant-syzygy witness:
the gap is `δ₂ − δ₁ = S − 2·max` and the imbalance is `ι = ⌊S/2⌋ − max` — the *balance defect*, the
SYZ47 tight value.  For balanced `a=b=c=d` this is `ι = ⌊d/2⌋`, exactly the SYZ45 `(4,4,4)⇒ι=2`. -/
theorem floor_attained_imbalance
    (a b c δ₁ : ℕ) (hattain : δ₁ = max a (max b c)) :
    SYZ45.imbalance a b c δ₁ = (a + b + c) / 2 - max a (max b c) := by
  unfold SYZ45.imbalance; omega

/-- **Packaged empty-middle dichotomy.**  Under the floor and the degree-sum law, if a realizable
triple is not in the middle band, then it is either floor-tight (`δ₁ = max`, constant-syzygy witness)
or near-balance (`ι ≤ 1`, spread route). -/
theorem empty_middle_dichotomy
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁)
    (hno_middle : ¬ middleBand a b c δ₁) :
    (δ₁ = max a (max b c)) ∨ SYZ45.imbalance a b c δ₁ ≤ 1 := by
  rcases (no_middle_iff_dichotomy a b c δ₁ δ₂ hsum hle hfloor).1 hno_middle with h | h
  · exact Or.inl h
  · exact Or.inr (near_balance_imbalance_le_one a b c δ₁ h)

/-! ## 3. Hand-entered constant-syzygy examples (product convention)

Each row is `(a, b, c, δ₁)` for a balanced profile `a = b = c = d` carrying a constant syzygy
(probe `probe_syz59_empty_middle.py`, exact linear algebra over `𝔽₁₀₁`), so `δ₁ = max = d` in the
product convention.  The rows are TYPED with `δ₁ = max`; the `decide` checks below are therefore
true by construction and certify nothing about which triples are realizable.  This list is NOT a
census: SYZ71's `μ₂₀ ⊂ 𝔽₄₁` witness (`middleBand 6 6 6 7`, no constant syzygy) shows that realizable
triples at `n ≤ 20` need not be floor-attained.  The row `(3,3,3)` is not balanced-interior
(`max + 1 = 4 = ⌊9/2⌋`). -/
def constSyzygyExamples : List (ℕ × ℕ × ℕ × ℕ) :=
  [ (3, 3, 3, 3),        -- S=9,  ⌊S/2⌋=4,  δ₁=max=3  (not balanced-interior: max+1 = ⌊S/2⌋)
    (4, 4, 4, 4),        -- S=12, ⌊S/2⌋=6,  δ₁=max=4  (the SYZ45 (4,4,4) witness, product reading)
    (5, 5, 5, 5) ]       -- S=15, ⌊S/2⌋=7,  δ₁=max=5

/-- Every hand-entered constant-syzygy example has `δ₁ = max(a,b,c)` (true by construction of
the rows). -/
theorem constSyzygyExamples_floor_attained :
    ∀ e ∈ constSyzygyExamples, e.2.2.2 = max e.1 (max e.2.1 e.2.2.1) := by decide

/-- No hand-entered constant-syzygy example is in the middle band (since `δ₁ = max` was typed in).
This is NOT an empty-middle statement about realizable triples (see SYZ71). -/
theorem constSyzygyExamples_no_middle :
    ∀ e ∈ constSyzygyExamples, ¬ middleBand e.1 e.2.1 e.2.2.1 e.2.2.2 := by
  intro e he
  fin_cases he <;> · unfold middleBand; decide

/-- The example list is nonempty. -/
theorem constSyzygyExamples_nonvacuous : constSyzygyExamples ≠ [] := by decide

/-! ## 4. General status and the residual (honest) -/

/-- **Reduction of the general empty middle to the SYZ45 geometric residual.**  The general empty
middle "no realizable syzygy in the middle band" is *equivalent* to "no realizable syzygy of
product-degree `≤ ⌊S/2⌋ − 2` above the floor", which — since the floor `δ₁ ≥ max` is discharged by
SYZ47 — is the non-existence of a realizable **non-constant** low-degree dependence.  SYZ45
(`imbalance_bound_requires_geometry`) proved this is *not* an algebraic identity: it needs band
realizability.  This lemma records the interface — given the geometric no-middle hypothesis, the
dichotomy holds.  The hypothesis is not available in general: SYZ71's `n = 20` probe witness
occupies `middleBand 6 6 6 7`. -/
theorem general_empty_middle_from_geometry
    (a b c δ₁ δ₂ : ℕ)
    (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂)
    (hfloor : max a (max b c) ≤ δ₁)
    (hGeom : ¬ middleBand a b c δ₁) :        -- the honest geometric residual (SYZ45)
    (δ₁ = max a (max b c)) ∨ SYZ45.imbalance a b c δ₁ ≤ 1 :=
  empty_middle_dichotomy a b c δ₁ δ₂ hsum hle hfloor hGeom

end ArkLib.ProximityGap.SYZ59

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ59.const_syzygy_cofactor_degree_zero
#print axioms ArkLib.ProximityGap.SYZ59.const_slot_product_degree_eq
#print axioms ArkLib.ProximityGap.SYZ59.const_syzygy_product_degree_eq_max
#print axioms ArkLib.ProximityGap.SYZ59.no_middle_iff_dichotomy
#print axioms ArkLib.ProximityGap.SYZ59.near_balance_imbalance_le_one
#print axioms ArkLib.ProximityGap.SYZ59.floor_attained_imbalance
#print axioms ArkLib.ProximityGap.SYZ59.empty_middle_dichotomy
#print axioms ArkLib.ProximityGap.SYZ59.constSyzygyExamples_floor_attained
#print axioms ArkLib.ProximityGap.SYZ59.constSyzygyExamples_no_middle
#print axioms ArkLib.ProximityGap.SYZ59.constSyzygyExamples_nonvacuous
#print axioms ArkLib.ProximityGap.SYZ59.general_empty_middle_from_geometry
