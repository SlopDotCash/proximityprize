/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ34StripInteriorGeneration

/-!
# SYZ35 — the punctured-pair interior law, localised to union-generation

This file carries forward the SYZ34 residual `SYZ34PairInteriorLaw`: the exact closed form for the
punctured-pair intersection driving the last open gate of the rate-`1/2` proximity strip theorem
(interior band `1/4 < δ < 1/3`).  SYZ34 reduced the triple-shortening deficiency to a single
subspace dimension via the fiber-product identity.  Here we determine **exactly where the residual
lives**: the sharp closed form is *equivalent*, not merely implied by, the union-generation
statement, and we prove the one unconditional inequality (the lower bracket) together with the
exact reduction and the generation equivalence.

## The object

Write `A = D_{Cᴬ}`, `B = D_{Cᴮ}`, `C = D_{Cᶜ}` for the shortened duals of an MDS/RS code on three
cores, dual distance `k + 1`, in the post-merge band where every pairwise core overlap is
`≤ k − 1 < k + 1`, so every pairwise dual intersection vanishes (SYZ23).  The generation deficiency
of the triple is governed by

`obj := finrank ((A ⊔ B) ⊓ C)`

(the fiber-product identity of SYZ34 equates this to the punctured-pair intersection
`finrank (π_C A ⊓ π_C B)` under the same disjointness hypotheses).

## What is proved here (unconditional, no coding hypotheses)

1. **Exact reduction** (`finrank_pairInf_add_finrank_sup`): with only `A ⊓ B = ⊥`,
   `finrank ((A ⊔ B) ⊓ C) + finrank (A ⊔ B ⊔ C) = finrank A + finrank B + finrank C`.
   So `obj = finrank A + finrank B + finrank C − finrank (A ⊔ B ⊔ C)`; it is a symmetric function of
   the three cores.

2. **Lower bracket** (`target_le_finrank_pairInf`): for any union ceiling
   `hU : finrank (A ⊔ B ⊔ C) ≤ u`, `finrank A + finrank B + finrank C ≤ obj + u`, i.e.
   `obj ≥ (finrank A + finrank B + finrank C) − u`.  Taking `u = finrank D_{Cᴬ ∪ Cᴮ ∪ Cᶜ}`
   (`A ⊔ B ⊔ C ≤ D_union`) and feeding the MDS shortening dimensions of SYZ21, the right side is the
   probe closed form `Σ_pair |Cᵢ ∩ Cⱼ| − |Cᴬ ∩ Cᴮ ∩ Cᶜ| − 2k`.  **This is the always-true direction
   of the closed form.**

3. **Generation equivalence** (`pairInteriorLaw_iff_generation`): under `A ⊓ B = ⊥` and the ceiling
   `A ⊔ B ⊔ C ≤ W`, the sharp law `obj = (finrank A + finrank B + finrank C) − finrank W`
   (equivalently `obj + finrank W = finrank A + finrank B + finrank C`) holds **iff**
   `finrank (A ⊔ B ⊔ C) = finrank W`, i.e. iff the three cores generate the union shortening
   `D_union`.  The closed-form value of the punctured pair is therefore *exactly as hard as* the
   union-generation gate — the sharp `−2k` is not a separable arithmetic fact.

4. **Closed-form arithmetic** (`closedForm_eq`): the abstract quantity
   `(finrank A + finrank B + finrank C) − finrank W`, with the SYZ21 substitutions
   `finrank A = |Cᴬ| − k`, …, `finrank W = |Cᴬ ∪ Cᴮ ∪ Cᶜ| − k`, equals the probe closed form
   `|Cᴬ∩Cᴮ| + |Cᴬ∩Cᶜ| + |Cᴮ∩Cᶜ| − |Cᴬ∩Cᴮ∩Cᶜ| − 2k` by inclusion–exclusion.

## Status (honest)

**Partial.**  The lower bracket, the exact reduction, and the generation equivalence are proved
unconditionally and axiom-clean.  The **sharp upper bound** `obj ≤ max(0, target)` — the direction
the interior-generation gate actually needs — is by (3) *equivalent* to the union-generation
statement `A ⊔ B ⊔ C = D_union`, which remains the named residual.  So SYZ35 does not close the gate;
it pins the residual to a single, cleanly-stated subspace-generation fact and discharges every
surrounding inequality.  This is the natural statement for the general-`D` peel: the `m`-core
generation gate is `A₁ ⊔ … ⊔ A_m = D_{⋃Cᵢ}`, attacked inductively — still open.  Probe:
`scripts/probes/probe_syz35_generation_equiv.py` (identity, lower bracket, and generation
equivalence, 3 fields, sizes to `n = 30`, ≈ 7000 band triples, `0` violations).

Verified against the SYZ34 fiber-product bricks (`finrank_sup_inf_eq_finrank_map_inf`): under the
disjointness hypotheses, `obj = finrank (π_C A ⊓ π_C B)`, so every statement below transports to the
punctured pair.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ35

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Exact reduction (SYZ35).**  With only `A ⊓ B = ⊥`, the pair-interior object
`finrank ((A ⊔ B) ⊓ C)` and the triple span add up to the sum of the three core dimensions:

`finrank ((A ⊔ B) ⊓ C) + finrank (A ⊔ B ⊔ C) = finrank A + finrank B + finrank C`.

Hence `obj = finrank A + finrank B + finrank C − finrank (A ⊔ B ⊔ C)`, a symmetric function of the
cores (the disjointness of `A`, `B` is all that is used).  No coding hypotheses. -/
theorem finrank_pairInf_add_finrank_sup
    (A B C : Submodule K V) (hAB : A ⊓ B = ⊥) :
    finrank K ↥((A ⊔ B) ⊓ C) + finrank K ↥(A ⊔ B ⊔ C)
      = finrank K A + finrank K B + finrank K C := by
  -- `finrank (A ⊔ B) = finrank A + finrank B` from `A ⊓ B = ⊥`.
  have hAB' : finrank K ↥(A ⊔ B) + finrank K ↥(A ⊓ B) = finrank K A + finrank K B :=
    Submodule.finrank_sup_add_finrank_inf_eq A B
  have hABbot : finrank K ↥(A ⊓ B) = 0 := by rw [hAB]; simp
  -- Modular law for the pair `(A ⊔ B)` and `C`.
  have hmod : finrank K ↥((A ⊔ B) ⊔ C) + finrank K ↥((A ⊔ B) ⊓ C)
      = finrank K ↥(A ⊔ B) + finrank K C :=
    Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) C
  -- `(A ⊔ B) ⊔ C` is `A ⊔ B ⊔ C`.
  omega

/-- **Lower bracket (the always-true direction of the closed form).**  For any ceiling
`hU : finrank (A ⊔ B ⊔ C) ≤ u` on the triple span (concretely `u = finrank D_{⋃Cᵢ}`, since
`A ⊔ B ⊔ C ≤ D_union`),

`finrank A + finrank B + finrank C ≤ finrank ((A ⊔ B) ⊓ C) + u`,

i.e. `obj ≥ (finrank A + finrank B + finrank C) − u`.  Substituting the SYZ21 shortening dimensions
this is the probe closed form as a **lower** bound; the reverse (the gate) is generation. -/
theorem target_le_finrank_pairInf
    (A B C : Submodule K V) (hAB : A ⊓ B = ⊥) {u : ℕ}
    (hU : finrank K ↥(A ⊔ B ⊔ C) ≤ u) :
    finrank K A + finrank K B + finrank K C ≤ finrank K ↥((A ⊔ B) ⊓ C) + u := by
  have h := finrank_pairInf_add_finrank_sup A B C hAB
  omega

/-- **Generation equivalence (localisation of the residual).**  With `A ⊓ B = ⊥` and a ceiling
subspace `W` containing the triple span (`A ⊔ B ⊔ C ≤ W`, so `finrank (A ⊔ B ⊔ C) ≤ finrank W`),
the sharp punctured-pair law

`finrank ((A ⊔ B) ⊓ C) + finrank W = finrank A + finrank B + finrank C`

holds **iff** the three cores generate the ceiling, `finrank (A ⊔ B ⊔ C) = finrank W`.  So the exact
closed-form value of the punctured pair is equivalent to the union-generation gate: the `−2k` sharp
bound is not a separable arithmetic fact.  (For `W = D_{⋃Cᵢ}` this is exactly deficiency `0`.) -/
theorem pairInteriorLaw_iff_generation
    (A B C W : Submodule K V) (hAB : A ⊓ B = ⊥)
    (hW : A ⊔ B ⊔ C ≤ W) :
    (finrank K ↥((A ⊔ B) ⊓ C) + finrank K W = finrank K A + finrank K B + finrank K C)
      ↔ finrank K ↥(A ⊔ B ⊔ C) = finrank K W := by
  have h := finrank_pairInf_add_finrank_sup A B C hAB
  have hle : finrank K ↥(A ⊔ B ⊔ C) ≤ finrank K W := Submodule.finrank_mono hW
  constructor
  · intro hlaw; omega
  · intro hgen; omega

/-- **Closed-form arithmetic.**  With the SYZ21 MDS shortening substitutions
`finrank A = |Cᴬ| − k`, `finrank B = |Cᴮ| − k`, `finrank C = |Cᶜ| − k`, and
`finrank W = |Cᴬ ∪ Cᴮ ∪ Cᶜ| − k` (all with the cores at least `k`, band regime), inclusion–exclusion
turns the abstract generation value `(finrank A + finrank B + finrank C) − finrank W` into the probe
closed form `|Cᴬ∩Cᴮ| + |Cᴬ∩Cᶜ| + |Cᴮ∩Cᶜ| − |Cᴬ∩Cᴮ∩Cᶜ| − 2k`.  Stated over `ℤ` to expose the exact
identity without truncation.  `pAB = |Cᴬ∩Cᴮ|`, etc.; `t = |Cᴬ∩Cᴮ∩Cᶜ|`; `un = |Cᴬ ∪ Cᴮ ∪ Cᶜ|`;
the inclusion–exclusion hypothesis `hIE : un = cA + cB + cC − pAB − pAC − pBC + t`. -/
theorem closedForm_eq
    (cA cB cC pAB pAC pBC t un k : ℤ)
    (hIE : un = cA + cB + cC - pAB - pAC - pBC + t) :
    ((cA - k) + (cB - k) + (cC - k)) - (un - k)
      = pAB + pAC + pBC - t - 2 * k := by
  linarith [hIE]

end ArkLib.ProximityGap.SYZ35

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ35.finrank_pairInf_add_finrank_sup
#print axioms ArkLib.ProximityGap.SYZ35.target_le_finrank_pairInf
#print axioms ArkLib.ProximityGap.SYZ35.pairInteriorLaw_iff_generation
#print axioms ArkLib.ProximityGap.SYZ35.closedForm_eq
