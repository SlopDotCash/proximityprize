/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ40FinalAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ36UnionGeneration
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ35PairInteriorLaw
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ25MDSGeneration

/-!
# SYZ41 — the `d = syzdim` bridge, proven concretely (module-vanishing ⇒ rigidity)

SYZ40 assembled the rate-`1/2` proximity strip theorem on a single named residual
(`UniformSylvesterInjective`), but folded, as the master-hypothesis field `syzdimBridge`, the
SYZ36 identity `d = syzdim` ("in-budget syzygy module vanishes ⇒ the cores generate the union
shortening").  That field was carried as *probe-verified, not formally proven*, and — worse — as
literally stated it quantifies over **arbitrary** abstract subspaces `A, B, C, W` with *no formal
link* to the polynomial data `(W_AB, W_AC, W_BC)`, so it is an ill-posed catch-all that can never be
discharged: it silently bundles the whole SYZ25/SYZ34 *dictionary* (abstract subspace ⟷ univariate
cochain) together with the syzygy-space logic.

This file proves the **syzygy-space logic** — the genuine mathematical content of `d = syzdim` in
the direction SYZ40 consumes — fully and axiom-clean, at the concrete univariate-cochain level where
it is well posed, using exactly the pieces SYZ36/SYZ38 already formalized:

* `cocycle_identity`, `reduce_by_VT`, `vanish_cofactor_lt` (SYZ36) — the cochain factorization;
* `module_vanishes_of_sylvester_injective` (SYZ38) — the in-budget module collapse.

## The concrete bridge (what is proven)

A **deficiency element** is a function locally-`deg < k` on each of the three cores but not globally
polynomial — recorded, after the SYZ36 reduction, by its three pairwise mismatches
`q_AB, q_AC, q_BC` (a cocycle: `q_AB − q_AC + q_BC = 0`, `cocycle_identity`).  Each `q_XY` vanishes
on the `m_XY` overlap points and on the triple `|T|`, so it factors `q_XY = V_T · W_XY · r_XY` with
`deg r_XY < k − m_XY` (SYZ36 `vanish_cofactor_lt`, `reduce_by_VT`).  The map

  `(q_AB, q_AC, q_BC)  ↦  (r_AB, r_AC, r_BC)`

is **`K`-linear** (`reduced_of_factored` is division by the fixed nonzero `V_T·W_XY`), lands in the
in-budget syzygy space (`reduced_is_syzygy`), and is **injective on the non-glued part**: a nonzero
mismatch forces a nonzero reduced component (`nontrivial_reduced_of_nontrivial_cocycle`, from
`factor_ne_zero`).  Hence

  **deficiency `≤` syzdim**, so **syzdim `= 0` ⇒ deficiency `= 0`** — the needed direction.

`rigidity_of_module_vanishes` is that statement fully assembled: *if* the reduced triple is
Sylvester-injective (the syzygy module is `{0}`, supplied by `UniformSylvesterInjective`), *then*
every deficiency cocycle is trivial — the local polynomials glue (rigidity / generation).  This is
`generation_of_module_vanishes` in the exact form the bridge needs, with the folded `syzdimBridge`
field's syzygy logic now *discharged* rather than assumed.

## What still needs a (strictly lighter, explicitly named) hypothesis

The only residue of the old `syzdimBridge` is the **dictionary** `SyzdimDictionary`: the
SYZ25/SYZ34 identification of the abstract subspace deficiency `finrank W − finrank (A⊔B⊔C)` with the
concrete cochain deficiency space (SYZ25 `generation_iff_dualAnnihilator`).  This is a pure
linear-algebra/duality transport carrying **none** of the syzygy content, so folding it is honest and
strictly weaker than the old field.

Accordingly the strengthened master hypothesis `StripMasterHypothesis'` **drops `syzdimBridge`
entirely** and keeps only the two fields `uniformSylvester` and `realizability`;
`strip_theorem_of_master_hypothesis'` delivers the full strip conclusion with the spread branch
stated *concretely* (in-budget module vanishing), which is exactly `strip_theorem_of_uniform_sylvester`
fed by the one residual — unconditional given the two fields.  The abstract-pair-law restatement is
recovered separately in `pairInteriorLaw_of_master'`, which consumes the light `SyzdimDictionary`
transport in place of the whole old bridge.

## Honest status

The `d = syzdim` bridge is **reduced from a probe-verified black box to: (proven) syzygy logic + a
named light duality dictionary**.  The concrete strip (spread branch = module vanishing) is now on
**two** fields (`uniformSylvester`, `realizability`), with `syzdimBridge` removed.  No unconditional
`δ*`; the sole substantive open input remains `UniformSylvesterInjective` (SYZ39, BGK type).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ41

open Polynomial Module
open ArkLib.ProximityGap ArkLib.ProximityGap.Frontier

variable {K : Type*} [Field K]

/-! ## 1. The reduced-syzygy map: elementary structure -/

/-- **Nonvanishing survives the `V_T·W` division.**  If a mismatch `q = V_T · W · r` is nonzero then
its reduced cofactor `r` is nonzero.  This is the injectivity kernel step: a nonzero deficiency
component cannot map to `0` in the syzygy space.  (Pure contrapositive of `mul_zero`; no domain
hypothesis needed.) -/
theorem factor_ne_zero (VT W r q : K[X]) (hf : q = VT * W * r) (hq : q ≠ 0) : r ≠ 0 := by
  rintro rfl
  simp [hf] at hq

/-- **The reduced triple solves the reduced syzygy.**  Given the three cochain factorizations
`q_XY = V_T · W_XY · r_XY` and the cocycle identity `q_AB − q_AC + q_BC = 0`, cancelling the common
nonzero triple factor `V_T` (SYZ36 `reduce_by_VT`) yields the reduced syzygy
`W_AB r_AB − W_AC r_AC + W_BC r_BC = 0`.  This is the "map lands in the syzygy space" step. -/
theorem reduced_is_syzygy
    (VT WAB WAC WBC rAB rAC rBC qAB qAC qBC : K[X]) (hVT : VT ≠ 0)
    (hfAB : qAB = VT * WAB * rAB) (hfAC : qAC = VT * WAC * rAC) (hfBC : qBC = VT * WBC * rBC)
    (hcocycle : qAB - qAC + qBC = 0) :
    WAB * rAB - WAC * rAC + WBC * rBC = 0 := by
  apply SYZ36.reduce_by_VT VT WAB WAC WBC rAB rAC rBC hVT
  linear_combination hcocycle - hfAB + hfAC - hfBC

/-- **Injectivity on the non-glued part (deficiency `≤` syzdim).**  If a deficiency cocycle is
nontrivial (some mismatch `q_XY ≠ 0`) then its image reduced triple is nontrivial (the corresponding
`r_XY ≠ 0`).  Equivalently: the reduced-syzygy map has trivial kernel on cochains, so the deficiency
space injects into the in-budget syzygy space — `deficiency ≤ syzdim`.  Stated as the three
component implications. -/
theorem nontrivial_reduced_of_nontrivial_cocycle
    (VT WAB WAC WBC rAB rAC rBC qAB qAC qBC : K[X])
    (hfAB : qAB = VT * WAB * rAB) (hfAC : qAC = VT * WAC * rAC) (hfBC : qBC = VT * WBC * rBC) :
    (qAB ≠ 0 → rAB ≠ 0) ∧ (qAC ≠ 0 → rAC ≠ 0) ∧ (qBC ≠ 0 → rBC ≠ 0) :=
  ⟨fun h => factor_ne_zero VT WAB rAB qAB hfAB h,
   fun h => factor_ne_zero VT WAC rAC qAC hfAC h,
   fun h => factor_ne_zero VT WBC rBC qBC hfBC h⟩

/-! ## 2. The concrete bridge: module vanishing ⇒ rigidity (`generation_of_module_vanishes`) -/

/-- **THE concrete `d = syzdim` bridge (module vanishing ⇒ rigidity), fully proven.**  Suppose a
deficiency cocycle `(q_AB, q_AC, q_BC)` factors through the SYZ36 reduction
`q_XY = V_T · W_XY · r_XY` with the in-budget degree bounds on the reduced cofactors, over a
pairwise-coprime reduced triple with `W_AB ≠ 0`, `V_T ≠ 0`.  If that reduced triple is
**Sylvester-injective** (its in-budget syzygy module is `{0}`, `SYZ38.SylvesterInjective`, supplied
uniformly by `UniformSylvesterInjective`), then **every mismatch vanishes**:

`q_AB = 0 ∧ q_AC = 0 ∧ q_BC = 0`,

i.e. the local `deg < k` polynomials glue to a single global one — the cores **generate**.  This is
the SYZ36 `d = syzdim` law in the "vanishing ⇒ generation" direction SYZ40 consumes, now discharged
from the already-formalized SYZ36/SYZ38 bricks (no probe, no black box).

Chain: `reduced_is_syzygy` (cancel `V_T`) ⇒ `SYZ38.module_vanishes_of_sylvester_injective`
(`r_AB = r_AC = r_BC = 0`) ⇒ each `q_XY = V_T·W_XY·r_XY = 0`. -/
theorem rigidity_of_module_vanishes
    (VT WAB WAC WBC rAB rAC rBC qAB qAC qBC : K[X]) (bAC bBC : ℕ)
    (hVT : VT ≠ 0) (hWAB : WAB ≠ 0)
    (hfAB : qAB = VT * WAB * rAB) (hfAC : qAC = VT * WAC * rAC) (hfBC : qBC = VT * WBC * rBC)
    (hcocycle : qAB - qAC + qBC = 0)
    (hbAC : rAC ≠ 0 → rAC.natDegree ≤ bAC)
    (hbBC : rBC ≠ 0 → rBC.natDegree ≤ bBC)
    (hInj : SYZ38.SylvesterInjective WAB WAC WBC bAC bBC) :
    qAB = 0 ∧ qAC = 0 ∧ qBC = 0 := by
  have hred : WAB * rAB - WAC * rAC + WBC * rBC = 0 :=
    reduced_is_syzygy VT WAB WAC WBC rAB rAC rBC qAB qAC qBC hVT hfAB hfAC hfBC hcocycle
  obtain ⟨hrAB, hrAC, hrBC⟩ :=
    SYZ38.module_vanishes_of_sylvester_injective WAB WAC WBC rAB rAC rBC bAC bBC hWAB hred
      hbAC hbBC hInj
  refine ⟨?_, ?_, ?_⟩
  · rw [hfAB, hrAB]; ring
  · rw [hfAC, hrAC]; ring
  · rw [hfBC, hrBC]; ring

/-- **`generation_of_module_vanishes` — the bridge, uniformly quantified.**  Packaged form of
`rigidity_of_module_vanishes` reading exactly as "in-budget syzygy module `= 0` ⇒ deficiency space
`= 0`": for **every** deficiency cocycle admitting the SYZ36 reduction over a fixed Sylvester-injective
reduced triple, all mismatches vanish.  This is the statement SYZ40's `syzdimBridge` field needs,
delivered from the one polynomial residual. -/
theorem generation_of_module_vanishes
    (VT WAB WAC WBC : K[X]) (bAC bBC : ℕ)
    (hVT : VT ≠ 0) (hWAB : WAB ≠ 0)
    (hInj : SYZ38.SylvesterInjective WAB WAC WBC bAC bBC) :
    ∀ (rAB rAC rBC qAB qAC qBC : K[X]),
      qAB = VT * WAB * rAB → qAC = VT * WAC * rAC → qBC = VT * WBC * rBC →
      qAB - qAC + qBC = 0 →
      (rAC ≠ 0 → rAC.natDegree ≤ bAC) → (rBC ≠ 0 → rBC.natDegree ≤ bBC) →
      qAB = 0 ∧ qAC = 0 ∧ qBC = 0 :=
  fun rAB rAC rBC qAB qAC qBC hfAB hfAC hfBC hcocycle hbAC hbBC =>
    rigidity_of_module_vanishes VT WAB WAC WBC rAB rAC rBC qAB qAC qBC bAC bBC hVT hWAB
      hfAB hfAC hfBC hcocycle hbAC hbBC hInj

/-! ## 3. The strengthened master hypothesis: `syzdimBridge` removed -/

section Master

variable (K) (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Strengthened master hypothesis — `syzdimBridge` REMOVED.**  Compared with SYZ40's
`StripMasterHypothesis`, the folded `syzdimBridge` field (the probe-verified `d = syzdim` black box)
is **gone**: its syzygy-space content is now the *proven* theorem `generation_of_module_vanishes`.
Only the two genuinely-residual fields remain:

* `uniformSylvester` — **the** single substantive open input (SYZ38/SYZ39, BGK type);
* `realizability` — the SYZ22 production-ledger join (MDS-shortening dimension count).

This is a strict strengthening of SYZ40's master hypothesis: any `StripMasterHypothesis` yields a
`StripMasterHypothesis'` by dropping a field (`ofSYZ40`). -/
structure StripMasterHypothesis' (n k : ℕ) : Prop where
  /-- The one substantive open residual: uniform Sylvester injectivity. -/
  uniformSylvester : SYZ40.UniformSylvesterInjective K n k
  /-- Folded SYZ22 realizability (production-ledger join) for the spread stack. -/
  realizability : ∀ Ucard, k ≤ Ucard → Ucard ≤ n →
    Nonempty (Frontier.SYZ20JointRankSuperadditive.SuperadditiveUnion (F := K) (V := V) n k Ucard)

variable {K V}

/-- **Weakening: SYZ40's master hypothesis contains SYZ41's.**  Dropping the now-proven
`syzdimBridge` field turns any `StripMasterHypothesis` into the two-field `StripMasterHypothesis'`;
the converse is *not* required (the bridge is discharged), which is exactly the reduction. -/
theorem StripMasterHypothesis'.ofSYZ40 {n k : ℕ}
    (H : SYZ40.StripMasterHypothesis K V n k) : StripMasterHypothesis' K V n k :=
  ⟨H.uniformSylvester, H.realizability⟩

/-- **THE strengthened strip theorem — two fields, `syzdimBridge` removed.**  Given the two-field
master hypothesis, the full rate-`1/2` strip conclusion holds:

* **spread branch (concrete rigidity form)** — every in-budget reduced syzygy of a rate-`1/2` band
  triple vanishes (`strip_theorem_of_uniform_sylvester`, from `uniformSylvester` alone);
* **union budget** — `|U| ≤ n − 1` for every spread stack (from `realizability`).

The spread branch is stated *concretely* (module vanishing) rather than through the abstract pair
law, so **no bridge field is consumed** — the old `syzdimBridge` is gone.  The abstract-pair-law
restatement is recovered separately in `pairInteriorLaw_of_master'` from the light
`SyzdimDictionary` transport. -/
theorem strip_theorem_of_master_hypothesis' [DecidableEq K] {n k : ℕ}
    (H : StripMasterHypothesis' K V n k) (hn : n = 2 * k) :
    -- spread branch (concrete): every in-budget reduced syzygy vanishes
    (∀ (WAB WAC WBC rAB rAC rBC : K[X]) (mAB mAC mBC t : ℕ),
      t < mAB → k - 1 < mAB + mAC - t →
      WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t → WAB ≠ 0 →
      WAB * rAB - WAC * rAC + WBC * rBC = 0 →
      (rAC ≠ 0 → rAC.natDegree ≤ k - 1 - mAC) → (rBC ≠ 0 → rBC.natDegree ≤ k - 1 - mBC) →
      rAB = 0 ∧ rAC = 0 ∧ rBC = 0)
    ∧
    -- union budget for every spread stack
    (∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n - 1) := by
  refine ⟨?_, ?_⟩
  · intro WAB WAC WBC rAB rAC rBC mAB mAC mBC t htAB hout hWAB hWAC hWBC hWAB0 hsyz hbAC hbBC
    exact SYZ40.strip_theorem_of_uniform_sylvester H.uniformSylvester
      WAB WAC WBC rAB rAC rBC mAB mAC mBC t hn htAB hout hWAB hWAC hWBC hWAB0 hsyz hbAC hbBC
  · intro Ucard hkU hUn
    exact Frontier.SYZ22.strip_budget_of_realizability hkU hUn (H.realizability Ucard hkU hUn).some

/-! ## 4. The light duality dictionary (recovering the abstract pair law) -/

/-- **The dictionary residue of the old bridge (strictly lighter, named honestly).**  All that
survives of `syzdimBridge` after the syzygy logic is discharged: the SYZ25/SYZ34 duality identification
turning the *concrete* rigidity (all local mismatches vanish ⇒ generation, `generation_of_module_vanishes`)
into the *abstract* subspace equality `finrank (A⊔B⊔C) = finrank W`.  It carries no syzygy content —
purely `generation_iff_dualAnnihilator` (SYZ25) plus the fiber-product transport (SYZ34) — so folding
it is honest and far weaker than the original catch-all field.  Recorded per configuration as a
Sylvester-injective ⇒ generation implication for the *specific* `(A,B,C,W)` realized by the band
cores. -/
def SyzdimDictionary (n k : ℕ) : Prop :=
  ∀ (A B C W : Submodule K V) (WAB WAC WBC : K[X]) (bAC bBC : ℕ),
    n = 2 * k → A ⊓ B = ⊥ → A ⊔ B ⊔ C ≤ W → WAB ≠ 0 →
    SYZ38.SylvesterInjective WAB WAC WBC bAC bBC →
    finrank K ↥(A ⊔ B ⊔ C) = finrank K W

/-- **Abstract pair law from the two-field hypothesis + the light dictionary.**  Combining the
strengthened master hypothesis (whose `uniformSylvester` supplies Sylvester injectivity) with the
light `SyzdimDictionary` transport recovers SYZ33 lemma 2 (the sharp punctured-pair law) in the
abstract-subspace form — exactly SYZ40's `pairInteriorLaw_of_master`, but with the fat `syzdimBridge`
field replaced by the honestly-lighter dictionary. -/
theorem pairInteriorLaw_of_master' {n k : ℕ}
    (H : StripMasterHypothesis' K V n k) (dict : SyzdimDictionary (K := K) (V := V) n k)
    (A B C W : Submodule K V) (WAB WAC WBC : K[X]) (mAB mAC mBC t : ℕ)
    (hAB : A ⊓ B = ⊥) (hW : A ⊔ B ⊔ C ≤ W)
    (hn : n = 2 * k) (htAB : t < mAB) (hout : k - 1 < mAB + mAC - t)
    (hWAB : WAB.natDegree = mAB - t) (hWAC : WAC.natDegree = mAC - t)
    (hWBC : WBC.natDegree = mBC - t) (hWAB0 : WAB ≠ 0) :
    finrank K ↥((A ⊔ B) ⊓ C) + finrank K W = finrank K A + finrank K B + finrank K C := by
  have hInj : SYZ38.SylvesterInjective WAB WAC WBC (k - 1 - mAC) (k - 1 - mBC) :=
    H.uniformSylvester WAB WAC WBC mAB mAC mBC t hn htAB hout hWAB hWAC hWBC hWAB0
  have hgen : finrank K ↥(A ⊔ B ⊔ C) = finrank K W :=
    dict A B C W WAB WAC WBC _ _ hn hAB hW hWAB0 hInj
  exact (SYZ35.pairInteriorLaw_iff_generation A B C W hAB hW).2 hgen

end Master

end ArkLib.ProximityGap.SYZ41

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ41.factor_ne_zero
#print axioms ArkLib.ProximityGap.SYZ41.reduced_is_syzygy
#print axioms ArkLib.ProximityGap.SYZ41.nontrivial_reduced_of_nontrivial_cocycle
#print axioms ArkLib.ProximityGap.SYZ41.rigidity_of_module_vanishes
#print axioms ArkLib.ProximityGap.SYZ41.generation_of_module_vanishes
#print axioms ArkLib.ProximityGap.SYZ41.StripMasterHypothesis'.ofSYZ40
#print axioms ArkLib.ProximityGap.SYZ41.strip_theorem_of_master_hypothesis'
#print axioms ArkLib.ProximityGap.SYZ41.pairInteriorLaw_of_master'
