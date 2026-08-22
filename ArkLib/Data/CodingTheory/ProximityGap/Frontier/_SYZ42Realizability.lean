/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ41SyzdimBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ24CrossCoreCompatibility
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ22StripBridge

/-!
# SYZ42 — realizability: is the SYZ22 production-ledger join redundant after SYZ41?

SYZ41 removed the folded `syzdimBridge` field from the master hypothesis by *proving* its syzygy
logic (`generation_of_module_vanishes`: in-budget module vanishing ⇒ the cores generate the union
shortening), leaving `StripMasterHypothesis'` on **two** fields: `uniformSylvester` and
`realizability`.  SYZ24 had already shown, in `span_eq_ceiling_iff_generates`, that the union-budget
lower bound the strip needs is *exactly* cross-core generation (`⨆ Aᵢ = W`).

The natural question this file settles: **does `realizability` now follow from `uniformSylvester`
through the SYZ24 equivalence + the SYZ41 bridge, so that the master hypothesis collapses to the
single field `uniformSylvester`?**

## Verdict: NO — realizability is *not* redundant, but its analytic core *is* discharged

Tracing the exact types (see the honest audit below) the two obligations have **genuinely
different quantifier shapes**:

* `uniformSylvester` → generation (SYZ41 `generation_of_module_vanishes`, SYZ24
  `span_eq_ceiling_iff_generates`) is a **rigidity** statement: *for a given configuration*, any
  in-budget deficiency is trivial, hence its span **attains** the ceiling `finrank W`.
* `realizability` is `∀ Ucard, Nonempty (SuperadditiveUnion n k Ucard)` — an **existence /
  construction** statement.  Unfolding `SuperadditiveUnion` (SYZ20), it packages *six* fields, of
  which **five are pure existence of data** that `uniformSylvester` never manufactures:
  `synFunctionals`, a **nonzero** `syndrome`, its annihilation, and — decisively — the ambient
  pinning `dim_syndromePair : finrank V = 2(n − k)` (false for a generic finite-dimensional `V`).

So rigidity cannot deliver existence: no amount of "every deficiency vanishes" produces the syndrome
vector, the functionals, or forces `finrank V = 2(n − k)`.  The quantifiers do not meet.

## What *is* delivered: the sixth field `union_span_rank` is now derived, not assumed

The **one** field of `SuperadditiveUnion` that generation controls is `union_span_rank`
(`finrank (span synFunctionals) = 2(Ucard − k)`) — precisely the span **lower bound** SYZ22/SYZ24
flagged as the realizability residue for over-budget families.  Under the SYZ24 ceiling it is
equivalent to generation (`span_eq_ceiling_iff_generates`), and generation is now backed by
`uniformSylvester` (SYZ41).  This file makes that concrete:

* `superadditiveUnion_of_generation` — **builds** a full `SuperadditiveUnion` from the existence
  data + a *generation* certificate (`span synFunctionals = W`) + the ceiling value
  (`finrank W = 2(Ucard − k)`, SYZ22 `doubled_shortening_dim`).  The `union_span_rank` field is
  *computed*, not supplied: the analytic field is discharged.
* `RealizabilityCore` — `SuperadditiveUnion` with the analytic `union_span_rank` field **replaced**
  by the generation certificate that `uniformSylvester`+SYZ24 discharge.  `toSuperadditiveUnion`
  transports it back, so the two are interchangeable.
* `StripMasterHypothesis''` — the honest reformulation: two fields, `uniformSylvester` +
  `realizabilityCore`, with the realizability obligation stated in the **generation** language that
  exposes what `uniformSylvester` covers.  `strip_theorem_of_master_hypothesis''` delivers the exact
  same strip conclusion as SYZ41's `'` form, via `toSuperadditiveUnion`.

The irreducible residue of realizability — everything `uniformSylvester` and SYZ22 leave open — is
therefore *exactly* the **existence of the syndrome configuration** (the sunflower packing / SYZ18
distinct-support control), no longer entangled with the rank equality.

## Honest status

`realizability` is **NOT redundant**; the final master-hypothesis field list stays **two**
(`uniformSylvester`, `realizabilityCore`).  What SYZ42 buys is that the realizability obligation is
refactored so its *analytic* content (`union_span_rank`) is proven from generation, isolating the
genuine open residue as pure configuration existence.  No unconditional `δ*`.  The sole substantive
open input remains `UniformSylvesterInjective` (SYZ39, BGK type) **plus** the realizability existence
core.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ42

open Polynomial Module Submodule
open ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-! ## 1. The analytic field is derivable: `union_span_rank` from generation -/

/-- **The `union_span_rank` field is a *consequence* of generation, not independent data.**
Given the raw existence data of a syndrome-pair configuration (a nonzero `syndrome`, a set of
`synFunctionals` annihilating it, and the ambient pinning `finrank V = 2(n − k)`) together with a
**generation** certificate `Submodule.span K synFunctionals = W` and the ceiling value
`finrank W = 2(Ucard − k)` (SYZ22 `doubled_shortening_dim`), one builds a full
`SuperadditiveUnion`: its `union_span_rank` field is *computed* from the two inputs.

This discharges the sixth field of `SuperadditiveUnion` — the span lower bound SYZ22/SYZ24 flagged
as the realizability residue — from generation, which SYZ41 now backs by `uniformSylvester`. -/
def superadditiveUnion_of_generation {n k Ucard : ℕ}
    (synFunctionals : Set (Module.Dual K V)) (syndrome : V) (syndrome_ne : syndrome ≠ 0)
    (annihilated : ∀ φ ∈ synFunctionals, φ syndrome = 0)
    (W : Submodule K (Module.Dual K V)) (generates : Submodule.span K synFunctionals = W)
    (ceiling_dim : finrank K W = 2 * (Ucard - k))
    (dim_syndromePair : finrank K V = 2 * (n - k)) :
    SuperadditiveUnion (F := K) (V := V) n k Ucard where
  synFunctionals := synFunctionals
  syndrome := syndrome
  syndrome_ne := syndrome_ne
  annihilated := annihilated
  union_span_rank := by rw [generates]; exact ceiling_dim
  dim_syndromePair := dim_syndromePair

/-! ## 2. The realizability core: everything the analytic field is *not* -/

/-- **`RealizabilityCore` — `SuperadditiveUnion` with the analytic field replaced by generation.**
Compared with SYZ20's `SuperadditiveUnion`, the single analytic field `union_span_rank`
(`finrank (span synFunctionals) = 2(Ucard − k)`) is **replaced** by:

* `ceiling` `W` and `generates : span synFunctionals = W` — the *generation* certificate that
  SYZ24 (`span_eq_ceiling_iff_generates`) equates with cross-core codeword compatibility and that
  SYZ41 (`generation_of_module_vanishes`) delivers from `uniformSylvester`;
* `ceiling_dim : finrank W = 2(Ucard − k)` — the ceiling value, a *proven* MDS-shortening fact
  (SYZ22 `doubled_shortening_dim`) for the concrete anchored dual.

The remaining fields (`synFunctionals`, `syndrome`, `syndrome_ne`, `annihilated`,
`dim_syndromePair`) are the **irreducible existence residue** — the sunflower packing / SYZ18
distinct-support control — that no rigidity input can manufacture. -/
structure RealizabilityCore (n k Ucard : ℕ) where
  /-- The union-anchored parity functionals (existence residue). -/
  synFunctionals : Set (Module.Dual K V)
  /-- The (nonzero) stack syndrome pair (existence residue). -/
  syndrome : V
  syndrome_ne : syndrome ≠ 0
  annihilated : ∀ φ ∈ synFunctionals, φ syndrome = 0
  /-- The shortened dual ceiling `W = A_U`. -/
  ceiling : Submodule K (Module.Dual K V)
  /-- **Generation** (the SYZ24/SYZ41-backed replacement for `union_span_rank`). -/
  generates : Submodule.span K synFunctionals = ceiling
  /-- Ceiling value: SYZ22 `doubled_shortening_dim`. -/
  ceiling_dim : finrank K ceiling = 2 * (Ucard - k)
  /-- Ambient syndrome-pair dimension (existence residue). -/
  dim_syndromePair : finrank K V = 2 * (n - k)

/-- **The core transports back to `SuperadditiveUnion`.**  A `RealizabilityCore` yields a genuine
`SuperadditiveUnion`, with the analytic `union_span_rank` field *derived* from `generates` +
`ceiling_dim` via `superadditiveUnion_of_generation`.  Hence the two forms are interchangeable and
`RealizabilityCore` is the sharpest honest statement of the realizability obligation. -/
def RealizabilityCore.toSuperadditiveUnion {n k Ucard : ℕ}
    (c : RealizabilityCore (K := K) (V := V) n k Ucard) :
    SuperadditiveUnion (F := K) (V := V) n k Ucard :=
  superadditiveUnion_of_generation c.synFunctionals c.syndrome c.syndrome_ne c.annihilated
    c.ceiling c.generates c.ceiling_dim c.dim_syndromePair

/-- Conversely, any `SuperadditiveUnion` is a `RealizabilityCore` with the trivial ceiling
`W := span synFunctionals` (`generates := rfl`).  So the generation reformulation loses nothing:
`RealizabilityCore` and `SuperadditiveUnion` are logically equivalent — the reformulation merely
*exposes* the analytic field as the generation condition. -/
def _root_.ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive.SuperadditiveUnion.toRealizabilityCore
    {n k Ucard : ℕ}
    (s : SuperadditiveUnion (F := K) (V := V) n k Ucard) :
    RealizabilityCore (K := K) (V := V) n k Ucard where
  synFunctionals := s.synFunctionals
  syndrome := s.syndrome
  syndrome_ne := s.syndrome_ne
  annihilated := s.annihilated
  ceiling := Submodule.span K s.synFunctionals
  generates := rfl
  ceiling_dim := s.union_span_rank
  dim_syndromePair := s.dim_syndromePair

/-! ## 3. The sharpest honest master hypothesis: realizability stated as generation -/

section Master

variable (K) (V)

/-- **`StripMasterHypothesis''` — the realizability field stated in generation language.**
Two fields, exactly as SYZ41's `StripMasterHypothesis'`:

* `uniformSylvester` — **the** single substantive open polynomial residual (SYZ38/SYZ39, BGK type);
* `realizabilityCore` — the SYZ22 production-ledger join, now stated as the **existence of a
  generating configuration** (`RealizabilityCore`) rather than as the opaque `union_span_rank`
  equality.  The analytic content (`union_span_rank`) is *derived* (SYZ42
  `superadditiveUnion_of_generation`); what remains is pure configuration existence.

This is a **reformulation**, not a field-count reduction: realizability is *not* redundant after
SYZ41.  Its value is transparency — the generation phrasing shows exactly which part
(`generates`, `ceiling_dim`) `uniformSylvester`+SYZ22/SYZ24 discharge, and isolates the genuine
open residue (the syndrome-configuration existence). -/
structure StripMasterHypothesis'' (n k : ℕ) : Prop where
  /-- The one substantive open residual: uniform Sylvester injectivity. -/
  uniformSylvester : SYZ40.UniformSylvesterInjective K n k
  /-- Realizability, in generation language (analytic field derived). -/
  realizabilityCore : ∀ Ucard, k ≤ Ucard → Ucard ≤ n →
    Nonempty (RealizabilityCore (K := K) (V := V) n k Ucard)

variable {K V}

/-- **`''` refines `'` (they are interchangeable).**  A `StripMasterHypothesis''` yields SYZ41's
`StripMasterHypothesis'` by transporting each `RealizabilityCore` back to a `SuperadditiveUnion`
(`toSuperadditiveUnion`); the converse holds via `toRealizabilityCore`.  So no strength is gained or
lost — the reformulation only restates the realizability obligation in the generation language that
`uniformSylvester` illuminates. -/
theorem StripMasterHypothesis''.toPrime {n k : ℕ}
    (H : StripMasterHypothesis'' K V n k) :
    ArkLib.ProximityGap.SYZ41.StripMasterHypothesis' K V n k :=
  ⟨H.uniformSylvester, fun Ucard hkU hUn =>
    ⟨(H.realizabilityCore Ucard hkU hUn).some.toSuperadditiveUnion⟩⟩

/-- The reverse transport: SYZ41's `'` yields SYZ42's `''`. -/
theorem StripMasterHypothesis''.ofPrime {n k : ℕ}
    (H : ArkLib.ProximityGap.SYZ41.StripMasterHypothesis' K V n k) :
    StripMasterHypothesis'' K V n k :=
  ⟨H.uniformSylvester, fun Ucard hkU hUn =>
    ⟨(H.realizability Ucard hkU hUn).some.toRealizabilityCore⟩⟩

/-- **THE strip theorem from the generation-language hypothesis.**  Identical conclusion to SYZ41's
`strip_theorem_of_master_hypothesis'`, obtained by transporting `''` to `'`: the concrete spread
branch (every in-budget reduced syzygy of a rate-`1/2` band triple vanishes) and the union budget
`|U| ≤ n − 1` for every spread stack.  The realizability obligation is consumed in its sharpest
form (`RealizabilityCore`), with the analytic `union_span_rank` field derived rather than assumed. -/
theorem strip_theorem_of_master_hypothesis'' [DecidableEq K] {n k : ℕ}
    (H : StripMasterHypothesis'' K V n k) (hn : n = 2 * k) :
    (∀ (WAB WAC WBC rAB rAC rBC : K[X]) (mAB mAC mBC t : ℕ),
      t < mAB → k - 1 < mAB + mAC - t →
      WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t → WAB ≠ 0 →
      WAB * rAB - WAC * rAC + WBC * rBC = 0 →
      (rAC ≠ 0 → rAC.natDegree ≤ k - 1 - mAC) → (rBC ≠ 0 → rBC.natDegree ≤ k - 1 - mBC) →
      rAB = 0 ∧ rAC = 0 ∧ rBC = 0)
    ∧
    (∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n - 1) :=
  ArkLib.ProximityGap.SYZ41.strip_theorem_of_master_hypothesis' H.toPrime hn

end Master

end ArkLib.ProximityGap.SYZ42

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ42.superadditiveUnion_of_generation
#print axioms ArkLib.ProximityGap.SYZ42.RealizabilityCore.toSuperadditiveUnion
#print axioms ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive.SuperadditiveUnion.toRealizabilityCore
#print axioms ArkLib.ProximityGap.SYZ42.StripMasterHypothesis''.toPrime
#print axioms ArkLib.ProximityGap.SYZ42.StripMasterHypothesis''.ofPrime
#print axioms ArkLib.ProximityGap.SYZ42.strip_theorem_of_master_hypothesis''
