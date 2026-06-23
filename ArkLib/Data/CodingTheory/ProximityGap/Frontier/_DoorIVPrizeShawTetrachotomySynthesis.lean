/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVShawValueSharpFloor

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Lane-2 synthesis capstone: the prize is *both* a bounded Shaw value *and* a door-(iv)-only target

This module is the single citable Lane-2 synthesis for the proximity prize (#444).  It welds the two
previously *disconnected* Lane-2/3 capstones into one kernel-checked statement:

* `ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound` — the prize-family
  reduction `prize ⇔ Sh(n)=O(1)` (the worst-frequency sup family is uniformly prize-bounded iff the
  normalized Shaw values are uniformly bounded by an absolute constant); and
* `NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV` — the no-fifth-door exclusion (any mechanism
  whose certified scale reaches the prize floor `√n` must be a door-(iv) `newEvaluation` mechanism,
  given the proven classical-overshoot refutations of doors (i)-(iii)).

No file in the repository imported both before; this is the first kernel-checked bridge between the
*normalization* capstone (Shaw value) and the *mechanism-classification* capstone (tetrachotomy).

## What this module proves (and what it does NOT)

It packages the **conjunction** of the two established facts as one statement, so a citation can point
at a single theorem for the prose claim:

> "The proximity prize is exactly the demand that the normalized Shaw value be `O(1)`, and the only
>  mechanism that can deliver it is door (iv) (a genuinely new evaluation of the monomial sum)."

It does **not** prove the prize inequality, does **not** give any anti-concentration / cancellation
estimate for the monomial phase set, and does **not** claim door (iv) is achievable.  Both inputs are
pure restatements / exclusions; the open problem (a door-(iv) bound) is exactly as open as before.

Note the two namespaces use *different* normalizations on purpose, and we keep them apart:
`ShawValueCapstone.prizeScale n L = √(n·L)` is the BGK-shaped target used for the `O(1)` family
reduction; `NoFifthDoorTetrachotomy.prizeScale n = √n` is the prize *floor* used for the mechanism
exclusion.  The synthesis below references each through its own namespace so no normalization is
silently conflated.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis

open ArkLib.ProximityGap.Frontier

/-- **Synthesis capstone (conjunctive form).**

Given a parameter family of thin instances with pointwise positive Shaw-prize scale `√(nᵢ·Lᵢ)`, and
given the proven classical-overshoot refutations at a fixed reference instance `(n, L)` with `L > 1`,
the following two facts hold *simultaneously*:

1. **Reduction.**  The family admits an absolute raw prize constant `C` (`Mᵢ ≤ C·√(nᵢ·Lᵢ)` for all `i`)
   **iff** it admits an absolute Shaw-value constant `C` (`Sh(Mᵢ) ≤ C` for all `i`).  This is the
   `prize ⇔ Sh(n)=O(1)` reduction.

2. **Mechanism exclusion.**  At the reference instance, *every* mechanism whose certified scale reaches
   the prize floor `√n` is a door-(iv) `newEvaluation` mechanism; no classical door (moment /
   completion / extreme-value) survives.

This is the single Lane-2 statement behind the prose "the prize is a bounded Shaw value, deliverable
only through door (iv)."  No cancellation/anti-concentration estimate is asserted. -/
theorem prize_iff_shawBounded_and_doorIV_only
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ((∃ C, ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_⟩
  · exact ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound hs
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **Contrapositive packaging of the mechanism side.**  If, at the reference instance, the prize
family is *not* Shaw-bounded (no absolute `C`), the door-(iv) exclusion still holds verbatim: the
mechanism-classification fact is independent of whether the prize is actually achievable.  This
records that the no-fifth-door exclusion is unconditional on the (open) reduction outcome. -/
theorem doorIV_only_independent_of_reduction
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ∀ m : NoFifthDoorTetrachotomy.Mechanism,
      m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
      m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **Nonnegative-constant synthesis.**  The reduction half, in the sign-normalized constant form
usually quoted in prose (`prize iff Sh(n)=O(1)` with a *nonnegative* absolute constant), conjoined
with the same door-(iv) exclusion.  The nonnegative form is the one most directly cited. -/
theorem prize_iff_shawBounded_nonneg_and_doorIV_only
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ((∃ C, 0 ≤ C ∧ ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_⟩
  · exact
      ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **The remaining gap is a single `√L` factor, and it is door-(iv)-only.**  Conjoins the
quantitative door-(iv) obligation (the BGK ceiling exceeds the prize floor by exactly the factor
`√L`, so the corridor `[√n, √(n·L)]` has positive width in the regime `L > 1`) with the exclusion
(only door (iv) can shave that factor).  This is the crispest one-line statement of "what is left." -/
theorem remaining_gap_is_sqrtL_factor_doorIV_only
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (NoFifthDoorTetrachotomy.prizeScale nref < NoFifthDoorTetrachotomy.bgkScale nref Lref) ∧
      (NoFifthDoorTetrachotomy.bgkScale nref Lref =
        Real.sqrt Lref * NoFifthDoorTetrachotomy.prizeScale nref) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_, ?_⟩
  · exact NoFifthDoorTetrachotomy.doorIV_corridor_width_pos hnref hLref
  · exact NoFifthDoorTetrachotomy.bgkScale_eq_sqrtL_mul_prizeScale (le_of_lt hnref)
      (le_of_lt (lt_trans one_pos hLref))
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-! ## Floor-normalized prize ratio `M/√n` (the tetrachotomy's own `prizeScale n = √n` units)

The `ShawValueCapstone` reduction normalizes by the BGK-shaped scale `√(n·L)`, landing the Plancherel
floor at the `n`-independent but `L`-dependent value `1/√L`.  The tetrachotomy, by contrast, measures
the worst-frequency sup against the prize *floor* `prizeScale n = √n`.  In *that* normalization the
Plancherel/RMS floor lands at the clean absolute constant `1`, and the prize is exactly the demand
`M/√n = O(1)`.  This is the cleanest normalization in which to state the floor and it was absent from
both capstones.  These rungs add it and tie it to the door-(iv) exclusion. -/

/-- The floor-normalized prize ratio: worst-frequency sup divided by the prize *floor* `√n`. -/
noncomputable def floorPrizeRatio (M n : ℝ) : ℝ :=
  M / NoFifthDoorTetrachotomy.prizeScale n

/-- **The Plancherel floor lands the floor-normalized ratio at the absolute constant `1`.**  The
RMS/Plancherel lower bound `√n ≤ M` is, in `√n` units, exactly `1 ≤ M/√n`.  Unlike the `√(n·L)`
normalization (floor `1/√L`), this floor is a clean `n`- and `L`-independent constant. -/
theorem one_le_floorPrizeRatio_of_plancherel_floor {M n : ℝ} (hn : 0 < n)
    (hfloor : NoFifthDoorTetrachotomy.prizeScale n ≤ M) :
    1 ≤ floorPrizeRatio M n := by
  unfold floorPrizeRatio
  rw [le_div_iff₀ (NoFifthDoorTetrachotomy.prizeScale_pos hn), one_mul]
  exact hfloor

/-- **Prize bound ⇔ floor-normalized ratio ≤ C.**  The raw prize-floor-shaped bound `M ≤ C·√n` is
exactly `M/√n ≤ C`.  This is the prize-floor analogue of `ShawValueCapstone.prizeBound_iff_shawValue_le`,
in `√n` units.  (Note: the prize is `M ≤ C·√n` only up to the `√L` thinness factor — this rung is the
*floor*-scale reduction, complementary to the BGK-scale Shaw reduction.) -/
theorem prizeFloorBound_iff_floorPrizeRatio_le {M n C : ℝ} (hn : 0 < n) :
    M ≤ C * NoFifthDoorTetrachotomy.prizeScale n ↔ floorPrizeRatio M n ≤ C := by
  unfold floorPrizeRatio
  rw [div_le_iff₀ (NoFifthDoorTetrachotomy.prizeScale_pos hn), mul_comm]

/-- **Any floor-scale prize constant must be at least one.**  In `√n` units the Plancherel
floor is the hard baseline: if `√n ≤ M` and also `M ≤ K√n`, then necessarily `1 ≤ K`.  Thus a
floor-normalized certificate cannot have a sub-unit constant; all remaining work is to keep the
constant bounded above, not to push the floor below `1`. -/
theorem one_le_prizeFloorConstant_of_plancherel_floor
    {M n K : ℝ} (hn : 0 < n)
    (hfloor : NoFifthDoorTetrachotomy.prizeScale n ≤ M)
    (hbound : M ≤ K * NoFifthDoorTetrachotomy.prizeScale n) :
    1 ≤ K := by
  have hratio_floor : 1 ≤ floorPrizeRatio M n :=
    one_le_floorPrizeRatio_of_plancherel_floor hn hfloor
  have hratio_bound : floorPrizeRatio M n ≤ K :=
    (prizeFloorBound_iff_floorPrizeRatio_le hn).mp hbound
  exact le_trans hratio_floor hratio_bound

/-- **Floor-normalized synthesis.**  At the reference instance: the Plancherel floor pins the
floor-normalized ratio at `≥ 1`, the prize-floor bound is exactly `M/√n ≤ C`, and any mechanism
reaching the prize floor is door-(iv)-only.  One citable statement in the prize-floor `√n` units:
the ratio lives in `[1, …]`, the prize asks to cap it by an absolute constant, and only door (iv) can. -/
theorem floorRatio_bracketed_prize_iff_and_doorIV_only
    {M nref Lref C : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hfloor : NoFifthDoorTetrachotomy.prizeScale nref ≤ M)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (1 ≤ floorPrizeRatio M nref) ∧
      (M ≤ C * NoFifthDoorTetrachotomy.prizeScale nref ↔ floorPrizeRatio M nref ≤ C) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_, ?_⟩
  · exact one_le_floorPrizeRatio_of_plancherel_floor hnref hfloor
  · exact prizeFloorBound_iff_floorPrizeRatio_le hnref
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **The BGK ceiling lands the floor-normalized ratio at `≤ √L`.**  A classical-door BGK ceiling
`M ≤ √(n·L) = bgkScale n L` is, in `√n` units, exactly `M/√n ≤ √L`.  Together with the Plancherel
floor `1 ≤ M/√n`, the floor-normalized ratio lives in the corridor `[1, √L]`. -/
theorem floorPrizeRatio_le_sqrtL_of_bgk_ceiling {M n L : ℝ} (hn : 0 < n)
    (hceil : M ≤ NoFifthDoorTetrachotomy.bgkScale n L) :
    floorPrizeRatio M n ≤ Real.sqrt L := by
  unfold floorPrizeRatio NoFifthDoorTetrachotomy.prizeScale
  simp only [NoFifthDoorTetrachotomy.bgkScale] at hceil
  rw [div_le_iff₀ (Real.sqrt_pos.2 hn)]
  calc M ≤ Real.sqrt (n * L) := hceil
    _ = Real.sqrt L * Real.sqrt n := by
        rw [Real.sqrt_mul (le_of_lt hn), mul_comm]

/-- **Floor-unit corridor `[1, √L]`, door-(iv)-only.**  Given the Plancherel floor `√n ≤ M` and a
classical-door BGK ceiling `M ≤ √(n·L)`, the floor-normalized worst-frequency ratio `M/√n` lives in
the corridor `[1, √L]`; the prize is exactly the demand to collapse it to `[1, C]` for an absolute
`C`, and — by the no-fifth-door exclusion — only door (iv) can shave the `√L`.  This is the prize-floor
(`√n`-unit) corridor, distinct from the absolute `[√n, √(n·L)]` corridor and the `√(n·L)`-unit Shaw
bracket `[1/√L, √(n/L)]`. -/
theorem floorUnit_corridor_one_sqrtL_doorIV_only
    {M nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hfloor : NoFifthDoorTetrachotomy.prizeScale nref ≤ M)
    (hceil : M ≤ NoFifthDoorTetrachotomy.bgkScale nref Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (1 ≤ floorPrizeRatio M nref ∧ floorPrizeRatio M nref ≤ Real.sqrt Lref) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact one_le_floorPrizeRatio_of_plancherel_floor hnref hfloor
  · exact floorPrizeRatio_le_sqrtL_of_bgk_ceiling hnref hceil
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-! ## A fully-discharged instance: the named √q-completion lever fails, no postulate

The synthesis theorems above carry the abstract `hclassicalOvershoots` quantifier (ranging over *all*
classical mechanisms).  For the *named* √q-completion door (door (ii)), that overshoot is not a
postulate — it is *discharged* by the proven Polya-Vinogradov/Gauss-sum ceiling `M ≤ √q` via
`NoFifthDoorTetrachotomy.completionMechanism_overshootsBGK`.  This rung records the fully-discharged
consequence: in the prize regime (`n·L ≤ q`, `L > 1`) the concrete completion mechanism provably fails
to certify the prize floor, with NO assumed-overshoot hypothesis.  It is the one named lever for which
the synthesis is unconditional. -/

/-- **Discharged completion failure (no postulate).**  In the prize regime `L > 1`, `n·L ≤ q`, the
concrete √q-completion mechanism `⟨completion, √q⟩` provably overshoots BGK and therefore does *not*
certify the prize floor `√n`.  Combined with the floor-normalized Plancherel floor (`1 ≤ M/√n`) and
the floor-scale prize reduction (`M ≤ C·√n ⇔ M/√n ≤ C`), this gives an unconditional witness that at
least one named classical door is excluded — no `hclassicalOvershoots` postulate required. -/
theorem completion_excluded_discharged_floorPrize
    {M nref Lref q C : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hq : nref * Lref ≤ q)
    (hfloor : NoFifthDoorTetrachotomy.prizeScale nref ≤ M) :
    (¬ ((⟨NoFifthDoorTetrachotomy.DoorType.completion,
          NoFifthDoorTetrachotomy.completionScale q⟩ :
            NoFifthDoorTetrachotomy.Mechanism).certScale ≤
        NoFifthDoorTetrachotomy.prizeScale nref)) ∧
      (1 ≤ floorPrizeRatio M nref) ∧
      (M ≤ C * NoFifthDoorTetrachotomy.prizeScale nref ↔ floorPrizeRatio M nref ≤ C) := by
  refine ⟨?_, ?_, ?_⟩
  · exact NoFifthDoorTetrachotomy.not_certifies_prizeScale_of_overshoot hnref hLref
      (NoFifthDoorTetrachotomy.completionMechanism_overshootsBGK hq)
  · exact one_le_floorPrizeRatio_of_plancherel_floor hnref hfloor
  · exact prizeFloorBound_iff_floorPrizeRatio_le hnref

/-! ## Fully-discharged synthesis: Shaw reduction plus ceiling-respecting no-fifth-door

The earlier synthesis theorems combine the Shaw-value reduction with an abstract
`hclassicalOvershoots` hypothesis.  The no-fifth-door file later discharged that hypothesis for the
honest subclass of classical mechanisms whose certified scale respects the proven completion / SOTA
floors.  This final rung packages those two facts together: the reduction `prize ⇔ Sh(n)=O(1)` and
the door-(iv)-only conclusion, with no abstract overshoot postulate. -/

/-- **Fully-discharged Lane-2/3 synthesis.**  The Shaw-value family reduction holds, and past the
SOTA threshold every ceiling-respecting classical mechanism is excluded from a prize-floor certificate;
hence any prize-certifying mechanism is door `(iv)`.  Compared with
`prize_iff_shawBounded_nonneg_and_doorIV_only`, the classical-door overshoot hypothesis is discharged
from `NoFifthDoorTetrachotomy.forces_doorIV_ceilingRespecting` rather than assumed.  The remaining
`RespectsProvenScale` premise is the honest anti-degenerate guard: a claimed classical mechanism must
respect the proven scale of its own door. -/
theorem prize_iff_shawBounded_nonneg_and_discharged_doorIV_only
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {Lref q C δ : ℝ} (hLnn : 0 ≤ Lref) (hLref : 1 < Lref)
    (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ,
      ((∃ K, 0 ≤ K ∧ ShawValueCapstone.rawPrizeFamilyBound M n L K) ↔
          (∃ K, 0 ≤ K ∧ ShawValueCapstone.shawValueFamilyBound M n L K)) ∧
        (∀ nref : ℝ, max N₀ 1 ≤ nref → nref * Lref ≤ q →
          (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical →
              m'.RespectsProvenScale q C δ nref) →
          ∀ m : NoFifthDoorTetrachotomy.Mechanism,
            m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
            m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  obtain ⟨N₀, hdoor⟩ :=
    NoFifthDoorTetrachotomy.forces_doorIV_ceilingRespecting hLnn hLref hC hδ
  refine ⟨N₀, ?_, ?_⟩
  · exact
      ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs
  · exact hdoor

/-- **Fully-discharged wall-side synthesis.**  The negation of the Shaw-value reduction is packaged
with the same discharged no-fifth-door conclusion: failure of every nonnegative raw prize constant is
equivalent to failure of every nonnegative Shaw-value constant, and any actual prize-floor certificate
past the SOTA threshold must still be door `(iv)` for ceiling-respecting mechanisms.  This is the
wall-facing companion to
`prize_iff_shawBounded_nonneg_and_discharged_doorIV_only`; it adds no estimate, only the exact
contrapositive citation form. -/
theorem no_prizeBound_iff_no_shawBound_nonneg_and_discharged_doorIV_only
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {Lref q C δ : ℝ} (hLnn : 0 ≤ Lref) (hLref : 1 < Lref)
    (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ,
      (¬ (∃ K, 0 ≤ K ∧ ShawValueCapstone.rawPrizeFamilyBound M n L K) ↔
          ¬ (∃ K, 0 ≤ K ∧ ShawValueCapstone.shawValueFamilyBound M n L K)) ∧
        (∀ nref : ℝ, max N₀ 1 ≤ nref → nref * Lref ≤ q →
          (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical →
              m'.RespectsProvenScale q C δ nref) →
          ∀ m : NoFifthDoorTetrachotomy.Mechanism,
            m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
            m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  obtain ⟨N₀, hred, hdoor⟩ :=
    prize_iff_shawBounded_nonneg_and_discharged_doorIV_only hs hLnn hLref hC hδ
  exact ⟨N₀, not_congr hred, hdoor⟩

/-! ## Fully-discharged classical side in floor units

The previous discharged rung names only the completion door.  The tetrachotomy file now also proves
that, past the SOTA threshold, every ceiling-respecting moment/extreme-value mechanism overshoots BGK
at the same time as completion (`forces_doorIV_ceilingRespecting`).  This final synthesis rung feeds
that theorem back into the floor-normalized API: no abstract `hclassicalOvershoots` postulate remains
for real classical mechanisms, and the remaining prize burden is exactly the floor-ratio cap.
-/

/-- **Discharged classical-side synthesis in floor units.**  For `L > 1`, `C > 0`, and a SOTA
exponent `δ < 1/2`, there is a threshold `N₀` such that at every fixed prize-regime index `n ≥ N₀`
(with its pointwise field-size witness `n·L ≤ q`), if the classical mechanisms are honest instances
of their doors (they respect the proven completion/SOTA ceilings), then any mechanism certifying the
prize floor is forced to be door `(iv)`.  Simultaneously, the worst-frequency sup `M` is expressed in
floor units: the Plancherel floor is `1 ≤ M/√n`, and `M ≤ K√n` is exactly `M/√n ≤ K`.

This is Lane-2/3 bookkeeping only: it discharges the classical-door exclusion from already-proven
ceilings and restates the remaining target in `√n` units.  It proves no new monomial-sum cancellation. -/
theorem ceilingRespecting_classical_excluded_floorPrizeRatio
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.RespectsProvenScale q C δ n) →
      ∀ M K : ℝ, NoFifthDoorTetrachotomy.prizeScale n ≤ M →
        (1 ≤ floorPrizeRatio M n) ∧
          (M ≤ K * NoFifthDoorTetrachotomy.prizeScale n ↔ floorPrizeRatio M n ≤ K) ∧
          (∀ m : NoFifthDoorTetrachotomy.Mechanism,
            m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale n →
            m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  obtain ⟨N₀, hN₀⟩ :=
    NoFifthDoorTetrachotomy.forces_doorIV_ceilingRespecting hLnn hL hC hδ
  refine ⟨N₀, fun n hn hq hrespAll M K hfloor => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le one_pos hn1
  refine ⟨?_, ?_, ?_⟩
  · exact one_le_floorPrizeRatio_of_plancherel_floor hnpos hfloor
  · exact prizeFloorBound_iff_floorPrizeRatio_le hnpos
  · exact hN₀ n hn hq hrespAll

/-- **Wall-side reduction plus floor-ratio discharged door-(iv) package.**  This combines the
wall-facing Shaw equivalence with the floor-unit discharged classical-side statement: failure of every
nonnegative raw prize constant is exactly failure of every nonnegative Shaw-value constant, and past a
single threshold the remaining pointwise certificate problem is expressed as `M/√n` with all honest
classical doors excluded.  This is a citation convenience theorem only; it adds no estimate. -/
theorem no_prizeBound_iff_no_shawBound_nonneg_and_floorPrizeRatio
    {ι : Type*} {Mfam n Lfam : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Lfam i))
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ,
      (¬ (∃ K, 0 ≤ K ∧ ShawValueCapstone.rawPrizeFamilyBound Mfam n Lfam K) ↔
          ¬ (∃ K, 0 ≤ K ∧ ShawValueCapstone.shawValueFamilyBound Mfam n Lfam K)) ∧
        (∀ nref : ℝ, max N₀ 1 ≤ nref → nref * L ≤ q →
          (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical → m'.RespectsProvenScale q C δ nref) →
          ∀ M K : ℝ, NoFifthDoorTetrachotomy.prizeScale nref ≤ M →
            (1 ≤ floorPrizeRatio M nref) ∧
              (M ≤ K * NoFifthDoorTetrachotomy.prizeScale nref ↔ floorPrizeRatio M nref ≤ K) ∧
              (∀ m : NoFifthDoorTetrachotomy.Mechanism,
                m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
                m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation)) := by
  obtain ⟨Nwall, hwall, _hdoor⟩ :=
    no_prizeBound_iff_no_shawBound_nonneg_and_discharged_doorIV_only
      (q := q) hs hLnn hL hC hδ
  obtain ⟨Nfloor, hfloorPack⟩ :=
    ceilingRespecting_classical_excluded_floorPrizeRatio hLnn hL hC hδ
  refine ⟨max Nwall Nfloor, hwall, ?_⟩
  intro nref hn hq hrespAll M K hfloor
  have hnfloor : max Nfloor 1 ≤ nref := by
    refine max_le ?_ ?_
    · exact le_trans (le_trans (le_max_right Nwall Nfloor) (le_max_left _ _)) hn
    · exact le_trans (le_max_right _ _) hn
  exact hfloorPack nref hnfloor hq hrespAll M K hfloor

/-- **Positive-side reduction plus floor-ratio discharged door-(iv) package.**  This is the
positive companion to `no_prizeBound_iff_no_shawBound_nonneg_and_floorPrizeRatio`: existence of a
nonnegative raw prize constant is exactly existence of a nonnegative Shaw-value constant, and past a
single threshold the pointwise prize-floor certificate problem is expressed in floor units `M/√n` with
all honest classical doors excluded.  It is pure Lane-2/3 synthesis/bookkeeping, not a new estimate. -/
theorem prize_iff_shawBounded_nonneg_and_floorPrizeRatio
    {ι : Type*} {Mfam n Lfam : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Lfam i))
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ,
      ((∃ K, 0 ≤ K ∧ ShawValueCapstone.rawPrizeFamilyBound Mfam n Lfam K) ↔
          (∃ K, 0 ≤ K ∧ ShawValueCapstone.shawValueFamilyBound Mfam n Lfam K)) ∧
        (∀ nref : ℝ, max N₀ 1 ≤ nref → nref * L ≤ q →
          (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical → m'.RespectsProvenScale q C δ nref) →
          ∀ M K : ℝ, NoFifthDoorTetrachotomy.prizeScale nref ≤ M →
            (1 ≤ floorPrizeRatio M nref) ∧
              (M ≤ K * NoFifthDoorTetrachotomy.prizeScale nref ↔ floorPrizeRatio M nref ≤ K) ∧
              (∀ m : NoFifthDoorTetrachotomy.Mechanism,
                m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
                m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation)) := by
  obtain ⟨Nred, hred, _hdoor⟩ :=
    prize_iff_shawBounded_nonneg_and_discharged_doorIV_only
      (q := q) hs hLnn hL hC hδ
  obtain ⟨Nfloor, hfloorPack⟩ :=
    ceilingRespecting_classical_excluded_floorPrizeRatio hLnn hL hC hδ
  refine ⟨max Nred Nfloor, hred, ?_⟩
  intro nref hn hq hrespAll M K hfloor
  have hnfloor : max Nfloor 1 ≤ nref := by
    refine max_le ?_ ?_
    · exact le_trans (le_trans (le_max_right Nred Nfloor) (le_max_left _ _)) hn
    · exact le_trans (le_max_right _ _) hn
  exact hfloorPack nref hnfloor hq hrespAll M K hfloor

/-! ## Sharpening the floor-unit corridor lower end from `1` to `(5/4)^{1/4}`

The corridor `floorUnit_corridor_one_sqrtL_doorIV_only` pins the floor-normalized ratio `M/√n` in
`[1, √L]`, wiring the *lower* end to the bare Plancherel/Parseval floor `√n ≤ M` (ratio `≥ 1`).  But
the repository proves a *strictly stronger* unconditional period floor, the super-diagonal
Wick-permutation bound `(5/4)^{1/4}·√n ≤ M` (`ShawValueCapstone.superDiagonalFloorConst`, the constant
from `BGKFloorSharp.worstPeriod_ge_const_sqrt`, `≈ 1.0574 > 1`).  The Shaw-value (`√(n·L)`-unit) bracket
already absorbed this sharpening (`ShawValueCapstone.shawValue_ge_superDiagonal_floor`), but the
*floor-unit* (`√n`-unit) corridor in this synthesis still rested on the bare `1`.  These rungs lift the
floor-unit corridor lower end to the proven super-diagonal constant, so the `√n`-unit corridor sharpens
from `[1, √L]` to `[(5/4)^{1/4}, √L]`.  This is pure normalization chaining of two proven facts; it
adds no cancellation/anti-concentration estimate and leaves the open door-(iv) problem exactly as open
(the upper end `√L` — the thinness factor only door (iv) can shave — is unchanged). -/

/-- **Super-diagonal floor lands the floor-normalized ratio at `(5/4)^{1/4}`.**  Whenever the proven
unconditional super-diagonal period floor `(5/4)^{1/4}·√n ≤ M` holds, the floor-normalized prize ratio
`M/√n` is at least `(5/4)^{1/4} ≈ 1.0574`, strictly above the bare Plancherel value `1`.  This is the
`√n`-unit (floor-unit) analogue of `ShawValueCapstone.shawValue_ge_superDiagonal_floor`. -/
theorem superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor
    {M n : ℝ} (hn : 0 < n)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M) :
    ShawValueCapstone.superDiagonalFloorConst ≤ floorPrizeRatio M n := by
  unfold floorPrizeRatio NoFifthDoorTetrachotomy.prizeScale
  rw [le_div_iff₀ (Real.sqrt_pos.2 hn)]
  exact hfloor

/-- **The sharpened floor-unit lower end strictly exceeds the bare Plancherel `1`.**  Records that the
super-diagonal floor constant `(5/4)^{1/4}` genuinely raises the corridor floor above the bare value
`1`, so the sharpening is non-vacuous. -/
theorem one_lt_superDiagonalFloorConst_floorUnit :
    (1 : ℝ) < ShawValueCapstone.superDiagonalFloorConst :=
  ShawValueCapstone.superDiagonalFloorConst_gt_one

/-- **Any floor-scale prize constant must clear the super-diagonal floor `(5/4)^{1/4}`.**  Sharpens
`one_le_prizeFloorConstant_of_plancherel_floor` (which gives only `1 ≤ K`): if the proven super-diagonal
floor `(5/4)^{1/4}·√n ≤ M` holds and `M ≤ K·√n`, then necessarily `(5/4)^{1/4} ≤ K`.  So a
floor-normalized certificate cannot have a constant below `(5/4)^{1/4} ≈ 1.0574` — strictly above the
bare Plancherel `1`.  This is the floor-unit lower bound on the *achievable prize constant itself*
(not just the ratio), the citable strengthening of the constant-baseline constraint. -/
theorem superDiagonalFloorConst_le_prizeFloorConstant_of_superDiagonal_floor
    {M n K : ℝ} (hn : 0 < n)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M)
    (hbound : M ≤ K * NoFifthDoorTetrachotomy.prizeScale n) :
    ShawValueCapstone.superDiagonalFloorConst ≤ K := by
  have hratio_floor : ShawValueCapstone.superDiagonalFloorConst ≤ floorPrizeRatio M n :=
    superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor hn hfloor
  have hratio_bound : floorPrizeRatio M n ≤ K :=
    (prizeFloorBound_iff_floorPrizeRatio_le hn).mp hbound
  exact le_trans hratio_floor hratio_bound

/-- **Sharpened floor-unit corridor `[(5/4)^{1/4}, √L]`, door-(iv)-only.**  Given the proven
super-diagonal period floor `(5/4)^{1/4}·√n ≤ M`, a classical-door BGK ceiling `M ≤ √(n·L)`, and the
classical-overshoot refutations, the floor-normalized worst-frequency ratio `M/√n` lives in the
corridor `[(5/4)^{1/4}, √L]` — strictly narrower at the bottom than the bare `[1, √L]` of
`floorUnit_corridor_one_sqrtL_doorIV_only`, since `(5/4)^{1/4} > 1`.  As before, the prize is the demand
to collapse the corridor to `[(5/4)^{1/4}, C]` for an absolute `C`, and only door (iv) can shave the
`√L`.  This is the floor-unit (`√n`-unit) sibling of the sharpened Shaw bracket
`[(5/4)^{1/4}/√L, √(n/L)]`. -/
theorem sharpenedFloorUnit_corridor_doorIV_only
    {M nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt nref ≤ M)
    (hceil : M ≤ NoFifthDoorTetrachotomy.bgkScale nref Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (ShawValueCapstone.superDiagonalFloorConst ≤ floorPrizeRatio M nref
        ∧ floorPrizeRatio M nref ≤ Real.sqrt Lref)
      ∧ (1 < ShawValueCapstone.superDiagonalFloorConst)
      ∧ (∀ m : NoFifthDoorTetrachotomy.Mechanism,
          m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
          m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor hnref hfloor
  · exact floorPrizeRatio_le_sqrtL_of_bgk_ceiling hnref hceil
  · exact ShawValueCapstone.superDiagonalFloorConst_gt_one
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **Sharpened floor-normalized synthesis bundle (single citable statement).**  The unified
`floorRatio_bracketed_prize_iff_and_doorIV_only` with its lower end lifted from the bare Plancherel `1`
to the proven super-diagonal constant `c₀ = (5/4)^{1/4}`.  Given the proven super-diagonal period floor
`c₀·√n ≤ M` and the classical-overshoot refutations, at the reference instance:
(1) the floor-normalized ratio satisfies `c₀ ≤ M/√n` (sharper than the bare `1`);
(2) the floor-scale prize bound `M ≤ C·√n` is exactly `M/√n ≤ C`; and
(3) every mechanism reaching the prize floor is door-(iv) `newEvaluation`.
This is the `√n`-unit sibling of the sharpened Shaw bracket, packaged as one statement a citation can
point at for "the prize must clear `c₀` in `√n` units and only door (iv) can cap it."  Bundles
`superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor`,
`prizeFloorBound_iff_floorPrizeRatio_le`, and `prizeCertifying_subset_doorIV`. -/
theorem sharpenedFloorRatio_bracketed_prize_iff_and_doorIV_only
    {M nref Lref C : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt nref ≤ M)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (ShawValueCapstone.superDiagonalFloorConst ≤ floorPrizeRatio M nref) ∧
      (M ≤ C * NoFifthDoorTetrachotomy.prizeScale nref ↔ floorPrizeRatio M nref ≤ C) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_, ?_⟩
  · exact superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor hnref hfloor
  · exact prizeFloorBound_iff_floorPrizeRatio_le hnref
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **Unconditional outer ceiling `M/√n ≤ √n` from the trivial `M ≤ n` bound.**  The triangle
inequality gives `M = max_b |Σ_{x∈μ_n} e_p(bx)| ≤ |μ_n| = n` with NO door / BGK / completion
hypothesis (it is the bare cardinality ceiling on a sum of `n` unit phases).  In `√n` units this is
`floorPrizeRatio M n = M/√n ≤ √n`, the *unconditional* upper bracket — the highest the floor-ratio
can sit before any cancellation argument is invoked.  Complementary to
`floorPrizeRatio_le_sqrtL_of_bgk_ceiling`, which only gives the sharper `√L` end *under* the
classical-door BGK ceiling `M ≤ √(n·L)`. -/
theorem floorPrizeRatio_le_sqrtN_of_trivial_ceiling {M n : ℝ} (hn : 0 < n)
    (hceil : M ≤ n) :
    floorPrizeRatio M n ≤ Real.sqrt n := by
  unfold floorPrizeRatio NoFifthDoorTetrachotomy.prizeScale
  rw [div_le_iff₀ (Real.sqrt_pos.2 hn)]
  calc M ≤ n := hceil
    _ = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (le_of_lt hn)).symm

/-- **Unconditional floor-unit bracket `[c₀, √n]`, no door assumption.**  Combining the proven
super-diagonal period floor `c₀·√n ≤ M` (`c₀ = (5/4)^{1/4}`, the sharp Wick-permutation 4th-moment
constant) with the trivial cardinality ceiling `M ≤ n`, the floor-normalized worst-frequency ratio
`M/√n` lives in the corridor `[c₀, √n]` **with no BGK / completion / door hypothesis whatsoever**.
This is the bedrock unconditional bracket: it isolates the entire prize content as the demand to
collapse the *unconditional* `√n` ceiling all the way down to an absolute constant `C`.  The
conditional Shaw/BGK ceiling `√L` (`< √n` for `1 < L < n`) sits strictly inside this bracket; the
gap `[√L, √n]` is exactly what a classical door buys for free, and the residual `[C, √L]` is the
door-(iv)-only frontier.  Pairs with `floorUnit_corridor_one_sqrtL_doorIV_only` (the conditional
`√L`-end refinement) as its unconditional outer envelope. -/
theorem floorUnit_unconditional_bracket {M n : ℝ} (hn : 0 < n)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M)
    (hceil : M ≤ n) :
    ShawValueCapstone.superDiagonalFloorConst ≤ floorPrizeRatio M n ∧
      floorPrizeRatio M n ≤ Real.sqrt n :=
  ⟨superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor hn hfloor,
    floorPrizeRatio_le_sqrtN_of_trivial_ceiling hn hceil⟩

/-- **The conditional `√L` ceiling sits strictly below the unconditional `√n` ceiling.**  In the
prize regime `L = log(p/n) ≪ n`, in particular `1 < L < n`, the BGK/Shaw thinness factor satisfies
`√L < √n`.  This is the kernel-checked content of "a classical door strictly improves the
unconditional cardinality ceiling but cannot reach an absolute constant": the door buys the gap
`[√L, √n)` for free, yet `√L → ∞` as `n → ∞` (the open `√log` overshoot), so no classical door caps
the floor-ratio at an absolute `C`. -/
theorem sqrtL_lt_sqrtN_of_lt {L n : ℝ} (hL : 1 < L) (hLn : L < n) :
    Real.sqrt L < Real.sqrt n :=
  Real.sqrt_lt_sqrt (le_of_lt (lt_trans one_pos hL)) hLn

/-- **Strict floor-unit corridor nesting `[c₀, √L] ⊊ [c₀, √n]` in the prize regime.**  Combines the
proven super-diagonal floor lower end `c₀ ≤ M/√n` (shared by both corridors) with the strict ceiling
separation `√L < √n` (`1 < L < n`): the conditional Shaw/BGK floor-unit corridor `[c₀, √L]` is
contained in, and has a strictly lower ceiling than, the unconditional bracket `[c₀, √n]`.  This locks
the decomposition of the prize gap: the classical door shaves `[√L, √n]` off the ceiling for free,
leaving the residual `[c₀, √L]` (still unbounded as `n → ∞`) as the door-(iv)-only frontier. -/
theorem floorUnit_corridor_strict_nesting {M n L : ℝ} (hn : 0 < n)
    (hL : 1 < L) (hLn : L < n)
    (hfloor : ShawValueCapstone.superDiagonalFloorConst * Real.sqrt n ≤ M)
    (hceilL : M ≤ NoFifthDoorTetrachotomy.bgkScale n L) :
    ShawValueCapstone.superDiagonalFloorConst ≤ floorPrizeRatio M n ∧
      floorPrizeRatio M n ≤ Real.sqrt L ∧
      Real.sqrt L < Real.sqrt n :=
  ⟨superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor hn hfloor,
    floorPrizeRatio_le_sqrtL_of_bgk_ceiling hn hceilL,
    sqrtL_lt_sqrtN_of_lt hL hLn⟩

end ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.one_le_prizeFloorConstant_of_plancherel_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.superDiagonalFloorConst_le_floorPrizeRatio_of_superDiagonal_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.sharpenedFloorUnit_corridor_doorIV_only
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.superDiagonalFloorConst_le_prizeFloorConstant_of_superDiagonal_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.sharpenedFloorRatio_bracketed_prize_iff_and_doorIV_only
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio_le_sqrtN_of_trivial_ceiling
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.sqrtL_lt_sqrtN_of_lt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorUnit_corridor_strict_nesting
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.floorUnit_unconditional_bracket
