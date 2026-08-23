/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassEquivalence

/-!
# Door-(iv): the prize-family bound is exactly `BddAbove` of the normalized ratios (#444)

## Context

`_DoorIVHalfMassEquivalence` packages the honest door-(iv) Big-O reduction `prize ⇔ H(n)=O(scale)`
using a bespoke existential predicate
`∃ C, normalizedPrizeFamilyBound M scale C := ∃ C, ∀ i, M i / scale i ≤ C`,
i.e. "the normalized prize ratios `M i / scale i` are bounded above by some constant".

That existential is, definitionally, Mathlib's canonical `BddAbove (Set.range fun i => M i / scale i)`.
The two worst-b probes logged in `DISPROOF_LOG.md`
(`[doorIV-worstb-coherence-constant-prime-stable]`, `[doorIV-worstb-coherence-constant-n-drift-saturates]`)
measure *exactly* this object: whether the family `C(n) = ρ²(b*)·n/log(p/n)` of normalized ratios is
bounded above (the prize) or drifts to `∞` (the wall). This file welds the bespoke door-(iv) predicate
to the standard library boundedness predicate, so the door-(iv) Big-O capstone becomes interoperable
with Mathlib's `BddAbove`/`Set.range` API (and with anything stated in those terms, e.g. the empirical
`BddAbove` question the probes target).

## What this file proves (axiom-clean, no new estimate)

- `bddAbove_range_iff_exists_normalizedPrizeFamilyBound`: the `BddAbove (range (M/scale))` form is
  equivalent to the bespoke `∃ C, normalizedPrizeFamilyBound M scale C`.
- `bddAbove_range_iff_exists_normalizedHalfMassFamilyBound`: same for the half-mass ratios.
- `bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound`: with positive scales, `BddAbove` of the
  normalized prize ratios is equivalent to the RAW prize Big-O bound `∃ C, M ≤ C·scale`.
- `bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass`: the door-(iv) reduction itself,
  stated purely in `BddAbove` terms (the directly citable form: `prize ⇔ Sh_H(n)=O(1)` as boundedness
  of the half-mass Shaw value).

This is a pure restatement bridge — it proves NO arithmetic inequality, no cancellation, no CORE bound.
It only identifies the existing door-(iv) predicate with the standard `BddAbove`, which is the object the
worst-b probes empirically interrogate.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove

open ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence

/-- A family of reals is bounded above (`BddAbove` of its range) iff there is a uniform upper bound
on every member. This is the elementary unfolding of `BddAbove (Set.range f)` for `f : ι → ℝ`. -/
theorem bddAbove_range_iff_exists_forall_le {ι : Type*} (f : ι → ℝ) :
    BddAbove (Set.range f) ↔ ∃ C, ∀ i, f i ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    exact hC ⟨i, rfl⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro x ⟨i, rfl⟩
    exact hC i

/-- A bounded real family always has a **nonnegative** uniform upper constant.  This is the
`O(1)` sign-normalization used in the Shaw-value prose: replacing any upper bound `C` by
`max C 0` loses no information. -/
theorem bddAbove_range_iff_exists_nonneg_forall_le {ι : Type*} (f : ι → ℝ) :
    BddAbove (Set.range f) ↔ ∃ C, 0 ≤ C ∧ ∀ i, f i ≤ C := by
  rw [bddAbove_range_iff_exists_forall_le]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, le_max_right C 0, fun i => ?_⟩
    exact le_trans (hC i) (le_max_left C 0)
  · rintro ⟨C, _hCnonneg, hC⟩
    exact ⟨C, hC⟩

/-- The bespoke normalized prize-family predicate is exactly `BddAbove` of the normalized prize
ratios. -/
theorem bddAbove_range_iff_exists_normalizedPrizeFamilyBound {ι : Type*} (M scale : ι → ℝ) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, normalizedPrizeFamilyBound M scale C := by
  rw [bddAbove_range_iff_exists_forall_le]
  rfl

/-- Nonnegative-constant `BddAbove` form for normalized prize ratios.  This is the exact
standard-library statement of “the normalized prize/Shaw ratios are `O(1)`” with the conventional
constant sign `0 ≤ C`. -/
theorem bddAbove_range_iff_exists_nonneg_normalizedPrizeFamilyBound {ι : Type*}
    (M scale : ι → ℝ) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧ normalizedPrizeFamilyBound M scale C := by
  rw [bddAbove_range_iff_exists_nonneg_forall_le]
  rfl

/-- The bespoke normalized half-mass-family predicate is exactly `BddAbove` of the normalized
half-mass ratios. -/
theorem bddAbove_range_iff_exists_normalizedHalfMassFamilyBound {ι : Type*} (H scale : ι → ℝ) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, normalizedHalfMassFamilyBound H scale C := by
  rw [bddAbove_range_iff_exists_forall_le]
  rfl

/-- Nonnegative-constant `BddAbove` form for normalized half-mass Shaw ratios.  Boundedness of the
half-mass door-(iv) target is unchanged by requiring the witnessing `O(1)` constant to be
nonnegative. -/
theorem bddAbove_range_iff_exists_nonneg_normalizedHalfMassFamilyBound {ι : Type*}
    (H scale : ι → ℝ) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧ normalizedHalfMassFamilyBound H scale C := by
  rw [bddAbove_range_iff_exists_nonneg_forall_le]
  rfl

/-- With positive scales, `BddAbove` of the normalized prize ratios is equivalent to the RAW prize
Big-O statement `∃ C, ∀ i, M i ≤ C · scale i`. This is the standard-library form of the door-(iv)
prize predicate the worst-b probes measure. -/
theorem bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, prizeFamilyBound M scale C := by
  rw [bddAbove_range_iff_exists_normalizedPrizeFamilyBound]
  exact (exists_prizeFamilyBound_iff_exists_normalizedPrizeFamilyBound
    (M := M) (scale := scale) hscale).symm

/-- With positive scales, `BddAbove` of the normalized prize ratios is equivalent to the RAW
prize Big-O statement with a **nonnegative** absolute constant. This is the sign-normalized `O(1)`
form that downstream statements usually cite. -/
theorem bddAbove_range_normalizedPrize_iff_exists_nonneg_prizeFamilyBound {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧ prizeFamilyBound M scale C := by
  rw [bddAbove_range_iff_exists_nonneg_normalizedPrizeFamilyBound]
  constructor
  · rintro ⟨C, hCnonneg, hC⟩
    exact ⟨C, hCnonneg, (prizeFamilyBound_iff_normalizedPrizeFamilyBound hscale).2 hC⟩
  · rintro ⟨C, hCnonneg, hC⟩
    exact ⟨C, hCnonneg, (prizeFamilyBound_iff_normalizedPrizeFamilyBound hscale).1 hC⟩

/-- With positive scales, `BddAbove` of the normalized half-mass ratios is equivalent to the RAW
half-mass Big-O statement with a **nonnegative** absolute constant. -/
theorem bddAbove_range_normalizedHalfMass_iff_exists_nonneg_halfMassFamilyBound {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧ halfMassFamilyBound H scale C := by
  rw [bddAbove_range_iff_exists_nonneg_normalizedHalfMassFamilyBound]
  constructor
  · rintro ⟨C, hCnonneg, hC⟩
    exact ⟨C, hCnonneg, (halfMassFamilyBound_iff_normalizedHalfMassFamilyBound hscale).2 hC⟩
  · rintro ⟨C, hCnonneg, hC⟩
    exact ⟨C, hCnonneg, (halfMassFamilyBound_iff_normalizedHalfMassFamilyBound hscale).1 hC⟩

/-- **Door-(iv) reduction in `BddAbove` form.**  Under the family-wide half-mass comparison
(`M i ≤ H i` and `H i ≤ K · M i` with one `K ≥ 0`) and positive scales, the normalized prize ratios are
bounded above iff the normalized half-mass ratios are. This is the directly citable
`prize ⇔ Sh_H(n)=O(1)` stated entirely via Mathlib's `BddAbove`. -/
theorem bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      BddAbove (Set.range fun i => H i / scale i) := by
  rw [bddAbove_range_iff_exists_normalizedPrizeFamilyBound,
      bddAbove_range_iff_exists_normalizedHalfMassFamilyBound]
  exact exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    (M := M) (H := H) (scale := scale) hK hscale hMH hHM


/-- With positive scales, `BddAbove` of the normalized half-mass ratios is equivalent to the RAW
half-mass Big-O statement `∃ C, ∀ i, H i ≤ C · scale i`. This completes the standard-library
`BddAbove` bridge for the half-mass Shaw value, parallel to
`bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound`. -/
theorem bddAbove_range_normalizedHalfMass_iff_exists_halfMassFamilyBound {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, halfMassFamilyBound H scale C := by
  rw [bddAbove_range_iff_exists_normalizedHalfMassFamilyBound]
  exact (exists_halfMassFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    (H := H) (scale := scale) hscale).symm

/-- **Door-(iv) reduction, normalized-prize `BddAbove` versus raw half-mass Big-O.**  Under the
family-wide half-mass comparison and positive scales, bounded normalized prize ratios are equivalent
to a raw uniform half-mass bound. This is the `BddAbove` form of the mixed capstone with the half-mass
side left in the original unnormalized Big-O language. -/
theorem bddAbove_range_normalizedPrize_iff_exists_halfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, halfMassFamilyBound H scale C := by
  rw [bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
        hK hscale hMH hHM,
      bddAbove_range_normalizedHalfMass_iff_exists_halfMassFamilyBound (H := H) (scale := scale) hscale]

/-- **Door-(iv) reduction, normalized-half-mass `BddAbove` versus raw prize Big-O.**  Under the same
comparison hypotheses, bounded normalized half-mass ratios are equivalent to the raw uniform prize
bound. This is the opposite mixed `BddAbove`/raw face of the `prize ⇔ Sh_H(n)=O(1)` capstone. -/
theorem bddAbove_range_normalizedHalfMass_iff_exists_prizeFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, prizeFamilyBound M scale C := by
  rw [← bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
        hK hscale hMH hHM,
      bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound (M := M) (scale := scale) hscale]

/-- **Door-(iv) reduction, normalized-prize `BddAbove` versus raw half-mass Big-O with a
nonnegative constant.**  This is the sign-normalized mixed face of the Lane-2 capstone: bounded
normalized prize ratios are exactly the existence of a conventional `C ≥ 0` half-mass family bound. -/
theorem bddAbove_range_normalizedPrize_iff_exists_nonneg_halfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧ halfMassFamilyBound H scale C := by
  rw [bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
        hK hscale hMH hHM,
      bddAbove_range_normalizedHalfMass_iff_exists_nonneg_halfMassFamilyBound
        (H := H) (scale := scale) hscale]

/-- **Door-(iv) reduction, normalized-half-mass `BddAbove` versus raw prize Big-O with a
nonnegative constant.**  This is the symmetric sign-normalized mixed face: bounded normalized
half-mass Shaw ratios are exactly the existence of a conventional `C ≥ 0` prize-family bound. -/
theorem bddAbove_range_normalizedHalfMass_iff_exists_nonneg_prizeFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧ prizeFamilyBound M scale C := by
  rw [← bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
        hK hscale hMH hHM,
      bddAbove_range_normalizedPrize_iff_exists_nonneg_prizeFamilyBound
        (M := M) (scale := scale) hscale]

/-! ### The WALL (negative) characterization

The prize is the boundedness of the normalized ratios; the WALL is their UNBOUNDEDNESS. These lemmas
lock the dual side so the prize/wall dichotomy is a kernel-checked equivalence in both directions. The
`n`-drift probe (`DISPROOF_LOG [..-n-drift-saturates]`) interrogates exactly this failure side: whether
the family `C(n)=ρ²(b*)·n/log(p/n)` is unbounded (`∀ C, ∃ i, C(i) > C`). -/

/-- A family of reals is NOT bounded above iff for every candidate constant some member exceeds it.
This is the elementary unfolding of `¬ BddAbove (Set.range f)`. -/
theorem not_bddAbove_range_iff_forall_exists_lt {ι : Type*} (f : ι → ℝ) :
    ¬ BddAbove (Set.range f) ↔ ∀ C, ∃ i, C < f i := by
  rw [bddAbove_range_iff_exists_forall_le]
  push_neg
  rfl

/-- **The door-(iv) wall (no prize constant) characterization.**  With positive scales, the failure of
the prize Big-O bound (no absolute `C` with `M ≤ C·scale`) is exactly the unboundedness of the
normalized prize ratios: every candidate constant `C` is exceeded by `M i / scale i` for some index `i`.
This is the kernel-checked dual of `bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound`. -/
theorem not_exists_prizeFamilyBound_iff_forall_exists_lt_normalizedPrize {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, prizeFamilyBound M scale C) ↔ ∀ C, ∃ i, C < M i / scale i := by
  rw [← bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound (M := M) (scale := scale) hscale,
      not_bddAbove_range_iff_forall_exists_lt]


/-- **The half-mass wall characterization.**  With positive scales, failure of a raw uniform half-mass
Big-O bound is exactly unboundedness of the normalized half-mass ratios. This is the half-mass analogue
of `not_exists_prizeFamilyBound_iff_forall_exists_lt_normalizedPrize`. -/
theorem not_exists_halfMassFamilyBound_iff_forall_exists_lt_normalizedHalfMass {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, halfMassFamilyBound H scale C) ↔ ∀ C, ∃ i, C < H i / scale i := by
  rw [← bddAbove_range_normalizedHalfMass_iff_exists_halfMassFamilyBound (H := H) (scale := scale) hscale,
      not_bddAbove_range_iff_forall_exists_lt]

/-- **Sign-normalized prize wall characterization.**  With positive scales, failure of a raw uniform
prize Big-O bound with conventional `C ≥ 0` is exactly unboundedness of the normalized prize ratios.
This is the wall-facing dual of `bddAbove_range_normalizedPrize_iff_exists_nonneg_prizeFamilyBound`. -/
theorem not_exists_nonneg_prizeFamilyBound_iff_forall_exists_lt_normalizedPrize {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, 0 ≤ C ∧ prizeFamilyBound M scale C) ↔ ∀ C, ∃ i, C < M i / scale i := by
  rw [← bddAbove_range_normalizedPrize_iff_exists_nonneg_prizeFamilyBound
        (M := M) (scale := scale) hscale,
      not_bddAbove_range_iff_forall_exists_lt]

/-- **Sign-normalized half-mass wall characterization.**  With positive scales, failure of a raw
uniform half-mass Big-O bound with conventional `C ≥ 0` is exactly unboundedness of the normalized
half-mass Shaw ratios. -/
theorem not_exists_nonneg_halfMassFamilyBound_iff_forall_exists_lt_normalizedHalfMass {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, 0 ≤ C ∧ halfMassFamilyBound H scale C) ↔ ∀ C, ∃ i, C < H i / scale i := by
  rw [← bddAbove_range_normalizedHalfMass_iff_exists_nonneg_halfMassFamilyBound
        (H := H) (scale := scale) hscale,
      not_bddAbove_range_iff_forall_exists_lt]

/-- **Cross wall form, raw prize failure versus normalized half-mass unboundedness.**  Under the
family-wide half-mass comparison, failing the raw prize Big-O bound is equivalent to the half-mass
Shaw ratios exceeding every constant. -/
theorem not_exists_prizeFamilyBound_iff_forall_exists_lt_normalizedHalfMass {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ ∃ C, prizeFamilyBound M scale C) ↔ ∀ C, ∃ i, C < H i / scale i := by
  rw [← bddAbove_range_normalizedHalfMass_iff_exists_prizeFamilyBound
        hK hscale hMH hHM,
      not_bddAbove_range_iff_forall_exists_lt]

/-- **Cross wall form, raw half-mass failure versus normalized prize unboundedness.**  Under the same
comparison hypotheses, failing the raw half-mass Big-O bound is equivalent to the normalized prize
ratios exceeding every constant. -/
theorem not_exists_halfMassFamilyBound_iff_forall_exists_lt_normalizedPrize {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ ∃ C, halfMassFamilyBound H scale C) ↔ ∀ C, ∃ i, C < M i / scale i := by
  rw [← bddAbove_range_normalizedPrize_iff_exists_halfMassFamilyBound
        hK hscale hMH hHM,
      not_bddAbove_range_iff_forall_exists_lt]

/-- **Door-(iv) wall reduction in `BddAbove` form.** Under the family-wide half-mass
comparison and positive scales, unboundedness of the normalized prize ratios is equivalent to
unboundedness of the normalized half-mass Shaw ratios.  This is the direct `BddAbove` negation of
`bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass`, useful when the empirical
object is stated as a wall (`¬ BddAbove`) rather than as an explicit `∀ C, ∃ i, C < ...` drift. -/
theorem not_bddAbove_range_normalizedPrize_iff_not_bddAbove_range_normalizedHalfMass {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => M i / scale i)) ↔
      ¬ BddAbove (Set.range fun i => H i / scale i) := by
  exact not_congr (bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
    hK hscale hMH hHM)

/-- **Door-(iv) half-mass wall reduction in `BddAbove` form.** This is the symmetric orientation of
`not_bddAbove_range_normalizedPrize_iff_not_bddAbove_range_normalizedHalfMass`: failure of boundedness
for the normalized half-mass Shaw ratios is exactly failure of boundedness for the normalized prize
ratios. -/
theorem not_bddAbove_range_normalizedHalfMass_iff_not_bddAbove_range_normalizedPrize {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => H i / scale i)) ↔
      ¬ BddAbove (Set.range fun i => M i / scale i) := by
  exact (not_bddAbove_range_normalizedPrize_iff_not_bddAbove_range_normalizedHalfMass
    hK hscale hMH hHM).symm

/-- **Cross drift form, normalized-prize wall versus half-mass drift.** Under the family-wide
half-mass comparison, unbounded normalized prize ratios are equivalent to the normalized half-mass
Shaw ratios exceeding every candidate constant.  This is the direct standard-library wall statement
for probes that record `¬ BddAbove` on the prize side and explicit drift on the half-mass side. -/
theorem not_bddAbove_range_normalizedPrize_iff_forall_exists_lt_normalizedHalfMass {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => M i / scale i)) ↔
      ∀ C, ∃ i, C < H i / scale i := by
  rw [not_bddAbove_range_normalizedPrize_iff_not_bddAbove_range_normalizedHalfMass
        hK hscale hMH hHM,
      not_bddAbove_range_iff_forall_exists_lt]

/-- **Cross drift form, normalized-half-mass wall versus prize drift.** This is the symmetric direct
standard-library wall statement: unbounded normalized half-mass Shaw ratios are equivalent to the
normalized prize ratios exceeding every constant. -/
theorem not_bddAbove_range_normalizedHalfMass_iff_forall_exists_lt_normalizedPrize {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => H i / scale i)) ↔
      ∀ C, ∃ i, C < M i / scale i := by
  rw [not_bddAbove_range_normalizedHalfMass_iff_not_bddAbove_range_normalizedPrize
        hK hscale hMH hHM,
      not_bddAbove_range_iff_forall_exists_lt]

/-- **The door-(iv) prize/wall dichotomy in `BddAbove` form.**  Under the family-wide half-mass
comparison and positive scales, the prize-side (normalized prize ratios bounded above) and the
wall-side (normalized half-mass ratios unbounded) are exact negations of each other across the two
objects: the prize holds for `M` iff the half-mass ratios are NOT unbounded. This packages the full
two-sided `prize ⇔ Sh_H(n)=O(1)` / `wall ⇔ Sh_H(n)→∞` dichotomy as one kernel-checked statement. -/
theorem bddAbove_range_normalizedPrize_iff_not_forall_exists_lt_normalizedHalfMass {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ¬ ∀ C, ∃ i, C < H i / scale i := by
  rw [bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
        hK hscale hMH hHM,
      ← not_bddAbove_range_iff_forall_exists_lt (fun i => H i / scale i),
      not_not]

/-- **The symmetric door-(iv) half-mass/wall dichotomy in `BddAbove` form.**  Under the same
comparison hypotheses, boundedness of the normalized half-mass Shaw ratios is equivalent to the
normalized prize ratios *not* exceeding every constant.  This is the missing symmetric companion to
`bddAbove_range_normalizedPrize_iff_not_forall_exists_lt_normalizedHalfMass`, so the positive/wall
BddAbove API is closed on both sides of the half-mass reduction. -/
theorem bddAbove_range_normalizedHalfMass_iff_not_forall_exists_lt_normalizedPrize {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ¬ ∀ C, ∃ i, C < M i / scale i := by
  rw [← bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
        hK hscale hMH hHM,
      ← not_bddAbove_range_iff_forall_exists_lt (fun i => M i / scale i),
      not_not]

end ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_forall_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_nonneg_forall_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_nonneg_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_nonneg_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_nonneg_prizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_halfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_nonneg_halfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_halfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_prizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_nonneg_halfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_nonneg_prizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_iff_forall_exists_lt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_prizeFamilyBound_iff_forall_exists_lt_normalizedPrize
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_halfMassFamilyBound_iff_forall_exists_lt_normalizedHalfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_nonneg_prizeFamilyBound_iff_forall_exists_lt_normalizedPrize
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_nonneg_halfMassFamilyBound_iff_forall_exists_lt_normalizedHalfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_prizeFamilyBound_iff_forall_exists_lt_normalizedHalfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_halfMassFamilyBound_iff_forall_exists_lt_normalizedPrize
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedPrize_iff_not_bddAbove_range_normalizedHalfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedHalfMass_iff_not_bddAbove_range_normalizedPrize
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedPrize_iff_forall_exists_lt_normalizedHalfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedHalfMass_iff_forall_exists_lt_normalizedPrize
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_not_forall_exists_lt_normalizedHalfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_not_forall_exists_lt_normalizedPrize
