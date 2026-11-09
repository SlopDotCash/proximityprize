/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shaw-value capstone rungs for the proximity-prize normalization (#444)

Door (iv) has localized the remaining analytic object to the worst-frequency monomial-sum
coherence.  This file packages the harmless, citable normalization around that object:

* `prizeScale n L = sqrt (n * L)` is the native square-root target scale.
* `shawValue M n L = M / prizeScale n L` is the normalized Shaw value.
* `prizeBound_iff_shawValue_le` states the exact arithmetic equivalence, under a positive scale:
  bounding the raw worst-frequency value `M` by `C * sqrt(n L)` is the same as bounding the
  normalized Shaw value by `C`.
* `shawValue_floor_of_plancherel_floor` and `shawValue_le_of_trivial_ceiling` record the two easy
  ends of the chain: a Plancherel/RMS floor passes to the normalized value, and the trivial ceiling
  passes to the normalized value.

Scope: this is Lane-2 infrastructure only.  It does **not** prove the prize inequality or any new
anti-concentration for the monomial phase set; it makes the “prize ⇔ bounded Shaw value” arithmetic
rung explicit and axiom-clean so future door-(iv) work can cite the normalized target without
re-proving division-by-scale bookkeeping.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- The square-root target scale in the prize normalization.  In applications `n` is the subgroup
size and `L` is the logarithmic thinness parameter such as `log (p / n)`. -/
noncomputable def prizeScale (n L : ℝ) : ℝ :=
  Real.sqrt (n * L)

/-- The normalized Shaw value: raw worst-frequency size divided by the prize scale. -/
noncomputable def shawValue (M n L : ℝ) : ℝ :=
  M / prizeScale n L

/-- Positivity of the prize scale from positive subgroup size and positive logarithmic thinness. -/
theorem prizeScale_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    0 < prizeScale n L := by
  unfold prizeScale
  exact Real.sqrt_pos.2 (mul_pos hn hL)

/-- **Capstone normalization equivalence.**  Once the target scale is positive, the raw prize-shaped
bound `M ≤ C * sqrt(n L)` is exactly the statement that the Shaw value is at most `C`.

This is the formal Lane-2 rung behind the prose “prize ⇔ bounded Shaw value”: all hard content is in
proving a uniform bound for the normalized object; this theorem only removes the arithmetic wrapper. -/
theorem prizeBound_iff_shawValue_le {M C n L : ℝ} (hs : 0 < prizeScale n L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C := by
  constructor
  · intro h
    unfold shawValue
    have hdiv : M / prizeScale n L ≤ (C * prizeScale n L) / prizeScale n L :=
      div_le_div_of_nonneg_right h (le_of_lt hs)
    simpa [mul_comm, mul_left_comm, mul_assoc, ne_of_gt hs] using hdiv
  · intro h
    unfold shawValue at h
    calc
      M = (M / prizeScale n L) * prizeScale n L := by
        field_simp [ne_of_gt hs]
      _ ≤ C * prizeScale n L := mul_le_mul_of_nonneg_right h (le_of_lt hs)

/-- The equivalence in expanded parameters: for `0 < n` and `0 < L`, raw prize boundedness by `C`
is exactly boundedness of the normalized Shaw value by `C`. -/
theorem prizeBound_iff_shawValue_le_of_pos {M C n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C :=
  prizeBound_iff_shawValue_le (prizeScale_pos hn hL)

/-- **Strict capstone normalization equivalence.**  Under positive target scale, a strict raw
prize-shaped bound `M < C * sqrt(n L)` is exactly a strict Shaw-value bound `Sh(M) < C`.

This is the strict-slack companion to `prizeBound_iff_shawValue_le`: any claimed positive margin
inside the Door-IV normalization survives division by the prize scale, and conversely.  No
cancellation estimate is hidden here; it is only reversible arithmetic bookkeeping. -/
theorem strictPrizeBound_iff_shawValue_lt {M C n L : ℝ} (hs : 0 < prizeScale n L) :
    M < C * prizeScale n L ↔ shawValue M n L < C := by
  constructor
  · intro h
    unfold shawValue
    have hdiv : M / prizeScale n L < (C * prizeScale n L) / prizeScale n L :=
      div_lt_div_of_pos_right h hs
    simpa [mul_comm, mul_left_comm, mul_assoc, ne_of_gt hs] using hdiv
  · intro h
    unfold shawValue at h
    have hmul : (M / prizeScale n L) * prizeScale n L < C * prizeScale n L :=
      mul_lt_mul_of_pos_right h hs
    calc
      M = (M / prizeScale n L) * prizeScale n L := by
        field_simp [ne_of_gt hs]
      _ < C * prizeScale n L := hmul

/-- Strict prize/Shaw equivalence in expanded positive parameters. -/
theorem strictPrizeBound_iff_shawValue_lt_of_pos {M C n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    M < C * prizeScale n L ↔ shawValue M n L < C :=
  strictPrizeBound_iff_shawValue_lt (prizeScale_pos hn hL)



/-! ## Uniform-family capstone: the arithmetic form of `prize ⇔ Sh(n)=O(1)` -/

/-- A raw prize-family bound by the same constant `C` across a parameter family.  The parameters may
encode fields, subgroup sizes, or admissible thin instances; this definition is intentionally only the
arithmetic wrapper. -/
def rawPrizeFamilyBound {ι : Type*} (M n L : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i ≤ C * prizeScale (n i) (L i)

/-- A uniform Shaw-value bound by the same constant `C` across a parameter family. -/
def shawValueFamilyBound {ι : Type*} (M n L : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, shawValue (M i) (n i) (L i) ≤ C

/-- **Uniform-family Lane-2 capstone.**  Under pointwise positivity of the prize scale, a uniform raw
prize-family bound by `C` is exactly a uniform Shaw-value bound by `C`.

This is the machine-checked arithmetic core of the prose reduction `prize ⇔ Sh(n)=O(1)`: after
normalization, proving the prize with an absolute constant is the same as proving that the normalized
Shaw values are bounded by that absolute constant.  No cancellation estimate is hidden here. -/
theorem rawPrizeFamilyBound_iff_shawValueFamilyBound {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    rawPrizeFamilyBound M n L C ↔ shawValueFamilyBound M n L C := by
  constructor
  · intro h i
    exact (prizeBound_iff_shawValue_le (hs i)).1 (h i)
  · intro h i
    exact (prizeBound_iff_shawValue_le (hs i)).2 (h i)

/-- Uniform-family capstone in pointwise-positive parameters.  In applications the hypotheses are
usually `0 < n i` and `0 < L i`; this wrapper exposes the same raw-prize/Shaw-value equivalence
without forcing downstream files to build the positive scale assumption by hand. -/
theorem rawPrizeFamilyBound_iff_shawValueFamilyBound_of_pos {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    rawPrizeFamilyBound M n L C ↔ shawValueFamilyBound M n L C :=
  rawPrizeFamilyBound_iff_shawValueFamilyBound (fun i => prizeScale_pos (hn i) (hL i))

/-- A strict raw prize-family bound by the same constant `C` across a parameter family. -/
def strictRawPrizeFamilyBound {ι : Type*} (M n L : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i < C * prizeScale (n i) (L i)

/-- A strict uniform Shaw-value bound by the same constant `C` across a parameter family. -/
def strictShawValueFamilyBound {ι : Type*} (M n L : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, shawValue (M i) (n i) (L i) < C

/-- **Uniform strict-family Lane-2 capstone.**  Under pointwise positivity of the prize scale, a
uniform strict raw prize-family bound by `C` is exactly a uniform strict Shaw-value bound by `C`.
This is the strict-margin version of `rawPrizeFamilyBound_iff_shawValueFamilyBound`. -/
theorem strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    strictRawPrizeFamilyBound M n L C ↔ strictShawValueFamilyBound M n L C := by
  constructor
  · intro h i
    exact (strictPrizeBound_iff_shawValue_lt (hs i)).1 (h i)
  · intro h i
    exact (strictPrizeBound_iff_shawValue_lt (hs i)).2 (h i)

/-- Uniform strict-family capstone in pointwise-positive parameters. -/
theorem strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_of_pos
    {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    strictRawPrizeFamilyBound M n L C ↔ strictShawValueFamilyBound M n L C :=
  strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound (fun i => prizeScale_pos (hn i) (hL i))

/-- Existential constant form of the uniform strict-family capstone: there is an absolute strict
raw prize constant iff there is an absolute strict normalized Shaw-value constant, with the same
witness.  This is the existential wrapper around `strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound`. -/
theorem exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, strictShawValueFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound hs).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound hs).2 hC⟩

/-- Existential strict-family capstone in pointwise-positive parameters. -/
theorem exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_of_pos
    {ι : Type*} {M n L : ι → ℝ} (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∃ C, strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, strictShawValueFamilyBound M n L C) :=
  exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound
    (fun i => prizeScale_pos (hn i) (hL i))

/-- Wall-facing strict existential capstone: failure of every absolute strict raw prize constant is
exactly failure of every absolute strict Shaw-value constant.  This is the strict-slack analogue of
`not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound`, useful when a Door-IV obstruction
is formulated as the impossibility of a uniform strict margin. -/
theorem not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    ¬ (∃ C, strictRawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, strictShawValueFamilyBound M n L C) :=
  not_congr (exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound hs)

/-- Wall-facing strict existential capstone in pointwise-positive parameters. -/
theorem not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_of_pos
    {ι : Type*} {M n L : ι → ℝ} (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    ¬ (∃ C, strictRawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, strictShawValueFamilyBound M n L C) :=
  not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound
    (fun i => prizeScale_pos (hn i) (hL i))

/-- Monotonicity of the strict raw family constant: increasing the absolute constant preserves a
strict raw prize family bound, because the prize scale is nonnegative pointwise. -/
theorem strictRawPrizeFamilyBound_mono_const {ι : Type*} {M n L : ι → ℝ} {C D : ℝ}
    (hs : ∀ i, 0 ≤ prizeScale (n i) (L i)) (hCD : C ≤ D)
    (hC : strictRawPrizeFamilyBound M n L C) :
    strictRawPrizeFamilyBound M n L D := by
  intro i
  exact lt_of_lt_of_le (hC i) (mul_le_mul_of_nonneg_right hCD (hs i))

/-- Monotonicity of the strict normalized Shaw-value constant. -/
theorem strictShawValueFamilyBound_mono_const {ι : Type*} {M n L : ι → ℝ} {C D : ℝ}
    (hCD : C ≤ D) (hC : strictShawValueFamilyBound M n L C) :
    strictShawValueFamilyBound M n L D := by
  intro i
  exact lt_of_lt_of_le (hC i) hCD

/-- Nonnegative-constant form of the strict Lane-2 capstone.  Under positive prize scale, existence
of an absolute strict raw prize constant is equivalent to existence of a nonnegative absolute strict
raw prize constant: replace any witness `C` by `max C 0`. -/
theorem exists_nonneg_strictRawPrizeFamilyBound_iff_exists_strictRawPrizeFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, 0 ≤ C ∧ strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, strictRawPrizeFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, _hCnonneg, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, le_max_right C 0, ?_⟩
    exact strictRawPrizeFamilyBound_mono_const (fun i => le_of_lt (hs i)) (le_max_left C 0) hC

/-- Nonnegative-constant form for strict Shaw values: any strict bounded family has a nonnegative
strict bounding constant, again by replacing `C` with `max C 0`. -/
theorem exists_nonneg_strictShawValueFamilyBound_iff_exists_strictShawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} :
    (∃ C, 0 ≤ C ∧ strictShawValueFamilyBound M n L C) ↔
      (∃ C, strictShawValueFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, _hCnonneg, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, le_max_right C 0, ?_⟩
    exact strictShawValueFamilyBound_mono_const (le_max_left C 0) hC

/-- **Nonnegative strict-uniform Lane-2 capstone.**  Under positive prize scale, a strict raw prize
family has a nonnegative absolute constant exactly when the strict normalized Shaw-value family has
one.  This is the sign-normalized strict-margin version of `prize ⇔ Sh(n)=O(1)`. -/
theorem exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, 0 ≤ C ∧ strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧ strictShawValueFamilyBound M n L C) := by
  rw [exists_nonneg_strictRawPrizeFamilyBound_iff_exists_strictRawPrizeFamilyBound hs,
    exists_nonneg_strictShawValueFamilyBound_iff_exists_strictShawValueFamilyBound,
    exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound hs]

/-- Wall-facing nonnegative strict capstone.  Failure of every nonnegative strict raw prize constant
is exactly failure of every nonnegative strict Shaw-value constant. -/
theorem not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    ¬ (∃ C, 0 ≤ C ∧ strictRawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧ strictShawValueFamilyBound M n L C) :=
  not_congr (exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound hs)

/-- Existential constant form of the uniform-family capstone: there is an absolute raw prize constant
iff there is an absolute normalized Shaw-value constant, with the same witness. -/
theorem exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, rawPrizeFamilyBound M n L C) ↔ (∃ C, shawValueFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (rawPrizeFamilyBound_iff_shawValueFamilyBound hs).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (rawPrizeFamilyBound_iff_shawValueFamilyBound hs).2 hC⟩

/-- Existential constant capstone in pointwise-positive parameters.  This is the most direct
`prize ⇔ Sh(n)=O(1)` wrapper for a family indexed by admissible thin instances: if every subgroup
size and logarithmic thinness parameter is positive, the existence of one absolute raw prize constant
is equivalent to the existence of one absolute Shaw-value constant. -/
theorem exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound_of_pos
    {ι : Type*} {M n L : ι → ℝ} (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∃ C, rawPrizeFamilyBound M n L C) ↔ (∃ C, shawValueFamilyBound M n L C) :=
  exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound (fun i => prizeScale_pos (hn i) (hL i))

/-- Wall-facing existential capstone: failure of every absolute raw prize constant is exactly failure
of every absolute Shaw-value constant.  This is the contrapositive citation form of
`exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound`; it is useful when a Door-IV probe proves
that no normalized constant can survive.  No cancellation estimate is hidden here. -/
theorem not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    ¬ (∃ C, rawPrizeFamilyBound M n L C) ↔ ¬ (∃ C, shawValueFamilyBound M n L C) :=
  not_congr (exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound hs)

/-- Wall-facing capstone in pointwise-positive parameters.  Under `0 < nᵢ` and `0 < Lᵢ`, the
absence of an absolute raw prize constant is exactly the absence of an absolute Shaw-value constant. -/
theorem not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound_of_pos
    {ι : Type*} {M n L : ι → ℝ} (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    ¬ (∃ C, rawPrizeFamilyBound M n L C) ↔ ¬ (∃ C, shawValueFamilyBound M n L C) :=
  not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound
    (fun i => prizeScale_pos (hn i) (hL i))

/-- Monotonicity of the raw family constant: increasing the absolute constant preserves a raw prize
family bound, because the prize scale is nonnegative pointwise. -/
theorem rawPrizeFamilyBound_mono_const {ι : Type*} {M n L : ι → ℝ} {C D : ℝ}
    (hs : ∀ i, 0 ≤ prizeScale (n i) (L i)) (hCD : C ≤ D)
    (hC : rawPrizeFamilyBound M n L C) :
    rawPrizeFamilyBound M n L D := by
  intro i
  exact le_trans (hC i) (mul_le_mul_of_nonneg_right hCD (hs i))

/-- Monotonicity of the normalized Shaw-value constant. -/
theorem shawValueFamilyBound_mono_const {ι : Type*} {M n L : ι → ℝ} {C D : ℝ}
    (hCD : C ≤ D) (hC : shawValueFamilyBound M n L C) :
    shawValueFamilyBound M n L D := by
  intro i
  exact le_trans (hC i) hCD

/-- Nonnegative-constant form of the Lane-2 capstone.  Under positive prize scale, existence of an
absolute raw prize constant is equivalent to existence of a nonnegative absolute raw prize constant:
replace any witness `C` by `max C 0`. -/
theorem exists_nonneg_rawPrizeFamilyBound_iff_exists_rawPrizeFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound M n L C) ↔ (∃ C, rawPrizeFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, _hCnonneg, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, le_max_right C 0, ?_⟩
    exact rawPrizeFamilyBound_mono_const (fun i => le_of_lt (hs i)) (le_max_left C 0) hC

/-- Nonnegative-constant form for Shaw values: any bounded family has a nonnegative bounding
constant, again by replacing `C` with `max C 0`. -/
theorem exists_nonneg_shawValueFamilyBound_iff_exists_shawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} :
    (∃ C, 0 ≤ C ∧ shawValueFamilyBound M n L C) ↔ (∃ C, shawValueFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, _hCnonneg, hC⟩
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, le_max_right C 0, ?_⟩
    exact shawValueFamilyBound_mono_const (le_max_left C 0) hC

/-- **Nonnegative-uniform Lane-2 capstone.**  The prose statement “prize iff `Sh(n)=O(1)`” usually
uses a nonnegative absolute constant.  Under positive prize scale, the raw family has such a
nonnegative constant exactly when the normalized Shaw-value family has such a nonnegative constant.
No cancellation estimate is hidden here; this is only the sign-normalized constant wrapper. -/
theorem exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧ shawValueFamilyBound M n L C) := by
  rw [exists_nonneg_rawPrizeFamilyBound_iff_exists_rawPrizeFamilyBound hs,
    exists_nonneg_shawValueFamilyBound_iff_exists_shawValueFamilyBound,
    exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound hs]

/-- Nonnegative-uniform Lane-2 capstone in pointwise-positive parameters.  This is the citable
absolute-constant version of `prize ⇔ Sh(n)=O(1)` with the sign convention `0 ≤ C`, specialized to
the usual hypotheses `0 < n_i` and `0 < L_i`. -/
theorem exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound_of_pos
    {ι : Type*} {M n L : ι → ℝ} (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧ shawValueFamilyBound M n L C) :=
  exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound
    (fun i => prizeScale_pos (hn i) (hL i))

/-- Wall-facing nonnegative-constant capstone.  The usual `O(1)` convention uses `0 ≤ C`; in that
sign-normalized form too, failure of every raw prize constant is exactly failure of every Shaw-value
constant. -/
theorem not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound
    {ι : Type*} {M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    ¬ (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧ shawValueFamilyBound M n L C) :=
  not_congr (exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs)

/-- Wall-facing nonnegative capstone in pointwise-positive parameters.  This is the citable
`no prize bound ⇔ no Sh(n)=O(1)` statement under the standard positivity hypotheses. -/
theorem not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_of_pos
    {ι : Type*} {M n L : ι → ℝ} (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    ¬ (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧ shawValueFamilyBound M n L C) :=
  not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound
    (fun i => prizeScale_pos (hn i) (hL i))

/-- Uniform raw comparison transfers to a uniform Shaw-value bound with the same comparison constant.
If `H i ≤ K * M i` throughout a family and `M` has Shaw-value bound `C`, then `H` has Shaw-value
bound `K*C`.  The analytic input is only the raw comparison; this theorem is normalization
bookkeeping. -/
theorem shawValueFamilyBound_of_rawComparison {ι : Type*} {M H n L : ι → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hHM : ∀ i, H i ≤ K * M i) (hM : shawValueFamilyBound M n L C) :
    shawValueFamilyBound H n L (K * C) := by
  intro i
  have h1 : shawValue (H i) (n i) (L i) ≤ K * shawValue (M i) (n i) (L i) := by
    unfold shawValue
    have hdiv : H i / prizeScale (n i) (L i) ≤ (K * M i) / prizeScale (n i) (L i) :=
      div_le_div_of_nonneg_right (hHM i) (le_of_lt (hs i))
    have hrewrite : (K * M i) / prizeScale (n i) (L i) = K * (M i / prizeScale (n i) (L i)) := by
      ring
    exact hrewrite ▸ hdiv
  have h2 : K * shawValue (M i) (n i) (L i) ≤ K * C :=
    mul_le_mul_of_nonneg_left (hM i) hK
  exact le_trans h1 h2

/-- Raw-prize comparison transfers a raw family bound with the same multiplicative constant.  This
is the unnormalized companion to `shawValueFamilyBound_of_rawComparison`: a pointwise comparison
`H ≤ K*M` turns a raw prize bound `M ≤ C*scale` into `H ≤ (K*C)*scale`. -/
theorem rawPrizeFamilyBound_of_rawComparison {ι : Type*} {M H n L : ι → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hHM : ∀ i, H i ≤ K * M i) (hM : rawPrizeFamilyBound M n L C) :
    rawPrizeFamilyBound H n L (K * C) := by
  intro i
  calc
    H i ≤ K * M i := hHM i
    _ ≤ K * (C * prizeScale (n i) (L i)) := mul_le_mul_of_nonneg_left (hM i) hK
    _ = (K * C) * prizeScale (n i) (L i) := by ring

/-- **Shaw-value sandwich equivalence.**  If two raw door-(iv) targets are uniformly sandwiched
`M ≤ H ≤ K*M` with one `K`, then boundedness of their Shaw values is equivalent, up to constants.
For the current campaign, instantiate `M` as the prize supremum and `H` as worst half-mass. -/
theorem exists_shawValueFamilyBound_iff_of_rawSandwich {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, shawValueFamilyBound M n L C) ↔ (∃ C, shawValueFamilyBound H n L C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨K * C, shawValueFamilyBound_of_rawComparison hK hs hHM hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    have h1 : shawValue (M i) (n i) (L i) ≤ shawValue (H i) (n i) (L i) := by
      unfold shawValue
      exact div_le_div_of_nonneg_right (hMH i) (le_of_lt (hs i))
    exact le_trans h1 (hC i)

/-- Nonnegative-constant version of the raw-sandwich equivalence.  The usual prize formulation uses
an absolute constant `C ≥ 0`; if `M ≤ H ≤ K*M` pointwise, the existence of such a nonnegative Shaw
bound is invariant when passing between the prize supremum `M` and the sandwiched door-(iv) target
`H`.  This is still only normalization and constant bookkeeping. -/
theorem exists_nonneg_shawValueFamilyBound_iff_of_rawSandwich
    {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, 0 ≤ C ∧ shawValueFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧ shawValueFamilyBound H n L C) := by
  rw [exists_nonneg_shawValueFamilyBound_iff_exists_shawValueFamilyBound,
    exists_nonneg_shawValueFamilyBound_iff_exists_shawValueFamilyBound]
  exact exists_shawValueFamilyBound_iff_of_rawSandwich hK hs hMH hHM

/-- Raw-prize, nonnegative-constant version of the sandwich capstone.  Under positive prize scale,
if a door-(iv) target `H` is uniformly sandwiched between the raw prize supremum `M` and `K*M`, then
having an absolute nonnegative raw prize constant for `M` is equivalent to having one for `H`.
This states the same reduction entirely on the unnormalized prize side, so downstream statements can
cite the raw target without reopening the Shaw-value wrapper. -/
theorem exists_nonneg_rawPrizeFamilyBound_iff_of_rawSandwich
    {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound H n L C) := by
  rw [exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs,
    exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs]
  exact exists_nonneg_shawValueFamilyBound_iff_of_rawSandwich hK hs hMH hHM

/-- Wall-facing Shaw-value sandwich equivalence.  Under the same raw sandwich `M ≤ H ≤ K*M`,
failure of every nonnegative uniform Shaw bound is invariant when passing between `M` and `H`.
This is the obstruction-facing companion to `exists_nonneg_shawValueFamilyBound_iff_of_rawSandwich`:
if the sandwiched half-mass target is unbounded in Shaw units, so is the prize supremum, and conversely. -/
theorem not_exists_nonneg_shawValueFamilyBound_iff_of_rawSandwich
    {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    ¬ (∃ C, 0 ≤ C ∧ shawValueFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧ shawValueFamilyBound H n L C) :=
  not_congr (exists_nonneg_shawValueFamilyBound_iff_of_rawSandwich hK hs hMH hHM)

/-- Wall-facing raw-prize sandwich equivalence.  Under the raw sandwich `M ≤ H ≤ K*M`, failure of
every nonnegative raw prize-family bound for `M` is exactly failure of every nonnegative raw bound
for the sandwiched target `H`.  This records the obstruction side of the half-mass/prize reduction
without changing the analytic burden. -/
theorem not_exists_nonneg_rawPrizeFamilyBound_iff_of_rawSandwich
    {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    ¬ (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧ rawPrizeFamilyBound H n L C) :=
  not_congr (exists_nonneg_rawPrizeFamilyBound_iff_of_rawSandwich hK hs hMH hHM)

/-- Exact lower-floor normalization.  Under positive prize scale, a raw lower certificate
`B ≤ M` is equivalent to the normalized lower certificate `B/scale ≤ Sh(M)`.  This is the
lower-bound companion to `prizeBound_iff_shawValue_le`; it is useful for keeping the Plancherel /
Johnson floor rung reversible without hiding any analytic input. -/
theorem rawLowerBound_iff_shawValue_floor {B M n L : ℝ} (hs : 0 < prizeScale n L) :
    B ≤ M ↔ B / prizeScale n L ≤ shawValue M n L := by
  constructor
  · intro h
    unfold shawValue
    exact div_le_div_of_nonneg_right h (le_of_lt hs)
  · intro h
    unfold shawValue at h
    have hsne : prizeScale n L ≠ 0 := ne_of_gt hs
    have hmul : (B / prizeScale n L) * prizeScale n L ≤
        (M / prizeScale n L) * prizeScale n L :=
      mul_le_mul_of_nonneg_right h (le_of_lt hs)
    calc
      B = (B / prizeScale n L) * prizeScale n L := by field_simp [hsne]
      _ ≤ (M / prizeScale n L) * prizeScale n L := hmul
      _ = M := by field_simp [hsne]

/-- Strict lower-floor normalization.  Under positive prize scale, a strict raw floor
`B < M` is equivalent to the normalized strict floor `B/scale < Sh(M)`.  This is the strict companion
to `rawLowerBound_iff_shawValue_floor`, used when a Door-IV obstruction is recorded as a positive
floor gap rather than a weak lower bound. -/
theorem rawStrictLowerBound_iff_shawValue_strict_floor {B M n L : ℝ}
    (hs : 0 < prizeScale n L) :
    B < M ↔ B / prizeScale n L < shawValue M n L := by
  constructor
  · intro h
    unfold shawValue
    exact div_lt_div_of_pos_right h hs
  · intro h
    unfold shawValue at h
    have hsne : prizeScale n L ≠ 0 := ne_of_gt hs
    have hmul : (B / prizeScale n L) * prizeScale n L <
        (M / prizeScale n L) * prizeScale n L :=
      mul_lt_mul_of_pos_right h hs
    calc
      B = (B / prizeScale n L) * prizeScale n L := by field_simp [hsne]
      _ < (M / prizeScale n L) * prizeScale n L := hmul
      _ = M := by field_simp [hsne]

/-- Uniform-family exact lower-floor normalization.  A pointwise raw floor `B_i ≤ M_i` is exactly
the corresponding pointwise normalized Shaw floor `B_i/scale_i ≤ Sh_i`.  This packages the reversible
floor side of the prize `↔` Shaw-value reduction for families. -/
theorem rawLowerBoundFamily_iff_shawValueFloorFamily {ι : Type*} {B M n L : ι → ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∀ i, B i ≤ M i) ↔
      (∀ i, B i / prizeScale (n i) (L i) ≤ shawValue (M i) (n i) (L i)) := by
  constructor
  · intro h i
    exact (rawLowerBound_iff_shawValue_floor (B := B i) (M := M i)
      (n := n i) (L := L i) (hs i)).1 (h i)
  · intro h i
    exact (rawLowerBound_iff_shawValue_floor (B := B i) (M := M i)
      (n := n i) (L := L i) (hs i)).2 (h i)

/-- Uniform-family strict lower-floor normalization.  Pointwise strict raw floors are equivalent to
pointwise strict Shaw-value floors after dividing by the positive prize scale. -/
theorem rawStrictLowerBoundFamily_iff_shawValueStrictFloorFamily {ι : Type*}
    {B M n L : ι → ℝ} (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∀ i, B i < M i) ↔
      (∀ i, B i / prizeScale (n i) (L i) < shawValue (M i) (n i) (L i)) := by
  constructor
  · intro h i
    exact (rawStrictLowerBound_iff_shawValue_strict_floor (B := B i) (M := M i)
      (n := n i) (L := L i) (hs i)).1 (h i)
  · intro h i
    exact (rawStrictLowerBound_iff_shawValue_strict_floor (B := B i) (M := M i)
      (n := n i) (L := L i) (hs i)).2 (h i)

/-- Pointwise-positive parameter wrapper for the uniform lower-floor normalization.  In the prize
regime the available hypotheses are normally `0 < n_i` and `0 < L_i`; this theorem exposes the
same reversible floor rung without forcing each downstream reduction to rebuild positivity of
`prizeScale`. -/
theorem rawLowerBoundFamily_iff_shawValueFloorFamily_of_pos {ι : Type*} {B M n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∀ i, B i ≤ M i) ↔
      (∀ i, B i / prizeScale (n i) (L i) ≤ shawValue (M i) (n i) (L i)) :=
  rawLowerBoundFamily_iff_shawValueFloorFamily (fun i => prizeScale_pos (hn i) (hL i))

/-- Pointwise-positive wrapper for uniform strict lower-floor normalization. -/
theorem rawStrictLowerBoundFamily_iff_shawValueStrictFloorFamily_of_pos {ι : Type*}
    {B M n L : ι → ℝ} (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∀ i, B i < M i) ↔
      (∀ i, B i / prizeScale (n i) (L i) < shawValue (M i) (n i) (L i)) :=
  rawStrictLowerBoundFamily_iff_shawValueStrictFloorFamily (fun i => prizeScale_pos (hn i) (hL i))

/-- A Plancherel/RMS floor `sqrt n ≤ M` becomes the corresponding normalized lower bound for the
Shaw value.  This records the easy Johnson-side floor in Shaw-value units. -/
theorem shawValue_floor_of_plancherel_floor {M n L : ℝ} (hs : 0 < prizeScale n L)
    (hfloor : Real.sqrt n ≤ M) :
    Real.sqrt n / prizeScale n L ≤ shawValue M n L := by
  exact (rawLowerBound_iff_shawValue_floor (B := Real.sqrt n) (M := M) (n := n) (L := L) hs).1
    hfloor

/-- The trivial ceiling `M ≤ n` becomes the corresponding normalized upper bound for the Shaw value.
This is the harmless top bracket `M ≤ n`, in Shaw-value units. -/
theorem shawValue_le_of_trivial_ceiling {M n L : ℝ} (hs : 0 < prizeScale n L) (hceil : M ≤ n) :
    shawValue M n L ≤ n / prizeScale n L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right hceil (le_of_lt hs)


/-- Raw comparison survives Shaw-value normalization with the same constant.  In particular, when
`M` is the prize supremum and `H` is the worst half-mass target, a pointwise comparison `H ≤ K·M`
becomes `Sh(H) ≤ K·Sh(M)` after dividing by the positive prize scale.  This is only normalization
bookkeeping; the analytic input remains the raw comparison itself. -/
theorem shawValue_le_mul_shawValue_of_le_mul {M H K n L : ℝ}
    (hs : 0 < prizeScale n L) (hHM : H ≤ K * M) :
    shawValue H n L ≤ K * shawValue M n L := by
  unfold shawValue
  have h1 : H / prizeScale n L ≤ (K * M) / prizeScale n L :=
    div_le_div_of_nonneg_right hHM (le_of_lt hs)
  have h2 : (K * M) / prizeScale n L = K * (M / prizeScale n L) := by ring
  exact h2 ▸ h1

/-- Pointwise comparison equivalence after Shaw-value normalization.  Because the prize scale is
positive, a raw door-(iv) comparison `H ≤ K*M` is exactly the same as the normalized comparison
`Sh(H) ≤ K*Sh(M)`.  This packages both directions so reductions can move between raw worst-period
targets and Shaw-value targets without reopening division-by-scale algebra. -/
theorem rawComparison_iff_shawValueComparison {M H K n L : ℝ}
    (hs : 0 < prizeScale n L) :
    H ≤ K * M ↔ shawValue H n L ≤ K * shawValue M n L := by
  constructor
  · exact shawValue_le_mul_shawValue_of_le_mul hs
  · intro h
    unfold shawValue at h
    have hs_nonneg : 0 ≤ prizeScale n L := le_of_lt hs
    have hmul : (H / prizeScale n L) * prizeScale n L ≤
        (K * (M / prizeScale n L)) * prizeScale n L :=
      mul_le_mul_of_nonneg_right h hs_nonneg
    calc
      H = (H / prizeScale n L) * prizeScale n L := by
        field_simp [ne_of_gt hs]
      _ ≤ (K * (M / prizeScale n L)) * prizeScale n L := hmul
      _ = K * M := by
        field_simp [ne_of_gt hs]

/-- Uniform-family comparison equivalence: under pointwise positive prize scale, a pointwise raw
comparison between two door-(iv) targets is equivalent to the pointwise comparison of their
normalized Shaw values with the same multiplicative constant.  No cancellation estimate is present;
this is only the reversible normalization wrapper for comparison hypotheses. -/
theorem rawComparisonFamily_iff_shawValueComparisonFamily {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∀ i, H i ≤ K * M i) ↔
      (∀ i, shawValue (H i) (n i) (L i) ≤ K * shawValue (M i) (n i) (L i)) := by
  constructor
  · intro h i
    exact (rawComparison_iff_shawValueComparison (M := M i) (H := H i) (K := K)
      (n := n i) (L := L i) (hs i)).1 (h i)
  · intro h i
    exact (rawComparison_iff_shawValueComparison (M := M i) (H := H i) (K := K)
      (n := n i) (L := L i) (hs i)).2 (h i)

/-- Pointwise-positive parameter wrapper for uniform-family comparison normalization.  This is the
family comparison rung in the native admissible-instance hypotheses `0 < n_i`, `0 < L_i`. -/
theorem rawComparisonFamily_iff_shawValueComparisonFamily_of_pos
    {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∀ i, H i ≤ K * M i) ↔
      (∀ i, shawValue (H i) (n i) (L i) ≤ K * shawValue (M i) (n i) (L i)) :=
  rawComparisonFamily_iff_shawValueComparisonFamily (fun i => prizeScale_pos (hn i) (hL i))

/-- Strict raw comparison is also preserved and reflected by Shaw-value normalization.  Under a
positive prize scale, a genuine strict multiplicative gap `H < K*M` is exactly the normalized strict
gap `Sh(H) < K*Sh(M)`.  This packages the "strict slack survives normalization" rung needed when a
door-(iv) constraint is stated as a positive gap rather than a weak comparison. -/
theorem rawStrictComparison_iff_shawValueStrictComparison {M H K n L : ℝ}
    (hs : 0 < prizeScale n L) :
    H < K * M ↔ shawValue H n L < K * shawValue M n L := by
  constructor
  · intro h
    unfold shawValue
    have h1 : H / prizeScale n L < (K * M) / prizeScale n L :=
      div_lt_div_of_pos_right h hs
    have h2 : (K * M) / prizeScale n L = K * (M / prizeScale n L) := by ring
    exact h2 ▸ h1
  · intro h
    unfold shawValue at h
    have hsne : prizeScale n L ≠ 0 := ne_of_gt hs
    have hmul : (H / prizeScale n L) * prizeScale n L <
        (K * (M / prizeScale n L)) * prizeScale n L :=
      mul_lt_mul_of_pos_right h hs
    calc
      H = (H / prizeScale n L) * prizeScale n L := by field_simp [hsne]
      _ < (K * (M / prizeScale n L)) * prizeScale n L := hmul
      _ = K * M := by field_simp [hsne]

/-- Uniform-family strict comparison normalization.  Pointwise strict raw gaps and pointwise strict
Shaw-value gaps are equivalent under positive prize scale.  This is only algebraic normalization; it
contains no cancellation or anti-concentration input. -/
theorem rawStrictComparisonFamily_iff_shawValueStrictComparisonFamily
    {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∀ i, H i < K * M i) ↔
      (∀ i, shawValue (H i) (n i) (L i) < K * shawValue (M i) (n i) (L i)) := by
  constructor
  · intro h i
    exact (rawStrictComparison_iff_shawValueStrictComparison (M := M i) (H := H i) (K := K)
      (n := n i) (L := L i) (hs i)).1 (h i)
  · intro h i
    exact (rawStrictComparison_iff_shawValueStrictComparison (M := M i) (H := H i) (K := K)
      (n := n i) (L := L i) (hs i)).2 (h i)

/-- Pointwise-positive wrapper for uniform strict comparison normalization. -/
theorem rawStrictComparisonFamily_iff_shawValueStrictComparisonFamily_of_pos
    {ι : Type*} {M H n L : ι → ℝ} {K : ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∀ i, H i < K * M i) ↔
      (∀ i, shawValue (H i) (n i) (L i) < K * shawValue (M i) (n i) (L i)) :=
  rawStrictComparisonFamily_iff_shawValueStrictComparisonFamily
    (fun i => prizeScale_pos (hn i) (hL i))

/-! ## The two-sided Shaw-value bracket: the citable framing of the open prize

The prize asks to collapse the *width* of the bracket below to an absolute constant.  The two
easy rungs above are combined here into a single two-sided statement, and the bracket endpoints
are identified in closed form, so the entire open problem reads as "tighten a `sqrt n`-wide
bracket to `O(1)`".  All content here is harmless normalization arithmetic — no anti-concentration
or cancellation estimate is hidden. -/

/-- **Two-sided Shaw-value bracket.**  Whenever the Plancherel/RMS floor `sqrt n ≤ M` and the
trivial ceiling `M ≤ n` both hold, the normalized Shaw value is sandwiched between the two
normalized brackets.  This bundles `shawValue_floor_of_plancherel_floor` and
`shawValue_le_of_trivial_ceiling` into the single citable bracket the prize must collapse. -/
theorem shawValue_bracket {M n L : ℝ} (hs : 0 < prizeScale n L)
    (hfloor : Real.sqrt n ≤ M) (hceil : M ≤ n) :
    Real.sqrt n / prizeScale n L ≤ shawValue M n L ∧
      shawValue M n L ≤ n / prizeScale n L :=
  ⟨shawValue_floor_of_plancherel_floor hs hfloor,
   shawValue_le_of_trivial_ceiling hs hceil⟩

/-- Closed form of the **lower** bracket endpoint: `sqrt n / prizeScale n L = 1 / sqrt L`.
The Plancherel floor lands the normalized Shaw value at `1/sqrt(log(p/n))`, independent of `n`. -/
theorem floor_bracket_eq {n L : ℝ} (hn : 0 < n) :
    Real.sqrt n / prizeScale n L = 1 / Real.sqrt L := by
  unfold prizeScale
  rw [Real.sqrt_mul (le_of_lt hn), div_mul_eq_div_div,
    div_self (ne_of_gt (Real.sqrt_pos.2 hn))]

/-- Closed form of the **upper** bracket endpoint: `n / prizeScale n L = sqrt (n / L)`.
The trivial ceiling lands the normalized Shaw value at `sqrt(n / log(p/n))`, the SOTA-shaped scale. -/
theorem ceiling_bracket_eq {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    n / prizeScale n L = Real.sqrt (n / L) := by
  have hnL : (0 : ℝ) < n * L := mul_pos hn hL
  have hsnL : Real.sqrt (n * L) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnL)
  unfold prizeScale
  rw [div_eq_iff hsnL, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n / L)]
  have h2 : (n / L) * (n * L) = n ^ 2 := by field_simp
  rw [h2, Real.sqrt_sq (le_of_lt hn)]

/-- **Bracket width is `sqrt n`.**  The ratio of the upper to the lower bracket endpoint equals
`sqrt n`: the open prize is exactly the demand to collapse this `sqrt n`-wide normalized bracket
to an absolute constant.  (Probe `probe_shaw_bracket_arith.py`: ratio = 4,5.66,8,11.3,16 at
n=16..256 = `sqrt n`, non-vacuous.) -/
theorem bracket_width_eq_sqrt {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    (n / prizeScale n L) / (Real.sqrt n / prizeScale n L) = Real.sqrt n := by
  have hps : prizeScale n L ≠ 0 := ne_of_gt (prizeScale_pos hn hL)
  have hsn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  rw [div_div_div_cancel_right₀]
  · rw [div_eq_iff hsn, Real.mul_self_sqrt (le_of_lt hn)]
  all_goals try exact hps

/-! ## Uniform-family bracket corridor

The pointwise bracket above is often used over an admissible family of thin instances.  The next
rungs package exactly that use case: pointwise Plancherel floors and trivial ceilings produce a
uniform pointwise corridor for the normalized Shaw values, with the same `sqrt n` width at every
instance. -/

/-- Family version of the two-sided Shaw-value bracket.  If every instance has positive prize scale,
a Plancherel/RMS floor, and the trivial ceiling, then every normalized Shaw value lies in the
corresponding pointwise bracket.  This is still only normalization bookkeeping: no cancellation or
anti-concentration estimate is asserted. -/
theorem shawValueFamily_bracket {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hfloor : ∀ i, Real.sqrt (n i) ≤ M i) (hceil : ∀ i, M i ≤ n i) :
    ∀ i, Real.sqrt (n i) / prizeScale (n i) (L i) ≤ shawValue (M i) (n i) (L i) ∧
      shawValue (M i) (n i) (L i) ≤ n i / prizeScale (n i) (L i) := by
  intro i
  exact shawValue_bracket (hs i) (hfloor i) (hceil i)

/-- Pointwise-positive parameter wrapper for the family bracket.  Under the usual admissible
instance hypotheses `0 < n_i` and `0 < L_i`, Plancherel floors and trivial ceilings give the same
two-sided Shaw-value corridor pointwise. -/
theorem shawValueFamily_bracket_of_pos {ι : Type*} {M n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, Real.sqrt (n i) ≤ M i) (hceil : ∀ i, M i ≤ n i) :
    ∀ i, Real.sqrt (n i) / prizeScale (n i) (L i) ≤ shawValue (M i) (n i) (L i) ∧
      shawValue (M i) (n i) (L i) ≤ n i / prizeScale (n i) (L i) :=
  shawValueFamily_bracket (fun i => prizeScale_pos (hn i) (hL i)) hfloor hceil

/-- Family closed-form bracket endpoints.  Under positive `n` and `L`, the pointwise family
bracket from `shawValueFamily_bracket` has lower endpoint `1 / sqrt L` and upper endpoint
`sqrt (n / L)` at every instance. -/
theorem shawValueFamily_bracket_endpoints {ι : Type*} {n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    ∀ i, Real.sqrt (n i) / prizeScale (n i) (L i) = 1 / Real.sqrt (L i) ∧
      n i / prizeScale (n i) (L i) = Real.sqrt (n i / L i) := by
  intro i
  exact ⟨floor_bracket_eq (hn i), ceiling_bracket_eq (hn i) (hL i)⟩

/-- Family form of the width statement: at every admissible instance, the trivial-ceiling endpoint
divided by the Plancherel-floor endpoint equals `sqrt n`.  Thus a uniform Shaw-value bound is exactly
the demand to collapse a pointwise `sqrt n`-wide bracket throughout the family. -/
theorem shawValueFamily_bracket_width_eq_sqrt {ι : Type*} {n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    ∀ i, (n i / prizeScale (n i) (L i)) /
      (Real.sqrt (n i) / prizeScale (n i) (L i)) = Real.sqrt (n i) := by
  intro i
  exact bracket_width_eq_sqrt (hn i) (hL i)

/-- Equality is preserved and reflected by Shaw-value normalization.  Under positive prize scale,
two raw door-(iv) targets are equal exactly when their normalized Shaw values are equal.  This is
only division-by-scale bookkeeping, but it prevents equality rungs in the reduction chain from being
reproved ad hoc. -/
theorem rawEq_iff_shawValue_eq {M H n L : ℝ} (hs : 0 < prizeScale n L) :
    H = M ↔ shawValue H n L = shawValue M n L := by
  constructor
  · intro h
    rw [h]
  · intro h
    unfold shawValue at h
    have hsne : prizeScale n L ≠ 0 := ne_of_gt hs
    calc
      H = (H / prizeScale n L) * prizeScale n L := by field_simp [hsne]
      _ = (M / prizeScale n L) * prizeScale n L := by rw [h]
      _ = M := by field_simp [hsne]

/-- Uniform-family equality version of the Shaw normalization wrapper.  Pointwise equality of raw
targets is exactly pointwise equality of their Shaw values. -/
theorem rawEqFamily_iff_shawValueEqFamily {ι : Type*} {M H n L : ι → ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∀ i, H i = M i) ↔
      (∀ i, shawValue (H i) (n i) (L i) = shawValue (M i) (n i) (L i)) := by
  constructor
  · intro h i
    exact (rawEq_iff_shawValue_eq (M := M i) (H := H i) (n := n i) (L := L i) (hs i)).1 (h i)
  · intro h i
    exact (rawEq_iff_shawValue_eq (M := M i) (H := H i) (n := n i) (L := L i) (hs i)).2 (h i)

/-- Pointwise-positive parameter wrapper for equality normalization.  Equality rungs in a family
of raw door-(iv) targets can be moved to and from Shaw-value units directly from `0 < n_i` and
`0 < L_i`. -/
theorem rawEqFamily_iff_shawValueEqFamily_of_pos {ι : Type*} {M H n L : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    (∀ i, H i = M i) ↔
      (∀ i, shawValue (H i) (n i) (L i) = shawValue (M i) (n i) (L i)) :=
  rawEqFamily_iff_shawValueEqFamily (fun i => prizeScale_pos (hn i) (hL i))

end ArkLib.ProximityGap.Frontier.ShawValueCapstone

#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeBound_iff_shawValue_le
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeBound_iff_shawValue_le_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictPrizeBound_iff_shawValue_lt
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictPrizeBound_iff_shawValue_lt_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound_iff_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound_iff_shawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_mono_const
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound_mono_const
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_strictRawPrizeFamilyBound_iff_exists_strictRawPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_strictShawValueFamilyBound_iff_exists_strictShawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_rawPrizeFamilyBound_iff_not_exists_shawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound_mono_const
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound_mono_const
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_exists_rawPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_shawValueFamilyBound_iff_exists_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_rawPrizeFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound_of_rawComparison
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound_of_rawComparison
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_shawValueFamilyBound_iff_of_rawSandwich
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_shawValueFamilyBound_iff_of_rawSandwich
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_of_rawSandwich
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_shawValueFamilyBound_iff_of_rawSandwich
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_rawPrizeFamilyBound_iff_of_rawSandwich
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawLowerBound_iff_shawValue_floor
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawStrictLowerBound_iff_shawValue_strict_floor
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawLowerBoundFamily_iff_shawValueFloorFamily
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawStrictLowerBoundFamily_iff_shawValueStrictFloorFamily
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawLowerBoundFamily_iff_shawValueFloorFamily_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawStrictLowerBoundFamily_iff_shawValueStrictFloorFamily_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_floor_of_plancherel_floor
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_le_of_trivial_ceiling
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_le_mul_shawValue_of_le_mul
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawComparison_iff_shawValueComparison
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawComparisonFamily_iff_shawValueComparisonFamily
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawComparisonFamily_iff_shawValueComparisonFamily_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawStrictComparison_iff_shawValueStrictComparison
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawStrictComparisonFamily_iff_shawValueStrictComparisonFamily
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawStrictComparisonFamily_iff_shawValueStrictComparisonFamily_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_bracket
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.floor_bracket_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.ceiling_bracket_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.bracket_width_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamily_bracket
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamily_bracket_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamily_bracket_endpoints
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamily_bracket_width_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawEq_iff_shawValue_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawEqFamily_iff_shawValueEqFamily
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawEqFamily_iff_shawValueEqFamily_of_pos
