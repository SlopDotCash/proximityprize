/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Sampled-octave uniformity gate

Issue #464 records strong numerical evidence for the dyadic BGK/Paley wall: the normalized value
`C(n,p) = M(mu_n,p) / sqrt(n * log(p/n))` stays bounded, with the worst measured values below
`1.49` over the reachable octaves.  This is useful evidence, but the prize needs a uniform constant
at the worst allowed scale, not a finite table.

This file isolates that logical gap in a minimal form.  A finite sampled-octave table can be
preserved exactly while a later, unobserved octave spikes above the same budget.  Therefore the
missing mathematical input is not more finite samples by themselves; it is a tail/envelope theorem
that bounds every off-sample octave, or an equivalent coverage theorem.

No analytic estimate is claimed here.  The point is to make the consumer exact:

* sample bounds + coverage of all future indices imply a uniform bound;
* sample bounds + an off-sample tail/envelope imply a uniform bound;
* without such a tail/envelope, a one-octave spike countermodel preserves the sampled data.
-/

namespace ArkLib.ProximityGap.Frontier.SampledOctaveUniformityGate

/-- The score is bounded by `B` on the sampled indices `S`. -/
def SampleBounded (S : Finset ℕ) (score : ℕ -> ℕ) (B : ℕ) : Prop :=
  ∀ n : ℕ, n ∈ S -> score n <= B

/-- A single budget works for every index from `start` onward. -/
def UniformBoundFrom (start : ℕ) (score : ℕ -> ℕ) (B : ℕ) : Prop :=
  ∀ n : ℕ, start <= n -> score n <= B

/-- The sampled set covers every index from `start` onward. -/
def CoversFrom (S : Finset ℕ) (start : ℕ) : Prop :=
  ∀ n : ℕ, start <= n -> n ∈ S

/-- The off-sample tail/envelope bound: every index from `start` not in `S` is also bounded. -/
def OffSampleTailBound (S : Finset ℕ) (start : ℕ) (score : ℕ -> ℕ) (B : ℕ) : Prop :=
  ∀ n : ℕ, start <= n -> n ∉ S -> score n <= B

/-- Two score functions agree on the sampled indices. -/
def AgreesOn (S : Finset ℕ) (score datum : ℕ -> ℕ) : Prop :=
  ∀ n : ℕ, n ∈ S -> score n = datum n

/-- Coverage is a sufficient replacement for a tail theorem. -/
theorem uniformBound_of_sampleBounded_and_coversFrom
    {S : Finset ℕ} {score : ℕ -> ℕ} {start B : ℕ}
    (hsample : SampleBounded S score B) (hcover : CoversFrom S start) :
    UniformBoundFrom start score B := by
  intro n hn
  exact hsample n (hcover n hn)

/-- Sample control plus a tail/envelope theorem is the exact consumer that finite numerics lack. -/
theorem uniformBound_of_sampleBounded_and_offSampleTailBound
    {S : Finset ℕ} {score : ℕ -> ℕ} {start B : ℕ}
    (hsample : SampleBounded S score B)
    (htail : OffSampleTailBound S start score B) :
    UniformBoundFrom start score B := by
  intro n hn
  by_cases hmem : n ∈ S
  · exact hsample n hmem
  · exact htail n hn hmem

/-- A one-point spike above budget `B`, placed at `future`. -/
def pointSpikeAbove (B future : ℕ) : ℕ -> ℕ :=
  fun n : ℕ => if n = future then B + 1 else 0

/-- If the spike is off-sample, it obeys the sampled budget. -/
theorem sampleBounded_pointSpikeAbove
    {S : Finset ℕ} {B future : ℕ} (hnot : future ∉ S) :
    SampleBounded S (pointSpikeAbove B future) B := by
  intro n hn
  by_cases hnfuture : n = future
  · subst hnfuture
    exact False.elim (hnot hn)
  · simp [pointSpikeAbove, hnfuture]

/-- A spike at a future index violates the uniform bound from `start`. -/
theorem not_uniformBoundFrom_pointSpikeAbove
    {start B future : ℕ} (hfuture : start <= future) :
    ¬ UniformBoundFrom start (pointSpikeAbove B future) B := by
  intro huniform
  have h := huniform future hfuture
  simp [pointSpikeAbove] at h

/-- Finite sampled bounds alone cannot force a uniform constant past an unobserved future index. -/
theorem sampleBounded_not_force_uniform
    (S : Finset ℕ) {start B future : ℕ}
    (hfuture : start <= future) (hnot : future ∉ S) :
    ¬ (∀ score : ℕ -> ℕ, SampleBounded S score B -> UniformBoundFrom start score B) := by
  intro h
  exact not_uniformBoundFrom_pointSpikeAbove (start := start) (B := B) (future := future) hfuture
    (h (pointSpikeAbove B future) (sampleBounded_pointSpikeAbove hnot))

/-- Preserve a finite datum exactly and add a spike at one off-sample index. -/
def withFutureSpike (datum : ℕ -> ℕ) (B future : ℕ) : ℕ -> ℕ :=
  fun n : ℕ => if n = future then B + 1 else datum n

/-- An off-sample future spike does not change the sampled datum. -/
theorem agreesOn_withFutureSpike
    {S : Finset ℕ} {datum : ℕ -> ℕ} {B future : ℕ}
    (hnot : future ∉ S) :
    AgreesOn S (withFutureSpike datum B future) datum := by
  intro n hn
  by_cases hnfuture : n = future
  · subst hnfuture
    exact False.elim (hnot hn)
  · simp [withFutureSpike, hnfuture]

/-- If the datum is sample-bounded, adding an off-sample future spike preserves the sampled bound. -/
theorem sampleBounded_withFutureSpike
    {S : Finset ℕ} {datum : ℕ -> ℕ} {B future : ℕ}
    (hnot : future ∉ S) (hdatum : SampleBounded S datum B) :
    SampleBounded S (withFutureSpike datum B future) B := by
  intro n hn
  rw [agreesOn_withFutureSpike (S := S) (datum := datum) (B := B) (future := future) hnot n hn]
  exact hdatum n hn

/-- The future spike violates the uniform bound even though the sampled datum is unchanged. -/
theorem not_uniformBoundFrom_withFutureSpike
    {datum : ℕ -> ℕ} {start B future : ℕ} (hfuture : start <= future) :
    ¬ UniformBoundFrom start (withFutureSpike datum B future) B := by
  intro huniform
  have h := huniform future hfuture
  simp [withFutureSpike] at h

/-- A finite data table, even preserved exactly, cannot by itself force a uniform constant. -/
theorem finite_sample_data_not_force_uniform
    (S : Finset ℕ) (datum : ℕ -> ℕ) {start B future : ℕ}
    (hfuture : start <= future) (hnot : future ∉ S)
    (hdatum : SampleBounded S datum B) :
    ∃ score : ℕ -> ℕ,
      AgreesOn S score datum ∧
      SampleBounded S score B ∧
      ¬ UniformBoundFrom start score B := by
  refine ⟨withFutureSpike datum B future, ?_, ?_, ?_⟩
  · exact agreesOn_withFutureSpike hnot
  · exact sampleBounded_withFutureSpike hnot hdatum
  · exact not_uniformBoundFrom_withFutureSpike hfuture

/-! ## Concrete scaled version of the #464 octave evidence

We encode the visible normalized constants as integer hundredths.  The maximum sampled budget
`149` represents `1.49`.  This theorem does not question the data; it proves only that preserving
that finite table exactly still does not imply a uniform all-octave `1.49` bound without a tail
theorem.
-/

/-- The measured octave set `n = 8,16,...,1024`. -/
def observedOctaves : Finset ℕ := {8, 16, 32, 64, 128, 256, 512, 1024}

/-- The measured normalized constants, scaled by `100` and rounded as in the dossier table. -/
def observedC100 : ℕ -> ℕ
  | 8 => 107
  | 16 => 121
  | 32 => 131
  | 64 => 149
  | 128 => 142
  | 256 => 139
  | 512 => 128
  | 1024 => 133
  | _ => 0

/-- The recorded eight-octave data are bounded by `149` in the scaled units. -/
theorem observedC100_sampleBounded :
    SampleBounded observedOctaves observedC100 149 := by
  intro n hn
  simp only [observedOctaves, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h | h <;> subst h <;>
    (unfold observedC100; decide)

/-- The eight-octave `C <= 1.49` table is not, by itself, a uniform all-future bound. -/
theorem observedC100_not_decisive :
    ∃ score : ℕ -> ℕ,
      AgreesOn observedOctaves score observedC100 ∧
      SampleBounded observedOctaves score 149 ∧
      ¬ UniformBoundFrom 8 score 149 := by
  exact finite_sample_data_not_force_uniform observedOctaves observedC100
    (start := 8) (B := 149) (future := 2048)
    (by norm_num) (by decide) observedC100_sampleBounded

/-- A sequence of sampled indices misses `future`. -/
def Misses (trace : ℕ -> ℕ) (future : ℕ) : Prop :=
  ∀ k : ℕ, trace k ≠ future

/-- A trace hits every future index from `start`. -/
def HitsEveryFrom (trace : ℕ -> ℕ) (start : ℕ) : Prop :=
  ∀ n : ℕ, start <= n -> ∃ k : ℕ, trace k = n

/-- A score is bounded along a sampled trace. -/
def TraceBounded (trace : ℕ -> ℕ) (score : ℕ -> ℕ) (B : ℕ) : Prop :=
  ∀ k : ℕ, score (trace k) <= B

/-- Trace bounds imply a uniform bound exactly when the trace hits every future index. -/
theorem uniformBound_of_traceBounded_and_hitsEveryFrom
    {trace : ℕ -> ℕ} {score : ℕ -> ℕ} {start B : ℕ}
    (htrace : TraceBounded trace score B)
    (hhit : HitsEveryFrom trace start) :
    UniformBoundFrom start score B := by
  intro n hn
  obtain ⟨k, hk⟩ := hhit n hn
  rw [← hk]
  exact htrace k

/-- A sampled trace that misses one future index cannot force a uniform constant. -/
theorem traceBounded_not_force_uniform
    (trace : ℕ -> ℕ) {start B future : ℕ}
    (hfuture : start <= future) (hmiss : Misses trace future) :
    ¬ (∀ score : ℕ -> ℕ, TraceBounded trace score B -> UniformBoundFrom start score B) := by
  intro h
  let score := pointSpikeAbove B future
  have htrace : TraceBounded trace score B := by
    intro k
    by_cases hk : trace k = future
    · exact False.elim (hmiss k hk)
    · simp [score, pointSpikeAbove, hk]
  exact not_uniformBoundFrom_pointSpikeAbove (start := start) (B := B) (future := future) hfuture
    (h score htrace)

#print axioms uniformBound_of_sampleBounded_and_coversFrom
#print axioms uniformBound_of_sampleBounded_and_offSampleTailBound
#print axioms sampleBounded_pointSpikeAbove
#print axioms not_uniformBoundFrom_pointSpikeAbove
#print axioms sampleBounded_not_force_uniform
#print axioms finite_sample_data_not_force_uniform
#print axioms observedC100_sampleBounded
#print axioms observedC100_not_decisive
#print axioms uniformBound_of_traceBounded_and_hitsEveryFrom
#print axioms traceBounded_not_force_uniform

end ArkLib.ProximityGap.Frontier.SampledOctaveUniformityGate
