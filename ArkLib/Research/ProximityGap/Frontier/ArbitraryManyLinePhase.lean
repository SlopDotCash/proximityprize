/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ManyLineGridPhase
import ArkLib.Research.ProximityGap.Frontier.ArbitraryDomainHeadMass

/-! # Exact many-line phases over arbitrary evaluation domains

A common locator absorbs the collisions between private-site keys.
When field size and dimension both grow linearly with length, the finite
separation inequality eventually holds above an explicit field-size slope.
-/
set_option autoImplicit false
namespace ProximityGap.ArbitraryManyLinePhase
open Filter Topology MCAThresholdLedger
open scoped NNReal ENNReal
variable (F : ℕ → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (n k : ℕ → ℕ) [∀ i, NeZero (n i)] (x : ∀ i, Fin (n i) ↪ F i)


private theorem grid (r : ℕ) (hr : 1≤r) : ManyLineGridPhase.GridAttack F n k x r ((r+1)^4) := by
  intro i e hk inside pack room
  have lower := ArbitraryDomainHeadMass.grid_mass (t:=n i-e) (k:=k i) (x i) ((e:ℝ≥0)/n i)
    hr hk (by omega) (by omega) (by rwa [show n i-e-k i+1=n i-k i+1-e by omega])
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne (n i)),←Nat.cast_tsub]) room
  rwa [show n i-(n i-e)+1=e+1 by omega] at lower

/-- Sufficiently long prescribed domains admit r(e+1) distinct bad labels
under the strict packing and linear field-size hypotheses. -/
theorem eventually_attack (e : ℕ → ℕ) (r : ℕ) (hr : 1≤r) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 b)) (core : ρ+b<1)
    (packing : (r:ℝ)*(1-ρ-b)<1-ρ) (fieldSize : ((r+1:ℕ):ℝ)^4<slope*ρ) :
    ∀ᶠ i in atTop, ((r*(e i+1):ℕ):ℝ≥0∞)/(Fintype.card (F i)) ≤
      epsMCA (F:=F i) (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → F i)) ((e i:ℝ≥0)/n i) := by
  exact ManyLineGridPhase.eventually_attack F n k x e r ((r+1)^4)
    (grid F n k x r hr) hn hf rate positive err core packing
    (by simpa only [Nat.cast_pow] using fieldSize)

/-- An arbitrary injective domain has exactly r(e+1) worst-pair bad labels
in the strict many-line incidence range. -/
theorem eventually_mass (e : ℕ → ℕ) (r : ℕ) (hr : 1≤r) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 b)) (hb : 0<b) (core : ρ+b<1)
    (packing : (r:ℝ)*(1-ρ-b)<1-ρ) (moment : ρ<(1-b)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-b))
    (fieldSize : ((r+1:ℕ):ℝ)^4<slope*ρ) :
    ∀ᶠ i in atTop, epsMCA (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) ((e i:ℝ≥0)/n i) = ((r*(e i+1):ℕ):ℝ≥0∞)/(Fintype.card (F i)) := by
  exact ManyLineGridPhase.eventually_mass F n k x e r ((r+1)^4)
    (grid F n k x r hr) hr hn hf rate positive err hb core
    packing moment geometry (by simpa only [Nat.cast_pow] using fieldSize)

/-- In the open range the first failed grid index is eventually the integer
budget divided by r and rounded down, on every prescribed domain. -/
theorem exact_threshold (r Q : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ a : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : a=slope/Q/r) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)<1-ρ) (moment : ρ<(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-a))
    (fieldSize : ((r+1:ℕ):ℝ)^4<slope*ρ) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)) = ((Fintype.card (F i)/Q/r:ℕ):ℝ≥0)/n i := by
  exact ManyLineGridPhase.exact_threshold F n k x r ((r+1)^4) Q
    (grid F n k x r hr) hr hQ hn hf rate positive index ha core
    packing moment geometry (by simpa only [Nat.cast_pow] using fieldSize)

/-- The limiting radius is the rth share of the scalar budget even on the
three boundary faces of the phase. Only the field-size separation test
retains a strict margin. -/
theorem limit (r Q : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ a : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : (r:ℝ)*a=slope/Q) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)≤1-ρ) (moment : ρ≤(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ ≤ ((r+1:ℕ):ℝ)*(1-a))
    (fieldSize : ((r+1:ℕ):ℝ)^4<slope*ρ) :
    Tendsto (fun i => (mcaDeltaStar (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 a) := by
  exact ManyLineGridPhase.limit F n k x r ((r+1)^4) Q
    (grid F n k x r hr) hr hQ hn hf rate positive index ha core
    packing moment geometry (by simpa only [Nat.cast_pow] using fieldSize)

end ProximityGap.ArbitraryManyLinePhase
#print axioms ProximityGap.ArbitraryManyLinePhase.eventually_attack
#print axioms ProximityGap.ArbitraryManyLinePhase.eventually_mass
#print axioms ProximityGap.ArbitraryManyLinePhase.exact_threshold
#print axioms ProximityGap.ArbitraryManyLinePhase.limit
