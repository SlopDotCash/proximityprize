/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ManyLineGridPhase
import ArkLib.Research.ProximityGap.Frontier.PrimeHeadDifferences

/-! # Prime-field many-line phases with a linear head-count cost

Using consecutive prime-field coefficients makes every difference of two head
sums lie in an interval of length 4r+1. The construction therefore applies
whenever the field-size slope times the code rate exceeds 4r+1.
-/
set_option autoImplicit false
namespace ProximityGap.PrimeManyLinePhase
open Filter Topology MCAThresholdLedger
open scoped NNReal ENNReal
variable (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i))


private theorem grid (r : ℕ) (hr : 1≤r) :
    ManyLineGridPhase.GridAttack (fun i => ZMod (p i)) n k x r (4*r+1) := by
  intro i e hk inside pack room
  rw [ZMod.card] at room ⊢
  have room' : (n i*n i-n i)*(4*r+1)≤(p i-1)*(k i-2) := by
    apply le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    simpa only [pow_two] using room
  have lower := PrimeHeadDifferences.grid_mass (t:=n i-e) (k:=k i) (x i) ((e:ℝ≥0)/n i)
    hr hk (by omega) (by omega) (by rwa [show n i-e-k i+1=n i-k i+1-e by omega])
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne (n i)),←Nat.cast_tsub]) room'
  rwa [show n i-(n i-e)+1=e+1 by omega] at lower

/-- Sufficiently long prescribed domains admit r(e+1) distinct bad labels
under the strict packing and linear field-size hypotheses. -/
theorem eventually_attack (e : ℕ → ℕ) (r : ℕ) (hr : 1≤r) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 b)) (core : ρ+b<1)
    (packing : (r:ℝ)*(1-ρ-b)<1-ρ) (fieldSize : ((4*r+1:ℕ):ℝ)<slope*ρ) :
    ∀ᶠ i in atTop, ((r*(e i+1):ℕ):ℝ≥0∞)/(p i) ≤
      epsMCA (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) ((e i:ℝ≥0)/n i) := by
  simpa only [ZMod.card] using ManyLineGridPhase.eventually_attack (fun i => ZMod (p i)) n k x
    e r (4*r+1)
    (grid p n k x r hr) hn (by simpa only [ZMod.card] using hf) rate positive err core packing
    fieldSize

/-- An arbitrary injective domain has exactly r(e+1) worst-pair bad labels
in the strict many-line incidence range. -/
theorem eventually_mass (e : ℕ → ℕ) (r : ℕ) (hr : 1≤r) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 b)) (hb : 0<b) (core : ρ+b<1)
    (packing : (r:ℝ)*(1-ρ-b)<1-ρ) (moment : ρ<(1-b)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-b))
    (fieldSize : ((4*r+1:ℕ):ℝ)<slope*ρ) :
    ∀ᶠ i in atTop, epsMCA (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) ((e i:ℝ≥0)/n i) = ((r*(e i+1):ℕ):ℝ≥0∞)/(p i) := by
  simpa only [ZMod.card] using ManyLineGridPhase.eventually_mass (fun i => ZMod (p i)) n k x
    e r (4*r+1)
    (grid p n k x r hr) hr hn (by simpa only [ZMod.card] using hf) rate positive err hb core
    packing moment geometry fieldSize

/-- In the open range the first failed grid index is eventually the integer
budget divided by r and rounded down, on every prescribed domain. -/
theorem exact_threshold (r Q : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ a : ℝ} (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : a=slope/Q/r) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)<1-ρ) (moment : ρ<(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-a))
    (fieldSize : ((4*r+1:ℕ):ℝ)<slope*ρ) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) = ((p i/Q/r:ℕ):ℝ≥0)/n i := by
  simpa only [ZMod.card] using ManyLineGridPhase.exact_threshold (fun i => ZMod (p i)) n k x
    r (4*r+1) Q
    (grid p n k x r hr) hr hQ hn (by simpa only [ZMod.card] using hf) rate positive index ha core
    packing moment geometry fieldSize

/-- The limiting radius is the rth share of the scalar budget even on the
three boundary faces of the phase. Only the field-size separation test
retains a strict margin. -/
theorem limit (r Q : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ a : ℝ} (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : (r:ℝ)*a=slope/Q) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)≤1-ρ) (moment : ρ≤(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ ≤ ((r+1:ℕ):ℝ)*(1-a))
    (fieldSize : ((4*r+1:ℕ):ℝ)<slope*ρ) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 a) := by
  simpa only [ZMod.card] using ManyLineGridPhase.limit (fun i => ZMod (p i)) n k x
    r (4*r+1) Q
    (grid p n k x r hr) hr hQ hn (by simpa only [ZMod.card] using hf) rate positive index ha core
    packing moment geometry fieldSize

end ProximityGap.PrimeManyLinePhase
#print axioms ProximityGap.PrimeManyLinePhase.eventually_attack
#print axioms ProximityGap.PrimeManyLinePhase.eventually_mass
#print axioms ProximityGap.PrimeManyLinePhase.exact_threshold
#print axioms ProximityGap.PrimeManyLinePhase.limit
