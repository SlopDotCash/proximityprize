/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81FactorialPaddingWickAbsorption

/-!
# G89: all-depth Wick assembly under per-depth core-count caps

Every landed corrected-padding absorption result (G79S, G81, G82, and the reported G86/G88
counted-decoder chain) controls one primitive depth at a time against the full production Wick
budget.  A δ*-facing energy statement must control the *sum over every primitive depth*
`s = 0, …, r` simultaneously — spending the budget once, not `r + 1` times.

This file closes that assembly gap.  The budget is split evenly across the `r + 1` depths: the
named per-depth cap

```text
depthBudgetCap n r J s :
  (r + 1) * (J * (r.descFactorial s)^2 * (r - s)!) ≤ (2r - 1)!! * n^s
```

is exactly what one depth may consume.  The headline theorem proves that if every depth's sector
mass fits its factorial-corrected envelope (G80R/G81C shape, decoder discharged by G87/G88) and
every depth satisfies its cap, then the total across all depths fits the single full Wick budget
`(2r - 1)!! * n^r`.  The proof is ℕ-clean: multiply through by `r + 1` and cancel.

At the production point `(n, r) = (2^30, 110)` the caps are kernel-checked to hold
*unconditionally* with the crude universe counts at depths `0, 1, 2` (`J = n^(2s)`) and with the
elementary equal-sum fiber count at depth `3` (`J = n^5`) — even after paying the `111`-fold
budget split.  At depth `4`, the raw equal-sum fiber count `n^7` fails, while a count of `n^6`
passes even after the split (`production_cap_four_freeOrbit` records that arithmetic fact).
**Scope correction (post-G83-retraction, 2026-07-10):** the claim that the TRUE depth-4 sector
count is `≤ n^6` via the free-orbit quotient was retracted (`08aa56a202`) — a raw-sector decoder
must restore the scale coordinate, so the quotient saving does not transfer to the genuine
sector.  The summed gate is therefore fed *unconditionally* only through depth `3`; the depth-4
hypothesis `J 4 ≤ n^6` in the production consumer is an OPEN conditional input, alongside the
deep caps.

**Honest scope.**  The headline production consumer reduces the whole combinatorial
superstructure to the deep caps `5 ≤ s ≤ 110`, which for growing `s` are the open analytic wall
(square-root-scale subgroup cancellation); nothing here claims the true sector counts satisfy
them.  The envelope hypothesis at each depth is the counted-decoder bound (reported G88), taken
here as an interface.  CORE remains OPEN / ON-BGK.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly

open ArkLib.ProximityGap.Frontier.G79PrimitivePaddingSaddleLocalization
open ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption

/-- The even-split per-depth budget cap: depth `s` may consume at most a `1/(r+1)` share of the
full Wick budget, stated multiplicatively over ℕ. -/
def depthBudgetCap (n r J s : ℕ) : Prop :=
  (r + 1) * (J * (r.descFactorial s) ^ 2 * (r - s).factorial)
    ≤ Nat.doubleFactorial (2 * r - 1) * n ^ s

/-- The cap is monotone in the core count. -/
theorem depthBudgetCap_mono {n r J J' s : ℕ} (h : J' ≤ J)
    (hc : depthBudgetCap n r J s) : depthBudgetCap n r J' s := by
  unfold depthBudgetCap at hc ⊢
  exact le_trans (by gcongr) hc

/-- **All-depth Wick assembly.**  If every primitive depth `s ≤ r` has sector mass inside its
factorial-corrected envelope and satisfies the even-split budget cap, then the total mass across
all depths fits the single full Wick budget. -/
theorem allDepth_correctedSectors_le_fullWick
    {n r : ℕ} {J W : ℕ → ℕ}
    (hW : ∀ s ∈ Finset.range (r + 1), W s ≤ correctedPadEnvelope n r (J s) s)
    (hJ : ∀ s ∈ Finset.range (r + 1), depthBudgetCap n r (J s) s) :
    ∑ s ∈ Finset.range (r + 1), W s
      ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  have key : ∀ s ∈ Finset.range (r + 1),
      (r + 1) * W s ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
    intro s hs
    have hsr : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    calc
      (r + 1) * W s ≤ (r + 1) * correctedPadEnvelope n r (J s) s :=
        Nat.mul_le_mul_left _ (hW s hs)
      _ = ((r + 1) * (J s * (r.descFactorial s) ^ 2 * (r - s).factorial)) *
            n ^ (r - s) := by
        unfold correctedPadEnvelope; ring
      _ ≤ (Nat.doubleFactorial (2 * r - 1) * n ^ s) * n ^ (r - s) :=
        Nat.mul_le_mul_right _ (hJ s hs)
      _ = Nat.doubleFactorial (2 * r - 1) * n ^ r := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hsr]
  have hsum : (r + 1) * ∑ s ∈ Finset.range (r + 1), W s
      ≤ (r + 1) * (Nat.doubleFactorial (2 * r - 1) * n ^ r) := by
    rw [Finset.mul_sum]
    calc
      ∑ s ∈ Finset.range (r + 1), (r + 1) * W s
        ≤ ∑ _s ∈ Finset.range (r + 1),
            Nat.doubleFactorial (2 * r - 1) * n ^ r :=
        Finset.sum_le_sum key
      _ = (r + 1) * (Nat.doubleFactorial (2 * r - 1) * n ^ r) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  exact Nat.le_of_mul_le_mul_left hsum (Nat.succ_pos r)

/-- The shallow-half sufficient condition, G79S/G81 style: for `2s ≤ r + 1`, the normalized
condition `(r+1) * J * r^s ≤ n^s` already implies the even-split cap. -/
theorem depthBudgetCap_of_shallow {n r J s : ℕ}
    (hrs : 2 * s ≤ r + 1) (hsr : s ≤ r)
    (hJ : (r + 1) * J * r ^ s ≤ n ^ s) :
    depthBudgetCap n r J s := by
  unfold depthBudgetCap
  have hfall : r.descFactorial s ≤ r ^ s := Nat.descFactorial_le_pow r s
  have htail := pow_le_oddWickTail hrs
  have hfac := factorial_le_oddDoubleFactorial (r - s)
  calc
    (r + 1) * (J * (r.descFactorial s) ^ 2 * (r - s).factorial)
        ≤ (r + 1) * (J * (r ^ s * r ^ s) * (r - s).factorial) := by
      have : (r.descFactorial s) ^ 2 ≤ r ^ s * r ^ s := by
        have := Nat.mul_le_mul hfall hfall
        simpa [pow_two] using this
      gcongr
    _ = ((r + 1) * J * r ^ s) * (r ^ s * (r - s).factorial) := by ring
    _ ≤ n ^ s * (oddWickTail r s * Nat.doubleFactorial (2 * (r - s) - 1)) := by
      have hmix : r ^ s * (r - s).factorial
          ≤ oddWickTail r s * Nat.doubleFactorial (2 * (r - s) - 1) :=
        Nat.mul_le_mul htail hfac
      exact Nat.mul_le_mul hJ hmix
    _ = (oddWickTail r s * Nat.doubleFactorial (2 * (r - s) - 1)) * n ^ s := by ring
    _ = Nat.doubleFactorial (2 * r - 1) * n ^ s := by
      rw [← oddDoubleFactorial_split hsr]

/-! ## Production caps at `(n, r) = (2^30, 110)`

Kernel-checked: the even-split caps hold with the crude universe counts at depths `0, 1, 2`, the
elementary equal-sum fiber count at depth `3`, and G83's free-orbit-reduced count at depth `4`.
The unreduced equal-sum count still fails at depth `4`.
-/

/-- Depth `0` (the fully-cancelled diagonal sector, `J = 1`) satisfies its split cap:
`111 * (110!) ≤ 219!!`. -/
theorem production_cap_zero :
    depthBudgetCap (2 ^ 30) 110 1 0 := by
  unfold depthBudgetCap
  norm_num [Nat.doubleFactorial]

/-- Depth `1` with the crude universe count `J = n^2` satisfies its split cap. -/
theorem production_cap_one :
    depthBudgetCap (2 ^ 30) 110 ((2 ^ 30) ^ 2) 1 := by
  unfold depthBudgetCap
  norm_num [Nat.doubleFactorial]

/-- Depth `2` with the crude universe count `J = n^4` satisfies its split cap, even paying the
`111`-fold budget split (sharpens the G82 unsplit calibration). -/
theorem production_cap_two :
    depthBudgetCap (2 ^ 30) 110 ((2 ^ 30) ^ 4) 2 := by
  unfold depthBudgetCap
  norm_num [Nat.doubleFactorial]

/-- Depth `3` with the elementary equal-sum fiber count `J = n^5` satisfies its split cap. -/
theorem production_cap_three :
    depthBudgetCap (2 ^ 30) 110 ((2 ^ 30) ^ 5) 3 := by
  unfold depthBudgetCap
  norm_num [Nat.doubleFactorial]

/-- The raw elementary equal-sum fiber count `n^7` fails the split depth-4 cap. -/
theorem production_cap_four_equalSum_fails :
    ¬ depthBudgetCap (2 ^ 30) 110 ((2 ^ 30) ^ 7) 4 := by
  unfold depthBudgetCap
  norm_num [Nat.doubleFactorial]

/-- **Depth-4 free-orbit rescue under the split budget.**  G83's free subgroup quotient reduces
the elementary `n^7` universe to `n^6`, and that sharper count fits even after paying the
`111`-fold all-depth split. -/
theorem production_cap_four_freeOrbit :
    depthBudgetCap (2 ^ 30) 110 ((2 ^ 30) ^ 6) 4 := by
  unfold depthBudgetCap
  norm_num [Nat.doubleFactorial]

/-- **Production all-depth consumer.**  At `(n, r) = (2^30, 110)`: if every depth's sector mass
fits its factorial-corrected envelope, the shallow core counts are bounded by their elementary
values (crude universe at depths ≤ 2, equal-sum fiber at depth 3, free-orbit quotient at depth 4),
and the *deep caps* `5 ≤ s ≤ 110` hold, then the total mass over all `111` depths fits the single production Wick
budget.  The deep caps are the named open analytic wall; everything else is discharged. -/
theorem production_allDepth_absorbed_of_deep_caps
    {J W : ℕ → ℕ}
    (hW : ∀ s ∈ Finset.range 111,
      W s ≤ correctedPadEnvelope (2 ^ 30) 110 (J s) s)
    (h0 : J 0 ≤ 1) (h1 : J 1 ≤ (2 ^ 30) ^ 2)
    (h2 : J 2 ≤ (2 ^ 30) ^ 4) (h3 : J 3 ≤ (2 ^ 30) ^ 5)
    (h4 : J 4 ≤ (2 ^ 30) ^ 6)
    (hdeep : ∀ s, 5 ≤ s → s ≤ 110 → depthBudgetCap (2 ^ 30) 110 (J s) s) :
    ∑ s ∈ Finset.range 111, W s
      ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  refine allDepth_correctedSectors_le_fullWick hW ?_
  intro s hs
  have hsr : s ≤ 110 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  match s, hsr with
  | 0, _ => exact depthBudgetCap_mono h0 production_cap_zero
  | 1, _ => exact depthBudgetCap_mono h1 production_cap_one
  | 2, _ => exact depthBudgetCap_mono h2 production_cap_two
  | 3, _ => exact depthBudgetCap_mono h3 production_cap_three
  | 4, _ => exact depthBudgetCap_mono h4 production_cap_four_freeOrbit
  | (t + 5), hsr => exact hdeep (t + 5) (by omega) hsr

end ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.depthBudgetCap_mono
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.allDepth_correctedSectors_le_fullWick
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.depthBudgetCap_of_shallow
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.production_cap_zero
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.production_cap_one
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.production_cap_two
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.production_cap_three
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.production_cap_four_equalSum_fails
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.production_cap_four_freeOrbit
#print axioms
  ArkLib.ProximityGap.Frontier.G89AllDepthWickAssembly.production_allDepth_absorbed_of_deep_caps
