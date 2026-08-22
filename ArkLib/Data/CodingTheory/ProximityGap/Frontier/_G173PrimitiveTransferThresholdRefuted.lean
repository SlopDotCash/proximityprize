/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136ProductionInstantiation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW3G_GateClosesQuadraticExcess

/-!
# G173: `p > n^4` does not transfer primitive dyadic relations to characteristic zero

The G105 primitive-relation suppression probe sampled depth-four subset collisions at
`n ∈ {12,16,20}` and primes just above `n^4`, then suggested a characteristic-`p`
Lam--Leung transfer.  The threshold is false even for a dyadic subgroup and the first
primitive rung.

At the prime `p = 17318209 > 64^4`, the element `ω = 7937154` has order `64` and

```
ω^52 + ω^57 = ω^58 + 1.
```

After normalization this is the G136 accident `(ω^52,ω^57,ω^58)`, outside all three
characteristic-zero Mann families.  Thus the order-64 subgroup already has a primitive
signed four-term relation above the proposed `n^4` threshold.  This is the same exact
bad prime whose depth-three wraparound excess is `1658880` in `_AvW3G_...`; the present
statement identifies the literal low-weight kernel relation carrying the failure.

Asymptotically, an Archimedean resultant certificate for a signed relation of weight
`L` has only the envelope `p ≤ L^(φ(n)) = L^(n/2)` (FS16), not a polynomial threshold
such as `n^4`.  At production, `p = n^(~5.27)` is exponentially below `L^(n/2)` for every
fixed `L ≥ 2`, so a transfer theorem must use prime-specific nondivisibility.  It cannot
follow from field size alone.

Honest scope: this refutes the proposed transfer threshold and the extrapolation from
three zero cells.  It does not decide whether either certified production prime has a
rung-two accident; G136 proves that finite arithmetic question is exactly the anchor.
Issue #466.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace ArkLib.ProximityGap.Frontier.G173PrimitiveTransferThresholdRefuted

open ArkLib.ProximityGap.Frontier.G136EnergySolutionBijection
open ArkLib.ProximityGap.Frontier.G136LawfulCount
open ArkLib.ProximityGap.Frontier.G136ProductionInstantiation

local instance fact_prime_17318209 : Fact (Nat.Prime 17318209) := ⟨by norm_num⟩

/-- The counterexample prime lies strictly above the proposed `n^4` transfer threshold. -/
theorem prime_gt_sixtyFour_pow_four : (64 : ℕ) ^ 4 < 17318209 := by norm_num

/-- The concrete root used by the normalized four-term relation has exact order 64. -/
theorem orderOf_7937154_zmod17318209 : orderOf (7937154 : ZMod 17318209) = 64 := by
  have h32 : ¬ (7937154 : ZMod 17318209) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h64 : (7937154 : ZMod 17318209) ^ (2 : ℕ) ^ 6 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (7937154 : ZMod 17318209)) h32 h64
  norm_num at h
  exact h

/-- `7937154` is a primitive 64-th root in the counterexample field. -/
theorem isPrimitiveRoot_7937154_64_zmod17318209 :
    IsPrimitiveRoot (7937154 : ZMod 17318209) 64 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_7937154_zmod17318209

/-- The three powers in the normalized relation, reduced to canonical residues. -/
theorem concrete_pow52 : (7937154 : ZMod 17318209) ^ 52 = 5663213 := by decide

theorem concrete_pow57 : (7937154 : ZMod 17318209) ^ 57 = 17079628 := by decide

theorem concrete_pow58 : (7937154 : ZMod 17318209) ^ 58 = 5424631 := by decide

/-- The literal normalized signed relation. -/
theorem concrete_signed_relation :
    (5663213 : ZMod 17318209) + 17079628 = 5424631 + 1 := by decide

/-- The normalized solution is outside every lawful Mann family, hence is a genuine
characteristic-`p` rung-two accident. -/
theorem concrete_accident_mem :
    ((((5663213 : ZMod 17318209), 17079628), 5424631)) ∈
      accidents (rootsFinset (7937154 : ZMod 17318209) 64) := by
  let ω : ZMod 17318209 := 7937154
  have hω : IsPrimitiveRoot ω 64 := isPrimitiveRoot_7937154_64_zmod17318209
  have hn : (64 : ℕ) ≠ 0 := by norm_num
  have h52pow : ω ^ 52 ∈ rootsFinset ω 64 := pow_mem_rootsFinset hn hω 52
  have h57pow : ω ^ 57 ∈ rootsFinset ω 64 := pow_mem_rootsFinset hn hω 57
  have h58pow : ω ^ 58 ∈ rootsFinset ω 64 := pow_mem_rootsFinset hn hω 58
  have h52 : (5663213 : ZMod 17318209) ∈ rootsFinset ω 64 := by
    rw [← concrete_pow52]
    exact h52pow
  have h57 : (17079628 : ZMod 17318209) ∈ rootsFinset ω 64 := by
    rw [← concrete_pow57]
    exact h57pow
  have h58 : (5424631 : ZMod 17318209) ∈ rootsFinset ω 64 := by
    rw [← concrete_pow58]
    exact h58pow
  unfold accidents
  rw [Finset.mem_sdiff]
  constructor
  · unfold solutions
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_product]
      constructor
      · rw [Finset.mem_product]
        exact ⟨h52, h57⟩
      · exact h58
    · exact concrete_signed_relation
  · intro h
    unfold lawful at h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
        have hfirst := (Prod.ext_iff.mp (Prod.ext_iff.mp hb).1).1
        exact (by decide : ¬((1 : ZMod 17318209) = 5663213)) hfirst
      · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
        have hsecond := (Prod.ext_iff.mp (Prod.ext_iff.mp ha).1).2
        exact (by decide : ¬((1 : ZMod 17318209) = 17079628)) hsecond
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
      have hthird := (Prod.ext_iff.mp ha).2
      exact (by decide : ¬((-1 : ZMod 17318209) = 5424631)) hthird

#print axioms prime_gt_sixtyFour_pow_four
#print axioms isPrimitiveRoot_7937154_64_zmod17318209
#print axioms concrete_signed_relation
#print axioms concrete_accident_mem

end ArkLib.ProximityGap.Frontier.G173PrimitiveTransferThresholdRefuted
