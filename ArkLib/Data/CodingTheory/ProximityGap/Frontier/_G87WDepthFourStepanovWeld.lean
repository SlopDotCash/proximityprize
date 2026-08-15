/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87DepthFourPairSumReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G103FSubgroupCollisionBound

/-!
# G87W: the depth-four pair-sum hypothesis is DISCHARGED by the G103F Stepanov theorem

G87P reduced the production depth-four collision sector to `PairSumConcentration5`:
`max_{c≠0} pairCount S c ≤ n/5`.  G103F landed the classical two-relation Stepanov collision
bound `#(S ∩ (S+c)) ≤ 4B²`.  This file welds them: for a symmetric set (`-S = S`, true for
any multiplicative subgroup of even order since `-1 ∈ H`),

```text
pairCount S c = #{x ∈ S : c - x ∈ S} = #{x ∈ S : x - c ∈ S},
```

so at the production shape (`|S| = 2^30`, `x^(2^30) = 1` on `S`, `2^41 ≤ p`) the Stepanov
bound with `B = 2^11` gives `pairCount S c ≤ 4·2^22 = 2^24 ≤ ⌊2^30/5⌋` — a `2^3.68` margin.
`PairSumConcentration5` is therefore a THEOREM at production shape, and the G87P depth-four
absorption becomes unconditional up to the single remaining histogram-to-tuple bridge
hypothesis `orderedCoreCount ≤ equalSumQuadPairs` (owned by the G84/G88 decoder lane).

No Fourier input, no named analytic hypothesis: the depth-four sector of the padded collision
lane now rests entirely on in-tree Lean theorems plus the bridge.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G87WDepthFourStepanovWeld

open Finset
open scoped Nat
open ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction

/-! ## Part 1 — `pairCount` as a one-variable collision count -/

section AbstractGroup

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The pair fiber projects bijectively onto its first coordinate. -/
theorem pairCount_eq_filter (S : Finset G) (c : G) :
    pairCount S c = (S.filter fun x => c - x ∈ S).card := by
  unfold pairCount
  apply Finset.card_bij (fun q _ => q.1)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨h1, h2⟩, hsum⟩ := hq
    have : c - q.1 = q.2 := by rw [← hsum]; abel
    simp only [Finset.mem_filter]
    exact ⟨h1, this ▸ h2⟩
  · intro q1 hq1 q2 hq2 hfst
    simp only [Finset.mem_filter, Finset.mem_product] at hq1 hq2
    have h2 : q1.2 = q2.2 := by
      have e1 : c - q1.1 = q1.2 := by rw [← hq1.2]; abel
      have e2 : c - q2.1 = q2.2 := by rw [← hq2.2]; abel
      rw [← e1, ← e2, hfst]
    exact Prod.ext hfst h2
  · intro x hx
    simp only [Finset.mem_filter] at hx
    refine ⟨(x, c - x), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hx.1, hx.2⟩, by abel⟩

/-- For a symmetric set, the sum-fiber equals the shift-collision set of G103F. -/
theorem pairCount_eq_collision (S : Finset G) (hsym : ∀ x ∈ S, -x ∈ S) (c : G) :
    pairCount S c = (S.filter fun x => x - c ∈ S).card := by
  rw [pairCount_eq_filter]
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · intro h
    have := hsym _ h
    simpa [neg_sub] using this
  · intro h
    have := hsym _ h
    simpa [neg_sub] using this

end AbstractGroup

/-! ## Part 2 — the weld at production shape -/

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **`PairSumConcentration5` is a theorem at production shape.**  For any symmetric subset
of `ZMod p` of size `2^30` on which `x^(2^30) = 1` (e.g. the adversarial multiplicative
subgroup: even order gives `-1 ∈ H`), with `2^41 ≤ p`, the G103F Stepanov collision bound at
`B = 2^11` gives `pairCount S c ≤ 2^24 ≤ ⌊2^30/5⌋` for every `c ≠ 0`. -/
theorem pairSumConcentration5_production (S : Finset (ZMod p))
    (hsym : ∀ x ∈ S, -x ∈ S)
    (hpow : ∀ x ∈ S, x ^ (2 ^ 30) = 1)
    (hcard : S.card = 2 ^ 30)
    (hp : 2 ^ 41 ≤ p) :
    PairSumConcentration5 S := by
  intro c hc
  rw [pairCount_eq_collision S hsym c, hcard]
  calc
    (S.filter fun x => x - c ∈ S).card
        ≤ 4 * (2 ^ 11) ^ 2 := by
      refine ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound.card_collision_le_four_sq
        (p := p) S (t := 2 ^ 30) (B := 2 ^ 11) ?_ ?_ ?_ ?_ hpow hc
      · norm_num
      · norm_num
      · norm_num
      · calc (2 ^ 30 : ℕ) * 2 ^ 11 = 2 ^ 41 := by norm_num
          _ ≤ p := hp
    _ ≤ 2 ^ 30 / 5 := by norm_num

/-
DEFERRED HEADLINE (G86 sharp-envelope weld).  `production_depth_four_absorbed_of_bridge`
chained `pairSumConcentration5_production` → `equalSumQuadPairs_le_of_concentration` →
G87P's `production_depth_four_sector_absorbed`, whose conclusion `sectorMass ≤ Wick budget`
rests on G86's `sectorMass_le_sharpEnvelope`.  That G86 module
(`_G86SharpReconstructionIdentity`) was never landed, so the sector weld and this headline
are held out of the build.  What remains here, `pairCount_eq_collision` and the production
Stepanov discharge `pairSumConcentration5_production` (`max_{c≠0} pairCount S c ≤ n/5` at
production shape), is axiom-clean and stands on its own: `PairSumConcentration5` is a THEOREM
at production shape.  Re-weld the headline once the G86 sharp envelope lands; see DISPROOF_LOG
`[466-G87P-G87W-g86-deferral]`.
-/

end ArkLib.ProximityGap.Frontier.G87WDepthFourStepanovWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G87WDepthFourStepanovWeld.pairCount_eq_collision
#print axioms
  ArkLib.ProximityGap.Frontier.G87WDepthFourStepanovWeld.pairSumConcentration5_production
