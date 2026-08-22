/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G173PrimitiveTransferThresholdRefuted

/-!
# G179: Galois times rotation does not amplify a fixed-root wraparound relation

G173 exhibits the characteristic-`p` relation

`ω^8 + ω^13 - ω^14 - ω^20 = 0`

at a primitive 64th root `ω` modulo `p = 17318209`.  Its cyclotomic conjugates suggest a tempting
extra factor `φ(64)=32` beyond the known rotation orbit: act on exponents by
`e ↦ a e + b`, with `a` odd and `b` arbitrary.

The exact fixed-root audit below shows that this factor is illusory.  Among all
`φ(64) * 64 = 2048` affine transforms, exactly the 64 pure rotations (`a=1`) vanish at the chosen
root.  Every nontrivial Galois multiplier moves the relation to a different split prime embedding;
it preserves the cyclotomic norm certificate, not evaluation at the deployed root.

This is the concrete fixed-root form of the FS15--FS18 quantifier obstruction.  Galois closure can
amplify an almost-all-prime/resultant census, but it cannot amplify relation mass in one deployed
field.  The weighted-kernel consumer therefore retains the single rotation factor `n`, exactly as
G59's free-orbit delimiter states; there is no hidden `n φ(n)` packet gain.

Honest scope: this is an exact no-go for the proposed combined-affine amplification, proved on the
first known polynomial-threshold counterexample.  It does not bound the number or total weight of
unrelated primitive wraparound orbits at either production prime, and it does not prove CORE.
Issue #466.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.G179AffineFixedRootCollapse

open ArkLib.ProximityGap.Frontier.G173PrimitiveTransferThresholdRefuted

local instance fact_prime_17318209 : Fact (Nat.Prime 17318209) := ⟨by norm_num⟩

abbrev F := ZMod 17318209
abbrev ω : F := 7937154

/-- Evaluation at `ω` of the affine transform `e ↦ a e + b` of the G173 relation. -/
def affineRelationValue (a b : Fin 64) : F :=
  ω ^ ((a.val * 8 + b.val) % 64) + ω ^ ((a.val * 13 + b.val) % 64) -
    ω ^ ((a.val * 14 + b.val) % 64) - ω ^ ((a.val * 20 + b.val) % 64)

/-- The odd exponent multipliers, i.e. `(Z/64Z)ˣ`, represented inside `Fin 64`. -/
def unitMultipliers : Finset (Fin 64) :=
  Finset.univ.filter fun a => Nat.Coprime a.val 64

/-- All `φ(64) * 64` affine exponent transforms. -/
def affinePairs : Finset (Fin 64 × Fin 64) :=
  unitMultipliers ×ˢ Finset.univ

/-- Affine transforms which still vanish at the fixed deployed root `ω`. -/
def fixedRootVanishingPairs : Finset (Fin 64 × Fin 64) :=
  affinePairs.filter fun ab => affineRelationValue ab.1 ab.2 = 0

/-- The pure rotation packet (`a=1`). -/
def pureRotationPairs : Finset (Fin 64 × Fin 64) :=
  Finset.univ.image fun b : Fin 64 => (⟨1, by norm_num⟩, b)

/-- There are 2048 affine candidates before imposing fixed-root evaluation. -/
theorem affinePairs_card : affinePairs.card = 2048 := by decide

/-- **Exact fixed-root collapse.** The only affine transforms vanishing at `ω` are
pure rotations. -/
theorem fixedRootVanishingPairs_eq_pureRotationPairs :
    fixedRootVanishingPairs = pureRotationPairs := by decide

/-- Consequently the fixed-root packet has cardinality exactly 64, not 2048. -/
theorem fixedRootVanishingPairs_card : fixedRootVanishingPairs.card = 64 := by decide

/-- The apparent Galois factor is exactly 32, and all of it disappears after fixing the root. -/
theorem affine_card_eq_thirtyTwo_mul_fixed_card :
    affinePairs.card = 32 * fixedRootVanishingPairs.card := by
  rw [affinePairs_card, fixedRootVanishingPairs_card]

#print axioms affinePairs_card
#print axioms fixedRootVanishingPairs_eq_pureRotationPairs
#print axioms fixedRootVanishingPairs_card
#print axioms affine_card_eq_thirtyTwo_mul_fixed_card

end ArkLib.ProximityGap.Frontier.G179AffineFixedRootCollapse
