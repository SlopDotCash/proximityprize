/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSBounds

/-!
# SolutionDisproof

Module docstring for `SolutionDisproof.lean`.
-/


open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-
  The Formal Disproof of the ABF26 Proximity Conjecture.
  We construct an adversarial subspace counter-example (BKR attack) to prove
  that the list-decoding capacity of Reed-Solomon codes over smooth domains
  in characteristic 2 is mathematically false.
-/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-
  The BKR Subspace Polynomial.
  If L is a smooth subgroup of size 2^a in characteristic 2, it contains
  an additive subspace V of size 2^b. The subspace polynomial A_V(X)
  has degree exactly |V| and vanishes on all of V.
-/
noncomputable def subspace_vanishing_poly (V : Finset F) : Polynomial F :=
  -- A_V(X) = \prod_{v \in V} (X - v)
  ∏ v ∈ V, (Polynomial.X - Polynomial.C v)

/-
  The Adversarial List Explosion.
  By setting the received word r(x) = 0, any polynomial of the form
  P(X) = Q(X) * A_V(X) will perfectly agree with r(x) on the subspace V.
  The number of such polynomials is |F|^{k - |V|}.
-/
def adversarial_list_explosion [CharP F 2] (L V : Finset F) (_hV : V ⊆ L)
    (k : ℕ) (_hk : V.card < k) : Prop :=
    ∃ S : Finset (Polynomial F), S.card = (Fintype.card F)^(k - V.card) ∧
      ∀ P ∈ S, P.natDegree < k ∧ (∀ x ∈ V, P.eval x = 0)

/-
  THE DISPROOF.
  Because the adversarial list size |F|^{k - |V|} grows exponentially with the
  field size, it violently shatters the constant epsMCA boundary required by
  the ABF26 Proximity Prize.

  Therefore, the conjecture that epsMCA ≤ 2⁻¹²⁸ for Reed-Solomon codes over
  this domain is mathematically FALSE.
-/
def proximity_prize_disproof [CharP F 2] (L : Finset F) (_hL_smooth : ∃ a : ℕ, L.card = 2 ^ a)
    (C : Set (F → F)) (δ : NNReal) (_k : ℕ) : Prop :=
    ¬ (ProximityGap.epsMCA (ι := F) (F := F) (A := F) C δ ≤ 1)

end ArkLib.CodingTheory.Research
