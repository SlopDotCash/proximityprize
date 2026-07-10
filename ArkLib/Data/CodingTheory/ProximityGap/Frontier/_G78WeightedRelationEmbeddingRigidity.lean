/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R366CenteredRelationAnomaly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R367SignedShadowPairDiscrepancy

/-!
# G78: weighted-relation embedding rigidity — the single-embedding qualifier has zero slack

Issue #505 asks for control of the single-embedding, first-incidence **weighted** relation mass
across distinct relation orbits.  The OC equidistribution file proved that **unweighted**
marginal vanishing counts of a Galois-stable pool agree at every primitive embedding, and
honestly recorded that this does not control the weighted mass.  R384 proved the abstract
generator-averaging double count, but its no-gain audit consumed a *hypothesis* of uniform
centered load across generators.

This file discharges that hypothesis concretely, at the full weighted relation structure.
The mechanism is a set-level rigidity: for any exponent `a` coprime to `n`, the concrete
power-root set of `g ^ a` is literally the same finset as that of `g`, because exponent
dilation by a unit permutes the residues mod `n`.  Feeding this through R312's exact
subtraction identity `C = rEnergy − B` (whose right-hand side depends on `g` only through the
power-root set and the embedding-free shadow data) yields, unconditionally and axiom-cleanly:

* `shadowCollisionMass (g ^ a) = shadowCollisionMass g` — the NR-weighted wraparound collision
  mass is identical at every primitive embedding;
* `relationAnomaly (g ^ a) = relationAnomaly g` — the centered signed cross-orbit anomaly is
  identical at every primitive embedding;
* `signedShadowPairDiscrepancy (g ^ a) = signedShadowPairDiscrepancy g` — likewise for the
  R367 signed pair form;
* `DCEnergyBound (powerRootSet (g ^ a) n) r ↔ DCEnergyBound (powerRootSet g n) r` — the G75
  budget target holds at one primitive embedding iff it holds at all of them.

Honest scope: this is a rigidity/no-slack localization, not a bound.  It proves that the
"single-embedding" qualifier in the #505 admissible surface is free — no primitive embedding
of the same subgroup is easier than another, so any admissible first-incidence route must
already work at the Galois average, which G75 calibrates to `DCEnergyBound`.  Combined with
OC (unweighted counts equal) and G76 (higher distinct-generator moments blind), the open
content of #505 is confirmed to sit entirely in the embedding-independent weighted
cross-orbit mass.  CORE remains OPEN.  Issue #466 / #505.
Target axiom set: `[propext, Classical.choice, Quot.sound]`; no `sorry`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly
open ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy

variable {F : Type*} [Field F]

/-- A residue coprime to an even modulus is odd. -/
theorem odd_of_coprime_of_even {a n m : ℕ} (hn : n = 2 * m)
    (ha : Nat.Coprime a n) : Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · exfalso
    have h2a : 2 ∣ a := he.two_dvd
    have h2n : 2 ∣ n := ⟨m, hn⟩
    have h2g : 2 ∣ Nat.gcd a n := Nat.dvd_gcd h2a h2n
    have hg1 : Nat.gcd a n = 1 := ha
    omega
  · exact ho

/-- A residue coprime to a modulus `> 1` is nonzero. -/
theorem ne_zero_of_coprime {a n : ℕ} (hn1 : 1 < n) (ha : Nat.Coprime a n) : a ≠ 0 := by
  intro h0
  have hg1 : Nat.gcd a n = 1 := ha
  rw [h0, Nat.gcd_zero_left] at hg1
  omega

/-- Frame transport: a coprime power of an exact-order-`n` generator has exact order `n`. -/
theorem orderOf_pow_coprime {g : F} {a n : ℕ} (hn1 : 1 < n) (hord : orderOf g = n)
    (ha : Nat.Coprime a n) : orderOf (g ^ a) = n := by
  have ha0 : a ≠ 0 := ne_zero_of_coprime hn1 ha
  have hgcd : Nat.gcd n a = 1 := Nat.Coprime.gcd_eq_one (Nat.Coprime.symm ha)
  rw [orderOf_pow' g ha0, hord, hgcd, Nat.div_one]

/-- Frame transport: a coprime power keeps the sign relation `(g ^ a) ^ m = -1`. -/
theorem pow_coprime_pow_m_eq_neg_one {g : F} {a n m : ℕ} (hn : n = 2 * m)
    (ha : Nat.Coprime a n) (hg : g ^ m = -1) : (g ^ a) ^ m = -1 := by
  have hodd : Odd a := odd_of_coprime_of_even hn ha
  rw [← pow_mul, mul_comm a m, pow_mul, hg]
  exact hodd.neg_one_pow

/-- **Set-level embedding rigidity.**  For `a` coprime to `n`, the first `n` powers of `g ^ a`
form the same finset as the first `n` powers of `g`: exponent dilation by a unit permutes the
residues mod `n`. -/
theorem powerRootSet_pow_eq [DecidableEq F] {g : F} {a n : ℕ} (hnpos : 0 < n)
    (hord : orderOf g = n) (ha : Nat.Coprime a n) :
    powerRootSet (g ^ a) n = powerRootSet g n := by
  classical
  haveI : NeZero n := ⟨hnpos.ne'⟩
  have hmodpow : ∀ k : ℕ, g ^ (k % n) = g ^ k := by
    intro k
    have h := pow_mod_orderOf g k
    rwa [hord] at h
  refine Finset.ext fun x => ?_
  unfold powerRootSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨(a * (i : ℕ)) % n, Nat.mod_lt _ hnpos⟩, ?_⟩
    show g ^ ((a * (i : ℕ)) % n) = (g ^ a) ^ (i : ℕ)
    rw [hmodpow (a * (i : ℕ)), pow_mul]
  · rintro ⟨j, rfl⟩
    have hunit : IsUnit ((a : ZMod n)) := (ZMod.isUnit_iff_coprime a n).mpr ha
    obtain ⟨u, hu⟩ := hunit
    set i : ℕ := (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (((j : ℕ) : ZMod n))).val with hi
    refine ⟨⟨i, ZMod.val_lt _⟩, ?_⟩
    show (g ^ a) ^ i = g ^ (j : ℕ)
    have hival : ((i : ℕ) : ZMod n) =
        ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (((j : ℕ) : ZMod n)) := by
      rw [hi, ZMod.natCast_val, ZMod.cast_id]
    have hcast : ((a * i : ℕ) : ZMod n) = (((j : ℕ) : ZMod n)) := by
      push_cast
      rw [hival, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    have hmodeq : (a * i) % n = (j : ℕ) % n :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    calc (g ^ a) ^ i = g ^ (a * i) := (pow_mul g a i).symm
      _ = g ^ ((a * i) % n) := (hmodpow (a * i)).symm
      _ = g ^ ((j : ℕ) % n) := by rw [hmodeq]
      _ = g ^ (j : ℕ) := by rw [Nat.mod_eq_of_lt j.isLt]

/-- **Weighted collision-mass rigidity.**  The NR-weighted wraparound collision mass is
identical at every primitive embedding of the same subgroup. -/
theorem shadowCollisionMass_pow_eq [Fintype F] [DecidableEq F]
    {g : F} {a n m r : ℕ} (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) (ha : Nat.Coprime a n) :
    shadowCollisionMass (g ^ a) n m r = shadowCollisionMass g n m r := by
  have hn1 : 1 < n := by omega
  have hnpos : 0 < n := by omega
  have hga0 : g ^ a ≠ 0 := pow_ne_zero _ hg0
  have hgaord : orderOf (g ^ a) = n := orderOf_pow_coprime hn1 hord ha
  have hgam : (g ^ a) ^ m = -1 := pow_coprime_pow_m_eq_neg_one hn ha hg
  rw [shadowCollisionMass_eq_rEnergy_sub_shadowEnergy_of_orderOf
      (g ^ a) n m r hga0 hgaord hm hn hgam,
    shadowCollisionMass_eq_rEnergy_sub_shadowEnergy_of_orderOf
      g n m r hg0 hord hm hn hg,
    powerRootSet_pow_eq hnpos hord ha]

/-- **Centered-anomaly rigidity.**  The signed cross-orbit relation anomaly — the exact open
object of issue #505 — is identical at every primitive embedding. -/
theorem relationAnomaly_pow_eq [Fintype F] [DecidableEq F]
    {g : F} {a n m r : ℕ} (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) (ha : Nat.Coprime a n) :
    relationAnomaly (g ^ a) n m r = relationAnomaly g n m r := by
  unfold relationAnomaly
  rw [shadowCollisionMass_pow_eq hg0 hord hm hn hg ha]

/-- **Signed pair-discrepancy rigidity** (R367 form). -/
theorem signedShadowPairDiscrepancy_pow_eq [Fintype F] [DecidableEq F]
    {g : F} {a n m r : ℕ} (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) (ha : Nat.Coprime a n) :
    signedShadowPairDiscrepancy (g ^ a) n m r = signedShadowPairDiscrepancy g n m r := by
  rw [signedShadowPairDiscrepancy_eq_relationAnomaly,
    signedShadowPairDiscrepancy_eq_relationAnomaly]
  exact relationAnomaly_pow_eq hg0 hord hm hn hg ha

/-- **Budget-target rigidity.**  Any anomaly budget of the G75 shape (a function of the
embedding-free data `n, m, r` and the field size only) is met at one primitive embedding iff
it is met at all of them. -/
theorem relationAnomaly_le_iff_pow [Fintype F] [DecidableEq F]
    {g : F} {a n m r : ℕ} (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) (ha : Nat.Coprime a n) (W : ℝ) :
    relationAnomaly (g ^ a) n m r ≤ W ↔ relationAnomaly g n m r ≤ W := by
  rw [relationAnomaly_pow_eq hg0 hord hm hn hg ha]

/-- **DC-target rigidity.**  The threshold-consumer predicate `DCEnergyBound` at the
power-root set of `g ^ a` is literally the same statement as at `g`. -/
theorem dcEnergyBound_pow_iff [Fintype F] [DecidableEq F]
    {g : F} {a n r : ℕ} (hnpos : 0 < n) (hord : orderOf g = n) (ha : Nat.Coprime a n) :
    DCEnergyBound (powerRootSet (g ^ a) n) r ↔ DCEnergyBound (powerRootSet g n) r := by
  rw [powerRootSet_pow_eq hnpos hord ha]

end ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity.powerRootSet_pow_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity.shadowCollisionMass_pow_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity.relationAnomaly_pow_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity.signedShadowPairDiscrepancy_pow_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity.relationAnomaly_le_iff_pow
#print axioms
  ArkLib.ProximityGap.Frontier.G78WeightedRelationEmbeddingRigidity.dcEnergyBound_pow_iff
