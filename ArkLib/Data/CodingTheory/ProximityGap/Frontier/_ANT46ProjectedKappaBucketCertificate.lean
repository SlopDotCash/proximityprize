/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ANT46KappaProductionReduction

/-!
# Exact bucket certificates for the projected ANT46 kappa map

The production reduction leaves an exact finite question: on the `2^29` nontrivial inversion
classes of the subgroup of order `n = 2^30`, are the projected values

`((x - 1)^n)^e`

pairwise distinct?  The two selected projections land in prime-order groups of respectively 59
and 67 bits.  This file gives a deterministic certificate format for that question.

* Cover the representative inputs by lists indexed by buckets.
* Check that the projected-value list in each bucket is `Nodup`.
* Check that value lists belonging to different buckets are disjoint.

These checks imply injectivity on the whole representative set, and hence projected injectivity
modulo inversion.  A keyed variant assigns an input to the bucket `key(value)`; in that format
cross-bucket disjointness is automatic and only per-bucket `Nodup` remains.

The certificate is exact but not compressed.  Any covering family contains at least one row entry
per input.  At production scale this is `536870912` entries.  Storing one canonical 159/160-bit
field representative per entry takes ten GiB before indices or framing.  Choosing `2^20` buckets
only changes the working-set geometry to an average of 512 entries per bucket; it does not reduce
the number of projected evaluations.  A direct square-and-multiply pass uses a 100-bit exponent
at the first prime and a 93-bit exponent at the second prime.  The birthday ratios are favorable
(`3 * C(2^29,2) < r_1 < 4 * C(2^29,2)` and
`626 * C(2^29,2) < r_2 < 627 * C(2^29,2)`), but those are heuristics for collision rarity, not an
injectivity proof.

A single scalar product/fingerprint cannot replace the `Nodup` checks: over `ZMod 7`, the nodup
list `[1,4]` and the duplicate list `[2,2]` have the same product.  A full product polynomial does
encode the multiset exactly, but already has `2^29 + 1` coefficients.  Recursive product trees
therefore reorganize the same linear-scale exact work unless an additional non-algebraic or
probabilistic proof system is introduced.  Issue #466.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate

open ANT46KappaProductionReduction
open ANT46RungTwoAccidentOrbit

/-! ## Generic exact bucket certificates -/

variable {I B V : Type*}

/-- All rows concatenated in the canonical `Fintype` bucket order.  This is used only to state the
honest size lower bound; the injectivity theorem does not depend on a bucket ordering. -/
noncomputable def flattenedRows [Fintype B] [DecidableEq B] (rows : B → List I) : List I :=
  (Finset.univ.toList).flatMap rows

/-- Per-bucket nodup plus pairwise disjoint value ranges gives global injectivity on every covered
input.  Rows may contain extra inputs and may overlap as input lists; only value separation matters. -/
theorem injOn_of_bucket_value_nodup_and_disjoint
    [DecidableEq V] (T : Set I) (f : I → V) (rows : B → List I)
    (hcover : ∀ x, x ∈ T → ∃ b, x ∈ rows b)
    (hnodup : ∀ b, ((rows b).map f).Nodup)
    (hdisjoint : ∀ b c, b ≠ c →
      List.Disjoint ((rows b).map f) ((rows c).map f)) :
    Set.InjOn f T := by
  intro x hx y hy hxy
  obtain ⟨b, hxb⟩ := hcover x hx
  obtain ⟨c, hyc⟩ := hcover y hy
  by_cases hbc : b = c
  · subst c
    exact List.inj_on_of_nodup_map (hnodup b) hxb hyc hxy
  · have hfx : f x ∈ (rows b).map f := List.mem_map.mpr ⟨x, hxb, rfl⟩
    have hfy : f y ∈ (rows c).map f := List.mem_map.mpr ⟨y, hyc, rfl⟩
    have hnot := (List.disjoint_left.mp (hdisjoint b c hbc)) hfx
    exact (hnot (hxy ▸ hfy)).elim

/-- If the bucket is a deterministic function of the value, equality of values already forces
equality of bucket labels.  Thus exact per-bucket `Nodup` is the only remaining check. -/
theorem injective_of_keyed_bucket_nodup
    [DecidableEq V] (f : I → V) (key : V → B) (rows : B → List I)
    (hplaced : ∀ x, x ∈ rows (key (f x)))
    (hnodup : ∀ b, ((rows b).map f).Nodup) :
    Function.Injective f := by
  intro x y hxy
  apply List.inj_on_of_nodup_map (hnodup (key (f x)))
  · exact hplaced x
  · simpa [hxy] using hplaced y
  · exact hxy

/-- A flat exact bucket cover cannot contain fewer entries than the finite input type.  This is
the precise sense in which the certificate format reorganizes, but does not compress, evaluation. -/
theorem card_le_flattenedRows_length_of_cover
    [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    (rows : B → List I) (hcover : ∀ x : I, ∃ b, x ∈ rows b) :
    Fintype.card I ≤ (flattenedRows rows).length := by
  have hsubset : (Finset.univ : Finset I) ⊆ (flattenedRows rows).toFinset := by
    intro x _
    obtain ⟨b, hxb⟩ := hcover x
    simp only [List.mem_toFinset, flattenedRows, List.mem_flatMap,
      Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨b, hxb⟩
  calc
    Fintype.card I = (Finset.univ : Finset I).card := by simp
    _ ≤ (flattenedRows rows).toFinset.card := Finset.card_le_card hsubset
    _ ≤ (flattenedRows rows).length := by
      simpa using (List.toFinset_card_le (l := flattenedRows rows))

/-! ## From representative buckets to projected injectivity modulo inversion -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- Power projection preserves the inversion symmetry of the even ANT46 signature. -/
theorem projectedDifferenceSignature_inv_of_even {n e : Nat} (hn : Even n)
    (x : F) (hx : x ≠ 0) (hpow : x ^ n = 1) :
    projectedDifferenceSignature n e x⁻¹ = projectedDifferenceSignature n e x := by
  exact congrArg (fun z : F => z ^ e)
    (differenceSignature_inv_of_even hn x hx hpow)

/-- Injectivity of the projected map on the self class together with an inversion transversal
implies projected injectivity on the whole subgroup. -/
theorem projectedDifferenceSignatureInjectiveModInversion_of_transversal_injOn
    {H S : Finset F} {n e : Nat} {self : F}
    (hnpos : 0 < n) (hneven : Even n)
    (hpow : ∀ x ∈ H, x ^ n = 1)
    (htrans : IsInversionTransversal H S self)
    (hinj : Set.InjOn (projectedDifferenceSignature n e)
      (↑(insert self S) : Set F)) :
    ProjectedDifferenceSignatureInjectiveModInversion H n e := by
  rcases htrans with ⟨hselfH, _hself1, _hselfInv, hSH, _hnoInvDup, hcover⟩
  intro x hxH hx1 y hyH hy1 hxy
  have signature_inv (z : F) (hzH : z ∈ H) :
      projectedDifferenceSignature n e z⁻¹ = projectedDifferenceSignature n e z := by
    have hzpow := hpow z hzH
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      simpa [zero_pow hnpos.ne'] using hzpow
    exact projectedDifferenceSignature_inv_of_even hneven z hz0 hzpow
  have signature_of_representative (z a : F) (haS : a ∈ S)
      (hza : z = a ∨ z = a⁻¹) :
      projectedDifferenceSignature n e z = projectedDifferenceSignature n e a := by
    rcases hza with hza | hza
    · exact congrArg (projectedDifferenceSignature n e) hza
    · exact (congrArg (projectedDifferenceSignature n e) hza).trans
        (signature_inv a (hSH a haS).1)
  have self_mem : self ∈ (↑(insert self S) : Set F) := by simp
  have rep_mem (a : F) (haS : a ∈ S) : a ∈ (↑(insert self S) : Set F) := by
    simp [haS]
  rcases hcover x hxH hx1 with hxself | ⟨a, haS, hxa⟩
  · rcases hcover y hyH hy1 with hyself | ⟨b, hbS, hyb⟩
    · exact Or.inl (hyself.trans hxself.symm)
    · have hybSig := signature_of_representative y b hbS hyb
      have hselfb : self = b := hinj self_mem (rep_mem b hbS)
        ((congrArg (projectedDifferenceSignature n e) hxself).symm.trans
          (hxy.trans hybSig))
      exact ((hSH b hbS).2.2 hselfb.symm).elim
  · rcases hcover y hyH hy1 with hyself | ⟨b, hbS, hyb⟩
    · have hxaSig := signature_of_representative x a haS hxa
      have haself : a = self := hinj (rep_mem a haS) self_mem
        (hxaSig.symm.trans (hxy.trans (congrArg (projectedDifferenceSignature n e) hyself)))
      exact ((hSH a haS).2.2 haself).elim
    · have hxaSig := signature_of_representative x a haS hxa
      have hybSig := signature_of_representative y b hbS hyb
      have hab : a = b := hinj (rep_mem a haS) (rep_mem b hbS)
        (hxaSig.symm.trans (hxy.trans hybSig))
      rcases hxa with hxa | hxa <;> rcases hyb with hyb | hyb
      · exact Or.inl (hyb.trans (hab.symm.trans hxa.symm))
      · apply Or.inr
        exact hyb.trans (congrArg Inv.inv (hab.symm.trans hxa.symm))
      · apply Or.inr
        calc
          y = b := hyb
          _ = a := hab.symm
          _ = (a⁻¹)⁻¹ := (inv_inv a).symm
          _ = x⁻¹ := (congrArg Inv.inv hxa).symm
      · exact Or.inl (hyb.trans ((congrArg Inv.inv hab.symm).trans hxa.symm))

/-- The complete exact bucket adapter: local nodup and cross-bucket range separation on an
inversion transversal discharge the projected ANT46 socket. -/
theorem projectedDifferenceSignatureInjectiveModInversion_of_bucketCertificate
    {H S : Finset F} {n e : Nat} {self : F}
    [DecidableEq B] (rows : B → List F)
    (hnpos : 0 < n) (hneven : Even n)
    (hpow : ∀ x ∈ H, x ^ n = 1)
    (htrans : IsInversionTransversal H S self)
    (hcover : ∀ x ∈ insert self S, ∃ b, x ∈ rows b)
    (hnodup : ∀ b,
      ((rows b).map (projectedDifferenceSignature n e)).Nodup)
    (hdisjoint : ∀ b c, b ≠ c →
      List.Disjoint
        ((rows b).map (projectedDifferenceSignature n e))
        ((rows c).map (projectedDifferenceSignature n e))) :
    ProjectedDifferenceSignatureInjectiveModInversion H n e := by
  apply projectedDifferenceSignatureInjectiveModInversion_of_transversal_injOn
    hnpos hneven hpow htrans
  exact injOn_of_bucket_value_nodup_and_disjoint
    (insert self S : Finset F) (projectedDifferenceSignature n e) rows hcover hnodup hdisjoint

/-! ## A natural modular evaluator for checkable production tables -/

/-- Fuelled square-and-multiply in natural numbers modulo `p`. -/
def powModAux (p a n : Nat) : Nat -> Nat
  | 0 => 1 % p
  | fuel + 1 =>
      if n = 0 then 1 % p
      else if n % 2 = 0 then powModAux p ((a * a) % p) (n / 2) fuel
      else (a * powModAux p ((a * a) % p) (n / 2) fuel) % p

/-- Kernel-cheap natural modular exponentiation. -/
def powMod (p a n : Nat) : Nat := powModAux p a n (n + 1)

theorem powModAux_lt (p a n fuel : Nat) (hp : 0 < p) : powModAux p a n fuel < p := by
  cases fuel <;> simp only [powModAux]
  · exact Nat.mod_lt _ hp
  · split_ifs
    · exact Nat.mod_lt _ hp
    · exact powModAux_lt _ _ _ _ hp
    · exact Nat.mod_lt _ hp
termination_by fuel

theorem powMod_lt (p a n : Nat) (hp : 0 < p) : powMod p a n < p :=
  powModAux_lt p a n (n + 1) hp

/-- The natural evaluator agrees with exponentiation in `ZMod p`. -/
theorem natCast_powModAux_eq_pow (p a n fuel : Nat) (hnfuel : n < fuel) :
    ((powModAux p a n fuel : Nat) : ZMod p) = (a : ZMod p) ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [powModAux]
      split_ifs with hzero heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih ((a * a) % p) (n / 2) hhalf, ZMod.natCast_mod,
          Nat.cast_mul, <- pow_two, <- pow_mul]
        have hdvd : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr heven
        congr 1
        exact Nat.mul_div_cancel' hdvd
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ZMod.natCast_mod, Nat.cast_mul,
          ih ((a * a) % p) (n / 2) hhalf, ZMod.natCast_mod,
          Nat.cast_mul, <- pow_two, <- pow_mul, <- pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

theorem natCast_powMod (p a n : Nat) :
    ((powMod p a n : Nat) : ZMod p) = (a : ZMod p) ^ n :=
  natCast_powModAux_eq_pow p a n (n + 1) (by omega)

/-- Natural subtraction by one modulo `p`. -/
def subOneMod (p a : Nat) : Nat := (a + p - 1) % p

theorem natCast_subOneMod (p a : Nat) (hp : 0 < p) :
    ((subOneMod p a : Nat) : ZMod p) = (a : ZMod p) - 1 := by
  rw [subOneMod, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add,
    ZMod.natCast_self]
  simp

/-! ## Production tables, arithmetic scale, and exact adapters -/

abbrev productionInputCount : Nat := productionN / 2
abbrev productionBucketCount : Nat := 2 ^ 20
abbrev productionBucketAverage : Nat := 512

local instance firstPrimeFact : Fact (Nat.Prime firstP) :=
  ⟨PrizeShapePrimeP30.prime_P⟩

local instance secondPrimeFact : Fact (Nat.Prime secondP) :=
  ⟨PrizeShapePrimeP30Second.prime_P⟩

/-- Canonical natural evaluator for the first-prime projected table, indexed by exponent
`a = i+1` and therefore including the self-inverse class at the last index. -/
def firstProjectedTableNat (i : Fin productionInputCount) : Nat :=
  powMod firstP
    (subOneMod firstP (powMod firstP PrizeShapePrimeP30.g.val (i.val + 1)))
    firstProjectedExponent

/-- The corresponding second-prime table. -/
def secondProjectedTableNat (i : Fin productionInputCount) : Nat :=
  powMod secondP
    (subOneMod secondP (powMod secondP PrizeShapePrimeP30Second.g.val (i.val + 1)))
    secondProjectedExponent

theorem firstProjectedTableNat_lt (i : Fin productionInputCount) :
    firstProjectedTableNat i < firstP := by
  exact powMod_lt _ _ _ (by norm_num [firstP, PrizeShapePrimeP30.P])

theorem secondProjectedTableNat_lt (i : Fin productionInputCount) :
    secondProjectedTableNat i < secondP := by
  exact powMod_lt _ _ _ (by norm_num [secondP, PrizeShapePrimeP30Second.P])

/-- The natural first-prime table is exactly the projected field table. -/
theorem firstProjectedTableNat_cast (i : Fin productionInputCount) :
    (firstProjectedTableNat i : ZMod firstP) =
      projectedDifferenceSignature productionN firstProjectionPower
        (PrizeShapePrimeP30.g ^ (i.val + 1)) := by
  rw [firstProjectedTableNat, natCast_powMod, natCast_subOneMod _ _
    (by norm_num [firstP, PrizeShapePrimeP30.P]), natCast_powMod]
  simp only [ZMod.natCast_zmod_val]
  rw [projectedDifferenceSignature, differenceSignature, <- pow_mul,
    first_projection_exact_shape.2]

/-- The natural second-prime table is exactly the projected field table. -/
theorem secondProjectedTableNat_cast (i : Fin productionInputCount) :
    (secondProjectedTableNat i : ZMod secondP) =
      projectedDifferenceSignature productionN secondProjectionPower
        (PrizeShapePrimeP30Second.g ^ (i.val + 1)) := by
  rw [secondProjectedTableNat, natCast_powMod, natCast_subOneMod _ _
    (by norm_num [secondP, PrizeShapePrimeP30Second.P]), natCast_powMod]
  simp only [ZMod.natCast_zmod_val]
  rw [projectedDifferenceSignature, differenceSignature, <- pow_mul,
    second_projection_exact_shape.2]

/-- A checked keyed bucket table of natural representatives proves injectivity of the actual
first-prime projected field table. -/
theorem firstProjectedTable_injective_of_keyed_bucket_nodup
    [Fintype B] [DecidableEq B] (key : Nat → B)
    (rows : B → List (Fin productionInputCount))
    (hplaced : ∀ i, i ∈ rows (key (firstProjectedTableNat i)))
    (hnodup : ∀ b, ((rows b).map firstProjectedTableNat).Nodup) :
    Function.Injective (fun i : Fin productionInputCount =>
      projectedDifferenceSignature productionN firstProjectionPower
        (PrizeShapePrimeP30.g ^ (i.val + 1))) := by
  have hnat : Function.Injective firstProjectedTableNat :=
    injective_of_keyed_bucket_nodup firstProjectedTableNat key rows hplaced hnodup
  intro i j hij
  change projectedDifferenceSignature productionN firstProjectionPower
      (PrizeShapePrimeP30.g ^ (i.val + 1)) =
    projectedDifferenceSignature productionN firstProjectionPower
      (PrizeShapePrimeP30.g ^ (j.val + 1)) at hij
  rw [<- firstProjectedTableNat_cast, <- firstProjectedTableNat_cast] at hij
  apply hnat
  have hval := congrArg ZMod.val hij
  rw [ZMod.val_natCast_of_lt (firstProjectedTableNat_lt i),
    ZMod.val_natCast_of_lt (firstProjectedTableNat_lt j)] at hval
  exact hval

/-- The same exact keyed-bucket adapter for the second production prime. -/
theorem secondProjectedTable_injective_of_keyed_bucket_nodup
    [Fintype B] [DecidableEq B] (key : Nat → B)
    (rows : B → List (Fin productionInputCount))
    (hplaced : ∀ i, i ∈ rows (key (secondProjectedTableNat i)))
    (hnodup : ∀ b, ((rows b).map secondProjectedTableNat).Nodup) :
    Function.Injective (fun i : Fin productionInputCount =>
      projectedDifferenceSignature productionN secondProjectionPower
        (PrizeShapePrimeP30Second.g ^ (i.val + 1))) := by
  have hnat : Function.Injective secondProjectedTableNat :=
    injective_of_keyed_bucket_nodup secondProjectedTableNat key rows hplaced hnodup
  intro i j hij
  change projectedDifferenceSignature productionN secondProjectionPower
      (PrizeShapePrimeP30Second.g ^ (i.val + 1)) =
    projectedDifferenceSignature productionN secondProjectionPower
      (PrizeShapePrimeP30Second.g ^ (j.val + 1)) at hij
  rw [<- secondProjectedTableNat_cast, <- secondProjectedTableNat_cast] at hij
  apply hnat
  have hval := congrArg ZMod.val hij
  rw [ZMod.val_natCast_of_lt (secondProjectedTableNat_lt i),
    ZMod.val_natCast_of_lt (secondProjectedTableNat_lt j)] at hval
  exact hval

/-- Exact input, storage, bucket, bit-length, and birthday-scale arithmetic. -/
theorem production_bucket_certificate_dimensions :
    productionInputCount = 536870912 ∧
      productionInputCount * (productionInputCount - 1) / 2 = 144115187807420416 ∧
      productionBucketCount * productionBucketAverage = productionInputCount ∧
      productionInputCount * 20 = 10 * 2 ^ 30 ∧
      2 ^ 58 < firstProjectionOrder ∧ firstProjectionOrder < 2 ^ 59 ∧
      2 ^ 66 < secondProjectionOrder ∧ secondProjectionOrder < 2 ^ 67 ∧
      2 ^ 99 < firstProjectedExponent ∧ firstProjectedExponent < 2 ^ 100 ∧
      2 ^ 92 < secondProjectedExponent ∧ secondProjectedExponent < 2 ^ 93 := by
  norm_num [productionInputCount, productionN, productionBucketCount,
    productionBucketAverage, firstProjectionOrder, secondProjectionOrder,
    firstProjectedExponent, secondProjectedExponent]

/-- The first projected group is only about three birthday-pair counts across. -/
theorem first_projection_birthday_ratio :
    3 * (productionInputCount * (productionInputCount - 1) / 2) <
        firstProjectionOrder ∧
      firstProjectionOrder <
        4 * (productionInputCount * (productionInputCount - 1) / 2) := by
  norm_num [productionInputCount, productionN, firstProjectionOrder]

/-- The second projected group is about 626 birthday-pair counts across. -/
theorem second_projection_birthday_ratio :
    626 * (productionInputCount * (productionInputCount - 1) / 2) <
        secondProjectionOrder ∧
      secondProjectionOrder <
        627 * (productionInputCount * (productionInputCount - 1) / 2) := by
  norm_num [productionInputCount, productionN, secondProjectionOrder]

/-- Every explicit production bucket cover contains at least `536870912` input entries. -/
theorem production_bucket_cover_length_lower_bound
    [Fintype B] [DecidableEq B]
    (rows : B → List (Fin productionInputCount))
    (hcover : ∀ i : Fin productionInputCount, ∃ b, i ∈ rows b) :
    536870912 ≤ (flattenedRows rows).length := by
  have hlinear := card_le_flattenedRows_length_of_cover rows hcover
  simpa [productionInputCount, productionN] using hlinear

/-- A single scalar product does not certify nodup, even in a prime field. -/
theorem scalar_product_fingerprint_not_nodup_certificate :
    List.prod ([(1 : ZMod 7), 4]) = List.prod ([(2 : ZMod 7), 2]) ∧
      ([(1 : ZMod 7), 4]).Nodup ∧ ¬ ([(2 : ZMod 7), 2]).Nodup := by
  decide

end ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate.injOn_of_bucket_value_nodup_and_disjoint
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate.projectedDifferenceSignatureInjectiveModInversion_of_bucketCertificate
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate.natCast_powMod
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate.firstProjectedTableNat_cast
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate.firstProjectedTable_injective_of_keyed_bucket_nodup
#print axioms ArkLib.ProximityGap.Frontier.ANT46ProjectedKappaBucketCertificate.production_bucket_certificate_dimensions
