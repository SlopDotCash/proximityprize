/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKPrimitiveDepthSevenSparseCodeNoGo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS16SharpResultantEnvelope

/-!
# The sharp folded alphabet of primitive depth-seven collisions

Folding an injective seven-subset through `g^m = -1` is substantially sharper than the
previous height-`14` socket.  At one folded coordinate, each side can use the positive root and
its antipode at most once, so its signed coefficient lies in `{-1,0,1}`.  The difference of two
sides therefore lies in the sharp alphabet `{-2,-1,0,1,2}`.  This file proves that statement
without discarding the actual source tuples.  Together with the existing endpoint estimate it
gives, for every genuine primitive witness,

* coefficient alphabet `[-2,2]`;
* support at most `14`;
* `l1` mass at most `14`;
* a nonzero degree-`<m` polynomial vanishing at the field root.

The height `2` cannot be lowered.  An exact order-`16` countermodel in `ZMod 17` consists of the
globally disjoint seven-subsets

`A = {0,1,2,3,4,5,6}` and `B = {7,9,11,12,13,14,15}`

of exponent indices for `g=3`.  Their sums agree, while their folded relation is
`[1,2,1,2,2,2,2,0]`.  Thus even the sharp alphabet, global disjointness, power-of-two order, and
nonzero characteristic-zero label do not imply kernel-freeness.  Any production proof must use
arithmetic special to the two certified production primes, or an average/counting theorem rather
than a universal alphabet obstruction.

The source fibers have an exact bivariate local law: `w_{±2}=xy`, `w_{±1}=x+y`, and
`w_0=1+x²+y²`.  Its global occupancy identity is `2A+B+2Z=14`, so the number `B` of unit
letters is even and the number of occupied folded coordinates is exactly `7+B/2`.  The unique
degree-`14` sector therefore consists of fourteen distinct unit letters, with formal fiber
multiplicity `(7!)² choose(14,7)=14!` per fixed signed label; every antipodal/folded coincidence
loses at least one coordinate degree.  This isolates the dominant residual to sparse `±1` kernel
relations, but does not bound the exceptional sector inside the much rarer collision event without
an additional equidistribution estimate.

Finally, the file records the exact arithmetic target: the alphabet-sensitive argument must remove
`8264` of the Wick coefficient `135135`, strictly between `6.115%` and `6.116%`.  The sharp
resultant envelope still has base `14`, because it sees coefficient mass rather than height, so
the alphabet improvement alone does not strengthen that norm bound.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.BGKPrimitiveFoldedAlphabet

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R379SparseOrbitSupportBound
open ArkLib.ProximityGap.Frontier.R390RelationResultantCertificate
open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant
open ArkLib.ProximityGap.Frontier.FS16SharpResultantEnvelope
open ArkLib.ProximityGap.Frontier.BGKPrimitiveDepthSevenSparseCodeNoGo

/-! ## Injective tuples have ternary folded coefficients -/

/-- The sharp five-letter folded alphabet. -/
def InFoldedAlphabet {m : Nat} (d : Fin m -> Int) : Prop :=
  forall j, -2 <= d j ∧ d j <= 2

/-- An injective tuple remains injective after decoding the two signed halves. -/
theorem decodeSignedTuple_injective {m L : Nat} (t : Fin L -> Fin (2 * m))
    (ht : Function.Injective t) :
    Function.Injective (decodeSignedTuple t) := by
  intro i k hik
  apply ht
  have h := congrArg (signedIndexEquiv m) hik
  simpa [decodeSignedTuple] using h

/-- The multiplicity multiset of an injective tuple is duplicate-free. -/
theorem tupleMultiset_nodup_of_injective {A : Type*} {L : Nat}
    (t : Fin L -> A) (ht : Function.Injective t) :
    (tupleMultiset t).Nodup := by
  simpa [tupleMultiset] using (List.nodup_ofFn.mpr ht)

/-- Hence every signed root occurs at most once in an injective tuple. -/
theorem decoded_count_le_one {m L : Nat} (t : Fin L -> Fin (2 * m))
    (ht : Function.Injective t) (x : Fin m × Fin 2) :
    (tupleMultiset (decodeSignedTuple t)).count x <= 1 := by
  exact Multiset.nodup_iff_count_le_one.mp
    (tupleMultiset_nodup_of_injective _ (decodeSignedTuple_injective t ht)) x

/-- One injective tuple has a ternary folded coefficient at every coordinate. -/
theorem tupleVec_of_injective_mem_ternary {m L : Nat}
    (t : Fin L -> Fin (2 * m)) (ht : Function.Injective t) (j : Fin m) :
    -1 <= tupleVec (2 * m) m L t j ∧ tupleVec (2 * m) m L t j <= 1 := by
  have hformula := congrFun
    (tupleVec_encodeSignedTuple_eq_counts (decodeSignedTuple t)) j
  simp only [encodeSignedTuple_decodeSignedTuple] at hformula
  have hp := decoded_count_le_one t ht (j, 0)
  have hn := decoded_count_le_one t ht (j, 1)
  rw [hformula]
  omega

/-- **Sharp alphabet theorem.**  The folded difference of two injective tuples has every
coefficient in `{-2,-1,0,1,2}`.  Global disjointness is not needed for this pointwise bound. -/
theorem depthSevenRelation_mem_foldedAlphabet_of_injective {m : Nat}
    (a b : Fin 7 -> Fin (2 * m))
    (ha : Function.Injective a) (hb : Function.Injective b) :
    InFoldedAlphabet (depthSevenRelation m a b) := by
  intro j
  have hA := tupleVec_of_injective_mem_ternary a ha j
  have hB := tupleVec_of_injective_mem_ternary b hb j
  unfold depthSevenRelation
  omega

/-- Every globally-disjoint primitive source pair lies in the sharp five-letter alphabet. -/
theorem depthSevenRelation_mem_foldedAlphabet_of_globallyDisjoint {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) :
    InFoldedAlphabet (depthSevenRelation m a b) :=
  depthSevenRelation_mem_foldedAlphabet_of_injective a b h.1 h.2.1

/-! ## Exact local source profiles behind the five letters -/

/-- Multiplicity of one signed root in a tuple. -/
def signedMultiplicity {m L : Nat} (t : Fin L -> Fin (2 * m))
    (j : Fin m) (e : Fin 2) : Nat :=
  (tupleMultiset (decodeSignedTuple t)).count (j, e)

theorem mem_tupleMultiset_iff {A : Type*} {L : Nat} [DecidableEq A]
    (t : Fin L -> A) (x : A) :
    x ∈ tupleMultiset t ↔ ∃ i, t i = x := by
  simp [tupleMultiset]

theorem signedMultiplicity_le_one_of_injective {m L : Nat}
    (t : Fin L -> Fin (2 * m)) (ht : Function.Injective t)
    (j : Fin m) (e : Fin 2) :
    signedMultiplicity t j e <= 1 := by
  exact decoded_count_le_one t ht (j, e)

/-- Global disjointness says that one literal signed root occurs on at most one side. -/
theorem signedMultiplicity_add_le_one_of_globallyDisjoint {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b)
    (j : Fin m) (e : Fin 2) :
    signedMultiplicity a j e + signedMultiplicity b j e <= 1 := by
  have ha1 := signedMultiplicity_le_one_of_injective a h.1 j e
  have hb1 := signedMultiplicity_le_one_of_injective b h.2.1 j e
  by_contra hnot
  have haPos : 0 < signedMultiplicity a j e := by omega
  have hbPos : 0 < signedMultiplicity b j e := by omega
  have haMem : (j, e) ∈ tupleMultiset (decodeSignedTuple a) :=
    Multiset.count_pos.mp haPos
  have hbMem : (j, e) ∈ tupleMultiset (decodeSignedTuple b) :=
    Multiset.count_pos.mp hbPos
  obtain ⟨i, hi⟩ := (mem_tupleMultiset_iff (decodeSignedTuple a) (j, e)).mp haMem
  obtain ⟨k, hk⟩ := (mem_tupleMultiset_iff (decodeSignedTuple b) (j, e)).mp hbMem
  have hai : a i = signedIndexEquiv m (j, e) := by
    have hi' := congrArg (signedIndexEquiv m) hi
    simpa [decodeSignedTuple] using hi'
  have hbk : b k = signedIndexEquiv m (j, e) := by
    have hk' := congrArg (signedIndexEquiv m) hk
    simpa [decodeSignedTuple] using hk'
  have haImage : signedIndexEquiv m (j, e) ∈ Finset.univ.image a :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hai⟩
  have hbImage : signedIndexEquiv m (j, e) ∈ Finset.univ.image b :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hbk⟩
  exact (Finset.disjoint_left.mp h.2.2) haImage hbImage

/-- **Nine-profile classification at one folded coordinate.**  Write the four source bits as
`(A+, A-, B+, B-)`.  Injectivity makes them zero/one and global disjointness forbids simultaneous
use of the same signed root.  Each sign independently has exactly three states: unused, owned by
`A`, or owned by `B`; their Cartesian product gives exactly nine local profiles.  The final
equality computes the corresponding five-letter coefficient.  Thus letters `±2` have a unique
lift, letters `±1` have two lifts, and letter `0` is either empty or one antipodal pair wholly
owned by one side.  This is the local counting law needed by future enumeration. -/
theorem globallyDisjoint_local_nine_profiles {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) (j : Fin m) :
    let ap := signedMultiplicity a j 0
    let am := signedMultiplicity a j 1
    let bp := signedMultiplicity b j 0
    let bm := signedMultiplicity b j 1
    ((ap = 0 ∧ bp = 0) ∨ (ap = 1 ∧ bp = 0) ∨ (ap = 0 ∧ bp = 1)) ∧
      ((am = 0 ∧ bm = 0) ∨ (am = 1 ∧ bm = 0) ∨ (am = 0 ∧ bm = 1)) ∧
      depthSevenRelation m a b j =
        (ap : Int) - (am : Int) - (bp : Int) + (bm : Int) := by
  dsimp only
  let ap := signedMultiplicity a j 0
  let am := signedMultiplicity a j 1
  let bp := signedMultiplicity b j 0
  let bm := signedMultiplicity b j 1
  have hap : ap <= 1 := signedMultiplicity_le_one_of_injective a h.1 j 0
  have ham : am <= 1 := signedMultiplicity_le_one_of_injective a h.1 j 1
  have hbp : bp <= 1 := signedMultiplicity_le_one_of_injective b h.2.1 j 0
  have hbm : bm <= 1 := signedMultiplicity_le_one_of_injective b h.2.1 j 1
  have hpos : ap + bp <= 1 :=
    signedMultiplicity_add_le_one_of_globallyDisjoint a b h j 0
  have hneg : am + bm <= 1 :=
    signedMultiplicity_add_le_one_of_globallyDisjoint a b h j 1
  have hA := congrFun (tupleVec_encodeSignedTuple_eq_counts (decodeSignedTuple a)) j
  have hB := congrFun (tupleVec_encodeSignedTuple_eq_counts (decodeSignedTuple b)) j
  have hA' : tupleVec (2 * m) m 7 a j = (ap : Int) - (am : Int) := by
    simpa [ap, am, signedMultiplicity] using hA
  have hB' : tupleVec (2 * m) m 7 b j = (bp : Int) - (bm : Int) := by
    simpa [bp, bm, signedMultiplicity] using hB
  have hd : depthSevenRelation m a b j =
      (ap : Int) - (am : Int) - (bp : Int) + (bm : Int) := by
    unfold depthSevenRelation
    rw [hA', hB']
    ring
  have hposCases :
      (ap = 0 ∧ bp = 0) ∨ (ap = 1 ∧ bp = 0) ∨ (ap = 0 ∧ bp = 1) := by
    omega
  have hnegCases :
      (am = 0 ∧ bm = 0) ∨ (am = 1 ∧ bm = 0) ∨ (am = 0 ∧ bm = 1) := by
    omega
  exact ⟨hposCases, hnegCases, hd⟩

/-! ## The exact source-fiber occupancy law

The nine local profiles carry a useful bivariate weight.  Give one use by the first tuple weight
`x` and one use by the second tuple weight `y`.  At a fixed folded coordinate the five possible
labels then have weights

`w_{±2} = xy`, `w_{±1} = x + y`, and `w_0 = 1 + x² + y²`.

Thus, if a label has `A` double letters, `B` unit letters, and `C` zero letters, its globally
disjoint ordered seven-petal source fiber has the formal enumerator

`(7!)² [x⁷y⁷] (xy)^A (x+y)^B (1+x²+y²)^C`.

The full cardinality equivalence is not needed below.  Instead we prove its exact local content
and the strongest immediate global consequences: a conservation identity, evenness of `B`,
automatic nonzeroness of the folded label, and the one-power loss for every sector other than the
fourteen-unit-letter sector.
-/

/-- Number of literal signed roots from one tuple above a folded coordinate. -/
def sideSourceMass {m L : Nat} (t : Fin L -> Fin (2 * m)) (j : Fin m) : Nat :=
  signedMultiplicity t j 0 + signedMultiplicity t j 1

/-- Total number of literal signed roots from both source tuples above a folded coordinate. -/
def jointSourceMass {m L K : Nat} (a : Fin L -> Fin (2 * m))
    (b : Fin K -> Fin (2 * m)) (j : Fin m) : Nat :=
  sideSourceMass a j + sideSourceMass b j

/-- Summing the local source mass recovers the tuple length exactly. -/
theorem sum_sideSourceMass_eq_length {m L : Nat} (t : Fin L -> Fin (2 * m)) :
    ∑ j : Fin m, sideSourceMass t j = L := by
  classical
  calc
    (∑ j : Fin m, sideSourceMass t j) =
        ∑ x : Fin m × Fin 2, (tupleMultiset (decodeSignedTuple t)).count x := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      simp [sideSourceMass, signedMultiplicity, Fin.sum_univ_two]
    _ = (tupleMultiset (decodeSignedTuple t)).card := by simp
    _ = L := card_tupleMultiset _

/-- Exact local version of the five generating-function weights.  The four displayed numbers are
the occupancies `(A+, A-, B+, B-)`.  In particular `±2` has one profile, `±1` has two,
and `0` has the three profiles carrying weights `1`, `x²`, and `y²`. -/
theorem globallyDisjoint_local_five_weight_profiles {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) (j : Fin m) :
    let ap := signedMultiplicity a j 0
    let am := signedMultiplicity a j 1
    let bp := signedMultiplicity b j 0
    let bm := signedMultiplicity b j 1
    (depthSevenRelation m a b j = 2 <->
      ap = 1 ∧ am = 0 ∧ bp = 0 ∧ bm = 1) ∧
    (depthSevenRelation m a b j = -2 <->
      ap = 0 ∧ am = 1 ∧ bp = 1 ∧ bm = 0) ∧
    (depthSevenRelation m a b j = 1 <->
      (ap = 1 ∧ am = 0 ∧ bp = 0 ∧ bm = 0) ∨
      (ap = 0 ∧ am = 0 ∧ bp = 0 ∧ bm = 1)) ∧
    (depthSevenRelation m a b j = -1 <->
      (ap = 0 ∧ am = 1 ∧ bp = 0 ∧ bm = 0) ∨
      (ap = 0 ∧ am = 0 ∧ bp = 1 ∧ bm = 0)) ∧
    (depthSevenRelation m a b j = 0 <->
      (ap = 0 ∧ am = 0 ∧ bp = 0 ∧ bm = 0) ∨
      (ap = 1 ∧ am = 1 ∧ bp = 0 ∧ bm = 0) ∨
      (ap = 0 ∧ am = 0 ∧ bp = 1 ∧ bm = 1)) := by
  dsimp only
  have hlocal := globallyDisjoint_local_nine_profiles a b h j
  dsimp only at hlocal
  rcases hlocal with ⟨hpos, hneg, hd⟩
  rcases hpos with hpos | hpos | hpos <;>
    rcases hneg with hneg | hneg | hneg <;>
    simp_all

/-- The bivariate local-profile enumerator, represented as a polynomial in `x` whose
coefficients are polynomials in `y`.  Its `(7,7)` coefficient is the unordered source-profile
factor in the exact fiber formula; multiplying by `(7!)²` orders the two source tuples. -/
noncomputable def formalSourceFiberEnumerator (double unit zeroCount : Nat) :
    Polynomial (Polynomial Nat) :=
  (Polynomial.X * Polynomial.C Polynomial.X) ^ double *
    (Polynomial.X + Polynomial.C Polynomial.X) ^ unit *
      (1 + Polynomial.X ^ 2 + Polynomial.C (Polynomial.X ^ 2)) ^ zeroCount

/-- The formal `(x⁷y⁷)` source-profile coefficient. -/
noncomputable def formalSourceFiberCoefficient (double unit zeroCount : Nat) : Nat :=
  ((formalSourceFiberEnumerator double unit zeroCount).coeff 7).coeff 7

/-- In the dominant active-coordinate sector all fourteen labels are unit letters.  Its formal
profile coefficient is `choose(14,7)=3432`, and the corresponding formal ordered factor is
exactly `14!`.  Packaging this factor as the cardinality of the actual source fiber would require
the global bijection deliberately left outside this file. -/
theorem allUnitFormalSourceFiberCoefficient_exact :
    formalSourceFiberCoefficient 0 14 0 = 3432 := by
  norm_num [formalSourceFiberCoefficient, formalSourceFiberEnumerator,
    Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow, Nat.choose]

theorem allUnitFormalOrderedFiberFactor_eq_factorial :
    Nat.factorial 7 ^ 2 * formalSourceFiberCoefficient 0 14 0 = Nat.factorial 14 := by
  rw [allUnitFormalSourceFiberCoefficient_exact]
  norm_num [Nat.factorial]

/-- Number of folded coordinates carrying a double letter. -/
def doubleLetterCount {m : Nat} (d : Fin m -> Int) : Nat :=
  ∑ j : Fin m, if (d j).natAbs = 2 then 1 else 0

/-- Number of folded coordinates carrying a unit letter.  This is the exponent `B` in the source
fiber enumerator above. -/
def unitLetterCount {m : Nat} (d : Fin m -> Int) : Nat :=
  ∑ j : Fin m, if (d j).natAbs = 1 then 1 else 0

/-- Number of zero-label coordinates that contain an antipodal pair owned by one side. -/
def occupiedZeroCount {m : Nat} (a b : Fin 7 -> Fin (2 * m)) : Nat :=
  ∑ j : Fin m,
    if depthSevenRelation m a b j = 0 ∧ jointSourceMass a b j = 2 then 1 else 0

/-- Number of folded coordinates actually occupied by the source union. -/
def occupiedFoldedCount {m : Nat} (a b : Fin 7 -> Fin (2 * m)) : Nat :=
  ∑ j : Fin m, if jointSourceMass a b j = 0 then 0 else 1

/-- The local weight law partitions occupied folded coordinates into double, unit, and occupied
zero-label coordinates. -/
theorem occupiedFoldedCount_eq_profile_sum {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) :
    occupiedFoldedCount a b =
      doubleLetterCount (depthSevenRelation m a b) +
        unitLetterCount (depthSevenRelation m a b) + occupiedZeroCount a b := by
  unfold occupiedFoldedCount doubleLetterCount unitLetterCount occupiedZeroCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hlocal := globallyDisjoint_local_nine_profiles a b h j
  dsimp only at hlocal
  rcases hlocal with ⟨hpos, hneg, hd⟩
  rcases hpos with hpos | hpos | hpos <;>
    rcases hneg with hneg | hneg | hneg
  all_goals simp_all [jointSourceMass, sideSourceMass]

/-- **Exact occupancy conservation.**  Double letters consume two source roots, unit letters one,
and occupied zero letters an antipodal pair.  The two seven-petal sides therefore give total mass
`14 = 2A + B + 2Z`. -/
theorem globallyDisjoint_source_occupancy_identity {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) :
    2 * doubleLetterCount (depthSevenRelation m a b) +
        unitLetterCount (depthSevenRelation m a b) + 2 * occupiedZeroCount a b = 14 := by
  have hpoint : ∀ j : Fin m,
      2 * (if (depthSevenRelation m a b j).natAbs = 2 then 1 else 0) +
          (if (depthSevenRelation m a b j).natAbs = 1 then 1 else 0) +
          2 * (if depthSevenRelation m a b j = 0 ∧ jointSourceMass a b j = 2
            then 1 else 0) = jointSourceMass a b j := by
    intro j
    have hlocal := globallyDisjoint_local_nine_profiles a b h j
    dsimp only at hlocal
    rcases hlocal with ⟨hpos, hneg, hd⟩
    rcases hpos with hpos | hpos | hpos <;>
      rcases hneg with hneg | hneg | hneg
    all_goals simp_all [jointSourceMass, sideSourceMass]
  calc
    2 * doubleLetterCount (depthSevenRelation m a b) +
          unitLetterCount (depthSevenRelation m a b) + 2 * occupiedZeroCount a b =
        ∑ j : Fin m, jointSourceMass a b j := by
      unfold doubleLetterCount unitLetterCount occupiedZeroCount
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => hpoint j
    _ = (∑ j : Fin m, sideSourceMass a j) + ∑ j : Fin m, sideSourceMass b j := by
      simp [jointSourceMass, Finset.sum_add_distrib]
    _ = 14 := by rw [sum_sideSourceMass_eq_length, sum_sideSourceMass_eq_length]

/-- A genuine source fiber can only lie over a label having an even number of unit letters. -/
theorem unitLetterCount_even_of_globallyDisjoint {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) :
    Even (unitLetterCount (depthSevenRelation m a b)) := by
  rw [Nat.even_iff]
  have hid := globallyDisjoint_source_occupancy_identity a b h
  omega

/-- The source-coordinate exponent is exactly `7 + B/2`.  Consequently its unique degree-`14`
sector has fourteen unit letters; any antipodal/folded collision loses at least one power of the
ambient half-order. -/
theorem occupiedFoldedCount_eq_seven_add_half_unitLetterCount {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) :
    occupiedFoldedCount a b =
      7 + unitLetterCount (depthSevenRelation m a b) / 2 := by
  rw [occupiedFoldedCount_eq_profile_sum a b h]
  have hid := globallyDisjoint_source_occupancy_identity a b h
  have heven := unitLetterCount_even_of_globallyDisjoint a b h
  rw [Nat.even_iff] at heven
  omega

/-- Outside the all-unit-letter sector, at most thirteen folded coordinates are occupied.  In an
enumeration over unrestricted source locations this sector is therefore lower-order by at least
`1/m`; the remaining dominant residual consists of fourteen distinct `±1` coordinates.  This
dimension loss alone does **not** bound its share of the much smaller collision target: an
additional equidistribution or collision estimate is still required. -/
theorem occupiedFoldedCount_le_thirteen_of_nonunit_sector {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b)
    (hnonunit : 0 < doubleLetterCount (depthSevenRelation m a b) + occupiedZeroCount a b) :
    occupiedFoldedCount a b <= 13 := by
  rw [occupiedFoldedCount_eq_profile_sum a b h]
  have hid := globallyDisjoint_source_occupancy_identity a b h
  omega

/-- In the degree-`14` sector the label has exactly fourteen unit letters and no double or
occupied-zero coordinates. -/
theorem occupiedFoldedCount_eq_fourteen_iff_all_unit {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) :
    occupiedFoldedCount a b = 14 <->
      unitLetterCount (depthSevenRelation m a b) = 14 ∧
        doubleLetterCount (depthSevenRelation m a b) = 0 ∧ occupiedZeroCount a b = 0 := by
  rw [occupiedFoldedCount_eq_profile_sum a b h]
  have hid := globallyDisjoint_source_occupancy_identity a b h
  omega

/-- Odd source length makes the folded label automatically nonzero: a zero label would force each
side to be a disjoint union of antipodal pairs, hence to have even cardinality. -/
theorem depthSevenRelation_ne_zero_of_globallyDisjoint {m : Nat}
    (a b : Fin 7 -> Fin (2 * m)) (h : GloballyDisjointSevenPetals a b) :
    depthSevenRelation m a b ≠ 0 := by
  intro hd
  have hdiv : ∀ j : Fin m, 2 ∣ sideSourceMass a j := by
    intro j
    have hdj : depthSevenRelation m a b j = 0 := by
      simpa using congrFun hd j
    have hlocal := globallyDisjoint_local_nine_profiles a b h j
    dsimp only at hlocal
    rcases hlocal with ⟨hpos, hneg, hformula⟩
    have hcases : sideSourceMass a j = 0 ∨ sideSourceMass a j = 2 := by
      rcases hpos with hpos | hpos | hpos <;>
        rcases hneg with hneg | hneg | hneg <;>
        simp_all [sideSourceMass]
    rcases hcases with hz | htwo
    · simp [hz]
    · simp [htwo]
  have hsumDiv : 2 ∣ ∑ j : Fin m, sideSourceMass a j := by
    exact Finset.dvd_sum fun j _ => hdiv j
  rw [sum_sideSourceMass_eq_length] at hsumDiv
  norm_num at hsumDiv

/-! ## The strengthened socket for actual primitive witnesses -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The previous sparse-polynomial socket with its coefficient height sharpened from `14` to `2`.
This theorem applies directly to `PrimitiveDepthSevenCollision`, not to an enlarged ambient code. -/
theorem primitiveDepthSevenCollision_gives_sharp_alphabet_polynomial
    (g : F) (m : Nat) (hm : 0 < m) (hg : g ^ m = -1)
    (a b : Fin 7 -> Fin (2 * m))
    (h : PrimitiveDepthSevenCollision g m a b) :
    let d := depthSevenRelation m a b
    InFoldedAlphabet d ∧
      endpointL1 d <= 14 ∧
      (vectorSupport d).card <= 14 ∧
      relPoly m d ≠ 0 ∧
      (relPoly m d).natDegree < m ∧
      (forall i, |(relPoly m d).coeff i| <= 2) ∧
      Polynomial.aeval g (relPoly m d) = 0 := by
  dsimp only
  have hsparse := primitiveDepthSevenCollision_gives_sparse_polynomial g m hm hg a b h
  refine ⟨depthSevenRelation_mem_foldedAlphabet_of_globallyDisjoint a b h.1,
    depthSevenRelation_l1_le_fourteen m a b,
    depthSevenRelation_support_card_le_fourteen m a b,
    hsparse.1, hsparse.2.1, ?_, hsparse.2.2.2.2⟩
  intro i
  by_cases hi : i < m
  · let j : Fin m := ⟨i, hi⟩
    rw [show i = (j : Nat) from rfl, relPoly_coeff]
    have hj := depthSevenRelation_mem_foldedAlphabet_of_globallyDisjoint a b h.1 j
    rw [abs_le]
    exact hj
  · have hz : (relPoly m (depthSevenRelation m a b)).coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le (relPoly_degree_lt m _)
        (by exact_mod_cast Nat.le_of_not_gt hi)
    rw [hz]
    norm_num

/-- The coefficient mass of a relation polynomial is exactly the endpoint `l1` mass of its
coefficient vector. -/
theorem coeffMass_relPoly_eq_endpointL1 (m : Nat) (d : Fin m -> Int) :
    coeffMass (relPoly m d) = endpointL1 d := by
  unfold coeffMass endpointL1
  rw [relPoly_support_eq_vectorSupport_map]
  rw [Finset.sum_map]
  calc
    (∑ j ∈ vectorSupport d, ((relPoly m d).coeff (j : Nat)).natAbs) =
        ∑ j ∈ vectorSupport d, (d j).natAbs := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [relPoly_coeff]
    _ = ∑ j : Fin m, (d j).natAbs := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnot
      have hz : d j = 0 := by
        by_contra hne
        exact hnot (by simp [vectorSupport, hne])
      simp [hz]

/-- **Production-arithmetic obstruction attached to every actual primitive witness.**  At a
power-of-two half-order root in characteristic `p`, the sharp-alphabet relation owns a nonzero
integer resultant divisible by `p`; its absolute value lies between `p` and `14^m`.  The upper
base remains `14`, despite height `2`, because the norm envelope sees total coefficient mass. -/
theorem primitiveDepthSevenCollision_resultant_sandwich
    (k m p : Nat) (hm : m = 2 ^ k) [CharP F p]
    (g : F) (hg : g ^ m = -1)
    (a b : Fin 7 -> Fin (2 * m))
    (h : PrimitiveDepthSevenCollision g m a b) :
    let d := depthSevenRelation m a b
    InFoldedAlphabet d ∧
      ∃ N : Int, N ≠ 0 ∧ (p : Int) ∣ N ∧
        p <= N.natAbs ∧ N.natAbs <= 14 ^ m := by
  subst m
  dsimp only
  let d := depthSevenRelation (2 ^ k) a b
  have hs := primitiveDepthSevenCollision_gives_sharp_alphabet_polynomial
    g (2 ^ k) (by positivity) hg a b h
  change InFoldedAlphabet d ∧ endpointL1 d <= 14 ∧
    (vectorSupport d).card <= 14 ∧ relPoly (2 ^ k) d ≠ 0 ∧
    (relPoly (2 ^ k) d).natDegree < 2 ^ k ∧
    (forall i, |(relPoly (2 ^ k) d).coeff i| <= 2) ∧
    Polynomial.aeval g (relPoly (2 ^ k) d) = 0 at hs
  rcases hs with ⟨halphabet, hl1, _hsupport, hpoly0, hdegree, _hheight, heval⟩
  have hd0 : d ≠ 0 := by
    intro hd
    apply hpoly0
    rw [hd]
    unfold relPoly
    simp
  let N : Int := patternResultant (2 ^ k) (relPoly (2 ^ k) d)
  have hcert := relation_resultant_certificate k (2 ^ k) rfl p g hg d
    (by rw [← aeval_relPoly]; exact heval) hd0
  have hN0 : N ≠ 0 := by simpa [N] using hcert.1
  have hNdiv : (p : Int) ∣ N := by simpa [N] using hcert.2
  have hpNat : p ∣ N.natAbs := by
    exact Int.ofNat_dvd.mp (by simpa [Int.dvd_natAbs] using hNdiv)
  have hpLower : p <= N.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hN0) hpNat
  have hmass : coeffMass (relPoly (2 ^ k) d) <= 14 := by
    rw [coeffMass_relPoly_eq_endpointL1]
    exact hl1
  have hupper : N.natAbs <= 14 ^ (2 ^ k) := by
    calc
      N.natAbs <= coeffMass (relPoly (2 ^ k) d) ^ (2 ^ k) := by
        simpa [N] using patternResultant_natAbs_le_pow hdegree
      _ <= 14 ^ (2 ^ k) := Nat.pow_le_pow_left hmass _
  exact ⟨halphabet, N, hN0, hNdiv, hpLower, hupper⟩

local instance firstProductionPrime :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance secondProductionPrime :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The resultant sandwich and five-letter alphabet instantiated at both certified production
roots.  This is the exact finite arithmetic class in which the missing `8264` must be proved. -/
theorem production_primitive_sharp_resultant_socket :
    (forall (a b : Fin 7 -> Fin (2 ^ 30)),
      PrimitiveDepthSevenCollision ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 29) a b ->
      let d := depthSevenRelation (2 ^ 29) a b
      InFoldedAlphabet d ∧
        ∃ N : Int, N ≠ 0 ∧
          (ArkLib.ProximityGap.PrizeShapePrimeP30.P : Int) ∣ N ∧
          ArkLib.ProximityGap.PrizeShapePrimeP30.P <= N.natAbs ∧
          N.natAbs <= 14 ^ (2 ^ 29)) ∧
    (forall (a b : Fin 7 -> Fin (2 ^ 30)),
      PrimitiveDepthSevenCollision ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
        (2 ^ 29) a b ->
      let d := depthSevenRelation (2 ^ 29) a b
      InFoldedAlphabet d ∧
        ∃ N : Int, N ≠ 0 ∧
          (ArkLib.ProximityGap.PrizeShapePrimeP30Second.P : Int) ∣ N ∧
          ArkLib.ProximityGap.PrizeShapePrimeP30Second.P <= N.natAbs ∧
          N.natAbs <= 14 ^ (2 ^ 29)) := by
  constructor
  · intro a b h
    exact primitiveDepthSevenCollision_resultant_sandwich 29 (2 ^ 29)
      ArkLib.ProximityGap.PrizeShapePrimeP30.P rfl
      ArkLib.ProximityGap.PrizeShapePrimeP30.g firstProductionRoot_half_pow a b h
  · intro a b h
    exact primitiveDepthSevenCollision_resultant_sandwich 29 (2 ^ 29)
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.P rfl
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.g secondProductionRoot_half_pow a b h

/-! ## Exact countermodel: the alphabet is not a universal obstruction -/

def counterA : Fin 7 -> Fin 16 := ![0, 1, 2, 3, 4, 5, 6]

def counterB : Fin 7 -> Fin 16 := ![7, 9, 11, 12, 13, 14, 15]

def counterRelation : Fin 8 -> Int := ![1, 2, 1, 2, 2, 2, 2, 0]

/-- The counterexample uses genuine globally-disjoint seven-petals. -/
theorem counterPetals_globallyDisjoint :
    GloballyDisjointSevenPetals (m := 8) counterA counterB := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [counterA]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [counterB]
  · decide

/-- Its folded relation realizes the boundary letter `2`, so `[-2,2]` is sharp. -/
theorem counterRelation_exact :
    depthSevenRelation 8 counterA counterB = counterRelation := by
  decide

local instance primeSeventeen : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `3` is an order-`16` root in the countermodel field. -/
theorem counterRoot_order : orderOf (3 : ZMod 17) = 16 := by
  have h8 : ¬ (3 : ZMod 17) ^ (2 : Nat) ^ 3 = 1 := by decide
  have h16 : (3 : ZMod 17) ^ (2 : Nat) ^ 4 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (3 : ZMod 17)) h8 h16
  norm_num at h
  exact h

/-- The two seven-subset sums collide in `ZMod 17`. -/
theorem counterSums_collide :
    gsumR (3 : ZMod 17) 16 7 counterA = gsumR (3 : ZMod 17) 16 7 counterB := by
  decide

/-- **Exact restricted-class countermodel.**  Power-of-two order, global disjointness, the sharp
alphabet, support/l1 bounds, and a nonzero folded label can all coexist with a field collision. -/
theorem sharpAlphabet_universal_kernel_obstruction_false :
    PrimitiveDepthSevenCollision (3 : ZMod 17) 8 counterA counterB ∧
      depthSevenRelation 8 counterA counterB = counterRelation ∧
      InFoldedAlphabet counterRelation ∧
      (vectorSupport counterRelation).card = 7 ∧
      endpointL1 counterRelation = 12 ∧
      counterRelation 1 = 2 := by
  refine ⟨?_, counterRelation_exact, ?_, ?_, ?_, by decide⟩
  · exact ⟨counterPetals_globallyDisjoint,
      counterSums_collide, by rw [counterRelation_exact]; decide⟩
  · intro j
    fin_cases j <;> norm_num [counterRelation]
  · decide
  · decide

/-! ## What the production arithmetic must still save -/

/-- The unrestricted depth-seven Wick coefficient. -/
def wickCoefficient : Nat := 135135

/-- The production injective allowance. -/
def injectiveAllowance : Nat := 126871

/-- The exact deficit that a production-specific restricted-alphabet theorem must supply. -/
def requiredAlphabetSaving : Nat := wickCoefficient - injectiveAllowance

theorem requiredAlphabetSaving_exact : requiredAlphabetSaving = 8264 := by
  norm_num [requiredAlphabetSaving, wickCoefficient, injectiveAllowance]

/-- The required saving is strictly between `6.115%` and `6.116%` of the Wick coefficient. -/
theorem requiredAlphabetSaving_ratio_window :
    6115 * wickCoefficient < 100000 * requiredAlphabetSaving ∧
      100000 * requiredAlphabetSaving < 6116 * wickCoefficient := by
  norm_num [requiredAlphabetSaving, wickCoefficient, injectiveAllowance]

/-- Even after the height improvement `14 -> 2`, the sharp norm/resultant envelope still sees
the full coefficient mass `14`.  Thus an argument using only `l1` mass cannot provide the missing
`8264`; it must exploit the distribution of the five alphabet letters or production arithmetic. -/
theorem sharpAlphabet_resultant_base_still_fourteen :
    (14 : Nat) = 7 * 2 ∧
      injectiveAllowance + requiredAlphabetSaving = wickCoefficient := by
  norm_num [requiredAlphabetSaving, wickCoefficient, injectiveAllowance]

#print axioms decodeSignedTuple_injective
#print axioms tupleMultiset_nodup_of_injective
#print axioms tupleVec_of_injective_mem_ternary
#print axioms depthSevenRelation_mem_foldedAlphabet_of_injective
#print axioms globallyDisjoint_local_nine_profiles
#print axioms sum_sideSourceMass_eq_length
#print axioms globallyDisjoint_local_five_weight_profiles
#print axioms allUnitFormalSourceFiberCoefficient_exact
#print axioms allUnitFormalOrderedFiberFactor_eq_factorial
#print axioms occupiedFoldedCount_eq_profile_sum
#print axioms globallyDisjoint_source_occupancy_identity
#print axioms unitLetterCount_even_of_globallyDisjoint
#print axioms occupiedFoldedCount_eq_seven_add_half_unitLetterCount
#print axioms occupiedFoldedCount_le_thirteen_of_nonunit_sector
#print axioms occupiedFoldedCount_eq_fourteen_iff_all_unit
#print axioms depthSevenRelation_ne_zero_of_globallyDisjoint
#print axioms primitiveDepthSevenCollision_gives_sharp_alphabet_polynomial
#print axioms primitiveDepthSevenCollision_resultant_sandwich
#print axioms production_primitive_sharp_resultant_socket
#print axioms counterPetals_globallyDisjoint
#print axioms counterRelation_exact
#print axioms counterRoot_order
#print axioms counterSums_collide
#print axioms sharpAlphabet_universal_kernel_obstruction_false
#print axioms requiredAlphabetSaving_ratio_window

end ArkLib.ProximityGap.Frontier.BGKPrimitiveFoldedAlphabet
