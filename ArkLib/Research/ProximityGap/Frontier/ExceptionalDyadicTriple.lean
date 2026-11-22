/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237

/-! # The exceptional prime for a pair of order-1024 triple products

The six-site equality below occurs precisely when a primitive root or its
inverse satisfies the trinomial that defines the 237-bit spectral witness.
A degree-17 recurrence and an integer Bézout identity rule out every other
prime characteristic. The supplied integer coefficients are checked by ring
identities over the arbitrary field.
-/
namespace ProximityGap.ExceptionalDyadicTriple
open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)

private def ev {F : Type*} [Ring F] (z : F) : List ℤ → F
  | [] => 0
  | a::l => (a:F) + z*ev z l

private theorem half {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 1024) :
    z^512 = -1 := by
  have square : (z^512-1)*(z^512+1)=0 := by
    calc
      _ = z^1024-1 := by ring
      _ = 0 := by rw [hz.pow_eq_one,sub_self]
  rcases mul_eq_zero.mp square with one|neg
  · exact False.elim (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide) (sub_eq_zero.mp one))
  · linear_combination neg

private theorem recurrence {F : Type*} [Field F] (z : F) (h : z^17+z-1=0) :
    z^512+1=0 → (P:F)=0 := by
  have step32 : z^32 = ev z [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1] := by
    linear_combination (norm := (simp only [ev, Int.cast_neg, Int.cast_one, Int.cast_zero]; ring)) ev z [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] * h
  have step64 : z^64 = ev z [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -3, 3, -1] := by
    rw [show z^64=(z^32)^2 by ring, step32]
    linear_combination (norm := (simp only [ev, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero]; ring)) ev z [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1] * h
  have step128 : z^128 = ev z [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -7, 21, -35, 35, -21, 7, -1] := by
    rw [show z^128=(z^64)^2 by ring, step64]
    linear_combination (norm := (simp only [ev, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero]; ring)) ev z [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -6, 15, -20, 15, -6, 1] * h
  have step256 : z^256 = ev z [0, 1, -15, 105, -455, 1365, -3003, 5005, -6435, 6435, -5005, 3003, -1365, 455, -105, 15, -1] := by
    rw [show z^256=(z^128)^2 by ring, step128]
    linear_combination (norm := (simp only [ev, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero]; ring)) ev z [0, 1, -14, 91, -364, 1001, -2002, 3003, -3432, 3003, -2002, 1001, -364, 91, -14, 1] * h
  have step512 : z^512 = ev z [-155117520, 300540195, -265182524, 206253045, -141120090, 84668255, -44324760, 20017569,
      -7294950, 593775, 5116644, -14137239, 30013550, -54622805, 86492760, -119759819, 145422674] := by
    rw [show z^512=(z^256)^2 by ring, step256]
    linear_combination (norm := (simp only [ev, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero]; ring)) ev z [-155117520, 145422675, -119759850, 86493225, -54627300, 30045015, -14307150, 5852925, -2035800,
      593775, -142506, 27405, -4060, 435, -30, 1] * h
  rw [step512]
  intro last
  change (126205134105047729256068842055334737587878534445324289139206048206460929:F)=0
  linear_combination (norm := (simp only [ev, Int.cast_ofNat, Int.cast_neg]; ring))
    ev z [-14761249269236151979363162782505481205315440487994708806877044631610891593490129,
      10335707742252972426629883675860390510235797924458041263212989995962524722789655,
      -8970872417187376660724541343723414239743166561885110588427481118286151309877761,
      6199387851890168211951887555928956174087409232512523483587219990778030916905511,
      -4544651939090682819194435361688761982017063257310364726899758069931455866565177,
      1756138754313253539735785186864987846488567213325341206830188636591411416193563,
      -435243993815658941213349873414548289614495692289348929020086667430035931389153,
      1474286626364891071719984327456119768467673138055607336077358392608765166856523,
      430877775080576066664968441509373206338022432582175528030400341074671426370859,
      -880514757059037537368578756422904854038838561958517876062404688512544253961541,
      -1124017477157991357974878186993915526472097647667378027024624690189536957144469,
      -1547038269844717903181070595457932088773104386030072363162762001546858060284841,
      2807807120325775831437359779633636649915499253911818715893940538528748218261311,
      -754990409132863612232976055357285916252075098716389638439709822196850573556915,
      5232489801674613202634362071662058740612701558036089119444271797251820089198667,
      -7821394582298965696836870926208783404035061892060443672782745802919547910637414] * h + ev z [95161715054448607280235274562614936807883723953296173861269374044106800,
      22582641922665715427586761522152511365288233637859131275363977392975064,
      5533533450763862558414780244923800983609707157684471755860929692877984,
      848778834682806535780430394577581506106061987642672879854354244845688,
      4901086949518704161386880353054251840410230722881995984826680791450848,
      6180614841769379785498479496204552964080260703325181935928711103182612,
      -1048195498939428629623776839664961357414932639011635513124444828928504,
      -10314834565538401174615698635746133682603992186554599876152072535055996,
      -10386189147330715998036112121494051089375748099520151688290647610611696,
      1397098814443366959662379830924916383077055001267395003195899308747120,
      14318704805401011283432621713740672719029978129288081106195306396833296,
      14002610364505022578353210421498213933089477827173432973244070722757180,
      -2339652737378532750159212092839397638174613259859059166553445380890412,
      -20480793695962379933836925398503481873374792448180758855183766172905806,
      -19952602434655543475756261349250305384559664513791082649032501599654532,
      8311338401453542428169916492796664722727970606316499649970183417562183,
      53783872673796148851154194332919386450252330610152607101577198359862011] * last

/-- A primitive order-1024 root satisfying the sparse relation determines its
prime characteristic uniquely. -/
theorem prime_of_relation {p : ℕ} [Fact p.Prime] {z : ZMod p} (hz : IsPrimitiveRoot z 1024)
    (rel : z^17+z=1) : p=P := by
  have zero := recurrence z (sub_eq_zero.mpr rel) (by rw [half hz]; ring)
  exact (Nat.prime_dvd_prime_iff_eq Fact.out (Fact.out : P.Prime)).mp
    ((ZMod.natCast_eq_zero_iff P p).mp zero)

/-- The two compared triples after clearing all six denominators. -/
def collision {F : Type*} [Field F] (z : F) : Prop :=
  (z^9-1)*(z^7-1)*(z^18-1)*(z^34-z^16)*(z^527-z^16)*(z^545-z^16) =
    (z^34-1)*(z^527-1)*(z^545-1)*(z^9-z^16)*(z^7-z^16)*(z^18-z^16)

private theorem nonzero_add {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 1024)
    (j : ℕ) (hj : 0<j) (bound : 2*j<1024) : z^j+1 ≠ 0 := by
  intro h
  apply hz.pow_ne_one_of_pos_of_lt (by omega : 2*j ≠ 0) bound
  rw [mul_comm,pow_mul,show z^j=(-1:F) by linear_combination h]
  ring

/-- Over every field, the collision is equivalent to one of two reciprocal
trinomial relations. -/
theorem collision_iff {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 1024) :
    collision z ↔ z^17+z=1 ∨ z^17-z^16=1 := by
  have z₀ : z≠0 := by intro zero; simpa [zero] using hz.pow_eq_one
  have zplus : z+1 ≠ 0 := by simpa using nonzero_add hz 1 (by decide) (by decide)
  have seventeen := nonzero_add hz 17 (by decide) (by decide)
  have n₁ : z^16-1≠0 := sub_ne_zero.mpr (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have n₂ : z^9-1≠0 := sub_ne_zero.mpr (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have n₃ : z^7-1≠0 := sub_ne_zero.mpr (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  unfold collision
  rw [show z^527= -(z^15) by rw [show z^527=z^512*z^15 by ring,half hz]; ring,
      show z^545= -(z^33) by rw [show z^545=z^512*z^33 by ring,half hz]; ring, ← sub_eq_zero]
  rw [show _ - _ = -z^32*(z+1)*(z^16-1)^2*(z^9-1)*(z^7-1)*(z^17+1)*
          (z^17+z-1)*(z^17-z^16-1) by ring]
  simp [mul_eq_zero,z₀,zplus,n₁,n₂,n₃,seventeen,sub_eq_zero]

/-- Every realization of the six-site collision in a prime field has the
characteristic of the 237-bit witness. -/
theorem prime_of_collision {p : ℕ} [Fact p.Prime] {z : ZMod p} (hz : IsPrimitiveRoot z 1024)
    (h : collision z) : p=P := by
  rcases (collision_iff hz).mp h with direct|reverse
  · exact prime_of_relation hz direct
  apply prime_of_relation hz.inv
  have nz : z≠0 := by intro hz₀; simpa [hz₀] using hz.pow_eq_one
  rw [inv_pow]
  field_simp
  linear_combination -reverse

end ProximityGap.ExceptionalDyadicTriple
#print axioms ProximityGap.ExceptionalDyadicTriple.collision_iff
#print axioms ProximityGap.ExceptionalDyadicTriple.prime_of_collision
