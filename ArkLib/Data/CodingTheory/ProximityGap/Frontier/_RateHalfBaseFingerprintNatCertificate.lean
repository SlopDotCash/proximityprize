/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NatModProductCertificate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateHalfBaseFingerprintTable

/-!
# Natural-number evaluation certificate for the 93 base fingerprints

This file evaluates the three-core Lagrange defects entirely in `Nat` modulo
the certified prime.  It avoids direct reduction of large `ZMod` products and
inverses, while retaining a small proved cast bridge in
`_NatModProductCertificate.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000000

namespace ArkLib.ProximityGap.Frontier.RateHalfBaseFingerprintNatCertificate

open NatModProductCertificate
open RateHalfBaseFingerprintTable
open ArkLib.ProximityGap.PrizeShapePrimeP30

abbrev modulus : Nat := P
abbrev baseGeneratorNat : Nat :=
  321066668146402433440778728016715546214271526818

local instance localInstance_RateHalfBaseFingerprintNatCertificate_1 : Fact (Nat.Prime modulus) := ⟨prime_P⟩

/-- Natural representative of the `i`-th point of `mu_64`. -/
def domainNat (i : Nat) : Nat :=
  productMod modulus (List.replicate i baseGeneratorNat)

def basis0 : List Nat :=
  [0,2,4,6,8,9,11,14,15,16,22,23,24,25,26,28,29,31,
   32,33,34,36,37,38,42,44,48,49,50,55,56,57]

def basis1 : List Nat :=
  [1,3,5,6,8,10,13,15,17,18,19,21,22,23,26,27,28,30,
   32,35,36,42,46,48,53,55,56,57,58,59,60,62]

def basis2 : List Nat :=
  [2,6,9,11,14,15,16,18,19,20,22,25,26,27,28,29,30,32,
   35,36,37,38,45,46,48,49,51,53,56,57,58,60]

def basis : Fin 3 -> List Nat := ![basis0, basis1, basis2]

def outside0 : Fin 31 -> Nat := ![
  1,3,5,7,10,12,13,17,18,19,20,21,27,30,35,39,40,41,43,45,46,47,51,52,53,54,59,60,61,62,63]

def outside1 : Fin 31 -> Nat := ![
  0,2,4,7,9,11,12,14,16,20,24,25,29,31,33,34,37,38,39,40,41,43,44,45,47,49,50,51,52,54,61]

def outside2 : Fin 31 -> Nat := ![
  0,1,3,4,5,7,8,10,12,13,17,21,23,24,31,33,34,39,40,41,42,43,44,47,50,52,54,55,59,62,63]

def outside : Fin 3 -> Fin 31 -> Nat := ![outside0, outside1, outside2]

def coreOf (i : Fin 93) : Fin 3 := ⟨i.val / 31, by omega⟩
def slotOf (i : Fin 93) : Fin 31 := ⟨i.val % 31, Nat.mod_lt _ (by norm_num)⟩
def outsideOf (i : Fin 93) : Nat := outside (coreOf i) (slotOf i)

def modDiff (a b : Nat) : Nat := (a + modulus - b) % modulus

theorem domainNat_lt_modulus (i : Nat) : domainNat i < modulus :=
  productMod_lt modulus (by norm_num [modulus, P]) _

theorem natCast_modDiff_of_lt (a b : Nat) (hb : b < modulus) :
    ((modDiff a b : Nat) : ZMod modulus) =
      (a : ZMod modulus) - (b : ZMod modulus) := by
  rw [modDiff, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add,
    ZMod.natCast_self, add_zero]

theorem natCast_domainDiff (i j : Nat) :
    ((modDiff (domainNat i) (domainNat j) : Nat) : ZMod modulus) =
      (domainNat i : ZMod modulus) - (domainNat j : ZMod modulus) :=
  natCast_modDiff_of_lt _ _ (domainNat_lt_modulus j)

def numeratorFactors (c : Fin 3) (outsideCoord coord : Nat) : List Nat :=
  ((basis c).erase coord).map fun h => modDiff (domainNat outsideCoord) (domainNat h)

def denominatorFactors (c : Fin 3) (coord : Nat) : List Nat :=
  ((basis c).erase coord).map fun h => modDiff (domainNat coord) (domainNat h)

def numeratorZ (c : Fin 3) (outsideCoord coord : Nat) : ZMod modulus :=
  (((basis c).erase coord).map fun h =>
    (domainNat outsideCoord : ZMod modulus) - (domainNat h : ZMod modulus)).prod

def denominatorZ (c : Fin 3) (coord : Nat) : ZMod modulus :=
  (((basis c).erase coord).map fun h =>
    (domainNat coord : ZMod modulus) - (domainNat h : ZMod modulus)).prod

theorem natCast_numeratorProduct (c : Fin 3) (outsideCoord coord : Nat) :
    (productMod modulus (numeratorFactors c outsideCoord coord) : ZMod modulus) =
      numeratorZ c outsideCoord coord := by
  rw [natCast_productMod]
  apply congrArg List.prod
  simp only [numeratorFactors, List.map_map]
  apply List.map_congr_left
  intro h _
  exact natCast_domainDiff outsideCoord h

theorem natCast_denominatorProduct (c : Fin 3) (coord : Nat) :
    (productMod modulus (denominatorFactors c coord) : ZMod modulus) =
      denominatorZ c coord := by
  rw [natCast_productMod]
  apply congrArg List.prod
  simp only [denominatorFactors, List.map_map]
  apply List.map_congr_left
  intro h _
  exact natCast_domainDiff coord h

def checkedCoord : Fin 5 -> Nat := ![0, 1, 2, 6, 15]

theorem denominatorProduct_lt (c : Fin 3) (coord : Nat) :
    productMod modulus (denominatorFactors c coord) < modulus :=
  productMod_lt modulus (by norm_num [modulus, P]) _


/-- Kernel-cheap square-and-multiply modulo the prize prime. -/
def modPowAux (a n : Nat) : Nat -> Nat
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then modPowAux ((a * a) % modulus) (n / 2) fuel
      else (a * modPowAux ((a * a) % modulus) (n / 2) fuel) % modulus

def modPow (a n : Nat) : Nat := modPowAux a n (n + 1)
def inverseNat (a : Nat) : Nat := modPow a (modulus - 2)

/-- The natural square-and-multiply evaluator has the expected meaning after
casting to the residue field. -/
theorem natCast_modPowAux_eq_pow (a n fuel : Nat) (hnfuel : n < fuel) :
    ((modPowAux a n fuel : Nat) : ZMod modulus) = (a : ZMod modulus) ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [modPowAux]
      split_ifs with hzero heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih ((a * a) % modulus) (n / 2) hhalf, ZMod.natCast_mod,
          Nat.cast_mul, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr heven
        congr 1
        exact Nat.mul_div_cancel' hdvd
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ZMod.natCast_mod, Nat.cast_mul,
          ih ((a * a) % modulus) (n / 2) hhalf, ZMod.natCast_mod,
          Nat.cast_mul, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        congr 1
        have hdecomp := Nat.mod_add_div n 2
        omega

theorem natCast_modPow (a n : Nat) :
    ((modPow a n : Nat) : ZMod modulus) = (a : ZMod modulus) ^ n :=
  natCast_modPowAux_eq_pow a n (n + 1) (by omega)

theorem natCast_inverseNat (a : Nat) (ha : (a : ZMod modulus) ≠ 0) :
    ((inverseNat a : Nat) : ZMod modulus) = (a : ZMod modulus)⁻¹ := by
  rw [inverseNat, natCast_modPow]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact ZMod.pow_card_sub_one_eq_one ha

theorem natCast_modNeg (a : Nat) :
    (((modulus - a % modulus) % modulus : Nat) : ZMod modulus) =
      -(a : ZMod modulus) := by
  have hle : a % modulus ≤ modulus :=
    (Nat.mod_lt _ (by norm_num [modulus, P])).le
  calc
    (((modulus - a % modulus) % modulus : Nat) : ZMod modulus) =
        ((modulus - a % modulus : Nat) : ZMod modulus) := ZMod.natCast_mod _ _
    _ = (modulus : ZMod modulus) - ((a % modulus : Nat) : ZMod modulus) := by
      rw [Nat.cast_sub hle]
    _ = -(a : ZMod modulus) := by
      rw [ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

theorem natCast_domainNat (i : Nat) :
    ((domainNat i : Nat) : ZMod modulus) =
      (baseGeneratorNat : ZMod modulus) ^ i := by
  rw [domainNat, natCast_productMod]
  rw [List.map_replicate]
  simp

theorem baseGeneratorNat_eq_prize_power :
    modPow (ArkLib.ProximityGap.PrizeShapePrimeP30.g.val) (2 ^ 24) =
      baseGeneratorNat := by decide

theorem baseGenerator_cast_eq :
    (baseGeneratorNat : ZMod modulus) =
      ArkLib.ProximityGap.PrizeShapePrimeP30.g ^ (2 ^ 24 : Nat) := by
  rw [← baseGeneratorNat_eq_prize_power, natCast_modPow]
  simp only [ZMod.natCast_zmod_val]

theorem domainNat_cast_eq_prize_domain (i : Nat) :
    ((domainNat i : Nat) : ZMod modulus) =
      ArkLib.ProximityGap.PrizeShapePrimeP30.g ^ (2 ^ 24 * i) := by
  rw [natCast_domainNat, baseGenerator_cast_eq, ← pow_mul]

theorem baseGenerator_order :
    orderOf (baseGeneratorNat : ZMod modulus) = 64 := by
  have hdvd : 2 ^ 24 ∣ orderOf PrizeShapePrimeP30.g := by
    rw [PrizeShapePrimeP30.orderOf_g]
    norm_num
  rw [baseGenerator_cast_eq,
    orderOf_pow_of_dvd (x := PrizeShapePrimeP30.g) (by norm_num) hdvd,
    PrizeShapePrimeP30.orderOf_g]
  norm_num

theorem domainNat_cast_injective_below_64
    {i j : Nat} (hi : i < 64) (hj : j < 64)
    (heq : (domainNat i : ZMod modulus) = (domainNat j : ZMod modulus)) : i = j := by
  rw [natCast_domainNat, natCast_domainNat] at heq
  apply pow_injOn_Iio_orderOf (x := (baseGeneratorNat : ZMod modulus))
  · rw [baseGenerator_order]
    exact hi
  · rw [baseGenerator_order]
    exact hj
  · exact heq

theorem basis_nodup_and_lt : forall c,
    (basis c).Nodup ∧ forall h, h ∈ basis c -> h < 64 := by decide

theorem denominatorZ_ne_zero
    (c : Fin 3) (coord : Nat) (hcoord : coord ∈ basis c) :
    denominatorZ c coord ≠ 0 := by
  rw [denominatorZ]
  apply List.prod_ne_zero
  intro hzero
  simp only [List.mem_map] at hzero
  obtain ⟨h, hh, hdiff⟩ := hzero
  have hh' : h ≠ coord ∧ h ∈ basis c :=
    ((basis_nodup_and_lt c).1.mem_erase_iff).mp hh
  have hhc : h ≠ coord := by
    exact hh'.1
  have hhmem : h ∈ basis c := hh'.2
  have hlt := (basis_nodup_and_lt c).2 h hhmem
  have hcoordlt := (basis_nodup_and_lt c).2 coord hcoord
  apply hhc
  apply domainNat_cast_injective_below_64 hlt hcoordlt
  exact (sub_eq_zero.mp hdiff).symm

theorem denominatorProduct_cast_ne_zero
    (c : Fin 3) (q : Fin 5) (hcoord : checkedCoord q ∈ basis c) :
    (productMod modulus (denominatorFactors c (checkedCoord q)) : ZMod modulus) ≠ 0 := by
  rw [natCast_denominatorProduct]
  exact denominatorZ_ne_zero c (checkedCoord q) hcoord

/-- Coefficient of the external interpolation defect. -/
def defectNat (c : Fin 3) (outsideCoord coord : Nat) : Nat :=
  if coord = outsideCoord then 1
  else if coord ∈ basis c then
    (modulus - productMod modulus (numeratorFactors c outsideCoord coord) *
      inverseNat (productMod modulus (denominatorFactors c coord)) % modulus) % modulus
  else 0

def defectZ (c : Fin 3) (outsideCoord coord : Nat) : ZMod modulus :=
  if coord = outsideCoord then 1
  else if coord ∈ basis c then
    -(numeratorZ c outsideCoord coord / denominatorZ c coord)
  else 0

theorem natCast_defectNat_checked
    (c : Fin 3) (outsideCoord : Nat) (q : Fin 5) :
    (defectNat c outsideCoord (checkedCoord q) : ZMod modulus) =
      defectZ c outsideCoord (checkedCoord q) := by
  by_cases heq : checkedCoord q = outsideCoord
  · simp [defectNat, defectZ, heq]
  by_cases hmem : checkedCoord q ∈ basis c
  · simp only [defectNat, defectZ, heq, hmem, if_false, if_true]
    rw [natCast_modNeg, Nat.cast_mul,
      natCast_numeratorProduct, natCast_inverseNat,
      natCast_denominatorProduct]
    · simp [div_eq_mul_inv]
    · rw [natCast_denominatorProduct]
      exact denominatorZ_ne_zero c (checkedCoord q) hmem
  · simp [defectNat, defectZ, heq, hmem]

abbrev row0At6 : Nat := 240972375945632963342224903776639644690796586856
abbrev row1At6 : Nat := 83135197273689243477588137888062899021486972753
abbrev row2At6 : Nat := 63491388653432640767466837058092486385509547035
abbrev row0At15 : Nat := 268601307306210571600803297347436836967476343200
abbrev row1At15 : Nat := 228003850430197349733176828707999312919007092681
abbrev row2At15 : Nat := 337296824443171766836803838974401544918005647694

def reducedNat (c : Fin 3) (outsideCoord target r0 r1 r2 : Nat) : Nat :=
  (defectNat c outsideCoord target + 3 * modulus -
      defectNat c outsideCoord 0 * r0 % modulus -
      defectNat c outsideCoord 1 * r1 % modulus -
      defectNat c outsideCoord 2 * r2 % modulus) % modulus

theorem defectNat_lt_modulus (c : Fin 3) (outsideCoord coord : Nat) :
    defectNat c outsideCoord coord < modulus := by
  rw [defectNat]
  split_ifs
  · norm_num [modulus, P]
  · exact Nat.mod_lt _ (by norm_num [modulus, P])
  · norm_num [modulus, P]

theorem natCast_reducedNat
    (c : Fin 3) (outsideCoord target r0 r1 r2 : Nat) :
    (reducedNat c outsideCoord target r0 r1 r2 : ZMod modulus) =
      (defectNat c outsideCoord target : ZMod modulus) -
        (defectNat c outsideCoord 0 : ZMod modulus) * (r0 : ZMod modulus) -
        (defectNat c outsideCoord 1 : ZMod modulus) * (r1 : ZMod modulus) -
        (defectNat c outsideCoord 2 : ZMod modulus) * (r2 : ZMod modulus) := by
  let d := defectNat c outsideCoord target
  let t0 := defectNat c outsideCoord 0 * r0 % modulus
  let t1 := defectNat c outsideCoord 1 * r1 % modulus
  let t2 := defectNat c outsideCoord 2 * r2 % modulus
  have hd : d < modulus := defectNat_lt_modulus _ _ _
  have ht0 : t0 < modulus := Nat.mod_lt _ (by norm_num [modulus, P])
  have ht1 : t1 < modulus := Nat.mod_lt _ (by norm_num [modulus, P])
  have ht2 : t2 < modulus := Nat.mod_lt _ (by norm_num [modulus, P])
  have hsub0 : t0 ≤ d + 3 * modulus := by omega
  have hsub1 : t1 ≤ d + 3 * modulus - t0 := by omega
  have hsub2 : t2 ≤ d + 3 * modulus - t0 - t1 := by omega
  rw [reducedNat]
  change (((d + 3 * modulus - t0 - t1 - t2) % modulus : Nat) : ZMod modulus) = _
  rw [ZMod.natCast_mod, Nat.cast_sub hsub2, Nat.cast_sub hsub1,
    Nat.cast_sub hsub0]
  have hmod : (modulus : ZMod modulus) = 0 := ZMod.natCast_self modulus
  rw [Nat.cast_add, Nat.cast_mul, hmod, mul_zero, add_zero]
  dsimp only [d, t0, t1, t2]
  rw [ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_mod,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]

def reduced6 (i : Fin 93) : Nat :=
  reducedNat (coreOf i) (outsideOf i) 6 row0At6 row1At6 row2At6

def reduced15 (i : Fin 93) : Nat :=
  reducedNat (coreOf i) (outsideOf i) 15 row0At15 row1At15 row2At15

def chartNat (i : Fin 93) : Nat :=
  reduced15 i * inverseNat (reduced6 i) % modulus

set_option maxHeartbeats 4000000 in
-- Each block kernel-evaluates up to 31 large modular certificates.
private theorem reduced6_ne_zero_block0 (i : Fin 93) (hi : i.val < 31) :
    reduced6 i ≠ 0 := by
  fin_cases i <;> first | omega | decide

set_option maxHeartbeats 4000000 in
-- Each block kernel-evaluates up to 31 large modular certificates.
private theorem reduced6_ne_zero_block1 (i : Fin 93) (hlo : 31 ≤ i.val) (hi : i.val < 62) :
    reduced6 i ≠ 0 := by
  fin_cases i <;> first | omega | decide

set_option maxHeartbeats 4000000 in
-- Each block kernel-evaluates up to 31 large modular certificates.
private theorem reduced6_ne_zero_block2 (i : Fin 93) (hlo : 62 ≤ i.val) :
    reduced6 i ≠ 0 := by
  fin_cases i <;> first | omega | decide

/-- Every direction lies in the common coordinate-6 chart. -/
theorem reduced6_ne_zero : forall i, reduced6 i ≠ 0 := by
  intro i
  by_cases h0 : i.val < 31
  · exact reduced6_ne_zero_block0 i h0
  by_cases h1 : i.val < 62
  · exact reduced6_ne_zero_block1 i (by omega) h1
  · exact reduced6_ne_zero_block2 i (by omega)

set_option maxHeartbeats 4000000 in
-- Each block kernel-evaluates up to 31 large modular certificates.
private theorem chartNat_eq_fingerprintNat_block0 (i : Fin 93) (hi : i.val < 31) :
    chartNat i = fingerprintNat i := by
  fin_cases i <;> first | omega | decide

set_option maxHeartbeats 4000000 in
-- Each block kernel-evaluates up to 31 large modular certificates.
private theorem chartNat_eq_fingerprintNat_block1 (i : Fin 93) (hlo : 31 ≤ i.val)
    (hi : i.val < 62) : chartNat i = fingerprintNat i := by
  fin_cases i <;> first | omega | decide

set_option maxHeartbeats 4000000 in
-- Each block kernel-evaluates up to 31 large modular certificates.
private theorem chartNat_eq_fingerprintNat_block2 (i : Fin 93) (hlo : 62 ≤ i.val) :
    chartNat i = fingerprintNat i := by
  fin_cases i <;> first | omega | decide

/-- The natural evaluator reproduces the compact fingerprint table exactly. -/
theorem chartNat_eq_fingerprintNat : forall i, chartNat i = fingerprintNat i := by
  intro i
  by_cases h0 : i.val < 31
  · exact chartNat_eq_fingerprintNat_block0 i h0
  by_cases h1 : i.val < 62
  · exact chartNat_eq_fingerprintNat_block1 i (by omega) h1
  · exact chartNat_eq_fingerprintNat_block2 i (by omega)

def reducedZ (c : Fin 3) (outsideCoord target r0 r1 r2 : Nat) : ZMod modulus :=
  defectZ c outsideCoord target - defectZ c outsideCoord 0 * r0 -
    defectZ c outsideCoord 1 * r1 - defectZ c outsideCoord 2 * r2

def reduced6Z (i : Fin 93) : ZMod modulus :=
  reducedZ (coreOf i) (outsideOf i) 6 row0At6 row1At6 row2At6

def reduced15Z (i : Fin 93) : ZMod modulus :=
  reducedZ (coreOf i) (outsideOf i) 15 row0At15 row1At15 row2At15

def chartZ (i : Fin 93) : ZMod modulus := reduced15Z i / reduced6Z i

theorem natCast_reduced6 (i : Fin 93) :
    (reduced6 i : ZMod modulus) = reduced6Z i := by
  rw [reduced6, reduced6Z, reducedZ, natCast_reducedNat]
  rw [show (defectNat (coreOf i) (outsideOf i) 6 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 6 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (3 : Fin 5),
    show (defectNat (coreOf i) (outsideOf i) 0 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 0 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (0 : Fin 5),
    show (defectNat (coreOf i) (outsideOf i) 1 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 1 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (1 : Fin 5),
    show (defectNat (coreOf i) (outsideOf i) 2 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 2 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (2 : Fin 5)]

theorem natCast_reduced15 (i : Fin 93) :
    (reduced15 i : ZMod modulus) = reduced15Z i := by
  rw [reduced15, reduced15Z, reducedZ, natCast_reducedNat]
  rw [show (defectNat (coreOf i) (outsideOf i) 15 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 15 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (4 : Fin 5),
    show (defectNat (coreOf i) (outsideOf i) 0 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 0 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (0 : Fin 5),
    show (defectNat (coreOf i) (outsideOf i) 1 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 1 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (1 : Fin 5),
    show (defectNat (coreOf i) (outsideOf i) 2 : ZMod modulus) =
      defectZ (coreOf i) (outsideOf i) 2 by
        simpa [checkedCoord] using
          natCast_defectNat_checked (coreOf i) (outsideOf i) (2 : Fin 5)]

theorem reduced6_lt_modulus (i : Fin 93) : reduced6 i < modulus :=
  Nat.mod_lt _ (by norm_num [modulus, P])

theorem reduced6Z_ne_zero (i : Fin 93) : reduced6Z i ≠ 0 := by
  rw [← natCast_reduced6]
  intro hzero
  have hval := congrArg ZMod.val hzero
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (reduced6_lt_modulus i)] at hval
  simp only [ZMod.val_zero] at hval
  exact reduced6_ne_zero i hval

private theorem natCast_chartNat_of_ne_zero (i : Fin 93)
    (h : (reduced6 i : ZMod modulus) ≠ 0) :
    (chartNat i : ZMod modulus) = chartZ i := by
  rw [chartNat, chartZ, ZMod.natCast_mod, Nat.cast_mul,
    natCast_inverseNat _ h, natCast_reduced15, natCast_reduced6]
  rw [div_eq_mul_inv]

theorem natCast_chartNat (i : Fin 93) :
    (chartNat i : ZMod modulus) = chartZ i := by
  apply natCast_chartNat_of_ne_zero
  rw [natCast_reduced6]
  exact reduced6Z_ne_zero i

theorem chartZ_eq_fingerprint (i : Fin 93) : chartZ i = fingerprint i := by
  rw [← natCast_chartNat, chartNat_eq_fingerprintNat i]
  rfl

end ArkLib.ProximityGap.Frontier.RateHalfBaseFingerprintNatCertificate

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateHalfBaseFingerprintNatCertificate
#print axioms reduced6_ne_zero
#print axioms chartNat_eq_fingerprintNat
#print axioms natCast_modPow
#print axioms natCast_inverseNat
#print axioms domainNat_cast_eq_prize_domain
#print axioms natCast_numeratorProduct
#print axioms natCast_denominatorProduct
#print axioms denominatorZ_ne_zero
#print axioms natCast_defectNat_checked
