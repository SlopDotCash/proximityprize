#!/usr/bin/env python3
"""W7 fingerprint-seal generator for the rate-half three-core radix counterexample.

Recomputes the exact row-reduction data of
`probe_rate_half_three_core_radix_counterexample.py` (read-only sibling probe),
verifies every intermediate constant, and emits the Lean scalar-evaluation
certificate `_W7RateHalfFingerprintSeal*.lean` data blocks on request.

Checks performed here (all exact, modulo the certified prime P):
  * base generator = g^(2^24), order 64, half-order gives -1;
  * the three 33-cores from the published masks; basis = sorted(core)[:32];
  * RREF of the three parity checks has pivots (0,1,2);
  * the six reduced-row constants at coordinates 6 and 15;
  * reduced defect values at coordinates 0,1,2,6,15 for all 93 directions
    (coords 0,1,2 vanish after reduction -- the canonical-representative check);
  * reduced6 != 0 for all j and reduced15/reduced6 = fingerprint_j matching the
    93-entry table of `Frontier/_RateHalfBaseFingerprintTable.lean`.
"""

import json
import sys

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
M = 2**24
BASE_LENGTH = 64
BASE_DIMENSION = 32

CORE_MASKS = [
    542424784538028885,
    16114235817432360298,
    3975377171011979844,
]

# 93-entry fingerprint table copied verbatim from
# Frontier/_RateHalfBaseFingerprintTable.lean (fingerprintNat).
FINGERPRINT_TABLE = [
    6524216619379419265027960032285007280893416965,
    124045888548991012736551520256877363283554819126,
    78205154655305592335202998084031357481682584985,
    193163137771712671399382555976978509067032379327,
    80405763652083154931159960361737193112124351887,
    233209580125730856075147370922624716358323973644,
    63500761785130131375806454974459905064328302409,
    255271560274919704367899464910020595596305052979,
    23218018856862058350780878839988572819246617791,
    327968385387143433355941028662515983003555122452,
    160227487706596530280162528523106857477904018409,
    350066523534860444954003745662062651141265912872,
    247375374864416193136572476606388625351761672888,
    19152798527870669990011534388362830168229803478,
    327800481380033275466383605881432803796081172570,
    8758918359624234876649019779507409579865834583,
    32662660518444309544028608452408812686536313085,
    322757489273476040533894234847536105439978835461,
    228977910271476943702717001844190279532546087657,
    103046290960354110358959156733706599594187337050,
    157797791731897865391506902775241396691019619269,
    137047700522270319501854905935916932226959007359,
    131960141982292042329686819381209987500809960271,
    304690352079809913371286578201207705457482375165,
    336753677675989098798027218305782685865790219090,
    355954687579624268554276994344975936368224276880,
    139633254193999289888939480853440839629936389340,
    141751582429381237706743011508296641668266808232,
    279740617563882562523848563003446383662202245636,
    131823367490334859432005074315257073954562062752,
    359667351493780480783782066520321081523604711712,
    242414808873686220968007206655632129203548729448,
    138263457746687149530300047949748173509393533449,
    221850621812594939052438426941778736087519426184,
    277592505980696768087647951861044698282535905620,
    356652007073726325362218282000107144207644595322,
    252452731526049864794473861435024994767742927417,
    142623155316006674093120682369561121464590778775,
    160573670249780903752970269277377435091935729524,
    279978407065829833991792435262396706952298556237,
    247361413343501707437065819658213115674546547523,
    75176667982885008193841496360703386924092719808,
    317605262987410174573200345138873593258567263078,
    105342519473030271217590481482748338161978472139,
    198542067850714490487364434347611029597163042271,
    305805445250679395751630309627464431731696556207,
    55803696533312492916550270037410774191622803524,
    315179611673057301103228756955997021054665204795,
    269493264129862683986264789824619420625075459108,
    206427512949095726427148588523281526611606581360,
    298841136466685667950929925604265079861041718647,
    136868521762370108693503889343212603274729878238,
    302732280435343671380822042287064401797328883823,
    205305449498720247080394673451582411830556845916,
    247222755712635283276891364512359244482140415229,
    37588333991442504096920748180351693462046359904,
    193329321602975454467871340027414897562093870532,
    235246627816890490664368031088191730213677439845,
    137819796880267066363940662252709740246905401938,
    22473703298592912158413662440463315722446412680,
    141710940848925069793832778935509062183192567114,
    134746632064931341993132394912309710312537729554,
    268034455056125492782044832515486280524632269565,
    280384322054880254845585159087635324640070213483,
    257173911236812697240492113010413275005749511866,
    350122604952306266813759635061499055954229496958,
    95251791767022357444218835704023667080625045909,
    192764302054317204352458229514277488856560114488,
    141023403904683691480536701831368356626086440254,
    323067364520036363119263659095390595241599755027,
    327296330549663588109344172166560797306071936879,
    116813929089819384338817592311201993338063192907,
    97780344044954062752999670716685216550333530861,
    157272829917118727340755757866966840830406340771,
    21829971080456242739359033513609721031836609280,
    214594273134773447091817263027887209888396723768,
    285666828152390618209027296047448528597118602072,
    44177871775144706979071583254440014730428385128,
    335650038642704830628915551035483425671861050931,
    30465997243174182964042912625670628846137694857,
    7186056602083308053912767094400036521272374956,
    91650969923244945179001512680835425833367074782,
    232811628346734081320095220491727494039791902744,
    338140676786872208494129708258760481796413610378,
    152721965218371580943700046334350695930050395068,
    107297136567386723545908631513943604944198361884,
    61872307916401866148117216693536513958346328700,
    347158054120765095322643250715230470968746386977,
    207408216532690139037904495933487173367124348812,
    184128275891599264127774350402216581042259028911,
    103511632588387616076760675233867322809628177812,
    81691221358082787513702789644468558453813714546,
    294302854315108558433711175159509436411419687649,
]


def inverse(value: int) -> int:
    return pow(value, P - 2, P)


base_generator = pow(G, M, P)
assert pow(base_generator, BASE_LENGTH, P) == 1
assert pow(base_generator, BASE_LENGTH // 2, P) == P - 1
domain = [pow(base_generator, i, P) for i in range(BASE_LENGTH)]
cores = [
    {i for i in range(BASE_LENGTH) if (mask >> i) & 1}
    for mask in CORE_MASKS
]
assert all(len(core) == 33 for core in cores)


def core_constraint(core: set[int]) -> list[int]:
    result = [0] * BASE_LENGTH
    for i in core:
        denominator = 1
        for j in core:
            if i != j:
                denominator = denominator * (domain[i] - domain[j]) % P
        result[i] = inverse(denominator)
    return result


def external_defect(core: set[int], outside: int) -> list[int]:
    basis = sorted(core)[:BASE_DIMENSION]
    result = [0] * BASE_LENGTH
    result[outside] = 1
    for j in basis:
        numerator = 1
        denominator = 1
        for h in basis:
            if h != j:
                numerator = numerator * (domain[outside] - domain[h]) % P
                denominator = denominator * (domain[j] - domain[h]) % P
        result[j] = -numerator * inverse(denominator) % P
    return result


def rref(rows: list[list[int]]) -> tuple[list[list[int]], list[int]]:
    rows = [row[:] for row in rows]
    pivots: list[int] = []
    for rank in range(len(rows)):
        pivot = next(
            column
            for column in range(BASE_LENGTH)
            if any(rows[j][column] for j in range(rank, len(rows)))
        )
        source = next(j for j in range(rank, len(rows)) if rows[j][pivot])
        rows[rank], rows[source] = rows[source], rows[rank]
        scale = inverse(rows[rank][pivot])
        rows[rank] = [entry * scale % P for entry in rows[rank]]
        for j in range(len(rows)):
            if j != rank and rows[j][pivot]:
                scale = rows[j][pivot]
                rows[j] = [
                    (entry - scale * pivot_entry) % P
                    for entry, pivot_entry in zip(rows[j], rows[rank])
                ]
        pivots.append(pivot)
    return rows, pivots


constraint_rows, pivots = rref([core_constraint(core) for core in cores])

bases = [sorted(core)[:BASE_DIMENSION] for core in cores]
outsides = [sorted(set(range(BASE_LENGTH)) - core) for core in cores]

raw_defects = [
    external_defect(cores[c], outside)
    for c in range(3)
    for outside in outsides[c]
]


def reduce_vector(vector: list[int]) -> list[int]:
    vector = vector[:]
    for row, pivot in zip(constraint_rows, pivots):
        scale = vector[pivot]
        if scale:
            vector = [
                (entry - scale * pivot_entry) % P
                for entry, pivot_entry in zip(vector, row)
            ]
    return vector


reduced = [reduce_vector(v) for v in raw_defects]


# ---------------------------------------------------------------------------
# Exact mirror of the Lean-side evaluator in _W7RateHalfFingerprintSeal.lean.
# Any drift between these functions and the emitted Lean definitions is a bug;
# the assertions in `verify_lean_semantics` are the fabricate-then-refute gate.
# ---------------------------------------------------------------------------


def lean_getD(lst: list[int], i: int, default: int) -> int:
    return lst[i] if i < len(lst) else default


def lean_dom(i: int) -> int:
    return lean_getD(domain, i, 0)


def lean_mulP(a: int, b: int) -> int:
    return a * b % P


def lean_subP(a: int, b: int) -> int:
    return (a + P - b) % P


def lean_prodP(lst: list[int]) -> int:
    value = 1
    for x in reversed(lst):
        value = lean_mulP(x, value)
    return value


def lean_erase_first(lst: list[int], a: int) -> list[int]:
    out = list(lst)
    if a in out:
        out.remove(a)
    return out


def lean_invP(a: int) -> int:
    # powAux with fuel >= log2(n)+1 is plain binary powmod.
    return pow(a, P - 2, P)


def lean_defectN(c: int, outside_coord: int, coord: int) -> int:
    if coord == outside_coord:
        return 1
    if coord in bases[c]:
        numer = lean_prodP(
            [
                lean_subP(lean_dom(outside_coord), lean_dom(h))
                for h in lean_erase_first(bases[c], coord)
            ]
        )
        denom = lean_prodP(
            [
                lean_subP(lean_dom(coord), lean_dom(h))
                for h in lean_erase_first(bases[c], coord)
            ]
        )
        return lean_subP(0, lean_mulP(numer, lean_invP(denom)))
    return 0


def lean_directionNat(i: int, c: int) -> int:
    core = i // 31
    outside_coord = outsides[core][i % 31]
    d0 = lean_defectN(core, outside_coord, 0)
    d1 = lean_defectN(core, outside_coord, 1)
    d2 = lean_defectN(core, outside_coord, 2)
    combo = (
        d0 * constraint_rows[0][c]
        + d1 * constraint_rows[1][c]
        + d2 * constraint_rows[2][c]
    ) % P
    return lean_subP(lean_defectN(core, outside_coord, c), combo)


def verify_lean_semantics() -> None:
    reduced6 = [v[6] for v in reduced]
    reduced15 = [v[15] for v in reduced]
    for i in range(93):
        lhs6 = lean_directionNat(i, 6)
        lhs15 = lean_directionNat(i, 15)
        assert lhs6 == reduced6[i], (i, lhs6, reduced6[i])
        assert lhs15 == reduced15[i], (i, lhs15, reduced15[i])
        assert lhs6 != 0
        assert lean_mulP(lhs15, lean_invP(lhs6)) == FINGERPRINT_TABLE[i]
    # pivot normalization of the emitted rows
    for k in range(3):
        for ell in range(3):
            assert constraint_rows[k][ell] == (1 if k == ell else 0)


def fmt_nat_list(values: list[int], indent: str) -> str:
    body = (",\n").join(f"{indent}{v}" for v in values)
    return body


def fmt_bang_vec(values: list[int], indent: str) -> str:
    body = (",\n").join(f"{indent}{v}" for v in values)
    return body


LEAN_HEADER = """/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RankOneTensorProjectiveInjection

/-!
# W7 seal: the 186 scalar evaluation facts of the rate-half three-core base certificate

`docs/kb/deltastar-466-rate-half-three-core-radix-counterexample-2026-07-10.md` reduces the
base separation of the three-core radix counterexample to 186 scalar facts: for each of the
93 external-defect directions, the exact row-reduced representative is nonzero at coordinate 6
and its coordinate-15/coordinate-6 ratio equals the published fingerprint.

This file discharges all 186 facts by kernel computation and composes them with the
(restated) chart lemmas of `Frontier/_RateHalfBaseFingerprintTable.lean` into
hypothesis-free projective-separation theorems for the concrete direction family.

Definitional shape (mirrors `scripts/probes/probe_rate_half_three_core_radix_counterexample.py`,
regenerated and re-verified by `scripts/probes/probe_w7_emit_fingerprint_lemmas.py`):

* `dom i` — the 64 points of `mu_64` inside the certified field, as natural residues;
* `defectN c out coord` — the external interpolation defect of core `c` at evaluation
  point `out`, coordinate `coord` (Lagrange formula on the 32-point interpolation basis);
* `rowTab` — the reduced row echelon form (pivots 0,1,2) of the three 33-point parity
  checks, i.e. the canonical basis of the annihilator used for row reduction;
* `directionNat i` — the canonical reduced representative of the `i`-th defect:
  `defect - defect[0]*row0 - defect[1]*row1 - defect[2]*row2`;
* `direction i` — the same family in `ZMod P`.

All arithmetic is `Nat`-mod arithmetic with a proved cast bridge to `ZMod P`, following the
`binaryPow` precedent of `_PrizeShapePrimeP30.lean`.  This file is deliberately
self-contained (it does not import the in-flight table file); its `fingerprintNat` is
literal-identical to `_RateHalfBaseFingerprintTable.fingerprintNat`, so the final splice can
identify the two by `rfl`.

Generated by `scripts/probes/probe_w7_emit_fingerprint_lemmas.py --emit-lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace ArkLib.ProximityGap.Frontier.W7RateHalfFingerprintSeal

open ArkLib.ProximityGap.PrizeShapePrimeP30

/-! ## Data tables (verified against the executable probe) -/
"""

LEAN_CODE = """
/-! ## Exact modular arithmetic (kernel-cheap shapes) -/

/-- The `i`-th point of `mu_64` as a natural residue (`0` out of range). -/
def dom (i : Nat) : Nat := domList.getD i 0

def mulP (a b : Nat) : Nat := a * b % P

def subP (a b : Nat) : Nat := (a + P - b) % P

def prodP : List Nat -> Nat
  | [] => 1
  | x :: xs => mulP x (prodP xs)

/-- Structurally recursive fuel wrapper for kernel-cheap square-and-multiply
(shape from `_PrizeShapePrimeP30.binaryPowAux`). -/
def powAux (a n : Nat) : Nat -> Nat
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then powAux (mulP a a) (n / 2) fuel
      else mulP a (powAux (mulP a a) (n / 2) fuel)

def powP (a n : Nat) : Nat := powAux a n (n + 1)

def invP (a : Nat) : Nat := powP a (P - 2)

/-! ## The Lagrange defect and its canonical row reduction -/

/-- Numerator factors of the external interpolation defect. -/
def numerFactors (c : Fin 3) (outside coord : Nat) : List Nat :=
  ((basis c).erase coord).map fun h => subP (dom outside) (dom h)

/-- Denominator factors of the external interpolation defect. -/
def denomFactors (c : Fin 3) (coord : Nat) : List Nat :=
  ((basis c).erase coord).map fun h => subP (dom coord) (dom h)

/-- Coefficient of the external interpolation defect for core `c` at outside
point `outside`, coordinate `coord`. -/
def defectN (c : Fin 3) (outside coord : Nat) : Nat :=
  if coord = outside then 1
  else if coord ∈ basis c then
    subP 0 (mulP (prodP (numerFactors c outside coord))
      (invP (prodP (denomFactors c coord))))
  else 0

def coreOf (i : Fin 93) : Fin 3 := ⟨i.val / 31, by have := i.isLt; omega⟩

def slotOf (i : Fin 93) : Fin 31 := ⟨i.val % 31, Nat.mod_lt _ (by norm_num)⟩

def outsideOf (i : Fin 93) : Nat := outside (coreOf i) (slotOf i)

/-- The canonical reduced representative of the `i`-th external defect:
subtract the pivot components against the reduced parity-check rows. -/
def directionNat (i : Fin 93) (c : Fin 64) : Nat :=
  subP (defectN (coreOf i) (outsideOf i) c.val)
    ((defectN (coreOf i) (outsideOf i) 0 * rowTab 0 c
      + defectN (coreOf i) (outsideOf i) 1 * rowTab 1 c
      + defectN (coreOf i) (outsideOf i) 2 * rowTab 2 c) % P)

/-! ## The 186 scalar evaluation facts (kernel-checked) -/

/-- 93 facts: every reduced direction is nonzero at chart coordinate 6. -/
theorem directionNat_six_ne_zero : forall i : Fin 93, directionNat i 6 ≠ 0 := by
  decide +kernel

/-- 93 facts: the coordinate-15/coordinate-6 chart ratio is the published fingerprint. -/
theorem directionNat_chart_eval :
    forall i : Fin 93, mulP (directionNat i 15) (invP (directionNat i 6)) =
      fingerprintNat i := by
  decide +kernel

/-- The reduction rows are pivot-normalized at columns 0,1,2 (RREF shape). -/
theorem rowTab_pivot :
    forall k l : Fin 3, rowTab k ⟨l.val, by have := l.isLt; omega⟩ =
      if k = l then 1 else 0 := by
  decide

/-! ## Cast bridge to the certified field -/

theorem P_pos : 0 < P := by norm_num

theorem mulP_lt (a b : Nat) : mulP a b < P := Nat.mod_lt _ P_pos

theorem subP_lt (a b : Nat) : subP a b < P := Nat.mod_lt _ P_pos

theorem directionNat_lt (i : Fin 93) (c : Fin 64) : directionNat i c < P :=
  subP_lt _ _

theorem natCast_mulP (a b : Nat) :
    ((mulP a b : Nat) : ZMod P) = (a : ZMod P) * (b : ZMod P) := by
  rw [mulP, ZMod.natCast_mod, Nat.cast_mul]

theorem natCast_subP (a b : Nat) (hb : b ≤ P) :
    ((subP a b : Nat) : ZMod P) = (a : ZMod P) - (b : ZMod P) := by
  rw [subP, ZMod.natCast_mod, Nat.cast_sub (hb.trans (Nat.le_add_left P a)),
    Nat.cast_add, ZMod.natCast_self, add_zero]

theorem natCast_prodP (l : List Nat) :
    ((prodP l : Nat) : ZMod P) = (l.map fun x => (x : ZMod P)).prod := by
  induction l with
  | nil => simp [prodP]
  | cons x xs ih => simp [prodP, natCast_mulP, ih]

theorem natCast_powAux (a n fuel : Nat) (hfuel : n < fuel) :
    ((powAux a n fuel : Nat) : ZMod P) = (a : ZMod P) ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [powAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hpos (by norm_num)).trans_le (by omega)
        rw [ih (mulP a a) (n / 2) hhalf, natCast_mulP, ← pow_two, ← pow_mul]
        congr 1
        exact Nat.mul_div_cancel' ((Nat.dvd_iff_mod_eq_zero).mpr heven)
      · have hpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hpos (by norm_num)).trans_le (by omega)
        rw [natCast_mulP, ih (mulP a a) (n / 2) hhalf, natCast_mulP,
          ← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega

theorem natCast_powP (a n : Nat) :
    ((powP a n : Nat) : ZMod P) = (a : ZMod P) ^ n :=
  natCast_powAux a n (n + 1) (by omega)

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero P := ⟨P_pos.ne'⟩

theorem natCast_ne_zero_of_ne_zero_of_lt {a : Nat} (h0 : a ≠ 0) (hlt : a < P) :
    (a : ZMod P) ≠ 0 := by
  intro h
  have hdvd := (ZMod.natCast_eq_zero_iff a P).mp h
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd) (not_le.mpr hlt)

theorem natCast_invP_eq_inv (a : Nat) (ha : (a : ZMod P) ≠ 0) :
    ((invP a : Nat) : ZMod P) = (a : ZMod P)⁻¹ := by
  rw [invP, natCast_powP]
  have hone : (a : ZMod P) ^ (P - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hexp : P - 2 + 1 = P - 1 := by norm_num
  have hmul : (a : ZMod P) * (a : ZMod P) ^ (P - 2) = 1 := by
    rw [← pow_succ', hexp]
    exact hone
  exact eq_inv_of_mul_eq_one_right hmul

/-! ## The direction family in the certified field -/

/-- The 93 reduced external-defect directions, as vectors in the certified field. -/
def direction (i : Fin 93) (c : Fin 64) : ZMod P := (directionNat i c : ZMod P)

/-- The fingerprint table in the certified field (literal-identical to
`_RateHalfBaseFingerprintTable.fingerprint`). -/
def fingerprint : Fin 93 -> ZMod P := fun i => fingerprintNat i

theorem fingerprintNat_lt_prime : forall i, fingerprintNat i < P := by decide

theorem fingerprintNat_injective : Function.Injective fingerprintNat := by decide

theorem fingerprint_injective : Function.Injective fingerprint := by
  intro i j h
  apply fingerprintNat_injective
  have hval := congrArg ZMod.val h
  rwa [fingerprint, fingerprint, ZMod.val_natCast_of_lt (fingerprintNat_lt_prime i),
    ZMod.val_natCast_of_lt (fingerprintNat_lt_prime j)] at hval

/-- **h6, sealed.**  The first 93 scalar facts in the consumer's field-level shape. -/
theorem direction_six_ne_zero : forall i, direction i 6 ≠ 0 := fun i =>
  natCast_ne_zero_of_ne_zero_of_lt (directionNat_six_ne_zero i) (directionNat_lt i 6)

/-- **hchart, sealed.**  The second 93 scalar facts in the consumer's field-level shape. -/
theorem direction_chart :
    forall i, direction i 15 / direction i 6 = fingerprint i := by
  intro i
  have h6 : (directionNat i 6 : ZMod P) ≠ 0 :=
    natCast_ne_zero_of_ne_zero_of_lt (directionNat_six_ne_zero i) (directionNat_lt i 6)
  calc direction i 15 / direction i 6
      = (directionNat i 15 : ZMod P) * (directionNat i 6 : ZMod P)⁻¹ :=
        div_eq_mul_inv _ _
    _ = (directionNat i 15 : ZMod P) * ((invP (directionNat i 6) : Nat) : ZMod P) := by
        rw [natCast_invP_eq_inv _ h6]
    _ = ((mulP (directionNat i 15) (invP (directionNat i 6)) : Nat) : ZMod P) :=
        (natCast_mulP _ _).symm
    _ = fingerprint i := by rw [directionNat_chart_eval i]; rfl

/-! ## Composed base separation (hypothesis-free)

The proof below restates `_RateHalfBaseFingerprintTable.projectively_separated_of_chart`
verbatim (that file is in-flight/uncommitted, so it cannot be imported yet; the splice
replaces this restatement by a direct application once the table file lands). -/

/-- **Composed base certificate.**  The 93 concrete reduced defect directions are
pairwise projectively distinct — no free hypotheses. -/
theorem direction_projectively_separated :
    forall i j, (exists c : ZMod P, direction i = c • direction j) -> i = j := by
  intro i j hproj
  apply fingerprint_injective
  rw [← direction_chart i, ← direction_chart j]
  obtain ⟨c, hc⟩ := hproj
  have h6eq := congrFun hc (6 : Fin 64)
  have h15eq := congrFun hc (15 : Fin 64)
  simp only [Pi.smul_apply, smul_eq_mul] at h6eq h15eq
  rw [h6eq, h15eq]
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at h6eq
    exact direction_six_ne_zero i h6eq
  field_simp

/-- **Composed lifted certificate.**  At every radix `m ≥ 2` the `93*m` lifted
rank-one directions are pairwise projectively distinct — no free hypotheses.
At the prize radix `m = 2^24` this realizes `93m > 64m = 2^30` distinct
projective labels, the count consumed by
`_RateHalfThreeCoreRadixArithmetic.badCount_gt_length_of_injected_directions`. -/
theorem direction_lifted_projectively_separated (m : Nat) (hm : 2 ≤ m) :
    forall (i j : Fin 93) (x y c : ZMod P),
      RankOneTensorProjectiveInjection.outer
          (direction i) (RankOneTensorProjectiveInjection.vandermonde m x) =
        c • RankOneTensorProjectiveInjection.outer
          (direction j) (RankOneTensorProjectiveInjection.vandermonde m y) ->
        i = j ∧ x = y := by
  apply RankOneTensorProjectiveInjection.outer_vandermonde_projectively_injective
    m hm direction
  · intro i hi
    exact direction_six_ne_zero i (congrFun hi (6 : Fin 64))
  · exact direction_projectively_separated

/-! ## Transparency layer for the downstream splice

The reduced representative is definitionally the Lagrange defect minus its
pivot combination against `rowTab`; these lemmas expose that shape in field
language so the downstream annihilator identification (rows span the actual
parity checks) can consume `direction` without re-evaluating anything. -/

theorem natCast_direction_decomposition (i : Fin 93) (c : Fin 64) :
    direction i c =
      (defectN (coreOf i) (outsideOf i) c.val : ZMod P) -
        ((defectN (coreOf i) (outsideOf i) 0 : ZMod P) * (rowTab 0 c : ZMod P)
          + (defectN (coreOf i) (outsideOf i) 1 : ZMod P) * (rowTab 1 c : ZMod P)
          + (defectN (coreOf i) (outsideOf i) 2 : ZMod P) * (rowTab 2 c : ZMod P)) := by
  rw [direction, directionNat, natCast_subP _ _ (Nat.mod_lt _ P_pos).le,
    ZMod.natCast_mod]
  push_cast
  ring_nf

/-- The Lagrange shape of the defect coefficient at an interpolation-basis
coordinate, in field language. -/
theorem natCast_defectN_basis (c : Fin 3) (outsideCoord coord : Nat)
    (hne : coord ≠ outsideCoord) (hmem : coord ∈ basis c)
    (hden : ((prodP (denomFactors c coord) : Nat) : ZMod P) ≠ 0) :
    ((defectN c outsideCoord coord : Nat) : ZMod P) =
      -((((numerFactors c outsideCoord coord).map fun x => (x : ZMod P)).prod) *
        ((((denomFactors c coord).map fun x => (x : ZMod P)).prod)⁻¹)) := by
  rw [defectN, if_neg hne, if_pos hmem,
    natCast_subP _ _ (mulP_lt _ _).le, natCast_mulP,
    natCast_invP_eq_inv _ hden, natCast_prodP, natCast_prodP,
    Nat.cast_zero, zero_sub]

/-- The evaluation domain really is the smooth `mu_64` subgroup of the prize
field: `dom i` is the `2^24 * i`-th power of the certified order-`2^30`
generator. -/
theorem dom_spec :
    forall i : Fin 64, dom i.val = powP (ZMod.val g) (2 ^ 24 * i.val) := by
  decide +kernel

theorem natCast_dom (i : Fin 64) :
    ((dom i.val : Nat) : ZMod P) = g ^ (2 ^ 24 * i.val) := by
  rw [dom_spec i, natCast_powP, ZMod.natCast_zmod_val]

end ArkLib.ProximityGap.Frontier.W7RateHalfFingerprintSeal

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.W7RateHalfFingerprintSeal
#print axioms directionNat_six_ne_zero
#print axioms directionNat_chart_eval
#print axioms rowTab_pivot
#print axioms direction_six_ne_zero
#print axioms direction_chart
#print axioms fingerprint_injective
#print axioms direction_projectively_separated
#print axioms direction_lifted_projectively_separated
#print axioms natCast_direction_decomposition
#print axioms natCast_defectN_basis
#print axioms natCast_dom
"""


def emit_lean(path: str) -> None:
    verify_lean_semantics()
    ind = "    "
    blocks: list[str] = [LEAN_HEADER]

    blocks.append(
        "/-- The 64 points of `mu_64` (powers of `g^(2^24)`), as natural residues.\n"
        "Verified below (`dom_spec`) to be the powers of the certified generator. -/\n"
        "def domList : List Nat := [\n" + fmt_nat_list(domain, ind) + "]\n"
    )

    for c in range(3):
        blocks.append(
            f"/-- Interpolation basis of core {c}: the 32 smallest core coordinates. -/\n"
            f"def basis{c} : List Nat :=\n"
            f"  [" + ", ".join(str(v) for v in bases[c]) + "]\n"
        )
    blocks.append("def basis : Fin 3 -> List Nat := ![basis0, basis1, basis2]\n")

    for c in range(3):
        blocks.append(
            f"/-- The 31 out-of-core coordinates of core {c}, ascending. -/\n"
            f"def outside{c} : Fin 31 -> Nat :=\n"
            f"  ![" + ", ".join(str(v) for v in outsides[c]) + "]\n"
        )
    blocks.append(
        "def outside : Fin 3 -> Fin 31 -> Nat := ![outside0, outside1, outside2]\n"
    )

    for k in range(3):
        blocks.append(
            f"/-- Row {k} of the reduced row echelon form of the three parity checks\n"
            f"(pivots at columns 0,1,2). -/\n"
            f"def row{k} : Fin 64 -> Nat := ![\n"
            + fmt_bang_vec(constraint_rows[k], ind)
            + "]\n"
        )
    blocks.append("def rowTab : Fin 3 -> Fin 64 -> Nat := ![row0, row1, row2]\n")

    blocks.append(
        "/-- Projective fingerprints, literal-identical to\n"
        "`_RateHalfBaseFingerprintTable.fingerprintNat` (core-major,\n"
        "outside-coordinate-minor order). -/\n"
        "def fingerprintNat : Fin 93 -> Nat := ![\n"
        + fmt_bang_vec(FINGERPRINT_TABLE, ind)
        + "]\n"
    )

    blocks.append(LEAN_CODE)
    text = "\n".join(blocks)
    with open(path, "w") as fh:
        fh.write(text)
    print(f"wrote {path} ({text.count(chr(10)) + 1} lines)")


def main() -> None:
    checks = {}
    checks["pivots"] = pivots
    assert pivots == [0, 1, 2], pivots

    # Canonical-representative sanity: reduced vectors vanish at the pivots.
    assert all(v[0] == 0 and v[1] == 0 and v[2] == 0 for v in reduced)

    # Simultaneous-vs-sequential reduction agreement (RREF rows are already
    # eliminated at the other pivots, so the closed formula
    # reduced = defect - defect[0]*row0 - defect[1]*row1 - defect[2]*row2 holds).
    for v in raw_defects:
        simul = [
            (entry - v[0] * r0 - v[1] * r1 - v[2] * r2) % P
            for entry, r0, r1, r2 in zip(
                v, constraint_rows[0], constraint_rows[1], constraint_rows[2]
            )
        ]
        assert simul == reduce_vector(v)

    reduced6 = [v[6] for v in reduced]
    reduced15 = [v[15] for v in reduced]
    assert all(x != 0 for x in reduced6)
    fingerprints = [b * inverse(a) % P for a, b in zip(reduced6, reduced15)]
    assert fingerprints == FINGERPRINT_TABLE, "fingerprint mismatch vs table file"

    data = {
        "P": P,
        "baseGenerator": base_generator,
        "domain": domain,
        "bases": bases,
        "outsides": outsides,
        "row_at6": [constraint_rows[k][6] for k in range(3)],
        "row_at15": [constraint_rows[k][15] for k in range(3)],
        "defect_at": {
            str(coord): [v[coord] for v in raw_defects] for coord in (0, 1, 2, 6, 15)
        },
        "reduced6": reduced6,
        "reduced15": reduced15,
        "fingerprints": fingerprints,
    }

    if len(sys.argv) > 1 and sys.argv[1] == "--json":
        json.dump(data, open(sys.argv[2], "w"))
        print(f"wrote {sys.argv[2]}")
        return

    if len(sys.argv) > 1 and sys.argv[1] == "--emit-lean":
        emit_lean(sys.argv[2])
        return

    print("pivots:", pivots)
    print("baseGenerator:", base_generator)
    print("row_at6:", data["row_at6"])
    print("row_at15:", data["row_at15"])
    print("bases[0]:", bases[0])
    print("bases[1]:", bases[1])
    print("bases[2]:", bases[2])
    print("outsides[0]:", outsides[0])
    print("outsides[1]:", outsides[1])
    print("outsides[2]:", outsides[2])
    print("reduced6[0..2]:", reduced6[:3])
    print("reduced15[0..2]:", reduced15[:3])
    print("ALL_CHECKS_PASS fingerprints==table 93/93, reduced6 nonzero 93/93")


if __name__ == "__main__":
    main()
