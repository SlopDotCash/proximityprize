/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime

/-! # Lucas certificates for the three upper-end prize-field primes

Each line supplies a witness of multiplicative order p−1 and the complete list
of prime factors of p−1 with multiplicity. Lean checks all modular powers. -/

namespace ProximityGap.PrizeCeilingPrimes

private theorem pow_eq_one {p g e : ℕ} (hp : 1 < p) :
    (g : ZMod p) ^ e = 1 ↔ Nat.powMod g e p = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.powMod_def,
    Nat.mod_eq_of_lt hp]

private theorem certify (p g : ℕ) (fs : List {q : ℕ // Nat.Prime q})
    (ok : 1 < p ∧ (fs.map Subtype.val).prod = p - 1 ∧ Nat.powMod g (p - 1) p = 1 ∧
      fs.all (fun f => decide (Nat.powMod g ((p - 1) / f.val) p ≠ 1)) = true) : p.Prime := by
  obtain ⟨hp, factors, full, proper⟩ := ok
  apply lucas_primality p (g : ZMod p) ((pow_eq_one hp).mpr full)
  intro v hv dvd
  rw [← factors] at dvd
  obtain ⟨_, part, hd⟩ := hv.prime.dvd_prod_iff.mp dvd
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp part
  have h := (Nat.prime_dvd_prime_iff_eq hv f.property).mp hd
  rw [h]
  exact fun eq => (of_decide_eq_true (List.all_eq_true.mp proper f hf)) ((pow_eq_one hp).mp eq)

-- Modular exponentiation on these 256-bit inputs unfolds one branch per bit.
set_option maxRecDepth 20000

private theorem node0 : Nat.Prime 1103 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨19, by decide⟩, ⟨29, by decide⟩]
    (by decide)

private theorem node1 : Nat.Prime 1117 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
     ⟨31, by decide⟩]
    (by decide)

private theorem node2 : Nat.Prime 1223 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨13, by decide⟩, ⟨47, by decide⟩]
    (by decide)

private theorem node3 : Nat.Prime 1297 :=
  certify _ 10
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
     ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩]
    (by decide)

private theorem node4 : Nat.Prime 1303 :=
  certify _ 6
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩, ⟨31, by decide⟩]
    (by decide)

private theorem node5 : Nat.Prime 1579 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨263, by decide⟩]
    (by decide)

private theorem node6 : Nat.Prime 1627 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨271, by decide⟩]
    (by decide)

private theorem node7 : Nat.Prime 2221 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩,
     ⟨37, by decide⟩]
    (by decide)

private theorem node8 : Nat.Prime 3659 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨31, by decide⟩, ⟨59, by decide⟩]
    (by decide)

private theorem node9 : Nat.Prime 3761 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩,
     ⟨47, by decide⟩]
    (by decide)

private theorem node10 : Nat.Prime 5273 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨659, by decide⟩]
    (by decide)

private theorem node11 : Nat.Prime 6257 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
     ⟨17, by decide⟩, ⟨23, by decide⟩]
    (by decide)

private theorem node12 : Nat.Prime 6263 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨31, by decide⟩, ⟨101, by decide⟩]
    (by decide)

private theorem node13 : Nat.Prime 6287 :=
  certify _ 7
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨449, by decide⟩]
    (by decide)

private theorem node14 : Nat.Prime 6619 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1103, node0⟩]
    (by decide)

private theorem node15 : Nat.Prime 14821 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩,
     ⟨13, by decide⟩, ⟨19, by decide⟩]
    (by decide)

private theorem node16 : Nat.Prime 27541 :=
  certify _ 19
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
     ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨17, by decide⟩]
    (by decide)

private theorem node17 : Nat.Prime 34039 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨31, by decide⟩,
     ⟨61, by decide⟩]
    (by decide)

private theorem node18 : Nat.Prime 36151 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩,
     ⟨241, by decide⟩]
    (by decide)

private theorem node19 : Nat.Prime 41953 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
     ⟨3, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩]
    (by decide)

private theorem node20 : Nat.Prime 42689 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
     ⟨2, by decide⟩, ⟨23, by decide⟩, ⟨29, by decide⟩]
    (by decide)

private theorem node21 : Nat.Prime 52517 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨19, by decide⟩, ⟨691, by decide⟩]
    (by decide)

private theorem node22 : Nat.Prime 87683 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨6263, node12⟩]
    (by decide)

private theorem node23 : Nat.Prime 87881 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩,
     ⟨13, by decide⟩, ⟨13, by decide⟩, ⟨13, by decide⟩]
    (by decide)

private theorem node24 : Nat.Prime 124781 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨17, by decide⟩,
     ⟨367, by decide⟩]
    (by decide)

private theorem node25 : Nat.Prime 195241 :=
  certify _ 11
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩,
     ⟨1627, node6⟩]
    (by decide)

private theorem node26 : Nat.Prime 218923 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨11, by decide⟩, ⟨31, by decide⟩,
     ⟨107, by decide⟩]
    (by decide)

private theorem node27 : Nat.Prime 222587 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩, ⟨1223, node2⟩]
    (by decide)

private theorem node28 : Nat.Prime 249563 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨124781, node24⟩]
    (by decide)

private theorem node29 : Nat.Prime 371951 :=
  certify _ 13
    [⟨2, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨43, by decide⟩,
     ⟨173, by decide⟩]
    (by decide)

private theorem node30 : Nat.Prime 499127 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨249563, node28⟩]
    (by decide)

private theorem node31 : Nat.Prime 504901 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
     ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩]
    (by decide)

private theorem node32 : Nat.Prime 526583 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨29, by decide⟩, ⟨1297, node3⟩]
    (by decide)

private theorem node33 : Nat.Prime 702529 :=
  certify _ 23
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
     ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3659, node8⟩]
    (by decide)

private theorem node34 : Nat.Prime 973591 :=
  certify _ 13
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨17, by decide⟩,
     ⟨23, by decide⟩, ⟨83, by decide⟩]
    (by decide)

private theorem node35 : Nat.Prime 1160867 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨283, by decide⟩, ⟨293, by decide⟩]
    (by decide)

private theorem node36 : Nat.Prime 1171447 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨195241, node25⟩]
    (by decide)

private theorem node37 : Nat.Prime 1227563 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨87683, node22⟩]
    (by decide)

private theorem node38 : Nat.Prime 1521613 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
     ⟨73, by decide⟩, ⟨193, by decide⟩]
    (by decide)

private theorem node39 : Nat.Prime 3880447 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨19, by decide⟩, ⟨34039, node17⟩]
    (by decide)

private theorem node40 : Nat.Prime 4463413 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨371951, node29⟩]
    (by decide)

private theorem node41 : Nat.Prime 7436071 :=
  certify _ 15
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩,
     ⟨27541, node16⟩]
    (by decide)

private theorem node42 : Nat.Prime 9194767 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩, ⟨218923, node26⟩]
    (by decide)

private theorem node43 : Nat.Prime 11779883 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨1117, node1⟩, ⟨5273, node10⟩]
    (by decide)

private theorem node44 : Nat.Prime 38804471 :=
  certify _ 19
    [⟨2, by decide⟩, ⟨5, by decide⟩, ⟨3880447, node39⟩]
    (by decide)

private theorem node45 : Nat.Prime 44921431 :=
  certify _ 6
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩,
     ⟨499127, node30⟩]
    (by decide)

private theorem node46 : Nat.Prime 172675897 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
     ⟨137, by decide⟩, ⟨52517, node21⟩]
    (by decide)

private theorem node47 : Nat.Prime 483448547 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨23, by decide⟩, ⟨61, by decide⟩,
     ⟨151, by decide⟩, ⟨163, by decide⟩]
    (by decide)

private theorem node48 : Nat.Prime 1796857241 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩,
     ⟨44921431, node45⟩]
    (by decide)

private theorem node49 : Nat.Prime 3025219403 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨1303, node4⟩, ⟨1160867, node35⟩]
    (by decide)

private theorem node50 : Nat.Prime 4979420713 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
     ⟨7, by decide⟩, ⟨1579, node5⟩, ⟨6257, node11⟩]
    (by decide)

private theorem node51 : Nat.Prime 10262543633 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
     ⟨11, by decide⟩, ⟨83, by decide⟩, ⟨702529, node33⟩]
    (by decide)

private theorem node52 : Nat.Prime 36387422447 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨14821, node15⟩, ⟨1227563, node37⟩]
    (by decide)

private theorem node53 : Nat.Prime 89842862051 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩, ⟨1796857241, node48⟩]
    (by decide)

private theorem node54 : Nat.Prime 246301047193 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
     ⟨10262543633, node51⟩]
    (by decide)

private theorem node55 : Nat.Prime 278693710723 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩,
     ⟨19, by decide⟩, ⟨38804471, node44⟩]
    (by decide)

private theorem node56 : Nat.Prime 1219974856409 :=
  certify _ 6
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩,
     ⟨11, by decide⟩, ⟨3761, node9⟩, ⟨526583, node32⟩]
    (by decide)

private theorem node57 : Nat.Prime 17097628463159 :=
  certify _ 23
    [⟨2, by decide⟩, ⟨17, by decide⟩, ⟨42689, node20⟩, ⟨11779883, node43⟩]
    (by decide)

private theorem node58 : Nat.Prime 68964293214041 :=
  certify _ 12
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩,
     ⟨246301047193, node54⟩]
    (by decide)

private theorem node59 : Nat.Prime 337134914195791 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨19, by decide⟩,
     ⟨504901, node31⟩, ⟨1171447, node36⟩]
    (by decide)

private theorem node60 : Nat.Prime 12036730438063937 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
     ⟨2, by decide⟩, ⟨11, by decide⟩, ⟨17097628463159, node57⟩]
    (by decide)

private theorem node61 : Nat.Prime 34400489300742979 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩,
     ⟨43, by decide⟩, ⟨43, by decide⟩, ⟨6619, node14⟩, ⟨7436071, node41⟩]
    (by decide)

private theorem node62 : Nat.Prime 103730042959544593 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
     ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨79, by decide⟩, ⟨6287, node13⟩,
     ⟨483448547, node47⟩]
    (by decide)

private theorem node63 : Nat.Prime 23236691026952546459 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨7, by decide⟩, ⟨41, by decide⟩, ⟨587, by decide⟩,
     ⟨68964293214041, node58⟩]
    (by decide)

private theorem node64 : Nat.Prime 14220365526706201077871 :=
  certify _ 6
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩,
     ⟨23, by decide⟩, ⟨2221, node7⟩, ⟨36151, node18⟩, ⟨87881, node23⟩,
     ⟨973591, node34⟩]
    (by decide)

private theorem node65 : Nat.Prime 324283015810421005973242541 :=
  certify _ 7
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨17, by decide⟩,
     ⟨9194767, node42⟩, ⟨103730042959544593, node62⟩]
    (by decide)

private theorem node66 : Nat.Prime 51229664085644375768993619505829381 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩,
     ⟨37, by decide⟩, ⟨3025219403, node49⟩, ⟨36387422447, node52⟩,
     ⟨89842862051, node53⟩]
    (by decide)

private theorem node67 : Nat.Prime 440208639276132997491800604758226661590679912188273141493 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩,
     ⟨13, by decide⟩, ⟨1219974856409, node56⟩, ⟨23236691026952546459, node63⟩,
     ⟨14220365526706201077871, node64⟩]
    (by decide)

private theorem node68 :
    Nat.Prime 355736065245211045848144347184909087106820229387528614560545572988980429 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨107, by decide⟩, ⟨172675897, node46⟩,
     ⟨278693710723, node55⟩, ⟨337134914195791, node59⟩,
     ⟨51229664085644375768993619505829381, node66⟩]
    (by decide)

private theorem node69 :
    Nat.Prime 7237005577332262213973186563042994240829374041602535252466099000494570602367 :=
  certify _ 5
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨43, by decide⟩, ⟨41953, node19⟩,
     ⟨4979420713, node50⟩, ⟨12036730438063937, node60⟩, ⟨34400489300742979, node61⟩,
     ⟨324283015810421005973242541, node65⟩]
    (by decide)

/-- The prime 2²⁵⁶ minus 2063. -/
theorem prime_2063 :
    Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007913129637873 :=
  certify _ 3
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
     ⟨7237005577332262213973186563042994240829374041602535252466099000494570602367, node69⟩]
    (by decide)

/-- The prime 2²⁵⁶ minus 435. -/
theorem prime_435 :
    Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007913129639501 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨5, by decide⟩,
     ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨31, by decide⟩,
     ⟨355736065245211045848144347184909087106820229387528614560545572988980429, node68⟩]
    (by decide)

/-- The prime 2²⁵⁶ minus 189. -/
theorem prime_189 :
    Nat.Prime 115792089237316195423570985008687907853269984665640564039457584007913129639747 :=
  certify _ 2
    [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨29, by decide⟩, ⟨222587, node27⟩,
     ⟨1521613, node38⟩, ⟨4463413, node40⟩,
     ⟨440208639276132997491800604758226661590679912188273141493, node67⟩]
    (by decide)

end ProximityGap.PrizeCeilingPrimes
