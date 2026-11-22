/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AffineRankMoment

/-! # Affine-rank obstructions at the eight named-prime list frontier cells -/

set_option autoImplicit false
noncomputable section
namespace ProximityGap.AffineRankMoment

private def half : List ℕ := [
    2, 3, 5, 8, 12, 17, 25, 36,
    51, 73, 104, 148, 210, 297, 421, 596,
    843, 1193, 1688, 2388, 3378, 4778, 6758, 9558,
    13518, 19118, 27037, 38237, 54076, 76476, 108154, 152953,
    216309, 305908, 432620, 611818, 865242, 1223637, 1730485, 2447276,
    3460971, 4894553, 6921944, 9789108, 13843890, 19578218, 27687782, 39156437,
    55375565, 78312876, 110751132, 156625754, 221502267, 313251512, 443004538, 626503028,
    886009082, 1253006064, 1772018175]

private def quarter : List ℕ := [
    3, 7, 15, 31, 63, 127, 255, 511,
    1023, 2047, 4095, 8191, 16383, 32767, 65535, 131071,
    262143, 524287, 1048575, 2097151, 4194303, 8388607, 16777215, 33554431,
    67108863, 134217727, 268435456, 536870916, 1073741840]

private def eighthFirst : List ℕ := [
    3, 9, 26, 74, 210, 594, 1681, 4755,
    13450, 38043, 107602, 304345, 860818, 2434761, 6886545, 19478091,
    55092362, 155824732, 440738901, 1246597867]

private def eighthSecond : List ℕ := [
    3, 9, 26, 74, 210, 594, 1681, 4755,
    13450, 38043, 107602, 304345, 860818, 2434762, 6886547, 19478097,
    55092379, 155824781, 440739042, 1246598273]

private def sixteenth : List ℕ := [
    5, 21, 85, 341, 1365, 5461, 21845, 87381,
    349525, 1398101, 5592405, 22369621, 89478486, 357913949, 1431655816]

variable {F I V : Type} [Field F] [Fintype I] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- Cardinality caps at the preceding rank for all four rates and both named budgets. -/
theorem production (hn : Fintype.card I = 1073741824) :
    Bound F I V 759250124 536870911 57 886009082 ∧
    Bound F I V 759250124 536870911 59 1772018175 ∧
    Bound F I V 536870910 268435455 28 536870916 ∧
    Bound F I V 536870910 268435455 29 1073741840 ∧
    Bound F I V 379625061 134217727 19 440738901 ∧
    Bound F I V 379625060 134217727 20 1246598273 ∧
    Bound F I V 268435453 67108863 14 357913949 ∧
    Bound F I V 268435453 67108863 15 1431655816 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact check_sound hn (half.take 57) (zero 759250124 536870911) (by decide)
  · exact check_sound hn (half.take 59) (zero 759250124 536870911) (by decide)
  · exact check_sound hn (quarter.take 28) (zero 536870910 268435455) (by decide)
  · exact check_sound hn (quarter.take 29) (zero 536870910 268435455) (by decide)
  · exact check_sound hn (eighthFirst.take 19) (zero 379625061 134217727) (by decide)
  · exact check_sound hn (eighthSecond.take 20) (zero 379625060 134217727) (by decide)
  · exact check_sound hn (sixteenth.take 14) (zero 268435453 67108863) (by decide)
  · exact check_sound hn (sixteenth.take 15) (zero 268435453 67108863) (by decide)

#print axioms production
end ProximityGap.AffineRankMoment
