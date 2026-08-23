/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._Close26_PrimitiveCleanRecursion

/-!
# Imprimitive bad-set decomposition, the companion of Close26 (target E5, #444)

## The obligation

`_Close26_PrimitiveCleanRecursion` discharges B26's exact-cover hypothesis at a **primitive** far
direction: there the level-`2n` bad set `B'` has **no odd (fixed sub-`μ_2`) residue**
(`hP_even : ∀ j ∈ B', 2 ∣ j.val`), so `B' = dbl '' B` *exactly* and `|B'| = |B|`: the clean
recursion, no plateau.

At an **imprimitive** direction (`b−a` even, `d = gcd(b−a,n)` even, `n = 2^μ`) B27
(`imprimitive_orbit_dvd_half`) shows the orbits are `μ_2`-invariant (`S ∣ n/2`): the antipodal
shift `h^{n/2}` acts trivially, and an **extra invariant rung** appears on the **odd** residues.
There `hP_even` *fails* and the clean primitive cover does not apply.

This file supplies the missing **structural companion**: for an *arbitrary* level-`2n` bad set
`B'` (no primitivity assumed), the exact set-partition into its even-residue and odd-residue parts,
and the resulting **cardinality identity**

  `|B'| = |even-part| + |odd-rung|`,    `even-part = dbl '' (half '' (B' ∩ evens))`,

with the even part halving back bijectively (Close26's machinery) and the odd part being **exactly**
the imprimitive extra rung B27 identifies. The primitive case (`hP_even`) is recovered as the
specialisation `odd-rung = ∅ ⟹ |B'| = |even-part|`.

## Honest scope (what is NOT proven)

This is a **structural decoupling**, NOT a closure. It proves the *partition* and the
*cardinality additivity* `|B'| = |even-part| + |odd-rung|`, pure `Fin`/`Finset` index arithmetic,
field-universal, thinness-agnostic. It makes the **plateau excess** of the dyadic cascade *equal to*
`|odd-rung|`, cleanly separating it from the even part (which obeys Close26's clean halving).

It does **NOT** bound `|odd-rung|`. Whether `|odd-rung|` contributes a `+1/level` (prize-holds) or a
`×2/level` (prize-fails) plateau width is the open quantitative E5/E7 input (BCHKS 1.12), the wall,
named in B27's honest scope and B28/B31, **not** discharged here. No capacity / beyond-Johnson /
sub-linear claim is made; the cliff-at-`n/2` is untouched. The prize CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

## Probe

`scripts/probes/probe_imprimitive_decomp.py` (PROPER thin `μ_n = 2^μ` index model, orbits of
`⟨h^{b−a}⟩`, `n = 4..256`, primitive + imprimitive shifts, never `n = q−1`): the exact partition
`B' = dbl '' B_even ⊎ Odd`, `|B'| = |B_even| + |Odd|`, with `primitive ⟺ Odd = ∅`: **47/47**.
-/

open Finset

namespace ArkLib.ProximityGap.ImprimitiveBadSetDecomp

open ArkLib.ProximityGap.Close26

/-- **The even-residue part of a level-`2n` set.**  `B'` filtered to the even residues, the part
covered by the doubling embedding `dbl`. -/
def evenPart (n : ℕ) (B' : Finset (Fin (2 * n))) : Finset (Fin (2 * n)) :=
  B'.filter (fun j => 2 ∣ j.val)

/-- **The odd-residue part (the imprimitive extra rung).**  `B'` filtered to the odd residues,
*empty at primitive directions* (Close26's `hP_even`), the antipodal-invariant rung at imprimitive
ones (B27). -/
def oddPart (n : ℕ) (B' : Finset (Fin (2 * n))) : Finset (Fin (2 * n)) :=
  B'.filter (fun j => ¬ 2 ∣ j.val)

/-- **Membership in the even part.** -/
theorem mem_evenPart (n : ℕ) (B' : Finset (Fin (2 * n))) (j : Fin (2 * n)) :
    j ∈ evenPart n B' ↔ j ∈ B' ∧ 2 ∣ j.val := by
  simp only [evenPart, Finset.mem_filter]

/-- **Membership in the odd part.** -/
theorem mem_oddPart (n : ℕ) (B' : Finset (Fin (2 * n))) (j : Fin (2 * n)) :
    j ∈ oddPart n B' ↔ j ∈ B' ∧ ¬ 2 ∣ j.val := by
  simp only [oddPart, Finset.mem_filter]

/-- **Even/odd parts are disjoint.** -/
theorem evenPart_disjoint_oddPart (n : ℕ) (B' : Finset (Fin (2 * n))) :
    Disjoint (evenPart n B') (oddPart n B') := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  rw [mem_evenPart] at hj
  rw [mem_oddPart] at hj'
  exact hj'.2 hj.2

/-- **Even/odd parts cover `B'`.**  Their union is all of `B'`. -/
theorem evenPart_union_oddPart (n : ℕ) (B' : Finset (Fin (2 * n))) :
    evenPart n B' ∪ oddPart n B' = B' := by
  simp only [evenPart, oddPart]
  exact Finset.filter_union_filter_not_eq _ B'

/-- **The exact cardinality partition (HEADLINE).**  For any level-`2n` bad set `B'`,
`|B'| = |even-part| + |odd-rung|`.  Pure `Finset` cardinality additivity over the even/odd split.
This is the identity that makes the plateau **excess** equal to `|odd-rung|`, decoupling it from the
even part (which obeys Close26's clean halving). -/
theorem card_eq_evenPart_add_oddPart (n : ℕ) (B' : Finset (Fin (2 * n))) :
    B'.card = (evenPart n B').card + (oddPart n B').card := by
  simp only [evenPart, oddPart]
  exact (Finset.card_filter_add_card_filter_not (s := B') (fun j : Fin (2 * n) => 2 ∣ j.val)).symm

/-- **The even part is exactly the doubled image of its halving.**  `even-part = dbl '' (half ''
even-part)`: the even residues are precisely the doubling embedding's image, recovering Close26's
cover machinery on the even half (no primitivity needed). -/
theorem evenPart_eq_image_dbl_half (n : ℕ) (B' : Finset (Fin (2 * n))) :
    evenPart n B' = ((evenPart n B').image (half n)).image (dbl n) := by
  ext j
  simp only [Finset.mem_image]
  constructor
  · intro hj
    have heven : 2 ∣ j.val := ((mem_evenPart n B' j).mp hj).2
    exact ⟨half n j, ⟨j, hj, rfl⟩, dbl_half_of_even n j heven⟩
  · rintro ⟨_, ⟨j₀, hj₀, rfl⟩, rfl⟩
    have heven : 2 ∣ j₀.val := ((mem_evenPart n B' j₀).mp hj₀).2
    rwa [dbl_half_of_even n j₀ heven]

/-- **`half` is injective on the even part.**  (It inverts `dbl` there, which is injective.) -/
theorem half_injOn_evenPart (n : ℕ) (B' : Finset (Fin (2 * n))) :
    Set.InjOn (half n) (evenPart n B') := by
  intro a ha b hb hab
  have hae : 2 ∣ a.val := ((mem_evenPart n B' a).mp ha).2
  have hbe : 2 ∣ b.val := ((mem_evenPart n B' b).mp hb).2
  calc a = dbl n (half n a) := (dbl_half_of_even n a hae).symm
    _ = dbl n (half n b) := by rw [hab]
    _ = b := dbl_half_of_even n b hbe

/-- **The even part's cardinality equals the halved level-`n` set.**  `|even-part| = |half ''
even-part|` (the level-`n` bad set carried over the clean halving).  Hence
`|B'| = |B_even| + |odd-rung|` with `B_even = half '' even-part`. -/
theorem evenPart_card_eq (n : ℕ) (B' : Finset (Fin (2 * n))) :
    (evenPart n B').card = ((evenPart n B').image (half n)).card :=
  (Finset.card_image_of_injOn (half_injOn_evenPart n B')).symm

/-- **Full structural decomposition (level-`n` form).**  `|B'| = |B_even| + |odd-rung|`, where
`B_even = half '' (B' ∩ evens)` is the clean level-`n` carry-over (Close26's even half) and the
odd-rung is the imprimitive antipodal contribution.  Combines the cardinality partition with the
injective halving of the even part. -/
theorem card_eq_halfImage_add_oddPart (n : ℕ) (B' : Finset (Fin (2 * n))) :
    B'.card = ((evenPart n B').image (half n)).card + (oddPart n B').card := by
  rw [card_eq_evenPart_add_oddPart n B', evenPart_card_eq n B']

/-- **Primitive specialisation (recovers Close26).**  If `B'` has no odd residue
(Close26's `hP_even : ∀ j ∈ B', 2 ∣ j.val`) then the odd-rung is empty and
`|B'| = |B_even|`, the clean recursion, no plateau. -/
theorem oddPart_eq_empty_of_all_even (n : ℕ) (B' : Finset (Fin (2 * n)))
    (hP_even : ∀ j ∈ B', 2 ∣ j.val) :
    oddPart n B' = ∅ := by
  simp only [oddPart, Finset.filter_eq_empty_iff]
  intro j hj
  simp only [not_not]
  exact hP_even j hj

/-- **Primitive case: the decomposition collapses to the clean count.**  When `B'` is all-even,
`|B'| = |B_even|` (no odd rung), matching `primitive_clean_recursion`. -/
theorem card_eq_halfImage_of_all_even (n : ℕ) (B' : Finset (Fin (2 * n)))
    (hP_even : ∀ j ∈ B', 2 ∣ j.val) :
    B'.card = ((evenPart n B').image (half n)).card := by
  rw [card_eq_halfImage_add_oddPart n B', oddPart_eq_empty_of_all_even n B' hP_even,
    Finset.card_empty, Nat.add_zero]

/-- **Non-vacuity (the odd rung is genuinely realisable).**  A concrete imprimitive level-`4`
configuration: `B' = {0, 2, 1} ⊆ Fin 4` has even part `{0,2}` (halving to `{0,1} ⊆ Fin 2`) and a
**nonempty** odd rung `{1}`.  The partition gives `|B'| = 2 + 1 = 3`; the odd rung is *not* vacuous
slack. -/
example :
    let B' : Finset (Fin (2 * 2)) := {⟨0, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩}
    B'.card = ((evenPart 2 B').image (half 2)).card + (oddPart 2 B').card
      ∧ (oddPart 2 B').Nonempty := by
  refine ⟨card_eq_halfImage_add_oddPart 2 _, ?_⟩
  decide

end ArkLib.ProximityGap.ImprimitiveBadSetDecomp
