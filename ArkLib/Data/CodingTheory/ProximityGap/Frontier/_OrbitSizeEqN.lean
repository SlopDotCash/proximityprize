/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CliqueOrbitFreeness

/-!
# The translation orbit of an odd-card carrier has cardinality EXACTLY `n = 2^a` (#444)

`CliqueOrbitFreeness.prize_regime_fixed_eq_zero` proves the STABILIZER half of `lalalune`'s
orbit-count reformulation `D*(m) = (orbit size = n)·#orbits(m)`: for an **odd**-card exponent set
`E ⊆ ZMod (2^a)`, the translation `E ↦ E + j` fixes `E` only for `j = 0` (trivial stabilizer).
What that file leaves *implicit in prose* ("hence the orbit has size exactly `n = 2^a`") is the
**cardinality conclusion** itself, the literal orbit-size factor in `#bad = n·#orbits + 1`.

This file supplies that missing cardinality brick, axiom-clean.  We model the rotation action on
exponent sets by the explicit translate map `translate j E := E.image (· + j)` and prove:

* `translate_eq_self_iff`: `translate j E = E ↔ (∀ x ∈ E, x + j ∈ E)`.  In a group, `(· + j)` is
  injective, so an into-self image of a finite set is onto it; this reconciles the file's stabilizer
  predicate (`∀ x ∈ E, x + j ∈ E`) with the action-fixed-point predicate (`translate j E = E`).

* `translate_injective_of_odd_card`: for ODD-card `E` over `ZMod (2^a)`, the orbit map
  `j ↦ translate j E` is INJECTIVE.  (`translate i E = translate j E ⟹ translate (i − j) E = E ⟹
  i − j` is in the stabilizer ⟹ `i − j = 0` by `prize_regime_fixed_eq_zero`.)

* `orbit_card_eq_two_pow` (HEADLINE): the orbit `{translate j E : j}` of an odd-card `E` has
  cardinality **exactly `2^a = n`**: the injective orbit map has image of size `#(univ) = 2^a`.

* `orbit_card_eq_card_addGroup`: restated as `= Fintype.card (ZMod (2^a)) = Nat.card G`, the
  orbit-stabilizer conclusion with trivial stabilizer made explicit.

## Honest scope

This is the **orbit-SIZE = n** cardinality fact: the proven, p-independent multiplicative factor in
`#bad = n·#orbits + 1` (used by `DeepBandOrbitCountDescent`, ThreadD's union-count floor, and the
`D*(m) = (orbit size)·#orbits(m)` decay reformulation).  It is NOT a bound on `#orbits(m)` (the open
cyclotomic-collision growth law = the BGK/BCHKS wall).  Pure cyclic-group / Finset-image counting:
character-sum-free, char-agnostic, NOT thinness-essential; does **not** close CORE
`M(μ_n) ≤ C·√(n·log(p/n))`.  It removes the last bit of slack in the orbit-size half (the
companion file proves trivial stabilizer; this turns that into the cardinality `= n`).

Probe: `scripts/probes/probe_orbit_card_eq_n.py` (odd-card `E ⊆ Z/2^a` ⟹ orbit size EXACTLY `n`;
even-card `E` can have a smaller orbit; exact, `a = 2..6`, NEVER `n = q − 1`).
-/

open Finset

namespace ProximityGap.OrbitSizeEqN

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The translation of an exponent set `E` by `j`: `translate j E = { x + j : x ∈ E }`. -/
def translate (j : G) (E : Finset G) : Finset G := E.image (· + j)

theorem mem_translate {j : G} {E : Finset G} {y : G} :
    y ∈ translate j E ↔ ∃ x ∈ E, x + j = y := by
  rw [translate, Finset.mem_image]

theorem card_translate (j : G) (E : Finset G) : (translate j E).card = E.card := by
  rw [translate, Finset.card_image_of_injective]
  exact add_left_injective j

theorem translate_zero (E : Finset G) : translate 0 E = E := by
  ext y; rw [mem_translate]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro hy; exact ⟨y, hy, by rw [add_zero]⟩

theorem translate_translate (i j : G) (E : Finset G) :
    translate i (translate j E) = translate (j + i) E := by
  ext y; rw [mem_translate, mem_translate]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_translate] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, hz, by rw [add_assoc]⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z + j, ?_, by rw [add_assoc]⟩
    rw [mem_translate]; exact ⟨z, hz, rfl⟩

/-- **`translate j E = E` reconciles with the file's stabilizer predicate `∀ x ∈ E, x + j ∈ E`.**
In a group `(· + j)` is injective, so an into-self image of the finite set `E` is onto it. -/
theorem translate_eq_self_iff {j : G} {E : Finset G} :
    translate j E = E ↔ ∀ x ∈ E, x + j ∈ E := by
  constructor
  · intro h x hx
    rw [← h]; exact mem_translate.mpr ⟨x, hx, rfl⟩
  · intro hcl
    -- `translate j E ⊆ E` and both have the same card, so they are equal.
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_translate.mp hy
      exact hcl x hx
    · rw [card_translate]

end ProximityGap.OrbitSizeEqN

namespace ProximityGap.OrbitSizeEqN

open ProximityGap.CliqueOrbitFreeness

/-- **The orbit map `j ↦ translate j E` is injective for an odd-card carrier over `ZMod (2^a)`.**
If `translate i E = translate j E` then `translate (i − j) E = E`, so `i − j` stabilizes `E`, hence
`i − j = 0` by `prize_regime_fixed_eq_zero` (odd card ⇒ trivial stabilizer). -/
theorem translate_injective_of_odd_card (a : ℕ)
    {E : Finset (ZMod (2 ^ a))} (hodd : Odd E.card) :
    Function.Injective (fun j : ZMod (2 ^ a) => translate j E) := by
  intro i j hij
  simp only at hij
  -- Apply `translate (-j)` to both sides and use the action laws.
  have h2 : translate (-j) (translate i E) = translate (-j) (translate j E) := by rw [hij]
  rw [translate_translate, translate_translate] at h2
  -- `translate (i + -j) E = translate (j + -j) E = translate 0 E = E`.
  rw [add_neg_cancel j, translate_zero] at h2
  -- `h2 : translate (i + -j) E = E`, so `i + -j` stabilizes `E`.
  have hstab : ∀ x ∈ E, x + (i + -j) ∈ E := (translate_eq_self_iff).mp h2
  have hij0 : i + -j = 0 := prize_regime_fixed_eq_zero a hodd hstab
  -- `i + -j = 0 ⇒ i = j`.
  have : i - j = 0 := by rwa [sub_eq_add_neg]
  exact sub_eq_zero.mp this

/-- **HEADLINE: orbit of an odd-card carrier has cardinality EXACTLY `2^a = n`.**
The orbit `{ translate j E : j ∈ ZMod (2^a) }` (the rotation orbit of the exponent set `E`) has
`card = 2^a`.  Proof: the orbit is the image of `univ` under the orbit map `j ↦ translate j E`,
which is injective for odd-card `E` (`translate_injective_of_odd_card`), so its image has card
`#(univ : Finset (ZMod (2^a))) = 2^a`.  This is the proven orbit-size factor `n` in
`#bad = n·#orbits + 1`. -/
theorem orbit_card_eq_two_pow (a : ℕ)
    {E : Finset (ZMod (2 ^ a))} (hodd : Odd E.card) :
    (Finset.univ.image (fun j : ZMod (2 ^ a) => translate j E)).card = 2 ^ a := by
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  rw [Finset.card_image_of_injective _ (translate_injective_of_odd_card a hodd)]
  rw [Finset.card_univ, ZMod.card]

/-- **Orbit-stabilizer form:** the orbit cardinality equals `Nat.card (ZMod (2^a))` (`= 2^a = n`),
the orbit-stabilizer conclusion with the (proven-trivial) stabilizer made explicit. -/
theorem orbit_card_eq_card_addGroup (a : ℕ)
    {E : Finset (ZMod (2 ^ a))} (hodd : Odd E.card) :
    (Finset.univ.image (fun j : ZMod (2 ^ a) => translate j E)).card
      = Nat.card (ZMod (2 ^ a)) := by
  haveI : NeZero (2 ^ a) := ⟨pow_ne_zero a two_ne_zero⟩
  rw [orbit_card_eq_two_pow a hodd, Nat.card_eq_fintype_card, ZMod.card]

/-- Numerical anchor (`a = 4`, `n = 16`): the orbit of an odd-card carrier (here `{0}`, card `1`)
has size `16`. -/
theorem orbit_n16_singleton :
    (Finset.univ.image (fun j : ZMod (2 ^ 4) => translate j ({0} : Finset (ZMod (2 ^ 4))))).card
      = 16 :=
  orbit_card_eq_two_pow 4 (by decide)

end ProximityGap.OrbitSizeEqN

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, no sorryAx)
#print axioms ProximityGap.OrbitSizeEqN.translate_eq_self_iff
#print axioms ProximityGap.OrbitSizeEqN.translate_injective_of_odd_card
#print axioms ProximityGap.OrbitSizeEqN.orbit_card_eq_two_pow
#print axioms ProximityGap.OrbitSizeEqN.orbit_card_eq_card_addGroup
#print axioms ProximityGap.OrbitSizeEqN.orbit_n16_singleton
