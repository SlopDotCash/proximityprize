/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fintype

/-!
# E₃ closed form for 2-power roots of unity — the r=2 rung producer (#444)

## What this file is

The δ\* prize reduces (proven spines) to the char-`p` validity of the DC-subtracted Wick
bound `A_r = E_r − n^{2r}/q ≤ (2r−1)‼·n^r` at depth `r ≈ log m`. The SHALLOW rungs
(`r ≤ rMax ≈ 2β`) are provable in char `p` and DISCHARGE part of the spine. The `r = 1`
rung is already discharged from `E_2(μ_n) = 3n² − 3n` (`additiveEnergy_eq_of_sidonModNeg`).
**The r=2 rung's entire remaining producer obstruction** is the `r=3` analogue:

> `E_3(μ_{2^μ}) = zeroSumCount(μ_n, 6) = 15 n³ − 45 n² + 40 n`  exactly, for 2-power `n`.

(`E_3(μ_n)` = additive energy of order 3 = `#{6-tuples of n-th roots summing to 0}` after
the `(v,w) ↦ (v,−w)` negation bijection — `zeroSumCount G 6` in
`NegationClosedWalkBound.lean`.)

## The clean combinatorial reduction (this file's content)

The count factors into a **field-independent combinatorial identity** over the exponent
group `ZMod n`, plus ONE deep char-0 structural input (Lam–Leung), exactly mirroring how
the `E_2 = 3n²−3n` anchor was built. Write `n`-th roots as exponents in `ZMod n`, with the
antipode `−ζ^a = ζ^{a + n/2}` being the shift `+ n/2`.

* **`matchable n t`** — a 6-tuple of exponents `t : Fin 6 → ZMod n` is *antipodally
  matchable* iff its value-distribution is invariant under the antipodal shift `+ n/2`:
  for every value `x`, `#{i : t i = x} = #{i : t i = x + n/2}`. (Machine-verified in
  `scripts/probes/probe_e3_decomp.py` to coincide with "the 6 positions partition into 3
  antipodal pairs"; the slick distribution form is what makes the count tractable.)

* **`matchableCount n`** — the number of matchable 6-tuples over `ZMod n`. This is the
  PURELY COMBINATORIAL object: it has nothing to do with the prime `p`.

* **THE COUNT** (`MatchableCountClosedForm`, this file's combinatorial core) —
  `matchableCount n = 15 n³ − 45 n² + 40 n` for every even `n`. **PROVED here for every even
  `n`** (`matchableCountClosedForm`), not only on the 2-power tower. With `m = n/2` antipodal
  classes, a matchable tuple chooses, for each class `j`, a count `k_j ≥ 0` of antipodal pairs
  landing in it, with `∑ k_j = 3`, then distributes the 6 labelled positions as
  `6! / ∏_j (k_j!)²`. Only three shapes of `(k_j)` sum to 3:
  `120 m³ − 180 m² + 80 m = 20·m + 180·m(m−1) + 120·m(m−1)(m−2)`, and `m = n/2` gives
  `15 n³ − 45 n² + 40 n`. The Lean proof organises the same count differently: coordinates
  `ZMod (m + m) ≃ Fin m × Bool`, a split by the sign pattern (`20` patterns with three positive
  positions), and the count `6m³ − 9m² + 4m` of pairs of triples with the same multiplicity
  vector. The base cases `n = 2` and `n = 4` are also proven by `decide`
  (`matchableCount_two`, `matchableCount_four`).
  *Overlap:* the same cubic is already proved in tree for another encoding of the count —
  count-balanced 6-tuples over a negation-closed subset `G` of a field
  (`E3StrataCharZero.negSymCount_six_closed`, with `|G|` in place of `n`). The proof here does
  not go through that file; what it adds is the named `ZMod` statement itself, with no field.

* **`LamLeungAntipodalMatchable`** — the deep char-0 input: for 2-power `n`, every zero-sum
  6-tuple of `n`-th roots is antipodally matchable. This is **Lam–Leung on vanishing sums of
  roots of unity** (the only ℤ-relations among `2^μ`-th roots are antipodal pairs). Mathlib
  lacks Lam–Leung; this is the SAME named char-0 wall the whole programme rests on
  (`NegationClosedWalkBound` calls it "the no-genuine-relation residual"). It is FALSE for
  `3 ∣ n` (then `1 + ζ₃ + ζ₃² = 0` supplies non-matchable zero-sum tuples), which is exactly
  why the closed form FAILS for `3 ∣ n` — machine-verified: `zeroSumCount(μ_12,6) = 23160 ≠
  19920` (`probe_e3_closedform.py`). Hence the strict 2-power restriction.

## The bridge (proven axiom-clean here)

`E3_closed_form_of_inputs`: the two named inputs above (`MatchableCountClosedForm` over
`ZMod n` + `LamLeungAntipodalMatchable` for 2-power `n`) give
`zeroSumCount(μ_n, 6) = 15 n³ − 45 n² + 40 n`. The first input is now a theorem
(`matchableCountClosedForm`), so `E3_closed_form_of_lamLeung` states the bridge with a single
hypothesis: the standing char-0 Lam–Leung transport `Z = matchableCount n`.

## Honesty status

PROVEN axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`):
`matchableCount_two`, `matchableCount_four`, the definitions, the general combinatorial
identity `matchableCountClosedForm` (every even `n`), and the bridges
`E3_closed_form_of_inputs` / `E3_closed_form_of_lamLeung`. NAMED open input (not claimed
proven): `LamLeungAntipodalMatchable` (the char-0 Lam–Leung wall), consumed as the explicit
hypothesis `Z = matchableCount n`. This file is still a *reduces-to-a-named-input*, not a
closure of `E_3(μ_n)`: the combinatorial count is settled, the transport from zero-sum
6-tuples of roots of unity to matchable exponent tuples is not, and nothing here concerns
characteristic `p`.

## References
* `NegationClosedWalkBound.lean` (`zeroSumCount`, the K1 upper bound `≤ (2r−1)‼·n^r`).
* `AdditiveEnergySidonModNeg.lean` (`additiveEnergy_eq_of_sidonModNeg`, the `E_2` anchor).
* Probes: `probe_e3_closedform.py`, `probe_e3_decomp.py`, `probe_e3_inclexcl.py`.
-/

set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.E3ClosedForm

/-! ## The field-independent combinatorial object over the exponent group -/

/-- A 6-tuple of exponents `t : Fin 6 → ZMod n` is **antipodally matchable** iff its
value-distribution is invariant under the antipodal shift `x ↦ x + n/2`: for every value
`x`, the number of positions mapping to `x` equals the number mapping to its antipode
`x + n/2`. (Machine-verified equivalent to "the 6 positions partition into 3 antipodal
pairs"; see `probe_e3_decomp.py`.) -/
def matchable (n : ℕ) [NeZero n] (t : Fin 6 → ZMod n) : Prop :=
  ∀ x : ZMod n, (Finset.univ.filter (fun i => t i = x)).card
              = (Finset.univ.filter (fun i => t i = x + (n / 2 : ℕ))).card

instance (n : ℕ) [NeZero n] (t : Fin 6 → ZMod n) : Decidable (matchable n t) := by
  unfold matchable; infer_instance

/-- The **matchable count**: the number of antipodally-matchable 6-tuples over `ZMod n`.
This is the purely combinatorial object — independent of the field/prime. -/
def matchableCount (n : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter (fun t : Fin 6 → ZMod n => matchable n t)).card

/-- The target cubic `15 n³ − 45 n² + 40 n`, phrased over `ℤ` to avoid `Nat`-truncation
pitfalls with the intermediate subtraction. (The value is a nonnegative integer for all `n`:
it factors as `5n(3n² − 9n + 8)` with `3n² − 9n + 8 > 0` always.) -/
def e3Cubic (n : ℕ) : ℤ := 15 * (n : ℤ) ^ 3 - 45 * (n : ℤ) ^ 2 + 40 * (n : ℤ)

/-! ## Axiom-clean base case: `n = 2` -/

/-- **Base case `n = 2`, proven axiom-clean by `decide`.** The matchable count for `n = 2`
is `20`, matching `e3Cubic 2 = 15·8 − 45·4 + 40·2 = 120 − 180 + 80 = 20`. This is the
smallest instance of the prize 2-power tower (`2^6 = 64` tuples). -/
theorem matchableCount_two : matchableCount 2 = 20 := by decide

/- **Second 2-power instance `n = 4`, proven axiom-clean by `decide`** (`matchableCount_four`
below). The matchable count for `n = 4` is `400 = e3Cubic 4 = 15·64 − 45·16 + 40·4 = 960 −
720 + 160`. (`4^6 = 4096` tuples; reachable by the kernel with the raised recursion/heartbeat
limits below. `n ≥ 8` — `8^6 = 262144` tuples — is over the kernel's brute-force ceiling, an
honest *tooling* limit, not a math gap: the closed form is machine-checked exact for
`n = 8,16,32` in `probe_e3_closedform.py`.) -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem matchableCount_four : matchableCount 4 = 400 := by decide

/-- `e3Cubic 2 = 20`: the base value matches the cubic. -/
theorem e3Cubic_two : e3Cubic 2 = 20 := by decide

/-- `e3Cubic 4 = 400`: the `n=4` value matches the cubic. -/
theorem e3Cubic_four : e3Cubic 4 = 400 := by decide

/-- The base case stated against the closed form: `matchableCount 2 = e3Cubic 2`. -/
theorem matchableCount_two_eq_cubic : (matchableCount 2 : ℤ) = e3Cubic 2 := by
  rw [matchableCount_two, e3Cubic_two]; norm_num

/-- The `n=4` case stated against the closed form: `matchableCount 4 = e3Cubic 4`. -/
theorem matchableCount_four_eq_cubic : (matchableCount 4 : ℤ) = e3Cubic 4 := by
  rw [matchableCount_four, e3Cubic_four]; norm_num

/-! ## The combinatorial core as a named statement (general closed form) -/

/-- **The combinatorial core** (PROVED below as `matchableCountClosedForm`). For every even
`n`, the matchable count equals the cubic `15 n³ − 45 n² + 40 n`. This is a FINITE,
FIELD-INDEPENDENT combinatorial identity (the count over `n/2` antipodal classes); it is
NOT the deep char-0 wall — that is `LamLeungAntipodalMatchable` below. -/
def MatchableCountClosedForm : Prop :=
  ∀ (n : ℕ) [NeZero n], Even n → (matchableCount n : ℤ) = e3Cubic n

/-! ## The deep char-0 structural input (Lam–Leung)

**The Lam–Leung antipodal-matchability input** (named char-0 wall). For 2-power `n`, under
any faithful realization of `μ_n` in a field of characteristic 0 (or large enough char),
every zero-sum 6-tuple of `n`-th roots, transported to its exponent tuple
`t : Fin 6 → ZMod n`, is antipodally matchable — and this transport is a *bijection* onto
the matchable tuples. Hence the realized zero-sum 6-tuple count of `μ_n` equals
`matchableCount n`. This is Lam–Leung on vanishing sums of roots of unity (the only
ℤ-relations among `2^μ`-th roots are antipodal pairs); Mathlib lacks it. It is the SAME
named char-0 input the programme rests on (`NegationClosedWalkBound`'s "no-genuine-relation
residual"). It is FALSE for `3 ∣ n` (`1 + ζ₃ + ζ₃² = 0` gives non-matchable zero-sum
tuples), which is exactly why the closed form fails for `3 ∣ n`.

We do NOT axiomatize a vacuous wrapper for it. Instead the bridge below consumes its precise
content — the equality `Z = matchableCount n` — as an explicit hypothesis `hLL`, so the
open input is named exactly where it is used and nowhere laundered. -/

/-! ## The bridge: named inputs ⟹ the E₃ closed form

We state the bridge at the level of the abstract zero-sum count `Z`. The consumer supplies
`Z = zeroSumCount(μ_n, 6)` and the Lam–Leung identity `Z = matchableCount n`; the
combinatorial closed form then pins `Z = e3Cubic n`. -/

/-- **The bridge (proven axiom-clean).** If the general combinatorial closed form holds and
the realized zero-sum count of `μ_n` equals the matchable count (the Lam–Leung transport),
then `Z = 15 n³ − 45 n² + 40 n`. The first hypothesis is discharged by
`matchableCountClosedForm` (see `E3_closed_form_of_lamLeung`); the second is the Lam–Leung
transport, available only for 2-power `n`. -/
theorem E3_closed_form_of_inputs (n : ℕ) [NeZero n] (hn : Even n)
    (hcomb : MatchableCountClosedForm)
    (Z : ℕ) (hLL : Z = matchableCount n) :
    (Z : ℤ) = e3Cubic n := by
  rw [hLL]
  exact hcomb n hn

/-- **Discharged base instance of the bridge (`n = 2`).** The bridge fires *without* the
named combinatorial residual, because the base case is proven: any realized zero-sum count
equal to the matchable count is `20 = e3Cubic 2`. So at `n = 2` the r=2 rung's producer
obstruction reduces to ONLY the Lam–Leung input (`Z = matchableCount 2`). -/
theorem E3_closed_form_two (Z : ℕ) (hLL : Z = matchableCount 2) :
    (Z : ℤ) = e3Cubic 2 := by
  rw [hLL, matchableCount_two_eq_cubic]

/-- **Discharged instance of the bridge (`n = 4`).** Same as `E3_closed_form_two` but for
the second 2-power instance: the combinatorial residual is proven (`matchableCount 4 = 400`),
so at `n = 4` the obstruction reduces to ONLY the Lam–Leung input. -/
theorem E3_closed_form_four (Z : ℕ) (hLL : Z = matchableCount 4) :
    (Z : ℤ) = e3Cubic 4 := by
  rw [hLL, matchableCount_four_eq_cubic]

/-! ## The combinatorial core, proved

`MatchableCountClosedForm` holds for every even `n = 2m`.  Coordinates `ZMod (m + m) ≃ Fin m × Bool`
(class, sign) turn the antipodal shift into a sign flip.  A matchable tuple has exactly three
positive positions (`C(6,3) = 20` patterns, all equivalent under a permutation of the positions),
and against a fixed pattern it is a pair of triples of classes with the same multiplicity vector.
Such pairs are counted through the number of distinct rearrangements of a triple,
`6 − 3[a=b] − 3[a=c] − 3[b=c] + 4[a=b=c]`, which sums to `6m³ − 9m² + 4m`.  Hence
`matchableCount (2m) = 20·(6m³ − 9m² + 4m) = 15n³ − 45n² + 40n`. -/

section Triples
variable {α : Type*} [DecidableEq α]

/-- Two pairs with the same multiplicity vector are equal up to a swap. -/
theorem pair_perm_of_count {b c y z : α}
    (H : ∀ j : α, (if b = j then 1 else 0 : ℕ) + (if c = j then 1 else 0)
        = (if y = j then 1 else 0) + (if z = j then 1 else 0)) :
    (y = b ∧ z = c) ∨ (y = c ∧ z = b) := by
  have hy := H y
  by_cases hby : b = y
  · subst hby
    left
    refine ⟨rfl, ?_⟩
    have hc := H c
    by_contra hzc
    simp [hzc] at hc
  · have hcy : c = y := by
      by_contra hcy
      simp [hby, hcy] at hy
      omega
    subst hcy
    right
    refine ⟨rfl, ?_⟩
    have hb := H b
    by_contra hzb
    simp [hzb] at hb

/-- Two triples with the same multiplicity vector are rearrangements of one another:
peel off the first entry and apply `pair_perm_of_count`. -/
theorem triple_perm_of_count {a b c x y z : α}
    (H : ∀ j : α, (if a = j then 1 else 0 : ℕ) + (if b = j then 1 else 0)
          + (if c = j then 1 else 0)
        = (if x = j then 1 else 0) + (if y = j then 1 else 0) + (if z = j then 1 else 0)) :
    (x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c) ∨
    (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a) := by
  have hx := H x
  have hmem : a = x ∨ b = x ∨ c = x := by
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    simp [h1, h2, h3] at hx
    omega
  rcases hmem with rfl | rfl | rfl
  · have H' : ∀ j : α, (if b = j then 1 else 0 : ℕ) + (if c = j then 1 else 0)
        = (if y = j then 1 else 0) + (if z = j then 1 else 0) := by
      intro j; have := H j; omega
    rcases pair_perm_of_count H' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl, rfl⟩
  · have H' : ∀ j : α, (if a = j then 1 else 0 : ℕ) + (if c = j then 1 else 0)
        = (if y = j then 1 else 0) + (if z = j then 1 else 0) := by
      intro j; have := H j; omega
    rcases pair_perm_of_count H' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; right; left; exact ⟨rfl, rfl, rfl⟩
  · have H' : ∀ j : α, (if a = j then 1 else 0 : ℕ) + (if b = j then 1 else 0)
        = (if y = j then 1 else 0) + (if z = j then 1 else 0) := by
      intro j; have := H j; omega
    rcases pair_perm_of_count H' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; right; right; right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; right; right; right; exact ⟨rfl, rfl, rfl⟩

/-- The six rearrangements of a triple. -/
def perms3 (p : α × α × α) : Finset (α × α × α) :=
  {(p.1, p.2.1, p.2.2), (p.1, p.2.2, p.2.1), (p.2.1, p.1, p.2.2),
   (p.2.1, p.2.2, p.1), (p.2.2, p.1, p.2.1), (p.2.2, p.2.1, p.1)}

/-- A triple has `6 − 3·[a=b] − 3·[a=c] − 3·[b=c] + 4·[a=b=c]` distinct rearrangements
(`6`, `3` or `1`), stated without subtraction. -/
theorem card_perms3 (a b c : α) :
    (perms3 (a, b, c)).card + 3 * (if a = b then 1 else 0) + 3 * (if a = c then 1 else 0)
        + 3 * (if b = c then 1 else 0)
      = 6 + 4 * (if a = b ∧ a = c then 1 else 0) := by
  unfold perms3
  rcases eq_or_ne a b with rfl | hab
  · rcases eq_or_ne a c with rfl | hac
    · simp
    · simp [hac, hac.symm]
  · rcases eq_or_ne a c with rfl | hac
    · simp [hab, hab.symm]
    · rcases eq_or_ne b c with rfl | hbc
      · simp [hab, hab.symm]
      · simp [hab, hab.symm, hac, hac.symm, hbc, hbc.symm]

/-- Two triples have the same multiplicity vector. -/
def SameCount (p q : α × α × α) : Prop :=
  ∀ j : α, (if p.1 = j then 1 else 0 : ℕ) + (if p.2.1 = j then 1 else 0)
      + (if p.2.2 = j then 1 else 0)
    = (if q.1 = j then 1 else 0) + (if q.2.1 = j then 1 else 0) + (if q.2.2 = j then 1 else 0)

/-- Equal multiplicity vectors ⟺ rearrangement. -/
theorem sameCount_iff_mem_perms3 (p q : α × α × α) : SameCount p q ↔ q ∈ perms3 p := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨x, y, z⟩ := q
  simp only [perms3, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro H
    exact triple_perm_of_count H
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> intro j <;> dsimp only <;> ring

instance (p q : α × α × α) : Decidable (SameCount p q) :=
  decidable_of_iff _ (sameCount_iff_mem_perms3 p q).symm

/-- **The triple count.** Over a type with `m` elements there are `6m³ − 9m² + 4m` ordered
pairs of triples with the same multiplicity vector (stated without subtraction). -/
theorem card_sameCount [Fintype α] :
    ((univ : Finset ((α × α × α) × (α × α × α))).filter (fun pq => SameCount pq.1 pq.2)).card
        + 9 * Fintype.card α ^ 2
      = 6 * Fintype.card α ^ 3 + 4 * Fintype.card α := by
  have h1 : ((univ : Finset ((α × α × α) × (α × α × α))).filter
        (fun pq => SameCount pq.1 pq.2)).card = ∑ p : α × α × α, (perms3 p).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp [sameCount_iff_mem_perms3]
  have h2 : ∑ p : α × α × α, ((perms3 p).card + 3 * (if p.1 = p.2.1 then 1 else 0)
        + 3 * (if p.1 = p.2.2 then 1 else 0) + 3 * (if p.2.1 = p.2.2 then 1 else 0))
      = ∑ p : α × α × α, (6 + 4 * (if p.1 = p.2.1 ∧ p.1 = p.2.2 then 1 else 0)) :=
    Finset.sum_congr rfl (fun p _ => card_perms3 p.1 p.2.1 p.2.2)
  have hrow : ∀ a : α, (∑ b : α, ∑ _c : α, (if a = b then 1 else 0 : ℕ)) = Fintype.card α := by
    intro a
    rw [Finset.sum_comm]
    simp
  have s1 : ∑ p : α × α × α, (if p.1 = p.2.1 then 1 else 0 : ℕ) = Fintype.card α ^ 2 := by
    simp only [Fintype.sum_prod_type, hrow, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have s2 : ∑ p : α × α × α, (if p.1 = p.2.2 then 1 else 0 : ℕ) = Fintype.card α ^ 2 := by
    simp only [Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    ring
  have s3 : ∑ p : α × α × α, (if p.2.1 = p.2.2 then 1 else 0 : ℕ) = Fintype.card α ^ 2 := by
    simp only [Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    ring
  have s4 : ∑ p : α × α × α, (if p.1 = p.2.1 ∧ p.1 = p.2.2 then 1 else 0 : ℕ)
      = Fintype.card α := by
    simp [Fintype.sum_prod_type, ite_and]
  have s0 : ∑ _p : α × α × α, (6 : ℕ) = 6 * Fintype.card α ^ 3 := by
    simp [Fintype.card_prod]; ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, s1, s2, s3, s4, s0] at h2
  rw [h1]
  omega

end Triples

section Positions
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Sign-split balance: in every class `j`, as many positions carry sign `true` as `false`. -/
def SignBalanced (u : Fin 6 → α) (s : Fin 6 → Bool) : Prop :=
  ∀ j : α, (univ.filter (fun i => u i = j ∧ s i = true)).card
         = (univ.filter (fun i => u i = j ∧ s i = false)).card

instance (u : Fin 6 → α) (s : Fin 6 → Bool) : Decidable (SignBalanced u s) := by
  unfold SignBalanced; infer_instance

variable (α) in
/-- Number of class assignments balanced against a fixed sign pattern. -/
def signBalancedCount (s : Fin 6 → Bool) : ℕ :=
  (univ.filter (fun u : Fin 6 → α => SignBalanced u s)).card

omit [Fintype α] in
/-- Sign-balance is invariant under a simultaneous permutation of the six positions. -/
theorem signBalanced_comp_perm (ρ : Equiv.Perm (Fin 6)) (u : Fin 6 → α) (s : Fin 6 → Bool) :
    SignBalanced (u ∘ ρ) (s ∘ ρ) ↔ SignBalanced u s := by
  unfold SignBalanced
  refine forall_congr' (fun j => ?_)
  have e1 : (univ.filter (fun i => (u ∘ ρ) i = j ∧ (s ∘ ρ) i = true)).card
      = (univ.filter (fun i => u i = j ∧ s i = true)).card :=
    Finset.card_equiv ρ (by simp)
  have e2 : (univ.filter (fun i => (u ∘ ρ) i = j ∧ (s ∘ ρ) i = false)).card
      = (univ.filter (fun i => u i = j ∧ s i = false)).card :=
    Finset.card_equiv ρ (by simp)
  rw [e1, e2]

/-- The count depends on the sign pattern only up to a permutation of the positions. -/
theorem signBalancedCount_comp_perm (ρ : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool) :
    signBalancedCount α (s ∘ ρ) = signBalancedCount α s := by
  unfold signBalancedCount
  refine Finset.card_equiv (ρ.arrowCongr (Equiv.refl α)) ?_
  intro u
  have hu : (ρ.arrowCongr (Equiv.refl α) u) ∘ ρ = u := by
    ext i; simp [Equiv.arrowCongr]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← signBalanced_comp_perm ρ (ρ.arrowCongr (Equiv.refl α) u) s, hu]

/-- The reference sign pattern: the first three positions positive. -/
def refSign : Fin 6 → Bool := ![true, true, true, false, false, false]

/-- Every sign pattern with exactly three positive positions is a rearrangement of `refSign`. -/
theorem exists_perm_of_card_true (s : Fin 6 → Bool)
    (hs : (univ.filter (fun i => s i = true)).card = 3) :
    ∃ ρ : Equiv.Perm (Fin 6), s ∘ ρ = refSign := by
  have h0 : (univ.filter (fun i => refSign i = true)).card = 3 := by decide
  have hcard : Fintype.card {i // refSign i = true} = Fintype.card {i // s i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hs, h0]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨e.extendSubtype, ?_⟩
  ext i
  by_cases hi : refSign i = true
  · have := e.extendSubtype_mem i hi
    simp [Function.comp, this, hi]
  · have := e.extendSubtype_not_mem i hi
    simp only [Bool.not_eq_true] at this hi
    simp [Function.comp, this, hi]

/-- A sign pattern without exactly three positive positions admits no balanced assignment:
summing the balance equations over the classes gives `#positive = #negative`. -/
theorem signBalancedCount_eq_zero_of_card_ne (s : Fin 6 → Bool)
    (hs : (univ.filter (fun i => s i = true)).card ≠ 3) : signBalancedCount α s = 0 := by
  unfold signBalancedCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ hbal
  apply hs
  have hfib : ∀ b : Bool, (univ.filter (fun i => s i = b)).card
      = ∑ j : α, (univ.filter (fun i => u i = j ∧ s i = b)).card := by
    intro b
    rw [Finset.card_eq_sum_card_fiberwise (f := u) (t := univ) (fun i _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.filter_filter]
    congr 1
    ext i
    simp [and_comm]
  have hsum : (univ.filter (fun i => s i = true)).card
      = (univ.filter (fun i => s i = false)).card := by
    rw [hfib true, hfib false]
    exact Finset.sum_congr rfl (fun j _ => hbal j)
  have htot : (univ.filter (fun i => s i = true)).card
      + (univ.filter (fun i => s i = false)).card = 6 := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin 6)))
      (fun i => s i = true)
    simpa using this
  omega

/-- Reading a 6-tuple as a pair of triples. -/
def sixEquiv : (Fin 6 → α) ≃ (α × α × α) × (α × α × α) where
  toFun u := ((u 0, u 1, u 2), (u 3, u 4, u 5))
  invFun pq := ![pq.1.1, pq.1.2.1, pq.1.2.2, pq.2.1, pq.2.2.1, pq.2.2.2]
  left_inv u := by ext i; fin_cases i <;> rfl
  right_inv pq := rfl

omit [Fintype α] in
/-- Against `refSign`, balance says the first and the last three entries have the same
multiplicity vector. -/
theorem signBalanced_refSign_iff (u : Fin 6 → α) :
    SignBalanced u refSign ↔ SameCount (u 0, u 1, u 2) (u 3, u 4, u 5) := by
  have h0 : refSign 0 = true := rfl
  have h1 : refSign 1 = true := rfl
  have h2 : refSign 2 = true := rfl
  have h3 : refSign 3 = false := rfl
  have h4 : refSign 4 = false := rfl
  have h5 : refSign 5 = false := rfl
  unfold SignBalanced SameCount
  refine forall_congr' (fun j => ?_)
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_six, Fin.sum_univ_six]
  simp [h0, h1, h2, h3, h4, h5]

/-- The count against `refSign` is the triple count. -/
theorem signBalancedCount_refSign : signBalancedCount α refSign
    = ((univ : Finset ((α × α × α) × (α × α × α))).filter
        (fun pq => SameCount pq.1 pq.2)).card := by
  unfold signBalancedCount
  refine Finset.card_equiv sixEquiv ?_
  intro u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact signBalanced_refSign_iff u

/-- Antipodal balance over the class/sign model `α × Bool`. -/
def AntipodalBalanced (t : Fin 6 → α × Bool) : Prop :=
  ∀ y : α × Bool, (univ.filter (fun i => t i = y)).card
    = (univ.filter (fun i => t i = (y.1, !y.2))).card

instance (t : Fin 6 → α × Bool) : Decidable (AntipodalBalanced t) := by
  unfold AntipodalBalanced; infer_instance

omit [Fintype α] in
/-- Antipodal balance of a tuple is sign-balance of its class and sign components. -/
theorem antipodalBalanced_iff (t : Fin 6 → α × Bool) :
    AntipodalBalanced t ↔ SignBalanced (fun i => (t i).1) (fun i => (t i).2) := by
  have key : ∀ (j : α) (b : Bool), (univ.filter (fun i => t i = (j, b)))
      = univ.filter (fun i => (t i).1 = j ∧ (t i).2 = b) := by
    intro j b; ext i; simp [Prod.ext_iff]
  constructor
  · intro H j
    have := H (j, true)
    simpa [key] using this
  · rintro H ⟨j, b⟩
    cases b
    · have := (H j).symm
      simpa [key] using this
    · have := H j
      simpa [key] using this

/-- Split the antipodally balanced tuples by their sign pattern. -/
theorem card_antipodalBalanced :
    (univ.filter (fun t : Fin 6 → α × Bool => AntipodalBalanced t)).card
    = ∑ s : Fin 6 → Bool, signBalancedCount α s := by
  have h1 : (univ.filter (fun t : Fin 6 → α × Bool => AntipodalBalanced t)).card
      = (univ.filter (fun p : (Fin 6 → α) × (Fin 6 → Bool) => SignBalanced p.1 p.2)).card := by
    refine Finset.card_equiv (Equiv.arrowProdEquivProdArrow (Fin 6) (fun _ => α) (fun _ => Bool)) ?_
    intro t
    simp [antipodalBalanced_iff, Equiv.arrowProdEquivProdArrow]
  rw [h1, Finset.card_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [signBalancedCount, Finset.card_filter]

/-- `C(6,3) = 20` sign patterns have exactly three positive positions. -/
theorem card_sign_three :
    (univ.filter (fun s : Fin 6 → Bool => (univ.filter (fun i => s i = true)).card = 3)).card
      = 20 := by decide

/-- **The count over `m` antipodal classes** is `20` times the triple count. -/
theorem card_antipodalBalanced_eq :
    (univ.filter (fun t : Fin 6 → α × Bool => AntipodalBalanced t)).card
    = 20 * ((univ : Finset ((α × α × α) × (α × α × α))).filter
        (fun pq => SameCount pq.1 pq.2)).card := by
  rw [card_antipodalBalanced]
  have hc : ∀ s : Fin 6 → Bool, signBalancedCount α s
      = if (univ.filter (fun i => s i = true)).card = 3 then
          ((univ : Finset ((α × α × α) × (α × α × α))).filter
            (fun pq => SameCount pq.1 pq.2)).card else 0 := by
    intro s
    split_ifs with h
    · obtain ⟨ρ, hρ⟩ := exists_perm_of_card_true s h
      rw [← signBalancedCount_comp_perm ρ s, hρ, signBalancedCount_refSign]
    · exact signBalancedCount_eq_zero_of_card_ne s h
  simp_rw [hc]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, card_sign_three,
    smul_eq_mul]

end Positions

section Transfer

/-- Coordinates on `ZMod (m + m)`: class `j < m` and a sign selecting `j` or its antipode
`j + m`. -/
def halfEnc (m : ℕ) (p : Fin m × Bool) : ZMod (m + m) :=
  ((p.1.val + (if p.2 then m else 0) : ℕ) : ZMod (m + m))

/-- `halfEnc` in terms of `ZMod.val`. -/
theorem halfEnc_val (m : ℕ) [NeZero (m + m)] (p : Fin m × Bool) :
    (halfEnc m p).val = p.1.val + (if p.2 then m else 0) := by
  unfold halfEnc
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  have := p.1.isLt
  split_ifs <;> omega

/-- `halfEnc` is injective. -/
theorem halfEnc_injective (m : ℕ) [NeZero (m + m)] : Function.Injective (halfEnc m) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  have h' := congrArg ZMod.val h
  rw [halfEnc_val, halfEnc_val] at h'
  have hj := j.isLt
  have hj' := j'.isLt
  cases b <;> cases b'
  · have h'' : j.val = j'.val := by simpa using h'
    exact Prod.ext (Fin.ext h'') rfl
  · exfalso
    have h'' : j.val = j'.val + m := by simpa using h'
    omega
  · exfalso
    have h'' : j.val + m = j'.val := by simpa using h'
    omega
  · have h'' : j.val = j'.val := by simpa using h'
    exact Prod.ext (Fin.ext h'') rfl

/-- `halfEnc` is a bijection `Fin m × Bool ≃ ZMod (m + m)`. -/
theorem halfEnc_bijective (m : ℕ) [NeZero (m + m)] : Function.Bijective (halfEnc m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨halfEnc_injective m, ?_⟩
  simp [ZMod.card]
  omega

/-- Flipping the sign is the antipodal shift `x ↦ x + n/2`. -/
theorem halfEnc_flip (m : ℕ) [NeZero (m + m)] (j : Fin m) (b : Bool) :
    halfEnc m (j, !b) = halfEnc m (j, b) + (((m + m) / 2 : ℕ) : ZMod (m + m)) := by
  have hhalf : (m + m) / 2 = m := by omega
  have hmm : (m : ZMod (m + m)) + m = 0 := by
    have := ZMod.natCast_self (m + m)
    push_cast at this
    exact this
  rw [hhalf]
  cases b
  · simp [halfEnc]
  · simp only [halfEnc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, add_zero, Nat.cast_add]
    rw [add_assoc, hmm, add_zero]

/-- Transport of `matchableCount (m + m)` to the class/sign model `Fin m × Bool`. -/
theorem matchableCount_eq_card_antipodalBalanced (m : ℕ) [NeZero (m + m)] :
    matchableCount (m + m)
      = (univ.filter (fun t : Fin 6 → Fin m × Bool => AntipodalBalanced t)).card := by
  let E : Fin m × Bool ≃ ZMod (m + m) := Equiv.ofBijective (halfEnc m) (halfEnc_bijective m)
  have hE : ∀ (t : Fin 6 → Fin m × Bool) (y : Fin m × Bool),
      (univ.filter (fun i => (Equiv.arrowCongr (Equiv.refl (Fin 6)) E) t i = E y))
        = univ.filter (fun i => t i = y) := by
    intro t y; ext i; simp
  have hflip : ∀ y : Fin m × Bool,
      E y + (((m + m) / 2 : ℕ) : ZMod (m + m)) = E (y.1, !y.2) := by
    rintro ⟨j, b⟩; exact (halfEnc_flip m j b).symm
  symm
  unfold matchableCount
  refine Finset.card_equiv (Equiv.arrowCongr (Equiv.refl (Fin 6)) E) ?_
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold AntipodalBalanced matchable
  constructor
  · intro H x
    obtain ⟨y, rfl⟩ := E.surjective x
    rw [hflip, hE, hE]
    exact H y
  · intro H y
    have := H (E y)
    rw [hflip, hE, hE] at this
    exact this

/-- **The combinatorial core, proved.** For every even `n`, the matchable count is the cubic
`15 n³ − 45 n² + 40 n`.  No hypothesis on `n` beyond evenness: this is a count over `ZMod n`,
independent of any field. -/
theorem matchableCountClosedForm : MatchableCountClosedForm := by
  intro n _ hn
  obtain ⟨m, rfl⟩ := hn
  rw [matchableCount_eq_card_antipodalBalanced, card_antipodalBalanced_eq]
  have hQ := card_sameCount (α := Fin m)
  simp only [Fintype.card_fin] at hQ
  have hQ' : (((univ : Finset ((Fin m × Fin m × Fin m) × (Fin m × Fin m × Fin m))).filter
      (fun pq => SameCount pq.1 pq.2)).card : ℤ) = 6 * (m : ℤ) ^ 3 + 4 * m - 9 * (m : ℤ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℤ) hQ
    push_cast at this
    linarith
  unfold e3Cubic
  push_cast
  rw [hQ']
  ring

end Transfer

/-- **The bridge with the combinatorial input discharged.** For every even `n`, a realized
zero-sum count equal to the matchable count is `15 n³ − 45 n² + 40 n`.  The only remaining input
is the Lam–Leung transport `Z = matchableCount n`, which is specific to 2-power `n`. -/
theorem E3_closed_form_of_lamLeung (n : ℕ) [NeZero n] (hn : Even n)
    (Z : ℕ) (hLL : Z = matchableCount n) :
    (Z : ℤ) = e3Cubic n :=
  E3_closed_form_of_inputs n hn matchableCountClosedForm Z hLL

/-! ## Source audit -/

#print axioms matchableCount_two
#print axioms matchableCount_four
#print axioms matchableCount_two_eq_cubic
#print axioms matchableCount_four_eq_cubic
#print axioms E3_closed_form_of_inputs
#print axioms E3_closed_form_two
#print axioms E3_closed_form_four
#print axioms card_sameCount
#print axioms card_antipodalBalanced_eq
#print axioms matchableCountClosedForm
#print axioms E3_closed_form_of_lamLeung

end ArkLib.ProximityGap.E3ClosedForm
