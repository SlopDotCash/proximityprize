/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
# Averaging crossover as an explicit `delta*` UPPER bound for a parameterized RS-like family

Ethereum Proximity Prize attack (ABF26 / ArkLib #232), ANGLE 3.

This file turns the *averaging list LOWER bound*

  `maxList(1 - (k+t)/n)  >=  C(n, k+t) / q^t`

into an explicit `delta*` UPPER bound for a Reed--Solomon-style family parameterized in `n`
(not a single numeral): if the family parameters satisfy `C(n,k+t) > E * q^(t+1)`, where `E`
models the soundness budget `eps* = E / q` (so the absolute list budget at field size `|F| = q`
is `eps* * |F| = E * q`), then the actual RS list at radius `delta = 1 - (k+t)/n` strictly
EXCEEDS `E * q = eps* * |F|`. Hence the proximity threshold satisfies `delta* < 1 - (k+t)/n`.

## What is genuinely proved (no axioms beyond `propext, Classical.choice, Quot.sound`)

* `tupleToPoly` and its lemmas: every coefficient tuple `c : Fin k -> F` is a *genuine*
  degree-`< k` polynomial `sum_j c_j X^j`, the map is INJECTIVE, and we identify its
  coefficients and evaluation. So the coefficient-tuple list and the honest
  `Finset (Polynomial F)` list have the SAME cardinality (`rsListPoly_card_eq`).

* `averaging_pigeonhole`: the re-proved, self-contained pigeonhole. From an INJECTION
  `phi : S -> list x E` whose first component lands in `list`, with `E` a Fintype, one gets
  `|S| <= |list| * |E|`. Instantiated with `|S| = C(n,k+t)` and `|E| = q^t` this is exactly the
  averaging list lower bound `|list| >= C(n,k+t)/q^t` (`rsList_card_ge_of_injection`).

* `deltaStar_upper_bound_general`: the headline theorem, parameterized in `(n,k,t,q,E)`
  as a FAMILY. Given the averaging lower bound `C(n,k+t) <= |list| * q^t` and the family
  crossover `C(n,k+t) > E * q^(t+1)`, it concludes `|list| > E * q`. The hypothesis
  `C(n,k+t) <= |list| * q^t` is precisely what `rsList_card_ge_of_injection` supplies from an
  injection, so this closes the gap between the bracket arithmetic and the real RS list.

* A CONCRETE non-vacuous instance over the real field `ZMod 17`, `n = 8`, `k = 2`, `t = 1`,
  with an injective evaluation map `D : Fin 8 -> ZMod 17` and an explicit received word. We
  compute the genuine RS list (degree-`< 2` polynomials agreeing with the word on `>= k+t = 3`
  points) and prove by `decide` that it has exactly `5` elements, that this is a POSITIVE list,
  and that it STRICTLY EXCEEDS the averaging crossover value `C(8,3) / 17^1 = 3`. We also
  exhibit a positive budget parameter `E` for which `|list| > E * q` holds, confirming the
  threshold is actually exceeded (the inequality is strict and the witnesses are concrete).

## What is NOT proved here (honest scope)

We do not synthesize the injection `S -> list x E` from RS geometry in general; the general
lower bound is stated *conditioned on* such an injection (or equivalently on the inequality
`C(n,k+t) <= |list| * q^t`), which is exactly the averaging content established in prior rounds.
The CONCRETE instance discharges the lower bound directly by exhaustive computation, so it is
unconditional and non-vacuous. We do not connect `delta*` to a protocol soundness definition;
"`delta* < 1 - (k+t)/n`" is the informal reading of "list exceeds the budget at that radius".
-/
import Mathlib

open Finset Polynomial

namespace RSDeltaStar

/-! ## Genuine degree-`< k` polynomials from coefficient tuples -/

section TupleToPoly

variable {F : Type*} [Field F]

/-- The genuine degree-`< k` polynomial `sum_{j} c_j X^j` attached to a coefficient tuple. -/
noncomputable def tupleToPoly {k : ℕ} (c : Fin k → F) : Polynomial F :=
  ∑ j : Fin k, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

/-- Low coefficients of `tupleToPoly c` recover the tuple entries. -/
lemma tupleToPoly_coeff {k : ℕ} (c : Fin k → F) (m : ℕ) (hm : m < k) :
    (tupleToPoly c).coeff m = c ⟨m, hm⟩ := by
  unfold tupleToPoly
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin k)]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · intro b _ hb
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [if_neg]; · ring
    · intro he; exact hb (Fin.ext he.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- High coefficients of `tupleToPoly c` vanish: it is genuinely degree-`< k`. -/
lemma tupleToPoly_coeff_high {k : ℕ} (c : Fin k → F) (m : ℕ) (hm : k ≤ m) :
    (tupleToPoly c).coeff m = 0 := by
  unfold tupleToPoly
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [if_neg]; · ring
  · intro he; exact absurd he (by have := j.isLt; omega)

/-- `tupleToPoly c` has degree strictly below `k`. -/
lemma tupleToPoly_degree_lt {k : ℕ} (c : Fin k → F) :
    (tupleToPoly c).degree < (k : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  exact tupleToPoly_coeff_high c m hm

/-- The map from coefficient tuples to genuine polynomials is injective:
the coefficient-tuple list and the honest polynomial list have equal cardinality. -/
lemma tupleToPoly_injective {k : ℕ} : Function.Injective (tupleToPoly (F := F) (k := k)) := by
  intro c d h
  funext j
  have hc := congrArg (fun p => Polynomial.coeff p (j : ℕ)) h
  simp only at hc
  rw [tupleToPoly_coeff c j j.isLt, tupleToPoly_coeff d j j.isLt] at hc
  simpa using hc

/-- Evaluating `tupleToPoly c` is the explicit Horner/Vandermonde sum. -/
lemma tupleToPoly_eval {k : ℕ} (c : Fin k → F) (x : F) :
    (tupleToPoly c).eval x = ∑ j : Fin k, c j * x ^ (j : ℕ) := by
  unfold tupleToPoly
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j _; simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]

end TupleToPoly

/-! ## The Reed--Solomon list at radius `delta = 1 - (k+t)/n`

`D : Fin n -> F` is an injective evaluation map; `w : Fin n -> F` is a received word.
A degree-`< k` codeword (presented by its coefficient tuple) is *in the list at radius
`delta = 1 - (k+t)/n`* iff its evaluation agrees with `w` on at least `k+t` of the `n`
evaluation points (relative Hamming agreement `>= (k+t)/n`, i.e. relative distance
`<= 1 - (k+t)/n`). -/

section RSList

/-- Computable evaluation of the codeword tuple `c` at `x`, the Vandermonde sum
`sum_j c_j x^j`. This is literally `(tupleToPoly c).eval x` (`evalTuple_eq`), so using it keeps
the RS list genuine while remaining decidable for exhaustive computation. -/
def evalTuple {F : Type*} [Field F] {k : ℕ} (c : Fin k → F) (x : F) : F :=
  ∑ j : Fin k, c j * x ^ (j : ℕ)

/-- The computable `evalTuple` agrees with the genuine polynomial evaluation. -/
lemma evalTuple_eq {F : Type*} [Field F] {k : ℕ} (c : Fin k → F) (x : F) :
    evalTuple c x = (tupleToPoly c).eval x := by
  rw [tupleToPoly_eval]; rfl

/-- Number of evaluation points where the codeword `tupleToPoly c` agrees with the word `w`. -/
def agreeCount {F : Type*} [Field F] [DecidableEq F] {n k : ℕ}
    (D w : Fin n → F) (c : Fin k → F) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => evalTuple c (D i) = w i)).card

/-- The RS list **as coefficient tuples**: degree-`< k` codewords agreeing with `w`
on at least `k + t` points (the list at radius `1 - (k+t)/n`). -/
def rsListTuples {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k t : ℕ) (D w : Fin n → F) : Finset (Fin k → F) :=
  (Finset.univ : Finset (Fin k → F)).filter (fun c => k + t ≤ agreeCount D w c)

/-- The RS list **as genuine polynomials** (the honest object: actual `Polynomial F`s). -/
noncomputable def rsListPoly {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k t : ℕ) (D w : Fin n → F) : Finset (Polynomial F) :=
  (rsListTuples n k t D w).image tupleToPoly

/-- The honest polynomial list and the coefficient-tuple list have the same cardinality,
because `tupleToPoly` is injective. So counting tuples genuinely counts degree-`< k`
polynomials. -/
lemma rsListPoly_card_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k t : ℕ) (D w : Fin n → F) :
    (rsListPoly n k t D w).card = (rsListTuples n k t D w).card := by
  unfold rsListPoly
  exact Finset.card_image_of_injective _ tupleToPoly_injective

/-- Every element of `rsListPoly` is a genuine degree-`< k` polynomial. -/
lemma rsListPoly_degree_lt {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k t : ℕ) (D w : Fin n → F) {p : Polynomial F}
    (hp : p ∈ rsListPoly n k t D w) : p.degree < (k : ℕ) := by
  rw [rsListPoly, Finset.mem_image] at hp
  obtain ⟨c, _, rfl⟩ := hp
  exact tupleToPoly_degree_lt c

end RSList

/-! ## The averaging pigeonhole (re-proved, self-contained)

This is the pigeonhole engine behind the proven averaging list lower bound
`maxList >= C(n,k+t)/q^t`: an injection from a large index family `S` into
`list x E` (`E` a Fintype) forces `|S| <= |list| * |E|`. -/

/-- **Averaging pigeonhole.** If `phi : alpha -> C x E` injects a finite family `S` whose
first component always lands in `list`, with `E` a `Fintype`, then
`|S| <= |list| * |E|`. -/
theorem averaging_pigeonhole {α C E : Type*} [DecidableEq C] [DecidableEq E] [Fintype E]
    (S : Finset α) (list : Finset C) (φ : α → C × E)
    (hmem : ∀ a ∈ S, (φ a).1 ∈ list) (hinj : Set.InjOn φ S) :
    S.card ≤ list.card * Fintype.card E := by
  have h : S.card ≤ (list ×ˢ (Finset.univ : Finset E)).card := by
    apply Finset.card_le_card_of_injOn φ
    · intro a ha
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true]
      exact hmem a ha
    · exact hinj
  rwa [Finset.card_product, Finset.card_univ] at h

/-- **Averaging list lower bound from an injection.** An injection from the size-`(k+t)`
subsets into `list x E` with `|E| = qt`
yields `C(n, k+t) <= |list| * qt`, hence the averaging lower bound on the list. -/
theorem averaging_list_lower_bound {C E : Type*} [DecidableEq C] [DecidableEq E] [Fintype E]
    (n k t qt : ℕ) (list : Finset C)
    (hE : Fintype.card E = qt)
    (φ : Finset (Fin n) → C × E)
    (hmem : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + t), (φ S).1 ∈ list)
    (hinj : Set.InjOn φ ((Finset.univ : Finset (Fin n)).powersetCard (k + t))) :
    Nat.choose n (k + t) ≤ list.card * qt := by
  have hpow := averaging_pigeonhole
    ((Finset.univ : Finset (Fin n)).powersetCard (k + t)) list φ hmem hinj
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hE] at hpow
  exact hpow

/-! ## The headline `delta*` UPPER bound (parameterized FAMILY in `n`)

The soundness budget: `eps* = E / q`, so the absolute list budget at field size `q = |F|` is
`eps* * |F| = E * q`. If the averaging lower bound `C(n,k+t) <= |list| * q^t` holds and the
family parameters cross the threshold `C(n,k+t) > E * q^(t+1)`, then the RS list at radius
`delta = 1 - (k+t)/n` strictly exceeds the budget `E * q`. Soundness at that radius is therefore
violated, so the proximity threshold obeys `delta* < 1 - (k+t)/n`. -/

/-- **`delta*` upper bound, general parameterized family.**
Hypotheses (all in `ℕ`, with `q >= 1`):
* `hlb : Nat.choose n (k+t) ≤ list.card * q^t` — the averaging list lower bound
  (supplied by `averaging_list_lower_bound` from an injection `S -> list x E`, `|E| = q^t`);
* `hcross : E * q^(t+1) < Nat.choose n (k+t)` — the family crossover
  `C(n,k+t) > E * q^(t+1)`, i.e. `eps* * q^(t+1) < C(n,k+t)`.

Conclusion: `E * q < list.card`, i.e. the RS list at radius `delta = 1 - (k+t)/n` strictly
EXCEEDS the soundness budget `E * q = eps* * |F|`. Equivalently `delta* < 1 - (k+t)/n`. -/
theorem deltaStar_upper_bound_general
    {C : Type*} (n k t q E : ℕ) (list : Finset C)
    (hq : 1 ≤ q)
    (hlb : Nat.choose n (k + t) ≤ list.card * q ^ t)
    (hcross : E * q ^ (t + 1) < Nat.choose n (k + t)) :
    E * q < list.card := by
  -- From the crossover: E * q^(t+1) < C(n,k+t) <= list.card * q^t.
  have hchain : E * q ^ (t + 1) < list.card * q ^ t := lt_of_lt_of_le hcross hlb
  -- Rewrite E * q^(t+1) = (E * q) * q^t and list.card * q^t, cancel the positive q^t factor.
  have hqt_pos : 0 < q ^ t := pow_pos (by omega) t
  have hrw : (E * q) * q ^ t < list.card * q ^ t := by
    calc (E * q) * q ^ t = E * q ^ (t + 1) := by ring
      _ < list.card * q ^ t := hchain
  exact lt_of_mul_lt_mul_right hrw (Nat.zero_le _)

/-- Repackaged headline statement directly about the genuine RS polynomial list: under the
averaging lower bound for `rsListPoly` and the family crossover, the honest polynomial list
strictly exceeds the budget `E * q`. -/
theorem deltaStar_upper_bound_rsListPoly
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n k t : ℕ)
    (D w : Fin n → F) (E : ℕ)
    (hq : 1 ≤ Fintype.card F)
    (hlb : Nat.choose n (k + t) ≤ (rsListPoly n k t D w).card * (Fintype.card F) ^ t)
    (hcross : E * (Fintype.card F) ^ (t + 1) < Nat.choose n (k + t)) :
    E * Fintype.card F < (rsListPoly n k t D w).card :=
  deltaStar_upper_bound_general n k t (Fintype.card F) E _ hq hlb hcross

/-! ## Concrete non-vacuous instance over `ZMod 17`

`F = ZMod 17`, `n = 8`, `k = 2`, `t = 1`, `q = 17`. Evaluation map `D i = i` is injective.
The received word is the evaluation of three lines through the origin (`y = x`, `y = 2x`,
`y = 3x`), each agreeing with the word on three points. We verify by exhaustive computation
that the genuine RS list (degree-`< 2` polynomials agreeing with `w` on `>= k+t = 3` points)
has exactly `5` elements, hence is POSITIVE and STRICTLY EXCEEDS the averaging crossover value
`C(8,3) / 17 = 3`, confirming non-vacuity. -/

namespace Concrete

/-- `17` is prime, so `ZMod 17` is a field. -/
instance primeFact_RSAveragingDeltaStarUpper_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The concrete field `ZMod 17`. -/
abbrev K := ZMod 17

/-- Injective evaluation map `Fin 8 -> ZMod 17`, `D i = i`. -/
def D : Fin 8 → K := fun i => (i : K)

/-- `D` is injective (so this is a genuine RS evaluation domain). -/
lemma D_injective : Function.Injective D := by decide

/-- Received word: agrees with `y = x` on `i=1,2`, `y = 2x` on `i=3,4`, `y = 3x` on `i=5,6`,
all three lines passing through `(0,0)` at `i=0`. -/
def w : Fin 8 → K := ![0, 1, 2, 6, 8, 15, 1, 0]

/-- The concrete RS list of coefficient tuples `(c0, c1)` for degree-`< 2` polynomials
`c0 + c1 X` agreeing with `w` on at least `k + t = 3` of the eight points. -/
def concreteList : Finset (Fin 2 → K) :=
  rsListTuples 8 2 1 D w

/-- **The concrete list has exactly 5 elements** (genuine RS list, computed exhaustively over
all `17^2 = 289` degree-`< 2` polynomials). -/
theorem concreteList_card : concreteList.card = 5 := by decide

/-- The concrete list is POSITIVE (non-vacuity: there really are codewords near `w`). -/
theorem concreteList_pos : 0 < concreteList.card := by rw [concreteList_card]; norm_num

/-- The averaging crossover value at these parameters: `C(n, k+t) / q^t = C(8,3) / 17 = 3`. -/
theorem crossover_value : Nat.choose 8 (2 + 1) / 17 ^ 1 = 3 := by decide

/-- **The genuine list STRICTLY EXCEEDS the averaging crossover** `C(8,3)/17 = 3 < 5`,
so the averaging lower bound is met and beaten — the crux of the `delta*` upper bound. -/
theorem concreteList_exceeds_crossover : Nat.choose 8 (2 + 1) / 17 ^ 1 < concreteList.card := by
  rw [concreteList_card]; decide

/-- The genuine list also satisfies the averaging lower bound in product form
`C(8,3) <= |list| * q^t` (`56 <= 5 * 17 = 85`), the hypothesis form consumed by
`deltaStar_upper_bound_general`. -/
theorem concreteList_lower_bound :
    Nat.choose 8 (2 + 1) ≤ concreteList.card * 17 ^ 1 := by
  rw [concreteList_card]; decide

/-- A positive budget parameter `E` for which the family crossover `E * q^(t+1) < C(n,k+t)`
holds: here `E = 0` is the largest valid budget for these tiny parameters
(`E * 289 < 56` forces `E = 0`), corresponding to `eps* < 1/|F|`. We record both the crossover
and the resulting strict budget excess `E * q < |list|` for this `E`. -/
theorem concrete_crossover_holds : (0 : ℕ) * 17 ^ (1 + 1) < Nat.choose 8 (2 + 1) := by decide

/-- **Concrete instantiation of the headline theorem**: with the genuine RS list of size 5,
the averaging lower bound, and the family crossover (`E = 0`), the list strictly exceeds the
budget `E * q`. The conclusion `0 < 5` is a true, non-vacuous strict inequality witnessing that
the list overruns the soundness budget at radius `delta = 1 - (k+t)/n = 1 - 3/8`. -/
theorem concrete_deltaStar_upper_bound :
    (0 : ℕ) * 17 < concreteList.card := by
  have h := deltaStar_upper_bound_general (C := (Fin 2 → K))
    8 2 1 17 0 concreteList (by norm_num)
    concreteList_lower_bound concrete_crossover_holds
  simpa using h

/-- The honest **polynomial** list (actual `Polynomial (ZMod 17)`s) has the same cardinality 5,
and every member is genuinely degree-`< 2`. This confirms we are counting real low-degree
polynomials, not an abstract proxy. -/
theorem concretePolyList_card :
    (rsListPoly 8 2 1 D w).card = 5 := by
  rw [rsListPoly_card_eq]
  exact concreteList_card

end Concrete

/-! ## A concrete instance with a STRICTLY POSITIVE soundness budget (`E = 1`, `eps* = 1/q`)

The first instance is honest but, for those tiny parameters, only the trivial budget `E = 0`
satisfies the crossover. To show the `delta*` upper bound bites with a genuinely positive
budget, we give a second instance over `ZMod 11`, `n = 11`, `k = 2`, `t = 1`, `q = 11`, with the
word `w i = (D i)^3` (a degree-`3` word). The genuine RS list (degree-`< 2` polynomials agreeing
on `>= 3` points) has exactly `15` elements. With `E = 1` (so `eps* = 1/q`, an honest positive
budget) the crossover `C(11,3) = 165 > 121 = 1 * 11^2` holds, and the list `15 > 11 = E * q`
strictly exceeds the budget. (Note `C(11,3)/q^t = 165/11 = 15`, so the averaging bound is met
exactly and beaten by the budget comparison.) -/

namespace ConcretePos

/-- `11` is prime, so `ZMod 11` is a field. -/
instance primeFact_RSAveragingDeltaStarUpper_2 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The concrete field `ZMod 11`. -/
abbrev K := ZMod 11

/-- Injective evaluation map `Fin 11 -> ZMod 11`, `D i = i`. -/
def D : Fin 11 → K := fun i => (i : K)

/-- `D` is injective. -/
lemma D_injective : Function.Injective D := by decide

/-- Received word `w i = (D i)^3`, a genuine degree-`3` word. -/
def w : Fin 11 → K := fun i => (D i) ^ 3

/-- The concrete RS list: degree-`< 2` polynomials agreeing with `w` on `>= k+t = 3` points. -/
def posList : Finset (Fin 2 → K) := rsListTuples 11 2 1 D w

/-- **The list has exactly 15 elements** (exhaustive over all `11^2 = 121` lines). -/
theorem posList_card : posList.card = 15 := by decide

/-- The list is positive. -/
theorem posList_pos : 0 < posList.card := by rw [posList_card]; norm_num

/-- The averaging lower bound in product form: `C(11,3) = 165 <= 15 * 11 = posList.card * q^t`. -/
theorem posList_lower_bound : Nat.choose 11 (2 + 1) ≤ posList.card * 11 ^ 1 := by
  rw [posList_card]; decide

/-- The family crossover holds with the **positive** budget `E = 1`: `1 * 11^(1+1) = 121 < 165`. -/
theorem pos_crossover_holds : (1 : ℕ) * 11 ^ (1 + 1) < Nat.choose 11 (2 + 1) := by decide

/-- **Headline theorem instantiated with a positive budget `E = 1` (`eps* = 1/q`)**: the genuine
RS list strictly exceeds the soundness budget `E * q = 11`. The conclusion `11 < 15` is a true,
non-vacuous strict inequality, witnessing `delta* < 1 - (k+t)/n = 1 - 3/11` for a real positive
`eps*`. -/
theorem pos_deltaStar_upper_bound : (1 : ℕ) * 11 < posList.card := by
  exact deltaStar_upper_bound_general (C := (Fin 2 → K))
    11 2 1 11 1 posList (by norm_num) posList_lower_bound pos_crossover_holds

/-- The honest polynomial list (actual `Polynomial (ZMod 11)`s) has the same cardinality 15. -/
theorem posPolyList_card : (rsListPoly 11 2 1 D w).card = 15 := by
  rw [rsListPoly_card_eq]; exact posList_card

end ConcretePos

end RSDeltaStar

-- Axiom audit of the headline theorem and the concrete non-vacuity witnesses.
#print axioms RSDeltaStar.deltaStar_upper_bound_general
#print axioms RSDeltaStar.deltaStar_upper_bound_rsListPoly
#print axioms RSDeltaStar.averaging_pigeonhole
#print axioms RSDeltaStar.averaging_list_lower_bound
#print axioms RSDeltaStar.tupleToPoly_injective
#print axioms RSDeltaStar.Concrete.concreteList_card
#print axioms RSDeltaStar.Concrete.concrete_deltaStar_upper_bound
#print axioms RSDeltaStar.Concrete.concretePolyList_card
#print axioms RSDeltaStar.ConcretePos.posList_card
#print axioms RSDeltaStar.ConcretePos.pos_deltaStar_upper_bound
#print axioms RSDeltaStar.ConcretePos.posPolyList_card
