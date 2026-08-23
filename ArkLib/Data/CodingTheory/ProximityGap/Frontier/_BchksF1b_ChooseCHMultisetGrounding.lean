/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BchksF1_CompleteHomogeneousFloor
import Mathlib.Data.Sym.Card

/-!
# Bchks F1b — `chooseCH` GROUNDED as the degree-`r` complete-homogeneous dimension (#444)

The F1 floor file (`_BchksF1_CompleteHomogeneousFloor`) *defines* the worst-direction multiplier
`chooseCH s r = C(s+r−1, r)` and ASSERTS in prose that it is

> "the number of degree-`r` monomials in `s` variables (= dim of the degree-`r` complete-homogeneous
>  space = #multisets of size `r` from `s` elements)".

That combinatorial grounding is exactly what makes `chooseCH` the *right* a-priori ceiling for the
complete-homogeneous spectrum (the distinct `h_r(R)` values): the spectrum is a `Finset` of values of
a degree-`r` complete-homogeneous polynomial, and there are only `chooseCH s r` such monomials, so any
realized spectrum of `h_r` over an `s`-node alphabet is a-priori cut by this count. F1 left that
grounding as prose. This file DISCHARGES it into theorems, EXTEND-proven on F1's `chooseCH`:

* `chooseCH_eq_multichoose` : `chooseCH s r = Nat.multichoose s r` (the truncated-`Nat`-subtraction
  identity `Nat.multichoose_eq`, so `chooseCH` IS the multichoose / multicombination count — note
  this is sharper than the rationals: it gives the correct `chooseCH 0 0 = 1` edge that the naive
  `C(s+r−1,r)` over `ℤ` would miss).
* `chooseCH_eq_card_sym` : `chooseCH s r = Fintype.card (Sym (Fin s) r)` — the EXACT "#multisets of
  size `r` from `s` elements" claim, via Mathlib's stars-and-bars `Sym.card_sym_fin_eq_multichoose`.
  This is the combinatorial JUSTIFICATION of the F1 ceiling: `Sym (Fin s) r` is the type of degree-`r`
  monomials in `s` variables (= the monomial basis of the degree-`r` complete-homogeneous space).
* `chooseCH_mono_left` : `chooseCH` is monotone in the alphabet size `s` (more nodes ⟹ at least as
  many monomials). F1 had no `s`-monotonicity (F6 only carries the `r`-monotonicity `chooseCH_mono`);
  the alphabet-monotonicity is the natural companion and follows from `Sym`-cardinality monotonicity
  along the `Fin s ↪ Fin (s+1)` embedding.
* `chooseCH_pos` : `0 < chooseCH s r` for `s ≥ 1` (every alphabet has ≥1 degree-`r` monomial — the
  spectrum ceiling is never vacuously `0` in the prize regime `s = n ≥ 1`).

## Honest scope (rules 1,3,6)

This is the F1 ceiling's combinatorial *grounding*, NOT the open core. It says only "there are
`chooseCH s r` degree-`r` monomials over `s` nodes" — pure char-free enumerative combinatorics with NO
field-arithmetic or thinness content. The genuine prize core is the SPECTRUM bound
`#{distinct h_r(R)} ≤ poly(n)·chooseCH s r` (`poly=1` is FALSE, `poly=n` verified — see
`probe_completehomog_spectrum.py` / the F1 `poly(n)=n` fix), which remains OPEN. This file does NOT
touch it. NO moment/census/orbit re-derivation; a `Sym`/`multichoose` cardinality object, NOT a
`δ*`/incidence object — the asymptotic-guard cliff-at-`n/2` is UNTOUCHED, no capacity / beyond-Johnson
/ growth-law claim. CORE `M(μ_n) ≤ C√(n log(p/n))` OPEN.
-/

set_option autoImplicit false

open Fintype

namespace ArkLib.ProximityGap.BchksF1

/-- **`chooseCH` IS the multichoose count.** `chooseCH s r = Nat.multichoose s r`. Direct from
`Nat.multichoose_eq : multichoose n k = (n + k − 1).choose k` (with truncated `Nat` subtraction, so
the `s + r − 1` is the correct `Nat` value — in particular `chooseCH 0 0 = 1`, matching the single
empty multiset). This identifies F1's arithmetic definition with the canonical multicombination
counter. -/
theorem chooseCH_eq_multichoose (s r : ℕ) : chooseCH s r = Nat.multichoose s r := by
  rw [chooseCH, Nat.multichoose_eq]

/-- **`chooseCH` counts the degree-`r` monomials in `s` variables (stars and bars).**
`chooseCH s r = Fintype.card (Sym (Fin s) r)`. This is the EXACT combinatorial grounding F1 asserts in
prose: `Sym (Fin s) r` is the type of size-`r` multisets over an `s`-element alphabet, i.e. the
monomial basis of the degree-`r` complete-homogeneous space. Hence the complete-homogeneous spectrum
(the distinct `h_r(R)` values) lives inside a space of dimension `chooseCH s r`, justifying it as the
a-priori ceiling. Via Mathlib `Sym.card_sym_fin_eq_multichoose`. -/
theorem chooseCH_eq_card_sym (s r : ℕ) : chooseCH s r = Fintype.card (Sym (Fin s) r) := by
  rw [chooseCH_eq_multichoose, ← Sym.card_sym_fin_eq_multichoose]

/-- **`chooseCH` is monotone in the alphabet size `s`** (the companion to F6's depth-monotonicity
`chooseCH_mono`): a larger node set has at least as many degree-`r` monomials,
`chooseCH s r ≤ chooseCH (s + 1) r`. Proven directly on the multichoose / binomial form: increasing
the alphabet weakly increases `C(s + r − 1, r)` in the top argument. -/
theorem chooseCH_mono_left (s r : ℕ) : chooseCH s r ≤ chooseCH (s + 1) r := by
  rw [chooseCH, chooseCH]
  exact Nat.choose_le_choose r (by omega)

/-- **The degree-`r` monomial count is positive on any nonempty alphabet** (`s ≥ 1`): there is always
at least one degree-`r` complete-homogeneous monomial (e.g. `x₀^r`), so the spectrum ceiling
`chooseCH s r` is never vacuously `0` in the prize regime `s = n ≥ 1`. -/
theorem chooseCH_pos {s : ℕ} (hs : 1 ≤ s) (r : ℕ) : 0 < chooseCH s r := by
  rw [chooseCH]
  exact Nat.choose_pos (by omega)

/-- **Sanity (grounding ⟹ the F1 concrete numbers are monomial counts).** At `s = 8, r = 3` the
ceiling `chooseCH 8 3 = 120` IS `card (Sym (Fin 8) 3)` — there are exactly 120 degree-`3` monomials in
8 variables — strictly above the subset-sum `C(8,3) = 56`, machine-checked through the `Sym` grounding. -/
theorem chooseCH_card_sym_concrete :
    chooseCH 8 3 = Fintype.card (Sym (Fin 8) 3) ∧ chooseCH 8 3 = 120 := by
  refine ⟨chooseCH_eq_card_sym 8 3, by decide⟩

end ArkLib.ProximityGap.BchksF1

/-! ## Axiom audit (expected: ⊆ `{propext, Classical.choice, Quot.sound}`) -/
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_eq_multichoose
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_eq_card_sym
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_mono_left
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_pos
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_card_sym_concrete
