/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettUnion
import ArkLib.Data.CodingTheory.GMMDS.LovettDivisibility
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparation

/-!
# Lovett's GM-MDS proof: the one-vector separation step (#389)

The closing contradiction of arXiv:1803.02523 (and the leaf steps of Lemmas 2.5/2.6) in one
move: if the reduced union `P(k,V')` is linearly independent and **every** `V' i` has a `1` in a
distinguished coordinate `j`, then adjoining the single polynomial `pFam vlast 0` of a vector
`vlast` with `vlast j = 0` keeps the family linearly independent — because every member of
`P(k,V')` is divisible by `(x − aⱼ)` while `pFam vlast 0` is not.

This is exactly `P(k, V' ∪ {vlast})` shown independent from `P(k,V')` independent, the inductive
payoff used to defeat the minimal counterexample.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-- **One-vector separation.**  `P(k,V')` independent + every `V' i` carries a `1` in coordinate
`j` + `vlast j = 0` ⟹ the `Option`-extension by `pFam vlast 0` is independent. -/
theorem linearIndependent_separate_one {V : Fin m → (Fin n → ℕ)} {k : ℕ} {j : Fin n}
    (hindep : LinearIndependent (MvPolynomial (Fin n) F) (pFamUnion (F := F) V k))
    (hall : ∀ i, 1 ≤ V i j) {vlast : Fin n → ℕ} (hsep : vlast j = 0) :
    LinearIndependent (MvPolynomial (Fin n) F)
      (fun o : Option (Σ i : Fin m, Fin (k - vAbs (V i))) =>
        o.elim (pFam (F := F) vlast 0) (pFamUnion (F := F) V k)) := by
  refine linearIndependent_option_of_dvd (c := MvPolynomial.X j) hindep (fun p => ?_) ?_
  · show (Polynomial.X - Polynomial.C (MvPolynomial.X j)) ∣ pFam (F := F) (V p.1) (p.2 : ℕ)
    exact xSubA_dvd_pFam (hall p.1) _
  · show ¬ (Polynomial.X - Polynomial.C (MvPolynomial.X j)) ∣ pFam (F := F) vlast 0
    exact not_xSubA_dvd_pFam hsep 0

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.linearIndependent_separate_one

/-
## Refuted approach (do not retry): naive block separation

One might hope to discharge `LovettPrimitiveCase` by adding a vector's ENTIRE fiber block
`{pVanish (V i) * X^e : e < k - vAbs (V i)}` to an independent family in one step, separated
at a coordinate `j` with `V i j = 0` (so the block does not vanish at `MvPolynomial.X j`).
This FAILS. `linearIndependent_option_of_eval` works for a *single* `p` because `r • p`
vanishing at `c` forces `r = 0` (`p c ≠ 0`, domain). For a block, an element is `w · q` with
`w = pVanish (V i)` (`w(c) ≠ 0`) and `q = Σ_e (C r_e) X^e`; it vanishes at `c` iff `Σ_e r_e c^e = 0`,
a SINGLE linear equation that does NOT force all `r_e = 0`. So the block is not disjoint from
`{y : eval c y = 0}`, and the span-disjointness hypothesis of the option lemma is false.
This is exactly why `linearIndependent_separate_one` adds only the `e = 0` fiber, and why the
primitive case needs Lovett's genuine argument (dimension counting / generalized-Vandermonde
nonsingularity over `Frac(R)`), not iterated single-coordinate separation. Issue #389.
-/
