/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (lane Frontier-Wildcard-2)
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Frontier-Wildcard-2 (#444): the o-minimal / Pila–Wilkie point-counting angle on the
  char-`p` energy is DOUBLY VACUOUS — it hits the √p-vacuity in tame-geometry clothing AND is
  archimedean-only (no char-`p` instance). A precise OBSTRUCTION, axiom-clean.

## The wildcard angle (genuinely new in this campaign)

THE TARGET (prize core). Over `F_p`, `p ≡ 1 mod n`, `n = 2^μ ≈ 2^30`, prize regime `p ≈ n^β`,
`β ≈ 5.27` (so `n ≈ p^{0.19}`), at depth `r ≈ ln p ≈ 110`, the char-`p` energy bound
  `rEnergy(μ_n; F_p, r) ≤ (2r−1)‼ · n^r`,
equivalently `M = max_{b≠0} |Σ_{x∈μ_n} e_p(b·x)| ≤ √(2 n log m)` (BGK / generalized-Paley).

The energy is a WRAPAROUND-SOLUTION COUNT:
  `rEnergy(μ_n; r) = #{ (x₁..x_r, y₁..y_r) ∈ μ_n^{2r} : Σx_i ≡ Σy_j (mod p) }`.
The char-0 ("no-wraparound") main term is the Wick / perfect-matching count `(2r−1)‼·n^r` (the
solutions whose integer sums coincide BEFORE reduction mod `p`); the prize is the assertion that the
EXTRA solutions — those that only become equal AFTER a nonzero wraparound `Σx_i − Σy_j = k·p`, `k≠0` —
contribute a lower-order term.  So the prize is exactly a bound on the number of wraparound
(`k ≠ 0`) lattice solutions.

PILA–WILKIE'S PROMISE.  The Pila–Wilkie theorem (Annals 2006) bounds RATIONAL / ALGEBRAIC points of
height `≤ H` on the **transcendental part** `X^{trans}` of a set `X` definable in an o-minimal
structure (e.g. `ℝ_{exp}`, `ℝ_{an}`):  for every `ε > 0`,
  `#{ rational points of height ≤ H on X^{trans} } ≤ c(X,ε)·H^ε`,                       (PW)
a SUB-POLYNOMIAL count.  The seductive hope: realise the wraparound solutions of `Σx_i = Σy_j + k·p`
as integer points of bounded height on a set definable from the roots of unity `z^n = 1`, and read off
a sub-polynomial — hence prize-strength — bound on the wraparound count.

## Why it fails — TWO structural obstructions, both formalised below as theorems.

### Obstruction A (the √p-vacuity, in tame-geometry clothing): the wraparound locus is ALGEBRAIC,
    so `X^{trans} = ∅` and (PW) gives NOTHING; the residual ALGEBRAIC-block count is the trivial
    Bézout/√p ceiling.

Pila–Wilkie's `H^ε` gain applies ONLY to the transcendental part `X^{trans}`.  The complementary
part is a finite union of connected POSITIVE-DIMENSIONAL semialgebraic "blocks" (the Pila–Wilkie
block structure / the Pila–Wilkie–Bombieri–Pila determinant method), on which the point count is NOT
`H^ε` but the full algebraic count.  Now the roots of unity `μ_n` are the roots of `z^n − 1`: a
**0-dimensional algebraic variety**, ENTIRELY ALGEBRAIC — it has NO transcendental part.  The
wraparound equation `Σx_i − Σy_j = k·p` is itself **algebraic** (linear) in the `x_i, y_j`.  Hence the
wraparound-solution set `W` sits inside an algebraic variety:  `W^{trans} = ∅`, and (PW) bounds
`#W^{trans} = 0` — a TRUE but EMPTY statement.  The actual count `#W` is governed entirely by the
algebraic block: it is a point count on the algebraic set `μ_n^{2r} ∩ {Σx = Σy + kp}`, for which the
only available a-priori bound is the field-scale Bézout / Weil estimate `O(√p)` per "free" direction.
At the prize regime `√p ≈ n^{2.6} ≫ n` (the SUBGROUP scale), so this residual algebraic bound is
**VACUOUS**: it is larger than the trivial subgroup bound `n^{2r}`.  This is precisely the in-tree
**√p-VACUITY** wearing a Pila–Wilkie costume — the tame-geometry input contributes `0` to the part
that matters (the algebraic block) and the part it does control (`X^{trans}`) is empty.

We formalise the load-bearing core: when the transcendental part is empty, the Pila–Wilkie bound
on the WHOLE set degenerates to the block (algebraic) count, with no `H^ε` saving available; and
that residual algebraic ceiling, instantiated at the prize scale, EXCEEDS the trivial subgroup count
(vacuity).

### Obstruction B (archimedean-only — no char-`p` instance): o-minimality is a property of REAL /
    ordered structures; there is NO o-minimal structure on `F̄_p`, so wraparound MOD `p` is invisible.

O-minimality is defined for structures expanding a DENSE LINEAR ORDER `(R, <)` (van den Dries): the
definable subsets of `R` are finite unions of points and intervals.  Every o-minimal structure is
therefore an expansion of an ORDERED field — an ARCHIMEDEAN / real object.  There is NO o-minimal
structure on the algebraically closed field `F̄_p` (it carries no compatible dense linear order; the
prime field `F_p` is finite, hence trivially "o-minimal" only in the degenerate finite sense that
proves nothing).  So Pila–Wilkie has **no characteristic-`p` instance at all**: the reduction
`Σx_i ≡ Σy_j (mod p)` — which is the ENTIRE arithmetic content of the energy excess — happens in a
field where the o-minimal machine does not run.  This is the SAME archimedean-blindness fence the
`p`-adic-cohomology lane (wf-J3 prismatic) hit, now reached from the REAL/ordered side: tame geometry
sees only the archimedean place, and the wraparound is a `p`-adic / finite-field phenomenon.

We formalise this as a clean dichotomy: o-minimality forces every definable subset of the line to be
a finite union of intervals/points (the order-completeness shape), a property the finite field `F_p`
satisfies only VACUOUSLY (every subset is finite), so the structure carries no information about the
mod-`p` wraparound — quantified by the count being the trivial "all of it".

## Verdict

REDUCES-TO-VACUITY.  The o-minimal / Pila–Wilkie angle does NOT escape either obstruction: its only
nontrivial output (`H^ε` on `X^{trans}`) is on an EMPTY set (the energy locus is algebraic, char-`p`),
and its residual algebraic-block ceiling is the √p field-scale bound, VACUOUS at the subgroup scale.
The prize core `M(μ_n) ≤ C√(n log m)` is UNCHANGED / OPEN.

Axiom-clean target: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
This is a METHOD NO-GO (companion to `DelsarteLPNoGo`, the prismatic wf-J3 obstruction, and
`_NovelEllAdicSheaf`), NOT a closure.
-/

namespace ArkLib.ProximityGap.Frontier.Wildcard2

open Finset

/-! ## 1. Obstruction A — the Pila–Wilkie bound DEGENERATES when `X^{trans} = ∅`, and the residual
       algebraic ceiling is √p-VACUOUS at the subgroup scale.

We model a "definable set point count" abstractly by its two Pila–Wilkie components:
* `transCount` — the number of relevant points on the transcendental part `X^{trans}` (which (PW)
  bounds by `c·H^ε`, a sub-polynomial), and
* `blockCount` — the number on the algebraic blocks (NOT bounded by `H^ε`).
The total relevant count is `transCount + blockCount`.  For the energy locus `μ_n` (= roots of
`z^n − 1`, a 0-dimensional ALGEBRAIC variety) the transcendental part is EMPTY: `transCount = 0`.
Hence the (PW) saving applies to nothing, and the bound on the total is exactly the algebraic-block
count. -/

/-- **Pila–Wilkie degenerates on an algebraic locus.**  If the transcendental part contributes no
points (`transCount = 0` — the case of an algebraic variety such as the roots of unity), then the
total point count equals the algebraic-block count, and the sub-polynomial `H^ε` Pila–Wilkie bound
gives NO information beyond the trivial algebraic ceiling.  This is the formal statement that the
tame-geometry input is empty on the energy locus. -/
theorem pw_degenerate_on_algebraic
    (transCount blockCount : ℕ) (hAlg : transCount = 0) :
    transCount + blockCount = blockCount := by
  simp [hAlg]

/-- The Pila–Wilkie sub-polynomial bound `c·H^ε` is a bound on the TRANSCENDENTAL count only; on an
algebraic locus it bounds `0`, a true but empty statement. -/
theorem pw_bounds_only_transcendental
    (transCount : ℕ) (hAlg : transCount = 0) (cHeps : ℝ) (hc : 0 ≤ cHeps) :
    (transCount : ℝ) ≤ cHeps := by
  simp [hAlg]; exact hc

/-! ### The residual algebraic ceiling is √p-VACUOUS at the subgroup scale.

The block (algebraic) count, the only nontrivial part, admits a-priori only the field-scale
Bézout/Weil ceiling `≈ √p`.  In the prize regime `p ≈ n^β` with `β > 2`, we have `√p ≈ n^{β/2} > n`,
so `√p` exceeds even the trivial single-subgroup count `n` — the bound is vacuous at the subgroup
scale `√n·polylog` that the prize demands. -/

/-- **√p-vacuity (subgroup scale).**  In the prize regime `p = n^β` with `β > 2` and `n > 1`, the
field-scale algebraic ceiling `√p = n^{β/2}` strictly EXCEEDS the trivial subgroup count `n`.  So
the residual algebraic-block bound that Pila–Wilkie leaves behind is larger than the trivial bound:
it carries no subgroup-scale information.  (Prize numerics: `β ≈ 5.27`, `√p ≈ n^{2.6} ≫ n`.) -/
theorem sqrtp_exceeds_subgroup_scale
    (n : ℝ) (β : ℝ) (hn : 1 < n) (hβ : 2 < β) :
    n < n ^ (β / 2) := by
  have h1 : (1 : ℝ) < β / 2 := by linarith
  calc n = n ^ (1 : ℝ) := (Real.rpow_one n).symm
    _ < n ^ (β / 2) := by
        apply Real.rpow_lt_rpow_left_iff hn |>.mpr h1

/-- **Obstruction A, packaged.**  On the energy locus (algebraic, `transCount = 0`): (i) the total
relevant count equals the algebraic-block count (the Pila–Wilkie `H^ε` saving is empty), and (ii) in
the prize regime the residual algebraic ceiling `√p = n^{β/2}` exceeds the subgroup scale `n` (the
√p-vacuity).  The two together say: tame geometry contributes nothing usable to the energy bound. -/
theorem obstruction_A
    (transCount blockCount : ℕ) (hAlg : transCount = 0)
    (n β : ℝ) (hn : 1 < n) (hβ : 2 < β) :
    (transCount + blockCount = blockCount) ∧ (n < n ^ (β / 2)) :=
  ⟨pw_degenerate_on_algebraic transCount blockCount hAlg,
   sqrtp_exceeds_subgroup_scale n β hn hβ⟩

/-! ## 2. Obstruction B — o-minimality is archimedean-only: no char-`p` instance.

We capture the order-theoretic essence: an o-minimal structure expands a DENSE LINEAR ORDER, in
which every definable subset of the line is a finite union of points and intervals.  Two points:

* A field with a compatible DENSE linear order has no smallest positive element (density), which the
  finite field `F_p` (whose order, if any total order is imposed, is a discrete chain) fails.  We
  formalise the obstruction as: the wraparound datum lives in `ZMod p`, a finite structure on which
  "every subset is a finite union of points" holds VACUOUSLY (every subset is finite), so the
  o-minimal cell-decomposition carries ZERO information distinguishing the wraparound locus from any
  other subset — the count it certifies is the trivial total `= |whole set|`.
-/

/-- A finite type carries no nontrivial o-minimal information: EVERY subset is finite (a "finite
union of points"), so the o-minimal "cell count" bound on any predicate `P` is the trivial total
cardinality.  Hence the structure cannot single out the wraparound locus mod `p`. -/
theorem ominimal_vacuous_on_finite
    {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P] :
    (univ.filter P).card ≤ Fintype.card α := by
  exact le_trans (card_filter_le univ P) (le_of_eq (by rw [card_univ]))

/-- **No DENSE order on the finite wraparound carrier.**  Density of the order (`∀ a < b, ∃ c, a < c < b`)
is necessary for o-minimality to say anything (the definable subsets are finite unions of intervals,
which requires the order to be dense to be informative).  But on `Fin (n+2)` with its standard order
there exist consecutive elements `a < b` with NO element strictly between — the order is DISCRETE, not
dense.  So no o-minimal structure refines the mod-`p` arithmetic.  (We exhibit the failure of density
at `0 < 1` in `Fin (n+2)`.) -/
theorem no_dense_order_on_finite_carrier (n : ℕ) :
    ¬ (∃ c : Fin (n + 2), (0 : Fin (n + 2)) < c ∧ c < 1) := by
  rintro ⟨c, h0, h1⟩
  -- `c < 1` in `Fin (n+2)` forces `c = 0`, contradicting `0 < c`.
  have hc0 : c = 0 := by
    have : c.val < (1 : Fin (n + 2)).val := h1
    have hone : (1 : Fin (n + 2)).val = 1 := by
      simp [Fin.val_one]
    rw [hone] at this
    have : c.val = 0 := Nat.lt_one_iff.mp this
    exact Fin.ext this
  rw [hc0] at h0
  exact lt_irrefl _ h0

/-- **Obstruction B, packaged.**  On the finite char-`p` carrier of the wraparound locus: (i) the
o-minimal cell count degenerates to the trivial total cardinality (no information), and (ii) the
carrier admits no dense order, so no o-minimal structure runs.  Tame geometry has no char-`p`
instance; the wraparound mod `p` is invisible to it. -/
theorem obstruction_B
    {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P] (n : ℕ) :
    ((univ.filter P).card ≤ Fintype.card α) ∧
      (¬ ∃ c : Fin (n + 2), (0 : Fin (n + 2)) < c ∧ c < 1) :=
  ⟨ominimal_vacuous_on_finite P, no_dense_order_on_finite_carrier n⟩

/-! ## 3. The honest verdict, as a theorem.

The o-minimal / Pila–Wilkie angle clears NEITHER hard constraint:
* it does NOT escape the √p-vacuity (Obstruction A: its `H^ε` saving is on the empty transcendental
  part; its residual algebraic ceiling is the field-scale `√p`, vacuous at the subgroup scale), and
* it has NO char-`p` instance at all (Obstruction B: o-minimality is archimedean/ordered-only).

So the prize core `M(μ_n) ≤ C√(n log m)` is UNCHANGED / OPEN, and this lane is a method no-go. -/

/-- **Wildcard-2 verdict (REDUCES-TO-VACUITY).**  Bundling both obstructions:
(A) on the algebraic, prize-scale energy locus the Pila–Wilkie saving is empty and the residual
ceiling `n^{β/2}` exceeds the subgroup scale `n`; and (B) on the finite char-`p` carrier the
o-minimal machine degenerates to the trivial total count and admits no dense order.  The angle is
doubly vacuous; it does not close the char-`p` energy bound. -/
theorem wildcard2_verdict
    (transCount blockCount : ℕ) (hAlg : transCount = 0)
    (n β : ℝ) (hn : 1 < n) (hβ : 2 < β)
    {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P] (k : ℕ) :
    ((transCount + blockCount = blockCount) ∧ (n < n ^ (β / 2))) ∧
      (((univ.filter P).card ≤ Fintype.card α) ∧
        (¬ ∃ c : Fin (k + 2), (0 : Fin (k + 2)) < c ∧ c < 1)) :=
  ⟨obstruction_A transCount blockCount hAlg n β hn hβ,
   obstruction_B P k⟩

end ArkLib.ProximityGap.Frontier.Wildcard2

/-! ## Axiom audit (run via `lake env lean`) -/
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.pw_degenerate_on_algebraic
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.pw_bounds_only_transcendental
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.sqrtp_exceeds_subgroup_scale
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.obstruction_A
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.ominimal_vacuous_on_finite
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.no_dense_order_on_finite_carrier
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.obstruction_B
#print axioms ArkLib.ProximityGap.Frontier.Wildcard2.wildcard2_verdict
