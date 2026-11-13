/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# Mollified / weighted SIGNED period: a frequency multiplier CANNOT separate the diagonal from the
structured off-diagonal (#444, door G6)

Companion to `_JacobiMomentIdentity` (the √p-removal identity + the diagonal/off-diagonal split) and
`_JacobiFermatCohomology` (the off-diagonal is STRUCTURED, weight `2r-1`, NOT √-cancelling). Those files
relocated the prize to `OffDiagonalJacobiCancellation`: the off-diagonal correlation of normalized
iterated-Jacobi phases must be lower-order than the diagonal Wick value. The raw off-diagonal does NOT
cancel (the measurement `W/√offdiag` GROWS `0, 0.95, 19.4` at `r=2,3,4` — structured, not square-root).

## The G6 door: a mollifier as the new degree of freedom

The proposal: introduce a **mollifier** `w : (ZMod p) → ℂ` — a weight on the frequency `b` — and form the
**weighted signed moment**
```
   M_w(r) := Σ_{b}  w(b) · |η_b|^{2r},        η_b = Σ_{u ∈ μ_n} e_p(b·u).
```
The hope (Vinogradov/Selberg mollification adapted to the subgroup `μ_n`): choose `w` so that `M_w(r)`
**kills the structured wraparound off-diagonal while preserving the diagonal** (the Wick value `(2r−1)‼·n^r`),
turning the open `OffDiagonalJacobiCancellation` into an identity. The mollifier `w` is a genuinely new degree
of freedom — neither AG nor a raw character sum.

## The structure the mollifier acts on — and the decisive obstruction

`|η_b|^{2r}` is a pure character sum in `b`:
```
   |η_b|^{2r} = Σ_{x, y ∈ (μ_n)^r}  e_p( b · (Σx_i − Σy_j) ).
```
Therefore, for ANY mollifier `w`,
```
   M_w(r) = Σ_{x, y ∈ (μ_n)^r}  ŵ( Σx_i − Σy_j ),        ŵ(t) := Σ_b w(b) e_p(b·t).      (★)
```
**The mollifier couples to the tuples `(x,y)` ONLY through the single scalar `t = Σx_i − Σy_j ∈ ZMod p`.**
It is a multiplier in the "additive-defect" variable `t`. This is the whole content of door G6, and it is the
obstruction:

* **Diagonal** = tuples with `Σx = Σy`, i.e. `t = 0`. Weight `ŵ(0)`.
* **Structured off-diagonal** = the part of the prize-relevant correlation that ALSO has `Σx = Σy` (same
  additive relation) but a DIFFERENT iterated-Jacobi phase `Jphase(y) ≠ Jphase(x)`. This also has `t = 0`.

The two pieces the mollifier must separate **live on the SAME fiber `t = 0`** (this is exactly the
diagonal/off-diagonal split of `_JacobiMomentIdentity`: both sit inside the relation locus `Σx = Σy`; they
differ only in the *Jacobi phase*, which is INVISIBLE to `t`). A frequency multiplier `w(b)` sees the tuples
only through `t`, so it applies the **same scalar `ŵ(0)`** to the diagonal and to the structured off-diagonal.

## The theorem (this file, axiom-clean): no separation

`mollifier_acts_through_defect` (★): `M_w(r)` is a function of the multiset of additive defects `{t(x,y)}`
alone. `multiplier_cannot_separate`: if the diagonal index set `D` and the structured-off-diagonal index set
`O` both lie in the fiber `t = 0` (the prize regime, where the off-diagonal is on the SAME relation), then for
EVERY mollifier `w` the contribution is `ŵ(0)·(|D| + Off)` — the diagonal weight `ŵ(0)·|D|` and the
off-diagonal weight `ŵ(0)·Off` are scaled by the SAME factor `ŵ(0)`. **No choice of `w` can null the
off-diagonal `Off` while keeping the diagonal `|D|` nonzero** (both are multiplied by `ŵ(0)`; killing one
kills the other). The mollifier CANNOT separate.

The escape would require a weight that depends on the *Jacobi phase* (not on `b`), i.e. a weight on the SHAPE
of the tuple — but that is no longer a period `Σ_b w(b)|η_b|^{2r}`; it is the off-diagonal cancellation itself,
restated. So mollification (as a frequency multiplier) **reduces** to `OffDiagonalJacobiCancellation` rather
than escaping it.

## Honest verdict

`boundsOnset = false`, `genuinelyNew = true` (the structural no-go is new and clean), `outcome = REDUCES`.
A frequency-multiplier mollifier `Σ_b w(b)|η_b|^{2r}` provably cannot separate the diagonal from the
structured off-diagonal, because both lie on the `t = 0` fiber and the mollifier acts only through `t`. The
only mollifier that *could* help is one that resolves the Jacobi phase — which is the open theorem itself.
This file PROVES the no-go (no fabricated cancellation), and is therefore an honest negative result for the
G6 door. It does NOT close #444 and gives NO new `r₀` bound. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned

open Finset

/-! ## The abstract multiplier structure

We model the situation abstractly to make the no-go a clean, machine-checked algebraic fact, independent of
the analytic `e_p`/`η_b` plumbing (which is the cited content of `_JacobiMomentIdentity`). The only inputs are:

* an index set `I` of tuple-pairs `(x,y)` (a `Fintype`),
* the additive-defect map `t : I → T` (`t(x,y) = Σx − Σy ∈ ZMod p`; here `T` abstract),
* the per-pair signed Jacobi correlation `c : I → ℂ` (`c = Jphase(x)·conj Jphase(y)`, a unit; `|c|=1`),
* the mollifier transform `ŵ : T → ℂ` (`ŵ(t) = Σ_b w(b) e_p(b t)`).

The weighted signed moment is `M_w = Σ_{i ∈ I} ŵ(t i) · c i`  (this is `(★)` after collecting tuples by
defect). The diagonal is the fiber `t = 0`; the structured off-diagonal is also in that fiber. -/

variable {I T : Type*} [Fintype I] [DecidableEq T]

/-- **The weighted signed moment** `M_w = Σ_i ŵ(t i)·c i` — the mollified period after expanding
`|η_b|^{2r}` into tuple-pairs and collecting by additive defect `t` (identity `(★)`). -/
noncomputable def weightedMoment (wHat : T → ℂ) (t : I → T) (c : I → ℂ) : ℂ :=
  ∑ i, wHat (t i) * c i

/-- **(★) The mollifier couples ONLY through the defect `t`.** Two mollifiers with the same transform on the
range of `t` give the SAME weighted moment, regardless of `c`. The frequency weight is invisible except
through `t = Σx − Σy`. -/
theorem mollifier_acts_through_defect (wHat wHat' : T → ℂ) (t : I → T) (c : I → ℂ)
    (h : ∀ i, wHat (t i) = wHat' (t i)) :
    weightedMoment wHat t c = weightedMoment wHat' t c := by
  unfold weightedMoment
  exact Finset.sum_congr rfl (fun i _ => by rw [h i])

/-- **Fiber decomposition.** Splitting `I` into the `t = t₀` fiber and its complement, the weighted moment is
`ŵ(t₀)·(Σ_{t=t₀} c) + Σ_{t≠t₀} ŵ(t)·c`. On the constant-`t₀` fiber the mollifier is the single scalar
`ŵ(t₀)`. -/
theorem weightedMoment_fiber_split [DecidableEq I] (wHat : T → ℂ) (t : I → T) (c : I → ℂ) (t₀ : T) :
    weightedMoment wHat t c
      = wHat t₀ * (∑ i ∈ univ.filter (fun i => t i = t₀), c i)
        + ∑ i ∈ univ.filter (fun i => t i ≠ t₀), wHat (t i) * c i := by
  unfold weightedMoment
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => t i = t₀)]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [hi.2]

/-! ## The decisive no-go: a multiplier cannot separate two index sets on the SAME fiber

In the prize regime the diagonal `D` and the structured off-diagonal `O` BOTH lie in the fiber `t = 0`
(`_JacobiMomentIdentity`: both are on the additive relation `Σx = Σy`). We model this directly: `D, O ⊆ I`
are disjoint subsets, ALL of whose indices have `t i = t₀` (the shared fiber). On such a configuration the
mollifier acts by the single scalar `ŵ(t₀)` on BOTH `D` and `O`. -/

variable [DecidableEq I]

/-- The signed weight a mollifier puts on a subset `S` whose indices all lie in the fiber `t = t₀`. On such a
fiber the mollifier is the single scalar `ŵ(t₀)`, so the weight is `ŵ(t₀)·(Σ_{S} c)`. -/
theorem mollifier_on_fiber (wHat : T → ℂ) (t : I → T) (c : I → ℂ) (t₀ : T) (S : Finset I)
    (hS : ∀ i ∈ S, t i = t₀) :
    ∑ i ∈ S, wHat (t i) * c i = wHat t₀ * ∑ i ∈ S, c i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hS i hi]

/-- **The no-separation theorem.** Let `D` (diagonal) and `O` (structured off-diagonal) be subsets of `I`,
ALL of whose indices lie in the SAME fiber `t = t₀` (the prize regime: both on the relation `Σx = Σy`). Then
for EVERY mollifier `ŵ`, the diagonal weight and the off-diagonal weight are the SAME scalar multiple `ŵ(t₀)`
of their respective signed correlation sums:
```
   (weight on D) = ŵ(t₀)·Diag,     (weight on O) = ŵ(t₀)·Off,
   Diag := Σ_D c,   Off := Σ_O c.
```
Consequently the off-diagonal weight is `ŵ(t₀)·Off` and the diagonal weight is `ŵ(t₀)·Diag` — TIED by the
common factor `ŵ(t₀)`. There is no `ŵ` killing `Off` while preserving `Diag` unless `ŵ(t₀) = 0`, which kills
BOTH. The mollifier cannot separate them. -/
theorem multiplier_cannot_separate (wHat : T → ℂ) (t : I → T) (c : I → ℂ) (t₀ : T) (D O : Finset I)
    (hD : ∀ i ∈ D, t i = t₀) (hO : ∀ i ∈ O, t i = t₀) :
    (∑ i ∈ D, wHat (t i) * c i = wHat t₀ * ∑ i ∈ D, c i)
      ∧ (∑ i ∈ O, wHat (t i) * c i = wHat t₀ * ∑ i ∈ O, c i)
      ∧ (∀ i ∈ O, wHat (t i) = wHat t₀ ∧ ∀ j ∈ D, wHat (t i) = wHat (t j)) := by
  refine ⟨mollifier_on_fiber wHat t c t₀ D hD, mollifier_on_fiber wHat t c t₀ O hO, ?_⟩
  intro i hi
  refine ⟨by rw [hO i hi], ?_⟩
  intro j hj
  rw [hO i hi, hD j hj]

/-- **The separation is impossible unless `ŵ(t₀) = 0` (which kills the diagonal too).** Concrete form: if a
mollifier makes the off-diagonal weight vanish (`ŵ(t₀)·Off = 0`) while `Off ≠ 0`, then `ŵ(t₀) = 0`, hence the
diagonal weight `ŵ(t₀)·Diag = 0` too — the mollifier destroys the diagonal it was meant to preserve. -/
theorem killing_offdiag_kills_diag (wHat : T → ℂ) (t : I → T) (c : I → ℂ) (t₀ : T) (D O : Finset I)
    (hD : ∀ i ∈ D, t i = t₀) (hO : ∀ i ∈ O, t i = t₀)
    (Off : ℂ) (hOff : Off = ∑ i ∈ O, c i) (hOffNe : Off ≠ 0)
    (hKill : (∑ i ∈ O, wHat (t i) * c i) = 0) :
    wHat t₀ = 0 ∧ (∑ i ∈ D, wHat (t i) * c i) = 0 := by
  have hOfib : (∑ i ∈ O, wHat (t i) * c i) = wHat t₀ * Off := by
    rw [mollifier_on_fiber wHat t c t₀ O hO, hOff]
  rw [hOfib] at hKill
  have hw0 : wHat t₀ = 0 := by
    rcases mul_eq_zero.mp hKill with h | h
    · exact h
    · exact absurd h hOffNe
  refine ⟨hw0, ?_⟩
  rw [mollifier_on_fiber wHat t c t₀ D hD, hw0, zero_mul]

/-! ## Why the only escape leaves the mollifier class

The previous theorems show a frequency multiplier `ŵ(t)` is a constant `ŵ(t₀)` on the shared fiber, so it
cannot separate `D` from `O`. The ONLY way to weight `D` and `O` differently is a weight `v : I → ℂ` that
depends on the index `i` itself (the SHAPE of the tuple / its Jacobi phase `c i`), not merely on `t i`. We
record this: such a `v` is exactly a weight that resolves `c`, i.e. it can null `O` (by choosing `v i` to
align with `c i`) — but that IS the off-diagonal cancellation, not a period multiplier. -/

/-- **The escape is the open theorem, restated.** A general index-weight `v : I → ℂ` CAN null the
off-diagonal: e.g. `v i = 0` on `O` and `v i = 1` on `D` gives diagonal `Σ_D c`, off-diagonal `0`. But this `v`
is NOT of multiplier form `v i = ŵ(t i)` whenever `D` and `O` share the fiber `t₀` and `Σ_O c ≠ 0`: a
multiplier would force the `O`-weight to equal the `D`-weight (`ŵ(t₀)`), contradicting `v|_O = 0 ≠ ŵ(t₀) = v|_D`
(when `D` nonempty). So no period-mollifier realizes the separating weight; the separation IS the open
cancellation. -/
theorem separating_weight_not_a_multiplier (t : I → T) (t₀ : T) (D O : Finset I)
    (hDne : D.Nonempty) (hD : ∀ i ∈ D, t i = t₀) (hO : ∀ i ∈ O, t i = t₀) (hDO : Disjoint D O)
    (v : I → ℂ) (hvD : ∀ i ∈ D, v i = 1) (hvO : ∀ i ∈ O, v i = 0)
    (hOne : O.Nonempty) :
    ¬ ∃ wHat : T → ℂ, ∀ i ∈ D ∪ O, v i = wHat (t i) := by
  rintro ⟨wHat, hw⟩
  obtain ⟨d, hd⟩ := hDne
  obtain ⟨o, ho⟩ := hOne
  -- on D: v d = 1 = ŵ(t₀);  on O: v o = 0 = ŵ(t₀);  both fibers are t₀ ⇒ 1 = 0.
  have hwd : (1 : ℂ) = wHat t₀ := by
    have := hw d (Finset.mem_union_left _ hd)
    rw [hvD d hd, hD d hd] at this; exact this
  have hwo : (0 : ℂ) = wHat t₀ := by
    have := hw o (Finset.mem_union_right _ ho)
    rw [hvO o ho, hO o ho] at this; exact this
  rw [← hwo] at hwd
  exact one_ne_zero hwd

end ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned.mollifier_acts_through_defect
#print axioms ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned.weightedMoment_fiber_split
#print axioms ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned.mollifier_on_fiber
#print axioms ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned.multiplier_cannot_separate
#print axioms ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned.killing_offdiag_kills_diag
#print axioms ArkLib.ProximityGap.Frontier.OnsetMollifiedSigned.separating_weight_not_a_multiplier
