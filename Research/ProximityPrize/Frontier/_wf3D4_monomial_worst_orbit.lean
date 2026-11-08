/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.LinearAlgebra.Span.Basic

/-!
# wf-D4 (#444): dilation-eigenvector asymmetry — a structural heuristic for the monomial worst direction

wf-NH proved the **per-witness over-determination dichotomy** (`incidence_subsingleton_of_not_mem`):
at the binding radius a far direction `b ∉ W` forces `≤ 1` γ per witness, so the far-line incidence
`I(u₀,u₁) = #{γ : u₀+γ•u₁ explainable}` is a *p-independent combinatorial union count*.  Exhaustively
at `n=16, k=4` the **monomial** direction maximises that count (`I=89`; generic dirs `~1`; 2-term ties
only via a degenerate sub-degree-`k` term).  This file proves an `n`-uniform **eigenvector** fact that is a structural
*heuristic* (not a proof) for why the monomial is singled out:

> **The dilation `D_μ : z ↦ μz` (μ a generator of `μ_n`) is an eigenvector action on a MONOMIAL
> direction and ONLY on a monomial direction.**

What is actually proved here (all field-size-free, `n`-uniform):

1. `orbit_closed_dir_forces_monomial` / `multiterm_not_eigen`: if `f∘D_μ` is a scalar multiple of
   `f` (`f` is a dilation eigenvector) and the powers `μ^j` are pairwise distinct on `supp f`
   (e.g. `deg f < orderOf μ = n`, the prize regime), then `f` has at most one monomial.  The
   positive direction is `monomial_dilated_line`: dilating a monomial line `a + γ•X^b` gives the
   line `a∘D_μ + (γ·μ^b)•X^b` with the same direction.  This is an *eigenvector* statement only;
   it does **not** prove that eigenvector-ness is the only route to orbit closure of a radius-`r`
   bad set.

2. `badSet_subsingleton_far`: for the **exact-membership** set
   `badSet W a b = {γ | a + γ•b ∈ W}` and any far direction `b ∉ W` (monomials included), the set
   has at most one element.  This exact-membership set therefore carries **no** large orbit
   structure for any far direction.

The genuine orbit-closure statement for the two-monomial pencil lives at the **radius-`w`
agreement** level, not for the exact-membership `badSet` of this file: it is
`ActionOrbitFRI.badSet_orbit_closed` (`ArkLib/Data/CodingTheory/ProximityGap/ActionOrbitFRI.lean`),
which shows the set of `α` such that `z^a + α z^b` agrees with some degree-`< k` polynomial on at
least `w` points of `D` is closed under `α ↦ α·μ^{b−a}`.  That radius-`w` incidence is not defined
or reproved in this file.

Heuristic reading (NOT proved here): the monomial is the direction whose radius-`w` incidence set
is orbit-aligned, and non-eigenvector directions lose that alignment.  The quantitative claim that
the monomial maximises the far-line incidence is recorded only as the schematic named Props at the
end of the file, which are parametrised by an **arbitrary** functional `I : F[X] → ℕ` and are
meaningful only once `I` is instantiated with the actual radius-`r` incidence count.

**Numerical anchor (probe `probe_wf3D4_orbit_asymmetry.py`, exact, p-independent):** at the binding
`n=16,k=4` radius `r=10`, the worst monomial `a=10,b=4` has `I=89`, its radius-`r` bad-γ set is `⟨μ^{b−a}⟩`-
orbit-closed, and every non-degenerate 2-term direction has `I≤89` with NO nontrivial orbit closure.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Polynomial

namespace ProximityGap.Frontier.wf3D4

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Part 1 — the eigenvector pin at the line/incidence level -/

/-- **Monomial ⟹ the dilated line is the SAME line (reparametrised).**  For a monomial direction
`f = X^b` (and any base `a`), dilating the argument by `μ` sends the affine line `a + γ•X^b` to the
affine line `(a∘D_μ) + (γ·μ^b)•X^b` — same direction `X^b`, with `γ` reparametrised by `μ^b`.  This
is the eigenvector identity at the *line* level: the direction is preserved.  (The radius-`w`
orbit closure for the two-monomial pencil is the separate theorem
`ActionOrbitFRI.badSet_orbit_closed`; it is not derived here.) -/
theorem monomial_dilated_line (μ : F) (b : ℕ) (a : F[X]) (γ : F) :
    (a + C γ * X ^ b).comp (C μ * X)
      = a.comp (C μ * X) + C (γ * μ ^ b) * X ^ b := by
  rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
    Polynomial.X_comp, mul_pow, ← C_pow, C_mul]
  ring

/-- **Coefficient extraction of an eigenvector identity** (mirrors
`ActionOrbitGeneralF.dilation_eigen_coeff`, re-proved self-contained): if `f∘D_μ = C c * f` then for
every support exponent `j`, `μ^j = c`. -/
theorem eigen_coeff (μ c : F) (f : F[X])
    (h : f.comp (C μ * X) = C c * f) (j : ℕ) (hj : f.coeff j ≠ 0) :
    μ ^ j = c := by
  have hcoeff : (f.comp (C μ * X)).coeff j = (C c * f).coeff j := by rw [h]
  have hL : (f.comp (C μ * X)).coeff j = f.coeff j * μ ^ j := by
    rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum, Polynomial.sum_def,
      Finset.sum_eq_single j]
    · have : (C μ * X) ^ j = C (μ ^ j) * X ^ j := by rw [mul_pow, ← C_pow]
      rw [this, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl, mul_one, mul_comm]
    · intro i _ hij
      have : (C μ * X) ^ i = C (μ ^ i) * X ^ i := by rw [mul_pow, ← C_pow]
      rw [this, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by simpa [eq_comm] using hij), mul_zero]
    · intro hmem
      rw [Polynomial.mem_support_iff, not_not] at hmem
      exact absurd hmem hj
  have hR : (C c * f).coeff j = c * f.coeff j := Polynomial.coeff_C_mul f
  rw [hL, hR] at hcoeff
  exact mul_right_cancel₀ hj (by rw [mul_comm (μ ^ j)]; exact hcoeff)

/-- **THE PIN (n-uniform): only a monomial direction keeps the line in place under dilation.**

If the dilated direction `f∘D_μ` is a scalar multiple of `f` (`f` is a dilation eigenvector; this
is necessary for the *direction* of the line `a + γ•f` to be preserved by `D_μ`) and the powers
`μ^j` are pairwise distinct on `supp f` (e.g. `μ` has multiplicative order exceeding `deg f`, the
prize regime `deg f < n`), then `f` has **at most one** monomial: `f` is a monomial.

Scope: this is an eigenvector statement only.  It does not show that a non-monomial direction's
radius-`r` bad set fails to be orbit-closed by some other mechanism. -/
theorem orbit_closed_dir_forces_monomial (μ c : F) (f : F[X])
    (h : f.comp (C μ * X) = C c * f)
    (hdistinct : ∀ i ∈ f.support, ∀ j ∈ f.support, μ ^ i = μ ^ j → i = j) :
    f.support.card ≤ 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty f.support with hemp | ⟨i, hi⟩
  · rw [hemp]; simp
  · have hsub : f.support ⊆ {i} := by
      intro j hj
      have hji : μ ^ j = μ ^ i := by
        rw [eigen_coeff μ c f h j (Polynomial.mem_support_iff.mp hj),
          eigen_coeff μ c f h i (Polynomial.mem_support_iff.mp hi)]
      rw [Finset.mem_singleton]; exact hdistinct j hj i hi hji
    calc f.support.card ≤ ({i} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton i

/-- **Contrapositive, packaged for the worst-direction argument.** A genuinely multi-term direction
(`2 ≤ #supp f`) with the prize distinctness hypothesis is **never** a dilation eigenvector: there is
no scalar `c` with `f∘D_μ = c·f`, i.e. its direction is not preserved by the dilation. -/
theorem multiterm_not_eigen (μ : F) (f : F[X]) (hmulti : 2 ≤ f.support.card)
    (hdistinct : ∀ i ∈ f.support, ∀ j ∈ f.support, μ ^ i = μ ^ j → i = j) :
    ¬ ∃ c : F, f.comp (C μ * X) = C c * f := by
  rintro ⟨c, hc⟩
  have := orbit_closed_dir_forces_monomial μ c f hc hdistinct
  omega

/-! ## Part 2 — the exact-membership bad-γ set is a subsingleton for every far direction -/

/-- The **exact-membership** bad-γ set of an affine line `γ ↦ a + γ•b` against a submodule `W`:
`γ` is bad when `a + γ•b ∈ W`.  This is *not* the radius-`r` incidence set (agreement on at least
`w` points); for that see `ActionOrbitFRI.badSet_orbit_closed`. -/
def badSet {V : Type*} [AddCommGroup V] [Module F V] (W : Submodule F V) (a b : V) : Set F :=
  {γ : F | a + γ • b ∈ W}

/-- **wf-NH at the set level (re-exported):** for a far direction `b ∉ W` (monomial or not) the
exact-membership bad-γ set is a subsingleton — the per-witness `≤ 1` γ. -/
theorem badSet_subsingleton_far {V : Type*} [AddCommGroup V] [Module F V]
    {W : Submodule F V} {a b : V} (hb : b ∉ W) : (badSet W a b).Subsingleton := by
  intro γ₁ h₁ γ₂ h₂
  by_contra hne
  apply hb
  have hdiff : (γ₁ - γ₂) • b ∈ W := by
    have : (a + γ₁ • b) - (a + γ₂ • b) ∈ W := W.sub_mem h₁ h₂
    simpa [sub_smul, add_sub_add_left_eq_sub] using this
  have hunit : (γ₁ - γ₂) ≠ 0 := sub_ne_zero.mpr hne
  have := W.smul_mem (γ₁ - γ₂)⁻¹ hdiff
  rwa [smul_smul, inv_mul_cancel₀ hunit, one_smul] at this

/-! ## Part 3 — the named residual: the quantitative monomial-worst statement -/

/-- **The `n`-uniform worst-direction Prop (named open core for the binding incidence).**

The structural facts above show: (i) only a monomial direction is a dilation eigenvector
(`orbit_closed_dir_forces_monomial`); (ii) for every far direction the exact-membership bad-γ set
is a subsingleton (`badSet_subsingleton_far`, wf-NH).  The radius-`w` orbit closure for monomial
pencils is `ActionOrbitFRI.badSet_orbit_closed` (not reproved here).  What
remains *quantitatively* — verified exhaustively at `n=16,k=4` (`I_mono=89` is the strict max; the
only 2-term tie is the degenerate `1 + X^k` whose `X^0` term is sub-degree-`k`) but not yet proven
`n`-uniformly — is:

> For the over-determined binding radius `s = k+2`, over every prime `p ≡ 1 (mod n)` and every
> far direction `f`, the far-line incidence is maximised by a monomial direction.

We record it as a schematic named `Prop` (the project's modularity convention).  **Caveat:** it is
parameterised by an arbitrary functional `I : F[X] → ℕ` and arbitrary predicates `IsFar`,
`IsMonomialDir`; it states the monomial-worst claim only after `I` is instantiated with the actual
radius-`r` far-line incidence count, which this file does not define. -/
def MonomialIsWorstFarDirection
    (I : (F[X]) → ℕ) (IsFar : (F[X]) → Prop) (IsMonomialDir : (F[X]) → Prop) : Prop :=
  ∀ f : F[X], IsFar f → ∃ g : F[X], IsMonomialDir g ∧ IsFar g ∧ I f ≤ I g

/-- The 2-term case of the worst-direction statement, reduced to its proven skeleton: a far 2-term
direction is either (a) degenerate — one term is a sub-degree-`k` monomial, so the direction reduces
to a monomial pencil with a `W`-absorbed term (the only tie observed) — or (b) genuinely 2-term, in
which case it is not a dilation eigenvector (`multiterm_not_eigen`).  (Heuristically its radius-`r`
bad set then lacks the orbit alignment; that is not proved here.)
This is the *named* statement; the quantitative comparison `I(2-term) ≤ I(monomial)` for case (b) is
the open inequality (exhaustively true at `n=16`, see probe).  Same caveat as above: `I`, `IsFar`,
`IsMonomialDir` are arbitrary parameters, so the Prop is schematic until instantiated. -/
def TwoTermNotBetterThanMonomial
    (I : (F[X]) → ℕ) (IsFar : (F[X]) → Prop) (IsMonomialDir : (F[X]) → Prop) : Prop :=
  ∀ f : F[X], IsFar f → f.support.card = 2 →
    ∃ g : F[X], IsMonomialDir g ∧ IsFar g ∧ I f ≤ I g

end ProximityGap.Frontier.wf3D4

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx) -/
#print axioms ProximityGap.Frontier.wf3D4.monomial_dilated_line
#print axioms ProximityGap.Frontier.wf3D4.eigen_coeff
#print axioms ProximityGap.Frontier.wf3D4.orbit_closed_dir_forces_monomial
#print axioms ProximityGap.Frontier.wf3D4.multiterm_not_eigen
#print axioms ProximityGap.Frontier.wf3D4.badSet_subsingleton_far
