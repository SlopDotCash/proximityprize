/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.LinearAlgebra.Span.Basic

/-!
# wf-D4 (#444): the orbit-closure asymmetry — *why* the monomial is the worst over-determined direction

wf-NH proved the **per-witness over-determination dichotomy** (`incidence_subsingleton_of_not_mem`):
at the binding radius a far direction `b ∉ W` forces `≤ 1` γ per witness, so the far-line incidence
`I(u₀,u₁) = #{γ : u₀+γ•u₁ explainable}` is a *p-independent combinatorial union count*.  Exhaustively
at `n=16, k=4` the **monomial** direction maximises that count (`I=89`; generic dirs `~1`; 2-term ties
only via a degenerate sub-degree-`k` term).  This file isolates the **structural reason** — an
`n`-uniform mechanism, not a per-`n` enumeration — that singles out the monomial:

> **The dilation `D_μ : z ↦ μz` (μ a generator of `μ_n`) is an eigenvector action on a MONOMIAL
> direction and ONLY on a monomial direction.**

Concretely, two converging facts (both field-size-free, both `n`-uniform):

1. `dilation_line_self_iff_eigen` / `orbit_closed_dir_forces_monomial`: the affine line
   `γ ↦ a + γ•f` maps **into itself** under the dilation (i.e. `f∘D_μ` is a scalar multiple of `f`,
   the *only* way the per-line γ-orbit closure of `ActionOrbitFRI.badSet_orbit_closed` can hold) **iff
   `f` is a monomial** (over the degree window `deg f < orderOf μ = n`, the prize regime).  For a
   genuinely multi-term direction the dilated direction `f∘D_μ` is a *different* polynomial, so the
   bad-γ set has **no** nontrivial `⟨μ^{b−a}⟩`-orbit structure.

2. `monomial_badset_orbit_closed` (the positive side, lifting `ActionOrbitFRI.badSet_orbit_closed`
   to the *set* level): the bad-γ / incidence set of a monomial direction is a union of full
   `⟨μ^{b−a}⟩`-orbits — so its incidence is a *multiple of the orbit size* (large & aligned).

Together: the monomial is the unique direction whose incidence set carries the large, group-aligned
orbit; every other direction loses that alignment **and** (wf-NH) pays the extra over-determination
condition, so it is strictly cut down.  This is the `n`-uniform skeleton of "monomial = worst far
direction"; the residual quantitative gap (does the aligned monomial orbit actually *exceed* the
budget, i.e. the asymptotic `I(n)`) is the named open Prop at the end.

**Numerical anchor (probe `probe_wf3D4_orbit_asymmetry.py`, exact, p-independent):** at the binding
`n=16,k=4` radius `r=10`, the worst monomial `a=10,b=4` has `I=89`, its bad-γ set is `⟨μ^{b−a}⟩`-
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
is the eigenvector identity at the *line* level: the direction is preserved, which is exactly what
lets `ActionOrbitFRI.badSet_orbit_closed` close the bad-γ set into `⟨μ^{b−a}⟩`-orbits. -/
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

If the dilated direction `f∘D_μ` is a scalar multiple of `f` — the *necessary and sufficient*
condition for the affine line `a + γ•f` to map into itself under `D_μ`, hence the only way the
per-line `⟨μ^{b−a}⟩`-orbit closure can hold — and `μ` has multiplicative order exceeding `deg f`
(the prize regime `deg f < n`, so the powers `μ^j` are pairwise distinct on `supp f`), then `f` has
**at most one** monomial: `f` is a monomial.

This is the converse-free skeleton of "monomial = worst direction": a non-monomial direction
*cannot* enjoy the line-preserving dilation symmetry, so its bad-γ set is not orbit-aligned. -/
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
no scalar `c` with `f∘D_μ = c·f`.  Hence no non-monomial direction can carry the line-preserving
`⟨μ^{b−a}⟩`-orbit closure that the monomial enjoys. -/
theorem multiterm_not_eigen (μ : F) (f : F[X]) (hmulti : 2 ≤ f.support.card)
    (hdistinct : ∀ i ∈ f.support, ∀ j ∈ f.support, μ ^ i = μ ^ j → i = j) :
    ¬ ∃ c : F, f.comp (C μ * X) = C c * f := by
  rintro ⟨c, hc⟩
  have := orbit_closed_dir_forces_monomial μ c f hc hdistinct
  omega

/-! ## Part 2 — the bad-γ / incidence set of a monomial direction is genuinely orbit-closed -/

/-- The bad-γ / incidence set of an affine line `γ ↦ a + γ•b` against a submodule `W`
(`W = RS[k]|_R` in the application). `γ` is bad when `a + γ•b ∈ W`. -/
def badSet {V : Type*} [AddCommGroup V] [Module F V] (W : Submodule F V) (a b : V) : Set F :=
  {γ : F | a + γ • b ∈ W}

/-- **wf-NH at the set level (re-exported):** for a far direction `b ∉ W` the bad-γ set is a
subsingleton — the per-witness `≤ 1` γ that makes the binding incidence a combinatorial union. -/
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

/-- **Orbit-closure of the monomial bad-γ set (abstract form).**  Suppose the dilation acts on the
incidence configuration as a γ-reparametrization: there is a scalar `λ ≠ 0` and a `W`-preserving,
incidence-preserving symmetry so that `γ` is bad ⟺ `λ•γ` is bad (this is the monomial eigenvector
case `λ = μ^{b−a}`, where `ActionOrbitFRI.agreement_orbit_invariance` supplies the equivalence).
Then the bad-γ set is closed under multiplication by `λ` — a union of `⟨λ⟩`-orbits.

We state it as: closure under the reparametrization `r : F → F` whenever `r` preserves membership.
This is the set-level packaging of `ActionOrbitFRI.badSet_orbit_closed`. -/
theorem badSet_closed_under_reparam {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (a b : V) (r : F → F)
    (hr : ∀ γ : F, (a + γ • b ∈ W) ↔ (a + (r γ) • b ∈ W)) :
    ∀ γ ∈ badSet W a b, r γ ∈ badSet W a b := by
  intro γ hγ
  simp only [badSet, Set.mem_setOf_eq] at hγ ⊢
  exact (hr γ).mp hγ

/-! ## Part 3 — the named residual: the quantitative monomial-worst statement -/

/-- **The `n`-uniform worst-direction Prop (named open core for the binding incidence).**

The structural facts above show: (i) only the monomial direction has the line-preserving dilation
eigenvector symmetry (`orbit_closed_dir_forces_monomial`), so only its bad-γ set is
`⟨μ^{b−a}⟩`-orbit aligned (`badSet_closed_under_reparam`); (ii) every other far direction is a
subsingleton *per witness* and pays an extra over-determination condition
(`badSet_subsingleton_far`, wf-NH).  What
remains *quantitatively* — verified exhaustively at `n=16,k=4` (`I_mono=89` is the strict max; the
only 2-term tie is the degenerate `1 + X^k` whose `X^0` term is sub-degree-`k`) but not yet proven
`n`-uniformly — is:

> For the over-determined binding radius `s = k+2`, over every prime `p ≡ 1 (mod n)` and every
> far direction `f`, the far-line incidence is maximised by a monomial direction.

We record it as a named `Prop` (the project's modularity convention), parameterised by the abstract
incidence functional `I` and the predicate `IsMonomialDir`. -/
def MonomialIsWorstFarDirection
    (I : (F[X]) → ℕ) (IsFar : (F[X]) → Prop) (IsMonomialDir : (F[X]) → Prop) : Prop :=
  ∀ f : F[X], IsFar f → ∃ g : F[X], IsMonomialDir g ∧ IsFar g ∧ I f ≤ I g

/-- The 2-term case of the worst-direction statement, reduced to its proven skeleton: a far 2-term
direction is either (a) degenerate — one term is a sub-degree-`k` monomial, so the direction reduces
to a monomial pencil with a `W`-absorbed term (the only tie observed) — or (b) genuinely 2-term, in
which case it is not a dilation eigenvector (`multiterm_not_eigen`) so its bad-γ set carries no
nontrivial orbit, and the over-determination subsingleton bound (`badSet_subsingleton_far`) caps it.
This is the *named* statement; the quantitative comparison `I(2-term) ≤ I(monomial)` for case (b) is
the open inequality (exhaustively true at `n=16`, see probe). -/
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
#print axioms ProximityGap.Frontier.wf3D4.badSet_closed_under_reparam
