/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Finite.Basic
import ArkLib.Data.CodingTheory.ProximityGap.StepanovPointCountEngine

/-!
# The Hasse-derivative ⟺ root-multiplicity bridge (Issue #232, Stepanov route)

The Stepanov counting engine (`StepanovPointCountEngine.lean`) consumes high-order vanishing in the
form `∀ a ∈ V, M ≤ Ψ.rootMultiplicity a`. In any concrete application the vanishing is verified by
*differentiating* the auxiliary polynomial — but over a finite field `𝔽_q` of characteristic `p`,
ordinary iterated derivatives are useless once the order reaches `p` (the `p`-th derivative of `X^p`
is `0`). The correct char-`p` tool is the **Hasse (divided) derivative** `hasseDeriv k`, whose
coefficients are the *Taylor* coefficients and which never collapses.

Mathlib has the full `hasseDeriv` algebra and the full `rootMultiplicity` API, but — as of the pinned
`v4.30.0-rc2` — **no lemma connecting them**. The only multiplicity-from-derivative criterion,
`lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors`, requires `(n ! : R)` to be
a non-zero-divisor, which *fails over `𝔽_q` exactly when `n ≥ p`* — precisely the Stepanov regime.

This file supplies the missing, **characteristic-free** bridge and wires it into the engine.

## Main results (all `sorry`-free; expected axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `le_rootMultiplicity_iff_hasseDeriv` — **the keystone.** For `f ≠ 0`,
  `n ≤ f.rootMultiplicity a ↔ ∀ m < n, (hasseDeriv m f).eval a = 0`.
  No factorial invertibility: it works for every `n`, including `n ≥ p`. (A clean mathlib upstream
  candidate; generalizes verbatim to a commutative domain.)
* `rootMultiplicity_ge_of_hasseDeriv_vanish` — the `mpr` direction packaged as the engine's feeder.
* `stepanov_card_le_of_hasseDeriv` — the **fused engine entry point**: a nonzero auxiliary `Ψ` whose
  first `M` Hasse derivatives vanish at every point of `V` forces `|V| ≤ Ψ.natDegree / M`. This is
  the interface a concrete Stepanov application uses: supply `Ψ` and check Hasse-vanishing; the count
  is automatic.
* `X_pow_card_sub_X_eq_prod` — the `𝔽_q`-rational points realized as the simple root set of
  `X^q − X`, giving the engine a concrete candidate set `V = univ`.

## The proof of the keystone (characteristic-free)

The Taylor shift `taylor a` is a ring homomorphism of `F[X]` sending `X − C a ↦ X`, with inverse
`taylor (−a)`, so divisibility transfers explicitly in both directions:
`(X − C a)^n ∣ f ↔ X^n ∣ taylor a f`. By `X_pow_dvd_iff` the right side says the first `n`
coefficients of `taylor a f` vanish, and `taylor_coeff` identifies those coefficients with the
Hasse-derivative evaluations `(hasseDeriv m f).eval a`. Chaining with `le_rootMultiplicity_iff`
gives the result with **no** use of `n !`.

## Honest scope

This is infrastructure + cartography for issue #232 (`advancesOpenCore = false`). It does **not**
construct the Stepanov auxiliary polynomial (the hard mathematical content), prove any
`√q`-strength character-sum / Weil bound, or close/advance the open prize core. It removes the last
glue between Mathlib's Hasse algebra and the proven Stepanov counting inequality.
-/

open Polynomial BigOperators Finset

namespace ArkLib.CodingTheory.HasseMultiplicityBridge

/-! ## 1. The characteristic-free Hasse-derivative ⟺ root-multiplicity bridge. -/

section Bridge

variable {F : Type*} [Field F]

/-- The Taylor shift sends `X − C a` to `X`: `taylor a (X − C a) = X`. -/
private lemma taylor_X_sub_C_self (a : F) : taylor a (X - C a) = X := by
  rw [map_sub, taylor_X, taylor_C, add_sub_cancel_right]

/-- The inverse Taylor shift sends `X` to `X − C a`: `taylor (−a) X = X − C a`. -/
private lemma taylor_neg_X_eq (a : F) : taylor (-a) X = X - C a := by
  rw [taylor_X, C_neg, ← sub_eq_add_neg]

/-- **The keystone: Hasse-derivative criterion for root multiplicity, characteristic-free.**
For a nonzero polynomial `f` over a field and a point `a`,

  `n ≤ f.rootMultiplicity a  ↔  ∀ m < n, (hasseDeriv m f).eval a = 0`.

Unlike the factorial-based criterion `…_of_mem_nonZeroDivisors`, this places **no** invertibility
hypothesis on `n !`, so it is valid in characteristic `p` for every `n` (in particular `n ≥ p`),
which is exactly the regime the Stepanov auxiliary-polynomial method operates in. -/
theorem le_rootMultiplicity_iff_hasseDeriv {f : F[X]} (hf : f ≠ 0) (a : F) (n : ℕ) :
    n ≤ f.rootMultiplicity a ↔ ∀ m < n, (hasseDeriv m f).eval a = 0 := by
  rw [le_rootMultiplicity_iff hf]
  -- `taylor a` is a ring hom with `taylor a (X − C a) = X` and inverse `taylor (−a)`, so
  -- divisibility transfers explicitly: `(X − C a)^n ∣ f ↔ X^n ∣ taylor a f`.
  have key : (X - C a) ^ n ∣ f ↔ X ^ n ∣ taylor a f := by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨taylor a g, by rw [taylor_mul, taylor_pow, taylor_X_sub_C_self]⟩
    · rintro ⟨h, hh⟩
      refine ⟨taylor (-a) h, ?_⟩
      have hf2 : taylor (-a) (taylor a f) = f := by
        rw [taylor_taylor, neg_add_cancel, taylor_zero]
      rw [← hf2, hh, taylor_mul, taylor_pow, taylor_neg_X_eq]
  rw [key, X_pow_dvd_iff]
  -- the first `n` coefficients of `taylor a f` are the Hasse-derivative evaluations of `f` at `a`.
  simp only [taylor_coeff]

/-- The `mpr` direction of the keystone, packaged as the Stepanov engine's vanishing feeder:
order-`M` Hasse vanishing at `a` certifies multiplicity `≥ M`. -/
theorem rootMultiplicity_ge_of_hasseDeriv_vanish {Ψ : F[X]} (hΨ : Ψ ≠ 0) (a : F) (M : ℕ)
    (hvan : ∀ j < M, (hasseDeriv j Ψ).eval a = 0) : M ≤ Ψ.rootMultiplicity a :=
  (le_rootMultiplicity_iff_hasseDeriv hΨ a M).mpr hvan

end Bridge

/-! ## 2. Fused Stepanov entry point: Hasse vanishing ⟹ few points. -/

section Engine

variable {F : Type*} [Field F] [DecidableEq F]

open ArkLib.CodingTheory.Round6Stepanov

/-- **The Stepanov method, taking pure Hasse-vanishing hypotheses.** If `Ψ ≠ 0`, `0 < M`, and the
first `M` Hasse derivatives of `Ψ` all vanish at every point of a finite candidate set `V ⊆ F`,
then `|V| ≤ Ψ.natDegree / M`. This is the keystone bridge composed with the proven counting engine
`stepanov_card_le_of_mult`: a concrete application only needs to exhibit `Ψ` and check the Hasse
derivatives — the count is then automatic. -/
theorem stepanov_card_le_of_hasseDeriv {Ψ : F[X]} (hΨ : Ψ ≠ 0) (V : Finset F) {M : ℕ} (hM : 0 < M)
    (hvan : ∀ a ∈ V, ∀ j < M, (hasseDeriv j Ψ).eval a = 0) :
    V.card ≤ Ψ.natDegree / M :=
  stepanov_card_le_of_mult hΨ V hM
    (fun a ha => rootMultiplicity_ge_of_hasseDeriv_vanish hΨ a M (hvan a ha))

end Engine

/-! ## 3. The `𝔽_q`-rational points as the engine's candidate set. -/

section FinitePoints

variable {F : Type*} [Field F] [Fintype F]

/-- **The `𝔽_q`-points are exactly the simple roots of `X^q − X`.** Over a finite field `F` with
`q = |F|`, `X^q − X = ∏_{a : F} (X − C a)`. This realizes the full rational-point set `V = univ` as
the (squarefree) root set the Stepanov engine counts. -/
theorem X_pow_card_sub_X_eq_prod :
    (X ^ Fintype.card F - X : F[X]) = ∏ a : F, (X - C a) := by
  classical
  have hcard : (1 : ℕ) < Fintype.card F := Fintype.one_lt_card
  have hmonic : (X ^ Fintype.card F - X : F[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hcard)
  have hroots : (X ^ Fintype.card F - X : F[X]).roots = (Finset.univ : Finset F).val :=
    FiniteField.roots_X_pow_card_sub_X F
  have hdeg : (X ^ Fintype.card F - X : F[X]).natDegree = Fintype.card F :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F hcard
  have hcardeq : Multiset.card (X ^ Fintype.card F - X : F[X]).roots
      = (X ^ Fintype.card F - X : F[X]).natDegree := by
    rw [hroots, hdeg]; simp
  -- a monic polynomial whose root multiset exhausts its degree is the product over its roots.
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcardeq
  rw [hroots] at hprod
  rw [Finset.prod_eq_multiset_prod]
  exact hprod.symm

end FinitePoints

/-! ## The Hasse-derivative power rule — multiplicity of `g^r`-weighted auxiliaries.

A Stepanov auxiliary that carries a factor `g^r` vanishes to *root multiplicity* `≥ r` at every
root of `g`, in **every** characteristic. The mechanism is the char-free power rule
`g^(r−k) ∣ E^k(g^r)` (Hanson, *Stepanov's Method for Hyperelliptic Curves*, Lemma 2): a `g^r`
prefactor survives `k` Hasse derivatives as `g^(r−k)`. This is the missing multiplicity input the
point-count engine consumes; it makes the order-`r` vanishing of a `g^r`-weighted auxiliary
automatic instead of a per-construction computation. -/
section PowerRule

/-- **Hasse-derivative power rule (divisibility form).** `g^(r−k) ∣ E^k(g^r)` — taking `k` Hasse
derivatives of `g^r` leaves a factor `g^(r−k)`. Characteristic-free. -/
theorem hasseDeriv_pow_dvd {R : Type*} [CommSemiring R] (g : R[X]) (r k : ℕ) :
    g ^ (r - k) ∣ hasseDeriv k (g ^ r) := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', hasseDeriv_mul]
    apply Finset.dvd_sum
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨i, j⟩ := ij
    simp only at hij ⊢
    rcases Nat.eq_zero_or_pos i with hi0 | hi1
    · subst hi0
      have hjk : j = k := by omega
      subst hjk
      rw [hasseDeriv_zero, LinearMap.id_coe, id_eq]
      calc g ^ (r + 1 - j) ∣ g ^ (1 + (r - j)) := pow_dvd_pow g (by omega)
        _ = g * g ^ (r - j) := by rw [pow_add, pow_one]
        _ ∣ g * hasseDeriv j (g ^ r) := mul_dvd_mul_left g (ih j)
    · have : g ^ (r + 1 - k) ∣ g ^ (r - j) := pow_dvd_pow g (by omega)
      exact this.trans ((ih j).trans (Dvd.dvd.mul_left (dvd_refl _) _))

/-- **Power rule with a prefactor.** `g^(r−k) ∣ E^k(f·g^r)`. -/
theorem hasseDeriv_mul_pow_dvd {R : Type*} [CommSemiring R] (f g : R[X]) (r k : ℕ) :
    g ^ (r - k) ∣ hasseDeriv k (f * g ^ r) := by
  rw [hasseDeriv_mul]
  apply Finset.dvd_sum
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨i, j⟩ := ij
  simp only at hij ⊢
  have : g ^ (r - k) ∣ g ^ (r - j) := pow_dvd_pow g (by omega)
  exact (this.trans (hasseDeriv_pow_dvd g r j)).mul_left _

/-- **Multiplicity from the power rule.** If `a` is a root of `g`, then `f·g^r` vanishes to
Hasse-order `≥ r` at `a` (every `E^k(f·g^r)`, `k < r`, vanishes at `a`) — hence, by
`rootMultiplicity_ge_of_hasseDeriv_vanish`, to root multiplicity `≥ r` when `f·g^r ≠ 0`. -/
theorem hasseDeriv_eval_eq_zero_of_root {F : Type*} [Field F]
    (f g : F[X]) (a : F) (ha : g.eval a = 0) (r k : ℕ) (hk : k < r) :
    (hasseDeriv k (f * g ^ r)).eval a = 0 := by
  obtain ⟨h, hh⟩ := hasseDeriv_mul_pow_dvd f g r k
  rw [hh, eval_mul, eval_pow, ha, zero_pow (by omega), zero_mul]

/-- **Root multiplicity from the power rule (the engine feeder).** A root `a` of `g` is a root of
`f·g^r` of multiplicity `≥ r` — in every characteristic. Directly supplies the
`∀ a ∈ V, M ≤ Ψ.rootMultiplicity a` hypothesis of `stepanov_card_mul_mult_le_natDegree` for a
`g^r`-weighted Stepanov auxiliary. -/
theorem rootMultiplicity_mul_pow_ge {F : Type*} [Field F]
    (f g : F[X]) (a : F) (ha : g.eval a = 0) (r : ℕ) (hne : f * g ^ r ≠ 0) :
    r ≤ (f * g ^ r).rootMultiplicity a :=
  rootMultiplicity_ge_of_hasseDeriv_vanish hne a r
    (fun k hk => hasseDeriv_eval_eq_zero_of_root f g a ha r k hk)

end PowerRule

end ArkLib.CodingTheory.HasseMultiplicityBridge

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.CodingTheory.HasseMultiplicityBridge
#print axioms le_rootMultiplicity_iff_hasseDeriv
#print axioms rootMultiplicity_ge_of_hasseDeriv_vanish
#print axioms stepanov_card_le_of_hasseDeriv
#print axioms X_pow_card_sub_X_eq_prod
#print axioms hasseDeriv_pow_dvd
#print axioms hasseDeriv_mul_pow_dvd
#print axioms hasseDeriv_eval_eq_zero_of_root
#print axioms rootMultiplicity_mul_pow_ge
end AxiomAudit
