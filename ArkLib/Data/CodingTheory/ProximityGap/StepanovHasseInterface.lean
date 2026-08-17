/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovPointCountEngine
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Issue #232 — the LINEAR (Hasse-derivative) entry point for univariate Stepanov constructions.

`StepanovPointCountEngine.lean` provides the **counting half** of Stepanov's method: a nonzero
auxiliary `Ψ` vanishing to *root multiplicity* `≥ M` at every point of a candidate set `V` gives
`|V|·M ≤ Ψ.natDegree`. A concrete Stepanov construction, however, produces its auxiliary by a
**linear-algebra dimension count** (`MultiplicityInterpolation.exists_ne_zero_map_eq_zero`: a linear
map into a lower-dimensional space has a nonzero kernel element), and the natural vanishing conditions
that count produces are the **Hasse-derivative** equations `(hasseDeriv k Ψ).eval a = 0` for `k < M` —
*not* a root-multiplicity hypothesis directly. (In characteristic `p`, iterated ordinary derivatives
miss the order of vanishing; the Hasse derivative is the correct char-`p`-safe notion.)

This file supplies the missing bridge and the resulting clean interface:

* `rootMultiplicity_ge_of_hasseDeriv_eval_eq_zero` — if `Ψ ≠ 0` and `(hasseDeriv k Ψ).eval a = 0` for
  all `k < M`, then `M ≤ Ψ.rootMultiplicity a` (via `taylor_coeff` + `X_pow_dvd_iff` +
  `le_rootMultiplicity_iff`, transported through the `taylorEquiv` algebra equivalence).
* `stepanov_card_mul_lt_of_hasse` — the **entry point**: a nonzero `Ψ` of `natDegree < D` whose Hasse
  derivatives of every order `k < M` vanish at every point of `V` forces `|V|·M < D`.

So a univariate Stepanov application now factors cleanly as: (1) build the linear map encoding
"vanish to order `M` at the structured points" (`hasseDeriv`-eval conditions); (2) dimension-count a
nonzero `Ψ` of bounded degree in its kernel; (3) the **non-vanishing** of that `Ψ` (the genuine
structural crux); then this interface delivers the point bound automatically.

## Scope / honest status

This is reusable Stepanov **scaffolding**, not the Weil bound. Toward issue #232 the target is the
Weil bound `|∑_{x} χ(x)ψ(f(x))| ≤ C√q` (which would make the Round-9 twisted-sum pieces
unconditional). Its univariate Stepanov proof plugs into this interface with the auxiliary
`Ψ(x) = ∑_{i,j} c_{ij} x^i f(x)^{j(q−1)/m}` (incorporating the multiplicative character via the
polynomial `f(x)^{(q−1)/m}`, whose value is `χ(f(x))` at the rational points) — the remaining work is
that auxiliary's construction and the **non-vanishing argument** (a leading/lowest-term or
`p`-th-power-structure argument), the genuine kernel Mathlib lacks. Note also that the Weil bound
recovers the **Johnson** radius (`√ρ`); pinning `δ*` strictly past Johnson is separately open.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
- Stepanov; Schmidt, *Equations over Finite Fields: An Elementary Approach*.
-/

set_option linter.style.longLine false


open Polynomial

namespace ArkLib.ProximityGap.StepanovHasseInterface

variable {F : Type*} [Field F]

/-- **Order of vanishing from Hasse derivatives (char-`p`-safe).** If `Ψ ≠ 0` and every Hasse
derivative `hasseDeriv k Ψ` of order `k < M` vanishes at `a`, then `a` is a root of `Ψ` of
multiplicity at least `M`. Unlike iterated ordinary derivatives, Hasse derivatives detect the order
of vanishing in every characteristic. -/
theorem rootMultiplicity_ge_of_hasseDeriv_eval_eq_zero
    {Ψ : F[X]} {a : F} {M : ℕ} (hΨ : Ψ ≠ 0)
    (h : ∀ k < M, (hasseDeriv k Ψ).eval a = 0) :
    M ≤ Ψ.rootMultiplicity a := by
  rw [le_rootMultiplicity_iff hΨ]
  have hdvd : (X : F[X]) ^ M ∣ taylor a Ψ := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [taylor_coeff]
    exact h d hd
  have key : taylor (-a) ((X : F[X]) ^ M) ∣ taylor (-a) (taylor a Ψ) :=
    (taylorEquiv (-a)).toAlgHom.toRingHom.map_dvd hdvd
  rw [taylor_taylor, neg_add_cancel, taylor_zero] at key
  rw [taylor_pow, taylor_X] at key
  rwa [map_neg, ← sub_eq_add_neg] at key

/-- **The Stepanov interface from Hasse-derivative linear conditions.** If there is a nonzero
auxiliary `Ψ` of degree `< D` whose Hasse derivatives of every order `k < M` vanish at every point of
the candidate set `V`, then `|V|·M < D`. This is the exact entry point a univariate Stepanov
construction plugs into: the only remaining work is to *produce* such a `Ψ` (dimension count + the
structural non-vanishing); the point-count conclusion is then automatic. -/
theorem stepanov_card_mul_lt_of_hasse (V : Finset F) {M D : ℕ}
    (hex : ∃ Ψ : F[X], Ψ ≠ 0 ∧ Ψ.natDegree < D ∧
      ∀ a ∈ V, ∀ k < M, (hasseDeriv k Ψ).eval a = 0) :
    V.card * M < D := by
  classical
  obtain ⟨Ψ, hΨ, hdeg, hvanish⟩ := hex
  have hmult : ∀ a ∈ V, M ≤ Ψ.rootMultiplicity a := fun a ha =>
    rootMultiplicity_ge_of_hasseDeriv_eval_eq_zero hΨ (hvanish a ha)
  exact lt_of_le_of_lt
    (ArkLib.CodingTheory.Round6Stepanov.stepanov_card_mul_mult_le_natDegree hΨ V M hmult) hdeg

/-- **Divided form.** With `0 < M`, the candidate set has `|V| ≤ (D−1)/M`. -/
theorem stepanov_card_le_of_hasse (V : Finset F) {M D : ℕ} (hM : 0 < M)
    (hex : ∃ Ψ : F[X], Ψ ≠ 0 ∧ Ψ.natDegree < D ∧
      ∀ a ∈ V, ∀ k < M, (hasseDeriv k Ψ).eval a = 0) :
    V.card ≤ (D - 1) / M := by
  have h := stepanov_card_mul_lt_of_hasse V hex
  rw [Nat.le_div_iff_mul_le hM]
  omega

end ArkLib.ProximityGap.StepanovHasseInterface

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovHasseInterface.rootMultiplicity_ge_of_hasseDeriv_eval_eq_zero
#print axioms ArkLib.ProximityGap.StepanovHasseInterface.stepanov_card_mul_lt_of_hasse
#print axioms ArkLib.ProximityGap.StepanovHasseInterface.stepanov_card_le_of_hasse
