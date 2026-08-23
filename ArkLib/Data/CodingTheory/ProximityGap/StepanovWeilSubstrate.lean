/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #232 — the Stepanov→Weil construction substrate: multiplicative-character realization,
# auxiliary existence by dimension count, and the non-vanishing seed.

The open analytic core of #232 is the Weil bound `|∑_{x∈F} χ(x)ψ(f(x))| ≤ C√q` for a multiplicative
character `χ` and additive `ψ` (this would make the Round-9 twisted-sum pieces unconditional; it
recovers the **Johnson** radius). Its elementary (Stepanov) proof bounds the number of "good" rational
points by an auxiliary polynomial `Ψ` vanishing to high order. `HasseMultiplicityBridge.lean` /
`StepanovHasseInterface.lean` supply the **counting** layer (order-`M` vanishing ⟹ `|V|·M ≤ deg Ψ`,
via Hasse derivatives) and the Frobenius splitting `X^q − X = ∏_{a}(X − C a)`. This file supplies the
three remaining substrate layers the construction needs:

## 1. The multiplicative character as a polynomial value (`MultiplicativeCharacterSubstrate`)

At a rational point `a` (these are exactly the roots of `X^q − X`), the order-`m` multiplicative
character `χ_m(f(a)) = (f.eval a)^((q−1)/m)` is the *evaluation of the polynomial substrate*
`g := f^((q−1)/m)` (`substrate_eq_char_value`). It is an `m`-th root of unity
(`substrate_pow_orderChar_eq_one`) and `g.eval a = 1` **iff** `f.eval a` is a nonzero `m`-th power
(`substrate_eval_eq_one_iff_isMthPow`), via the cyclic-group core
`units_pow_eq_one_iff_isMthPow` (generalizing Mathlib's `unit_isSquare_iff` from `m = 2` to any
`m ∣ q−1`). This realizes `χ` *as a polynomial*, the substrate of the Stepanov auxiliary.

## 2. Auxiliary existence by dimension count (`AuxiliaryExistence`)

`exists_stepanov_auxiliary`: if `|V|·M < D` then there is a **nonzero** `Ψ` of degree `< D` whose
Hasse derivatives `hasseDeriv k Ψ` (`k < M`) vanish at every point of `V` — the linear-algebra half,
realized as the nontrivial kernel of the jet-evaluation map `jetEval : degreeLT F D → (V → Fin M → F)`
(finrank `D` domain, finrank `|V|·M` codomain).

## 3. The non-vanishing seed (`NonVanishingSeed`)

`stepanov_nonvanishing_seed`: a nonzero `Ψ` of `natDegree < q` does not vanish at all `q` points and
is not divisible by `X^q − X` — the Frobenius relation cannot collapse a genuinely low-degree
auxiliary. This is the *seed*; the remaining **wall** (proved nowhere, Mathlib lacks it) is that the
*specific* dimension-count `Ψ`, after Frobenius reduction, stays nonzero with degree `< q` — the
leading-term / Wronskian / `p`-th-power argument, the irreducible Stepanov non-vanishing kernel,
characterized precisely in the section docstring.

So #232's Weil core is now reduced to **exactly** that construction-specific non-vanishing: every
other layer (counting, Frobenius split, character realization, auxiliary existence, non-vanishing
seed) is machine-checked and axiom-clean. (And even the full Weil bound recovers Johnson, not the
past-Johnson `δ*` prize.)

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- Stepanov; Schmidt, *Equations over Finite Fields*; Kopparty, *The Weil bounds* (Rutgers notes);
  Bombieri (1973); Kowalski, *Exponential sums over finite fields, an elementary approach*.
-/

set_option linter.style.longLine false


open Polynomial Module

namespace ArkLib.ProximityGap.StepanovWeilSubstrate

variable {F : Type*} [Field F] [Fintype F]

local notation3 "q" => Fintype.card F

/-! ## 1. The multiplicative character realized as a polynomial value. -/

omit [Fintype F] in
/-- The Stepanov substrate `g := f^d` evaluates pointwise as the `d`-th power. -/
theorem eval_pow_eq (f : F[X]) (a : F) (d : ℕ) : (f ^ d).eval a = (f.eval a) ^ d := by
  rw [eval_pow]

/-- The substrate value at a rational point where `f ≠ 0` is an `m`-th root of unity: with
`m·d = q−1`, `((f^d).eval a)^m = 1`. -/
theorem substrate_pow_orderChar_eq_one
    {f : F[X]} {a : F} (ha : f.eval a ≠ 0) {m d : ℕ} (hmd : m * d = q - 1) :
    ((f ^ d).eval a) ^ m = 1 := by
  rw [eval_pow_eq, ← pow_mul, mul_comm d m, hmd]
  exact FiniteField.pow_card_sub_one_eq_one (f.eval a) ha

/-- The substrate value is exactly `χ_m(f(a)) = (f.eval a)^((q−1)/m)`. -/
theorem substrate_eq_char_value (f : F[X]) (a : F) {m : ℕ} (_hm : m ∣ q - 1) :
    (f ^ ((q - 1) / m)).eval a = (f.eval a) ^ ((q - 1) / m) := eval_pow_eq f a _

/-- **Cyclic-group core.** In the cyclic unit group of a finite field, with `m·d = q−1`, a unit `y`
satisfies `y^d = 1` iff it is an `m`-th power. (Generalizes `unit_isSquare_iff` from `m = 2`.) -/
theorem units_pow_eq_one_iff_isMthPow
    {y : Fˣ} {m d : ℕ} (hmd : m * d = q - 1) (hd : 0 < d) :
    y ^ d = 1 ↔ ∃ z : Fˣ, z ^ m = y := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨n, hn⟩ : y ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]; apply hg
  have hord : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units]
  constructor
  · intro h
    rw [← hn, ← pow_mul] at h
    have hdvd : (m * d) ∣ n * d := by
      rw [hmd, ← hord]; exact orderOf_dvd_of_pow_eq_one h
    have hmn : m ∣ n := (Nat.mul_dvd_mul_iff_right hd).mp hdvd
    obtain ⟨k, rfl⟩ := hmn
    refine ⟨g ^ k, ?_⟩
    rw [← hn, ← pow_mul, mul_comm k m]
  · rintro ⟨z, rfl⟩
    rw [← pow_mul, hmd]
    have : z ^ (Fintype.card Fˣ) = 1 := pow_card_eq_one
    rwa [Fintype.card_units] at this

/-- **Field-level character realization.** For `f.eval a ≠ 0` and `m·d = q−1` (`d > 0`), the substrate
value `(f^d).eval a = 1` iff `f.eval a` is a nonzero `m`-th power. -/
theorem substrate_eval_eq_one_iff_isMthPow
    {f : F[X]} {a : F} (ha : f.eval a ≠ 0) {m d : ℕ} (hmd : m * d = q - 1) (hd : 0 < d) :
    (f ^ d).eval a = 1 ↔ ∃ y : F, y ≠ 0 ∧ y ^ m = f.eval a := by
  classical
  rw [eval_pow_eq]
  set u : Fˣ := Units.mk0 (f.eval a) ha with hu
  have hval : (u : F) = f.eval a := rfl
  have hL : (f.eval a) ^ d = 1 ↔ u ^ d = 1 := by
    rw [← hval, ← Units.val_pow_eq_pow_val, ← Units.val_one (α := F), Units.val_inj]
  rw [hL, units_pow_eq_one_iff_isMthPow hmd hd]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨(z : F), Units.ne_zero z, by rw [← Units.val_pow_eq_pow_val, hz, hval]⟩
  · rintro ⟨y, hy0, hy⟩
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.val_injective
    rw [Units.val_pow_eq_pow_val]
    simpa [hval] using hy

/-! ## 2. The Stepanov auxiliary existence by dimension count. -/

/-- The jet-evaluation linear map `Ψ ↦ (fun a k => (hasseDeriv k Ψ).eval a)`. -/
noncomputable def jetEval (D : ℕ) (V : Finset F) (M : ℕ) :
    (degreeLT F D) →ₗ[F] (V → Fin M → F) :=
  LinearMap.pi (fun a : V =>
    LinearMap.pi (fun k : Fin M =>
      (Polynomial.leval (a : F)).comp ((hasseDeriv (k : ℕ)).comp (degreeLT F D).subtype)))

@[simp] theorem jetEval_apply (D : ℕ) (V : Finset F) (M : ℕ)
    (Ψ : degreeLT F D) (a : V) (k : Fin M) :
    jetEval D V M Ψ a k = (hasseDeriv (k : ℕ) (Ψ : F[X])).eval (a : F) := rfl

theorem finrank_jetEval_domain (D : ℕ) : finrank F (degreeLT F D) = D := by
  rw [Module.finrank_eq_card_basis (degreeLT.basis F D), Fintype.card_fin]

theorem finrank_jetEval_codomain (V : Finset F) (M : ℕ) :
    finrank F (V → Fin M → F) = V.card * M := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe]

/-- **Stepanov auxiliary existence (linear-algebra half).** If `|V|·M < D` then there is a nonzero
`Ψ` of degree `< D` whose Hasse derivatives `hasseDeriv k Ψ` (`k < M`) vanish at every `a ∈ V`. The
nontrivial kernel of the jet-evaluation map. -/
theorem exists_stepanov_auxiliary (D : ℕ) (V : Finset F) (M : ℕ) (h : V.card * M < D) :
    ∃ Ψ : F[X], Ψ ≠ 0 ∧ Ψ ∈ degreeLT F D ∧
      ∀ a ∈ V, ∀ k < M, (hasseDeriv k Ψ).eval a = 0 := by
  have hlt : finrank F (V → Fin M → F) < finrank F (degreeLT F D) := by
    rw [finrank_jetEval_domain, finrank_jetEval_codomain]; exact h
  have hker : LinearMap.ker (jetEval D V M) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨Ψ, hΨmem, hΨne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(Ψ : F[X]), ?_, Ψ.2, ?_⟩
  · intro hzero; exact hΨne (Subtype.ext hzero)
  · intro a ha k hk
    rw [LinearMap.mem_ker] at hΨmem
    have := congrFun (congrFun hΨmem ⟨a, ha⟩) ⟨k, hk⟩
    rwa [jetEval_apply] at this

/-! ## 3. The non-vanishing seed. -/

set_option linter.unusedSectionVars false in
/-- **Non-vanishing seed (eval form).** A nonzero `Ψ` with `natDegree < q` does not vanish at all `q`
points: the Frobenius relation `a^q = a` cannot kill a genuinely low-degree polynomial. -/
theorem exists_eval_ne_zero_of_natDegree_lt
    (Ψ : F[X]) (hΨ : Ψ ≠ 0) (hdeg : Ψ.natDegree < q) :
    ∃ a : F, Ψ.eval a ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F).val ⊆ Ψ.roots := by
    intro a _ha
    exact (Polynomial.mem_roots hΨ).mpr (h a)
  have hcard : (Finset.univ : Finset F).card ≤ Ψ.natDegree :=
    Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ] at hcard
  exact absurd (lt_of_le_of_lt hcard hdeg) (lt_irrefl _)

set_option linter.unusedSectionVars false in
/-- **No low-degree divisor.** A nonzero `Ψ` with `natDegree < q` is not divisible by `X^q − X`; the
Frobenius relation does not collapse it (reduction mod `X^q − X` is faithful on degree `< q`). -/
theorem not_X_pow_card_sub_X_dvd_of_natDegree_lt
    (Ψ : F[X]) (hΨ : Ψ ≠ 0) (hdeg : Ψ.natDegree < q) :
    ¬ (X ^ q - X : F[X]) ∣ Ψ := by
  intro hdvd
  have h := Polynomial.natDegree_le_of_dvd hdvd hΨ
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card] at h
  exact absurd h (not_le.mpr hdeg)

set_option linter.unusedSectionVars false in
/-- **Combined non-vanishing seed.** A nonzero degree-`< q` auxiliary is genuinely nonzero on `F` and
not annihilated by the Frobenius relation. The remaining wall is that the *specific* dimension-count
`Ψ`, after Frobenius reduction, stays nonzero with degree `< q` (the leading-term / Wronskian /
`p`-th-power argument — the irreducible Stepanov non-vanishing kernel; see the module docstring). -/
theorem stepanov_nonvanishing_seed
    (Ψ : F[X]) (hΨ : Ψ ≠ 0) (hdeg : Ψ.natDegree < q) :
    (∃ a : F, Ψ.eval a ≠ 0) ∧ ¬ (X ^ q - X : F[X]) ∣ Ψ :=
  ⟨exists_eval_ne_zero_of_natDegree_lt Ψ hΨ hdeg,
   not_X_pow_card_sub_X_dvd_of_natDegree_lt Ψ hΨ hdeg⟩

end ArkLib.ProximityGap.StepanovWeilSubstrate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovWeilSubstrate.substrate_eval_eq_one_iff_isMthPow
#print axioms ArkLib.ProximityGap.StepanovWeilSubstrate.units_pow_eq_one_iff_isMthPow
#print axioms ArkLib.ProximityGap.StepanovWeilSubstrate.exists_stepanov_auxiliary
#print axioms ArkLib.ProximityGap.StepanovWeilSubstrate.stepanov_nonvanishing_seed
