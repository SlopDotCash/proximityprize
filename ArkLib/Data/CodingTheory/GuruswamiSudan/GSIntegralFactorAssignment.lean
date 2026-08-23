/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorAssignment

/-!
# The integral factor assignment — no bad set

`GSFactorAssignment.lean` assigned each per-`z` decoded factor to a `K = F(Z)`-level
irreducible factor, at the cost of a bad set `{z : (cn·d)(z) = 0}` of *uncontrolled* size
(the denominators come from the nonconstructive integer representative). This file removes
that cost by factoring **directly in the UFD `F[Z][X][Y]`**:

* `isUnit_triple_iff_exists` (`unit_shape`): units of `F[Z][X][Y]` are the nonzero
  *field* constants `C(C(C c))` — three applications of `Polynomial.isUnit_iff` — and such
  constants are **immune to `Z`-specialization** (`σ_z (C(C(C c))) = C(C c) ≠ 0` for every
  `z`);
* **`exists_integral_factor_assignment`** — for *every* `z` with `Q₀|_{Z:=z} ≠ 0` (no
  other exclusions!), every decoded linear factor `(Y − C q) ∣ Q₀|_{Z:=z}` divides the
  specialization of some irreducible factor of `Q₀` in `F[Z][X][Y]`.

Consequently the only degenerate scalars left in the whole chain are
`{z : Q₀|_{Z:=z} = 0}` — contained in the roots of any single nonzero `F[Z]`-coefficient
of `Q₀`, so of size `≤ deg_Z Q₀`. Unit (2) of the #302 ledger is thereby reduced to
exactly one statement: *a `Z`-degree budget for the GS interpolant* (the BCIKS20
Claim 5.4 `D_{YZ} ≤ (ℓ³/6)ρn` graded dimension count).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- Units of `F[Z][X][Y]` are nonzero field constants `C(C(C c))`. -/
lemma unit_shape {w : (F[X])[X][Y]} (hw : IsUnit w) :
    ∃ c : F, c ≠ 0 ∧ w = Polynomial.C (Polynomial.C (Polynomial.C c)) := by
  obtain ⟨v, hvu, hv⟩ := Polynomial.isUnit_iff.mp hw
  obtain ⟨v', hv'u, hv'⟩ := Polynomial.isUnit_iff.mp hvu
  obtain ⟨c, hcu, hc⟩ := Polynomial.isUnit_iff.mp hv'u
  exact ⟨c, hcu.ne_zero, by rw [← hv, ← hv', ← hc]⟩

/-- **The integral factor assignment (no bad set).** For every `z` with
`Q₀|_{Z:=z} ≠ 0`, every decoded linear factor of the specialized interpolant divides the
specialization of some irreducible factor of `Q₀` in the UFD `F[Z][X][Y]`: the UFD unit is
a field constant, immune to specialization, and the prime `Y − C q` routes through the
factor product. -/
theorem exists_integral_factor_assignment
    {Q₀ : (F[X])[X][Y]} (hQ₀ : Q₀ ≠ 0) (z : F)
    (q : F[X])
    (hq : (Polynomial.X - Polynomial.C q) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    ∃ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
      (Polynomial.X - Polynomial.C q) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  classical
  set σ : Polynomial (Polynomial (Polynomial F)) →+* Polynomial (Polynomial F) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z)) with hσ
  have hσapp : ∀ p : (F[X])[X][Y],
      σ p = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := fun _ => rfl
  -- UFD factorization with field-constant unit
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod (a := Q₀) hQ₀
  obtain ⟨c, hc0, hc⟩ := unit_shape u.isUnit
  -- specialize the factorization: the unit survives every specialization
  have hQz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) =
      (∏ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
        (σ R) ^ ((UniqueFactorizationMonoid.factors Q₀).count R)) *
      Polynomial.C (Polynomial.C c) := by
    have hQ : (UniqueFactorizationMonoid.factors Q₀).prod *
        Polynomial.C (Polynomial.C (Polynomial.C c)) = Q₀ := by
      rw [← hc]; exact hu
    calc Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))
        = σ Q₀ := rfl
      _ = σ ((UniqueFactorizationMonoid.factors Q₀).prod *
            Polynomial.C (Polynomial.C (Polynomial.C c))) := by rw [hQ]
      _ = σ ((UniqueFactorizationMonoid.factors Q₀).prod) *
            σ (Polynomial.C (Polynomial.C (Polynomial.C c))) :=
          map_mul σ _ _
      _ = (∏ R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset,
            (σ R) ^ ((UniqueFactorizationMonoid.factors Q₀).count R)) *
          Polynomial.C (Polynomial.C c) := by
          congr 1
          · rw [Finset.prod_multiset_count (UniqueFactorizationMonoid.factors Q₀),
              map_prod σ (fun R => R ^ ((UniqueFactorizationMonoid.factors Q₀).count R))
                (UniqueFactorizationMonoid.factors Q₀).toFinset]
            exact Finset.prod_congr rfl fun R _ => map_pow σ R _
          · rw [hσ, Polynomial.coe_mapRingHom, Polynomial.map_C,
              Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom,
              Polynomial.eval_C]
  -- the prime chase
  have hprime : Prime (Polynomial.X - Polynomial.C q : F[X][Y]) :=
    Polynomial.prime_X_sub_C q
  rw [hQz] at hq
  rcases hprime.dvd_or_dvd hq with hP | hC
  · obtain ⟨R, hRmem, hdvd⟩ := hprime.exists_mem_finset_dvd hP
    exact ⟨R, hRmem, by
      have := hprime.dvd_of_dvd_pow hdvd
      rwa [hσapp] at this⟩
  · exact absurd hC (not_linear_dvd_C (by simpa using hc0))

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.unit_shape
#print axioms GuruswamiSudan.OverRatFunc.exists_integral_factor_assignment
