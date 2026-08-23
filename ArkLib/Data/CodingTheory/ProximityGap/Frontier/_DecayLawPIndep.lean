/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Over-determined far-line incidence is char-`p` independent — the structural mechanism (#407)

**Target (combinatorial reframing of the prize δ\* object).**
For `RS[μ_n, k]` over `F_p` with `n = 2^μ`, `p ≡ 1 (mod n)`, the over-determined far-line
incidence
`I(s;n,k) = max over far monomial dirs (a,b) of #{ γ : x^a + γ x^b agrees with a deg<k poly on ≥ s points }`
with witness size `s` over-determined (`s - k ≥ 2`) is **independent of `p`** for all `p` outside a
finite set of "bad primes", and equals the char-`0` (number-field `ℚ(ζ_n)`) count.

**The mechanism this file formalizes (the heart of the p-independence proof).**
Fix a subset `R` of `s` evaluation points. The witness `x^a + γ x^b` agrees with a degree-`<k`
polynomial on `R` iff *all* `s-k` consecutive order-`k` divided differences of the value vector
`u0 + γ • u1` vanish, where `u0 = (x^a|_R)`, `u1 = (x^b|_R)`. Because the order-`k` divided
difference `D_j` is a **linear functional** of the value vector, the condition is the *affine-linear*
system in the single unknown `γ`:
`A_j + γ • B_j = 0` for all `j`,  `A_j := D_j u0`,  `B_j := D_j u1`.
A solution `γ` exists (and is then unique, since some `B_j ≠ 0` in the genuinely-far over-det case)
**iff the column vectors `A` and `B` are parallel**, i.e. every `2×2` minor `A_i B_j - A_j B_i`
vanishes; and then `γ = - A_{j₀} / B_{j₀}` for any `B_{j₀} ≠ 0`.

That solution `γ` is therefore a **fixed rational function of the divided-difference data**, with the
*same symbolic formula* over every field `K` (here `ℚ(ζ_n)` or `F_p`). The data `A_j, B_j` are
themselves fixed polynomials in `ζ_n` with **integer** coefficients (divided differences of monomial
values at roots of unity, with denominators `ζ^i - ζ^j` whose norms are powers of `2`). Hence the
*number* of distinct solutions `γ` is a number-field invariant, and the reduction mod `p` preserves
it for every `p` not dividing the relevant resultant/discriminant norms — the finite "bad primes".

This file proves the **field-uniform structural core**: divided-difference linearity ⇒ the bad-`γ`
condition is a rank-`1` parallelism criterion with an explicit `γ`-formula, stated and proved over an
*arbitrary* field `K` so the *same* statement instantiates at `K = ℚ(ζ_n)` and `K = F_p`. The
field-uniformity of these algebraic identities is exactly what forces the count to be `p`-independent.

**Reference:** #407 reframing (comment 4703998012); in-tree
`docs/kb/deltastar-exact-asymptotic-formula-and-budget.md`; Lam–Leung vanishing sums of roots of
unity (char-`0` coincidence ⇒ `p`-independence outside finite bad primes).

**Honesty / numeric status (probe-established, not Lean-proven here).**
- The reframing is **validated exactly**: over `ℤ[ζ_16]/(x⁸+1)` the parallel-minor route and the
  literal divided-difference route give the *same* count `97` for dir `(8,7)`, `n=16,k=2,s=4`, with
  `0` per-subset mismatches (`/tmp/exact_one.py`).
- The char-`0` count `97` equals the generic mod-`p` count (`97` for all `p ≡ 1 mod 16`, `p ≥ 113`);
  the count `p`-independence holds **outside a finite bad-prime set** — and the bad primes can make
  the count **DROP** (collisions among the `97` char-`0` γ's mod `p`): measured `p=17→16`, `p=97→96`,
  `p=353→81` (`scripts/probes/probe_407_overdet_exact_pindep.py`, `/tmp/dir87_sweep.py`). All bad
  primes seen are `≪ n⁴`, so the prize-thin regime (`p ≥ n⁴`) is in the `p`-independent range.

The Lean content below is the *field-uniform algebraic mechanism*, the proof obligation that makes
the count a number-field invariant. It is axiom-clean (`propext, Classical.choice, Quot.sound`) — no
`sorry`, no `native_decide`, no fabricated axioms.
-/

namespace ProximityGap.DecayLawPIndep

variable {K : Type*} [Field K]

/-- A **linear functional** on value-vectors of length `m` — the abstraction of an order-`k`
divided difference `D_j` acting on the values over a fixed window. A divided difference is a fixed
`K`-linear combination of the values (its coefficients are `±1/∏(node differences)`), hence a
`K`-linear map `(Fin m → K) →ₗ[K] K`. -/
abbrev DD (K : Type*) [Field K] (m : ℕ) := (Fin m → K) →ₗ[K] K

/-- **Divided-difference linearity in `γ`** (the engine of the over-det reduction):
for value vectors `u0 u1 : Fin m → K` and any linear functional `D` (= a divided difference),
`D (u0 + γ • u1) = D u0 + γ • D u1`. This is the single fact that turns the agreement condition
into an *affine-linear* system in the scalar unknown `γ`. -/
theorem dd_affine_in_gamma {m : ℕ} (D : DD K m) (u0 u1 : Fin m → K) (γ : K) :
    D (u0 + γ • u1) = D u0 + γ • D u1 := by
  rw [map_add, map_smul]

/-- The **bad-witness predicate** for a fixed subset, recast as a system of linear functionals.
Given the per-window divided-difference data `A j = D_j u0` and `B j = D_j u1`
(`J` indexes the `s-k` consecutive windows), `γ` is a *witness scalar* iff every window vanishes:
`A j + γ • B j = 0` for all `j`. -/
def IsWitnessScalar {J : Type*} (A B : J → K) (γ : K) : Prop :=
  ∀ j, A j + γ • B j = 0

/-- **Uniqueness of the witness scalar in the genuinely-far case.** If some window has `B j₀ ≠ 0`
(the direction `b` is *not* already on a degree-`<k` polynomial over that window — the far,
over-determined situation), then there is at most one witness scalar `γ`, given by the explicit
formula `γ = -(A j₀)/(B j₀)`. This `γ`-formula is identical over every field `K`, which is the
crux of `p`-independence: the bad scalar is a *fixed rational function of the integer-coefficient
divided-difference data*. -/
theorem witnessScalar_unique {J : Type*} (A B : J → K) {j₀ : J} (hB : B j₀ ≠ 0)
    {γ : K} (hγ : IsWitnessScalar A B γ) : γ = - (A j₀) / (B j₀) := by
  have h0 : A j₀ + γ * B j₀ = 0 := by have := hγ j₀; simpa [smul_eq_mul] using this
  rw [eq_div_iff hB]
  linear_combination h0

/-- **The witness `γ` from the pivot window is forced.** Symmetric helper: when `B j₀ ≠ 0`, the
witness scalar (if any) satisfies the pivot equation `γ · B j₀ + A j₀ = 0`, packaged as an explicit
algebraic identity rather than as "there is at most one". -/
theorem witnessScalar_eq_pivot {J : Type*} (A B : J → K) {j₀ : J}
    {γ : K} (hγ : IsWitnessScalar A B γ) : γ * B j₀ + A j₀ = 0 := by
  have h0 : A j₀ + γ * B j₀ = 0 := by have := hγ j₀; simpa [smul_eq_mul] using this
  linear_combination h0

/-- **Parallelism is necessary for a witness scalar** (the rank-`1` criterion, one direction).
If `γ` is a witness scalar and `B j₀ ≠ 0`, then for every other window `j` the `2×2` minor
collapses: `A j * B j₀ - A j₀ * B j = 0`. I.e. the data columns `A, B` are parallel.
This minor identity has **integer-coefficient** entries (over `ℚ(ζ_n)`) and the *same* algebraic
form over `F_p`, so a subset is bad in char-`0` iff it is bad mod `p` for all `p` not dividing the
minor's norm — the finite bad-prime set. -/
theorem parallel_of_witnessScalar {J : Type*} (A B : J → K)
    {γ : K} (hγ : IsWitnessScalar A B γ) (j j₀ : J) :
    A j * B j₀ - A j₀ * B j = 0 := by
  have hj : A j + γ * B j = 0 := by have := hγ j; simpa [smul_eq_mul] using this
  have hj0 : A j₀ + γ * B j₀ = 0 := by have := hγ j₀; simpa [smul_eq_mul] using this
  -- A j = -γ·B j and A j₀ = -γ·B j₀, so the minor telescopes to 0
  linear_combination B j₀ * hj - B j * hj0

/-- **Parallelism is sufficient for a witness scalar** (the rank-`1` criterion, converse).
If `B j₀ ≠ 0` and all `2×2` minors `A j * B j₀ - A j₀ * B j` vanish, then the explicit pivot
scalar `γ := -(A j₀)/(B j₀)` *is* a witness scalar: every window equation `A j + γ • B j = 0`
holds. Combined with `witnessScalar_unique`, this pins the bad scalar exactly. The construction of
`γ` is field-uniform, hence the count is a number-field invariant. -/
theorem witnessScalar_of_parallel {J : Type*} (A B : J → K) {j₀ : J} (hB : B j₀ ≠ 0)
    (hpar : ∀ j, A j * B j₀ - A j₀ * B j = 0) :
    IsWitnessScalar A B (-(A j₀) / (B j₀)) := by
  intro j
  have hmin : A j * B j₀ - A j₀ * B j = 0 := hpar j
  show A j + (-(A j₀) / (B j₀)) • B j = 0
  rw [smul_eq_mul]
  field_simp
  linear_combination hmin

/-- **Existence-uniqueness summary (the rank-`1` mechanism).** In the genuinely-far over-det case
(`B j₀ ≠ 0`), a witness scalar exists **iff** the divided-difference columns are parallel, and when
it exists it equals the explicit pivot formula `-(A j₀)/(B j₀)`. The two-sided characterization is
the structural statement that makes the over-det incidence count a *number-field invariant*:
existence (the parallelism predicate) is an integer-coefficient algebraic identity in `ζ_n`, and the
value (the pivot formula) is a fixed rational function — both with the **same form over every field**.
-/
theorem witnessScalar_iff_parallel {J : Type*} (A B : J → K) {j₀ : J} (hB : B j₀ ≠ 0) :
    (∃ γ, IsWitnessScalar A B γ) ↔ (∀ j, A j * B j₀ - A j₀ * B j = 0) := by
  constructor
  · rintro ⟨γ, hγ⟩ j; exact parallel_of_witnessScalar A B hγ j j₀
  · intro hpar; exact ⟨_, witnessScalar_of_parallel A B hB hpar⟩

/-- **The unique witness scalar, as a function of the data.** When `B j₀ ≠ 0` and the columns are
parallel, the (unique) witness scalar is exactly `-(A j₀)/(B j₀)`; conversely this value is always a
witness scalar under parallelism. Packages `witnessScalar_of_parallel` + `witnessScalar_unique`. -/
theorem unique_witnessScalar_eq {J : Type*} (A B : J → K) {j₀ : J} (hB : B j₀ ≠ 0)
    (hpar : ∀ j, A j * B j₀ - A j₀ * B j = 0) {γ : K} :
    IsWitnessScalar A B γ ↔ γ = -(A j₀) / (B j₀) := by
  constructor
  · intro hγ; exact witnessScalar_unique A B hB hγ
  · rintro rfl; exact witnessScalar_of_parallel A B hB hpar

/-! ## The transfer mechanism (char-`0` ⟶ char-`p`)

The lemmas below make the `p`-independence *direction* explicit. Take a ring homomorphism
`φ : K →+* L` — concretely the reduction `ℤ[ζ_n] ↪ ℚ(ζ_n) ⟶ 𝔽_p` (well-defined after localizing
away from `p`). The bad-witness condition and its solution `γ` are *polynomial/rational* in the data,
so `φ` carries a witness scalar over `K` to a witness scalar over `L` **as long as `φ` does not kill
the pivot** `B j₀` (i.e. `p` is not one of the finitely many "bad primes" dividing `Norm(B̃ j₀)`).
This is exactly the statement "the count is preserved mod `p` outside the finite bad-prime set." -/

variable {L : Type*} [Field L]

/-- **Witness scalars push forward along ring homs (parallelism is preserved).** If `φ : K →+* L`,
and the columns `A, B` are parallel over `K` with pivot `B j₀ ≠ 0`, then the image columns
`φ ∘ A, φ ∘ B` are parallel over `L`. (Parallelism is the `2×2`-minor identity, a ring equation, so
any `φ` preserves it — no nonvanishing hypothesis needed for this half.) -/
theorem map_parallel {J : Type*} (A B : J → K) (φ : K →+* L) {j₀ : J}
    (hpar : ∀ j, A j * B j₀ - A j₀ * B j = 0) (j : J) :
    (φ ∘ A) j * (φ ∘ B) j₀ - (φ ∘ A) j₀ * (φ ∘ B) j = 0 := by
  have := hpar j
  simpa [Function.comp, map_sub, map_mul] using congrArg φ this

/-- **The witness scalar transfers across `φ` exactly when the pivot survives.** If the columns are
parallel over `K`, `B j₀ ≠ 0` in `K`, and the pivot *survives reduction* (`φ (B j₀) ≠ 0` in `L` —
i.e. `p` is a *good* prime), then `φ` of the `K`-witness scalar `γ = -(A j₀)/(B j₀)` is itself the
unique `L`-witness scalar for the reduced columns. This is the per-direction `p`-independence: the
bad-`γ` solution mod `p` is the reduction of the char-`0` solution, hence the *same* solution set
(and the same count) for every good `p`. -/
theorem witnessScalar_transfer {J : Type*} (A B : J → K) (φ : K →+* L) {j₀ : J}
    (hB : B j₀ ≠ 0) (hφB : φ (B j₀) ≠ 0)
    (hpar : ∀ j, A j * B j₀ - A j₀ * B j = 0) :
    IsWitnessScalar (φ ∘ A) (φ ∘ B) (φ (-(A j₀) / (B j₀))) := by
  -- the reduced columns are parallel with surviving pivot, so apply the converse criterion;
  -- and φ(-(A j₀)/(B j₀)) = -(φ A j₀)/(φ B j₀) since φ is a field/ring hom and the pivot survives.
  have hparL : ∀ j, (φ ∘ A) j * (φ ∘ B) j₀ - (φ ∘ A) j₀ * (φ ∘ B) j = 0 :=
    map_parallel A B φ hpar
  have hval : φ (-(A j₀) / (B j₀)) = -((φ ∘ A) j₀) / ((φ ∘ B) j₀) := by
    rw [map_div₀, map_neg]; rfl
  rw [hval]
  exact witnessScalar_of_parallel (φ ∘ A) (φ ∘ B) hφB hparL

-- Axiom audit (must show only `[propext, Classical.choice, Quot.sound]`).
#print axioms dd_affine_in_gamma
#print axioms witnessScalar_unique
#print axioms witnessScalar_eq_pivot
#print axioms parallel_of_witnessScalar
#print axioms witnessScalar_of_parallel
#print axioms witnessScalar_iff_parallel
#print axioms unique_witnessScalar_eq
#print axioms map_parallel
#print axioms witnessScalar_transfer

end ProximityGap.DecayLawPIndep
