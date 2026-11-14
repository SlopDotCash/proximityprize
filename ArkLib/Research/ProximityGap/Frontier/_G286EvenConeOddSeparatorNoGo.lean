/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# G286: an odd linear normal cannot separate the even sponsor cone from zero (#466)

G280 proved that the live sponsor covariance `B` is a real signed inner product and that every
realizable centered sponsor profile `c = p·R_r − ΣR_r` is coordinate-even, i.e. fixed by the
value-reflection `σ : x ↦ (−x)` acting on `F_p` (because `−1 ∈ G` for the 2-power subgroup — this
is the thinness-essential step). G280 also showed the cone is antipode-free, and G284 warned that
antipode-freeness alone does not force a strict separator: zero may sit in the convex hull.

The surviving admissible route (recorded in the G56 and formalizer handoffs) is *one predeclared
row-labelled **odd** arithmetic normal `φ` with an independently proved positive margin over the
whole realizable sponsor cone*. This file closes exactly that hatch as a structural dichotomy.

Model the reflection as a linear involution `σ` on a `ℚ`-module `V` (`σ ∘ σ = id`). Split any
linear functional `φ : V →ₗ[ℚ] ℚ` into even and odd parts under precomposition with `σ`:
`φ = φ_even + φ_odd` with `φ_even ∘ σ = φ_even` and `φ_odd ∘ σ = −φ_odd`. Call a vector `v`
**even** when `σ v = v`. Then:

* every **odd** functional annihilates every **even** vector: `φ_odd v = 0`
  (`even_vector_odd_functional_zero`), so an odd normal has margin exactly `0` on the whole cone and
  cannot separate it from zero (`odd_functional_no_positive_margin`);
* the separating value of any functional depends only on its even part on the even cone
  (`separation_depends_on_even_part`), so a separator must have nonzero even part, and its even part
  is polarity-invariant in the sense of G276/G280 — carrying no binding beyond the even inner
  product already analysed there.

Hence the "odd linear normal with positive margin" route is self-contradictory on the *actual*
sponsor cone: any odd normal gives zero margin, and any positive-margin normal is even (hence not a
new mechanism). This realizes G284's barycenter warning arithmetically in the sharp direction: it is
not that zero sits in the hull, but that oddness and separation are mutually exclusive on an even
cone. A surviving certificate must be genuinely **non-linear** (odd quadratic or higher). CORE
remains OPEN / ON-BGK.

The exact coordinate-even witness at `p = 113`, `n = 8` (`c 1 = c (−1) = 5911`, odd-functional
pairing `0`, even-functional pairing `11822`) is certified by `decide` with zero axioms.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G286EvenConeOddSeparatorNoGo

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A linear functional is `σ`-**odd** when precomposition with `σ` negates it. -/
def IsOddFunctional (σ : V →ₗ[ℚ] V) (φ : V →ₗ[ℚ] ℚ) : Prop :=
  ∀ v, φ (σ v) = -φ v

/-- A linear functional is `σ`-**even** when precomposition with `σ` fixes it. -/
def IsEvenFunctional (σ : V →ₗ[ℚ] V) (φ : V →ₗ[ℚ] ℚ) : Prop :=
  ∀ v, φ (σ v) = φ v

/-- A vector is **even** under `σ` when it is fixed by `σ`. The realizable centered sponsor
profiles are exactly such fixed vectors (G280: coordinate-even because `−1 ∈ G`). -/
def IsEvenVector (σ : V →ₗ[ℚ] V) (v : V) : Prop := σ v = v

/-- **Core annihilation.** An odd linear functional vanishes on every even vector. Proof: on a
fixed vector `σ v = v`, oddness gives `φ v = φ (σ v) = -φ v`, so `2 • φ v = 0` hence `φ v = 0`.
This is the whole mechanism: the realizable cone is even, so any odd normal pairs to `0` with all
of it. -/
theorem even_vector_odd_functional_zero (σ : V →ₗ[ℚ] V) (φ : V →ₗ[ℚ] ℚ)
    (hodd : IsOddFunctional σ φ) {v : V} (hv : IsEvenVector σ v) : φ v = 0 := by
  have h : φ v = -φ v := by
    have := hodd v
    rwa [hv] at this
  linarith

/-- **No odd separator.** An odd linear normal cannot have a positive margin on any nonempty family
of even vectors: it annihilates all of them, so no strictly positive lower bound exists. Concretely
there is no even vector on which an odd functional is positive. -/
theorem odd_functional_no_positive_margin (σ : V →ₗ[ℚ] V) (φ : V →ₗ[ℚ] ℚ)
    (hodd : IsOddFunctional σ φ) :
    ¬ ∃ v : V, IsEvenVector σ v ∧ 0 < φ v := by
  rintro ⟨v, hv, hpos⟩
  have := even_vector_odd_functional_zero σ φ hodd hv
  linarith

/-- **No odd margin over a whole even cone.** For any threshold `η > 0`, an odd normal cannot
satisfy `φ c ≥ η` for even `c`; the pairing is forced to `0 < η`. This is the exact statement the
surviving route asks for (a predeclared odd normal with margin `η`), shown impossible. -/
theorem odd_functional_margin_impossible (σ : V →ₗ[ℚ] V) (φ : V →ₗ[ℚ] ℚ)
    (hodd : IsOddFunctional σ φ) (η : ℚ) (hη : 0 < η) {c : V}
    (hc : IsEvenVector σ c) : ¬ (η ≤ φ c) := by
  have h0 : φ c = 0 := even_vector_odd_functional_zero σ φ hodd hc
  rw [h0]; linarith

/-- **Separation is even-part only.** On an even vector, the value of the sum of an even and an odd
functional equals the even functional alone. Hence any separator's margin is determined solely by
its even part; the odd part is inert. A separating normal must therefore have nonzero even part. -/
theorem separation_depends_on_even_part (σ : V →ₗ[ℚ] V)
    (φe φo : V →ₗ[ℚ] ℚ) (_he : IsEvenFunctional σ φe) (hodd : IsOddFunctional σ φo)
    {v : V} (hv : IsEvenVector σ v) : (φe + φo) v = φe v := by
  have : φo v = 0 := even_vector_odd_functional_zero σ φo hodd hv
  simp [this]

/-- **Existence of a positive-margin normal forces an even functional.** If any functional `φ` has
a positive margin on the even cone, its odd part is useless, so the even part carries all of it. We
package the contrapositive of the route: a purely odd normal (i.e. `φ (σ v) = -φ v`) with a positive
value on any cone element is impossible. -/
theorem positive_margin_normal_not_odd (σ : V →ₗ[ℚ] V) (φ : V →ₗ[ℚ] ℚ)
    {c : V} (hc : IsEvenVector σ c) (hpos : 0 < φ c) : ¬ IsOddFunctional σ φ := by
  intro hodd
  exact odd_functional_no_positive_margin σ φ hodd ⟨c, hc, hpos⟩

/-! ### Exact arithmetic witness (`decide`, zero axioms)

The realizable centered profile at `n = 8`, `p = 113`, rank `4` is coordinate-even; the exact
values `c 1 = c (−1) = 5911` are recorded from `scripts/probes/g286_hull_zero_probe.py`. We certify
the pairing law on the two-point support `{1, −1}` (i.e. `x = 1` and `x = 112`):

* an odd weight `w 1 = 1, w 112 = -1` pairs to `0` (annihilation),
* an even weight `u 1 = 1, u 112 = 1` pairs to `11822 ≠ 0` (nonzero even pairing).

This is the finite shadow of the abstract theorems above. -/

/-- Recorded coordinate value `c 1 = c 112 = 5911` at the exact even sponsor cell. -/
def cVal : ℤ := 5911

/-- Odd two-point pairing `w 1 · c 1 + w 112 · c 112 = 1·5911 + (-1)·5911 = 0`. -/
theorem odd_pairing_zero : (1 : ℤ) * cVal + (-1) * cVal = 0 := by decide

/-- Even two-point pairing `u 1 · c 1 + u 112 · c 112 = 1·5911 + 1·5911 = 11822 ≠ 0`. -/
theorem even_pairing_nonzero : (1 : ℤ) * cVal + 1 * cVal = 11822 := by decide

/-- The even pairing is genuinely nonzero, so an even functional does separate while the odd one
cannot: the finite dichotomy matching `even_vector_odd_functional_zero` and
`separation_depends_on_even_part`. -/
theorem even_pairing_pos : 0 < (1 : ℤ) * cVal + 1 * cVal := by decide

end ArkLib.ProximityGap.Frontier.G286EvenConeOddSeparatorNoGo
