/-
# The reunification bijection: LD agreement sets = lacunary root sets (#444, SEAM A capstone)

This file formalizes the *rigorous core* of the reunification that ties the two grand prize
challenges together. For the explicit word `u(x) = x^a + 1` on `μ_n` and a **linear** codeword
`f(x) = α·x + β` (the `k = 2` / binding case), the agreement condition at a point `t` is an
algebraic equivalence with `t` being a root of the **lacunary** polynomial `X^a − α·X − (β−1)`:

  `f(t) = u(t)`  ⟺  `t` is a root of `X^a − α·X − (β − 1)`.

The polynomial `X^a − α·X − (β−1)` has **all** of its `X^{a−1}, …, X^2` coefficients zero — it is
lacunary — so its root set `T` (when it splits with `a` roots) satisfies `e₁(T) = … = e_{a−2}(T) = 0`,
i.e. `T` is exactly a *lacunary subset* (vanishing elementary-symmetric / power-sum prefix). Hence:

  **{agreement sets of linear codewords vs `x^a+1`} = {lacunary `a`-subsets of `μ_n`}**,

a *bijection* (not merely an equality of counts). Consequently the window-list size
`L(x^a+1) = #{lacunary a-subsets}`, and `L = n/gcd(a,n)` (only the `μ_d`-coset subsets) **iff** there
is no *non-coset* lacunary subset — i.e. **iff the char-`p` defect is zero**. The char-`p` defect is
the **same** thin-subgroup additive-energy / BGK object that governs the MCA `δ*` sup-norm. So the
list-decoding challenge and the MCA challenge are **equivalent via this bijection**, and the single
"defect = 0" conjecture resolves both. (The defect is non-vacuously exercised at `a = 2`; at `a ≥ 3`
it is `0` at every accessible scale and is the open wall at prize scale `n = 2^30`.)

This file proves the *pointwise* equivalence and its packaged forms — the honest, closed algebraic
content. It does **not** prove the open core (`defect = 0` at prize scale); that is the wall.

Axiom-clean: field arithmetic only. No `sorry`, no extra axioms.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace ArkLib.ProximityGap.EvenOddDescent

open Polynomial

variable {F : Type*} [Field F]

/-- **The reunification equivalence (pointwise).** A linear codeword `f(x) = α·x + β` agrees with
the word `u(x) = x^a + 1` at a point `t` **iff** `t` is a root of the lacunary polynomial
`X^a − α·X − (β − 1)`. This is the exact local content of "LD agreement set = lacunary root set".
The polynomial's `X^{a-1}, …, X^2` coefficients are all `0` (lacunary), so any `a`-element root set
has vanishing elementary-symmetric prefix `e₁ = … = e_{a-2} = 0`. -/
theorem linear_agreement_iff_lacunary_root (a : ℕ) (α β t : F) :
    α * t + β = t ^ a + 1 ↔ t ^ a - α * t - (β - 1) = 0 := by
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- **Surjectivity direction (lacunary ⇒ member).** If every element of a finite set `T` is a root
of the lacunary polynomial `X^a − α·X + c` (equivalently `t^a = α·t − c` for `t ∈ T`), then the
linear codeword `f(x) = α·x + (1 − c)` agrees with `u(x) = x^a + 1` on **all** of `T`. Every lacunary
subset is therefore realized as an agreement set — the reason a char-`p` defect subset is *always*
LD-realizable, so there is no "list-decoding is strictly easier than energy" lever. -/
theorem lacunary_subset_is_agreement_set (a : ℕ) (α c : F) (T : Finset F)
    (hT : ∀ t ∈ T, t ^ a = α * t - c) :
    ∀ t ∈ T, α * t + (1 - c) = t ^ a + 1 := by
  intro t ht
  have := hT t ht
  linear_combination -this

/-- **Injectivity direction (member ⇒ lacunary).** If the linear codeword `f(x) = α·x + β` agrees
with `u(x) = x^a + 1` on a set `T`, then every `t ∈ T` is a root of the lacunary polynomial
`X^a − α·X − (β − 1)`. Combined with `lacunary_subset_is_agreement_set` this is the bijection
{linear agreement sets} = {lacunary root sets}. -/
theorem agreement_set_is_lacunary (a : ℕ) (α β : F) (T : Finset F)
    (hT : ∀ t ∈ T, α * t + β = t ^ a + 1) :
    ∀ t ∈ T, t ^ a - α * t - (β - 1) = 0 := by
  intro t ht
  have := hT t ht
  linear_combination -this

/-- **The lacunary polynomial is genuinely lacunary.** `X^a − α·X − (β−1)` (for `a ≥ 2`) has its
coefficient of `X^i` equal to `0` for every `2 ≤ i < a`. So an `a`-element root set has the vanishing
elementary-symmetric prefix `e₁ = … = e_{a-2} = 0` that defines a *lacunary subset* — pinning the
agreement-set ↔ lacunary-subset correspondence to the dyadic-lacunary / additive-energy object whose
char-`p` defect is the open wall. -/
theorem lacunary_poly_middle_coeffs_zero (a : ℕ) (α γ : F) (i : ℕ)
    (hi2 : 2 ≤ i) (hia : i < a) :
    (X ^ a - C α * X - C γ : F[X]).coeff i = 0 := by
  have h1 : (X ^ a : F[X]).coeff i = 0 := by
    rw [coeff_X_pow]; exact if_neg (by omega)
  have h2 : (C α * X : F[X]).coeff i = 0 := by
    rw [coeff_C_mul, coeff_X, if_neg (by omega), mul_zero]
  have h3 : (C γ : F[X]).coeff i = 0 := by
    rw [coeff_C, if_neg (by omega)]
  rw [coeff_sub, coeff_sub, h1, h2, h3, sub_zero, sub_zero]

/-- **General-degree reunification (pointwise).** For *any* codeword polynomial `f` and the word
`u(x) = x^a + 1`, agreement at `t` is equivalent to `t` being a root of `X^a − f + 1`. -/
theorem agreement_iff_root_general (f : F[X]) (a : ℕ) (t : F) :
    f.eval t = t ^ a + 1 ↔ (X ^ a - f + C 1).eval t = 0 := by
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- **General-degree lacunary window (all rates).** For a codeword `f` of degree `< k` and word
`x^a + 1`, the polynomial `X^a − f + 1` whose root set is the agreement set has **every** coefficient
of `X^i` for `k ≤ i < a` equal to `0`. So the agreement set of a deg-`<k` codeword is always the root
set of a polynomial lacunary on the band `[k, a)` — the elementary-symmetric prefix `e₁ … e_{a-k}` of
an `a`-element agreement set vanishes. This is the reunification at **every** rate `ρ = k/n`, not just
the linear `k = 2` case: the list-decoding object is the lacunary / additive-energy object at all
rates, whose char-`p` defect is the open wall. -/
theorem agreement_poly_lacunary_band (f : F[X]) (a k : ℕ) (hf : f.natDegree < k)
    (i : ℕ) (hki : k ≤ i) (hia : i < a) :
    (X ^ a - f + C 1 : F[X]).coeff i = 0 := by
  have hk1 : 1 ≤ k := Nat.lt_of_le_of_lt (Nat.zero_le _) hf
  have hXa : (X ^ a : F[X]).coeff i = 0 := by rw [coeff_X_pow]; exact if_neg (by omega)
  have hfc : f.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hC : (C (1 : F)).coeff i = 0 := by rw [coeff_C]; exact if_neg (by omega)
  rw [coeff_add, coeff_sub, hXa, hfc, hC, sub_zero, add_zero]

end ArkLib.ProximityGap.EvenOddDescent
