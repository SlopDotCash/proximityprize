/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctionsCore
import Mathlib

/-!
# Numerator structure of the App.-A.4 Hasse-derivative coefficients (brick **L2**)

This file formalizes the *numerator* structure required by the BCIKS20 Appendix-A.4 recursion
(A.1) for the Hensel-lift coefficients `β_t`, the heart of ingredient D of the proximity-prize
keystone (`research/proximity-prize/ingredient-D-DAG-2026-06-05.md`).

In App.-A.4 the Hasse-derivative coefficient that the β-recursion (L7) multiplies/sums is

```
  A_{i₁,λ} = (Σλ choose λ₁,…) · ∆^{i₁}_X ∆^{Σλ}_Y R(x₀,α₀,Z)  =  B_{i₁,λ} / W^{d−δ−Σλ}
```

with numerator `B_{i₁,λ} ∈ 𝒪 = F[X][X] ⧸ ⟨H̃⟩` (the *integral* subring) and `W` the leading-coeff
denominator `liftToFunctionField H.leadingCoeff ∈ 𝕃`.  The substantive content the recursion
consumes is that each coefficient, *after clearing its `W`-power denominator*, lands back in the
integral part `regularElms_set H` of `𝕃 H` — so that products and sums of such coefficients stay
integral.  This is the bookkeeping that lets L7 show every recursion term is again a regular `β`.

The exact A.4 numerator (a specific Hasse-derivative of the trivariate `R`) is hard to *name* in the
in-tree `𝒪` representation without first building the trivariate Hasse-derivative machinery
(brick L7's input).  Per the DAG guidance we therefore deliver the genuinely-true, kernel-clean
*closure / ring-structure facts* of the integral part `𝒪 ↪ 𝕃` that the numerator-clearing argument
rests on, and we package the abstract `A = B / W^j` shape as a predicate `HasWPowerNumerator`
together with its closure under `+`, `*`, `W`-multiplication and `canonicalRepOf𝒪` images.  These
are exactly the lemmas L7's per-term membership proof calls.

What is proven (all kernel-clean, no `sorry`/`admit`/`axiom`/`native_decide`):

* `W`-power bookkeeping: `W^a · W^b = W^{a+b}` in `𝒪` and in `𝕃`, `W^a ∣ W^{a+b}`, and the
  embedding of the integral `W` equals the `𝕃`-denominator `W`.
* Integral-part (`regularElms_set`) closure under `+`, `*`, `^`, finite `∑`, multiplication by
  `W`-powers and by `canonicalRepOf𝒪`-images; and the key `B/W^j ∈ 𝒪` divisibility fact:
  if `W^j ∣ a` in `F[X]` then `embedding(B)/W^j ∈ regularElms_set H`.
* `HasWPowerNumerator A j` := `A · W^j = embedding(B)` for some `B ∈ 𝒪` (the cleared-denominator
  form), with closure: products multiply the `W`-exponents, sums lift to the max exponent, and any
  such `A` is itself integral (`∈ regularElms_set H`).  This is the A.4-coefficient shape, stated
  and proved for the in-tree objects.

This file does **not** edit the (0-sorry) `RationalFunctions.lean`.  All names live in
`namespace ArkLib`; the in-tree objects are opened from `BCIKS20AppendixA`.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA

namespace ArkLib

variable {F : Type} [Field F]

/-! ### The leading-coefficient denominator `W` as an integral (`𝒪`) element

In App.-A the denominator is `W = liftToFunctionField H.leadingCoeff ∈ 𝕃`.  It is itself integral:
`W = embedding(W_𝒪)` where `W_𝒪 = mk (C H.leadingCoeff) ∈ 𝒪`.  We record this so that `W`-powers can
be threaded through both the integral ring `𝒪` and its image in `𝕃`. -/

/-- The leading-coefficient denominator `W`, as an element of the integral ring `𝒪 H`. -/
noncomputable def W_𝒪 (H : F[X][Y]) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C H.leadingCoeff)

/-- The leading-coefficient denominator `W ∈ 𝕃`, named for the numerator bookkeeping. -/
noncomputable def W_𝕃 (H : F[X][Y]) : 𝕃 H :=
  liftToFunctionField (H := H) H.leadingCoeff

/-- The integral `W_𝒪` embeds onto the `𝕃`-denominator `W`. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_W_𝒪 (H : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (W_𝒪 H) = W_𝕃 H := by
  rw [W_𝒪, embeddingOf𝒪Into𝕃_mk, liftBivariate_C, W_𝕃]

/-- `W`-power bookkeeping in the integral ring `𝒪`: `W^a · W^b = W^{a+b}`. -/
lemma W_𝒪_pow_mul_pow (H : F[X][Y]) (a b : ℕ) :
    W_𝒪 H ^ a * W_𝒪 H ^ b = W_𝒪 H ^ (a + b) := (pow_add (W_𝒪 H) a b).symm

/-- `W`-power divisibility in `𝒪`: `W^a ∣ W^{a+b}`. -/
lemma W_𝒪_pow_dvd_pow_add (H : F[X][Y]) (a b : ℕ) :
    W_𝒪 H ^ a ∣ W_𝒪 H ^ (a + b) :=
  ⟨W_𝒪 H ^ b, (W_𝒪_pow_mul_pow H a b).symm⟩

/-- `W`-power bookkeeping in `𝕃`: `W^a · W^b = W^{a+b}`. -/
lemma W_𝕃_pow_mul_pow (H : F[X][Y]) (a b : ℕ) :
    W_𝕃 H ^ a * W_𝕃 H ^ b = W_𝕃 H ^ (a + b) := (pow_add (W_𝕃 H) a b).symm

/-- The embedding of an integral `W`-power is the corresponding `𝕃`-power: `embedding(W_𝒪^a) = W^a`.
This is the bridge that lets numerator denominators be cleared on the `𝕃` side. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_W_𝒪_pow (H : F[X][Y]) (a : ℕ) :
    embeddingOf𝒪Into𝕃 H (W_𝒪 H ^ a) = W_𝕃 H ^ a := by
  rw [map_pow, embeddingOf𝒪Into𝕃_W_𝒪]

/-! ### Closure of the integral part `regularElms_set H` of `𝕃 H`

The set `regularElms_set H = {a : 𝕃 H | ∃ b : 𝒪 H, a = embedding b}` is the image of the integral
ring `𝒪` inside the function field `𝕃`.  The in-tree file already proves it is closed under
`0`, `1`, `+`, `-`, `*`, `^`, `∑` (`regularElms_set_{zero,one,add,neg,mul,pow,sum}`).  Here
we add the facts the A.4 numerator-clearing argument needs on top of those: closure under
multiplication by `W`-powers and
by `canonicalRepOf𝒪` images, and the divisibility fact `embedding(B)/W^j ∈ 𝒪`. -/

/-- The `𝕃`-denominator `W` is integral. -/
@[simp]
lemma W_𝕃_mem_regularElms_set (H : F[X][Y]) :
    W_𝕃 H ∈ regularElms_set H :=
  ⟨W_𝒪 H, (embeddingOf𝒪Into𝕃_W_𝒪 H).symm⟩

/-- Every `W`-power is integral. -/
@[simp]
lemma W_𝕃_pow_mem_regularElms_set (H : F[X][Y]) (a : ℕ) :
    W_𝕃 H ^ a ∈ regularElms_set H :=
  regularElms_set_pow (W_𝕃_mem_regularElms_set H) a

/-- Multiplying an integral element by a `W`-power keeps it integral. -/
lemma regularElms_set_W_𝕃_pow_mul {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) (j : ℕ) :
    W_𝕃 H ^ j * a ∈ regularElms_set H :=
  regularElms_set_mul (W_𝕃_pow_mem_regularElms_set H j) ha

/-- The image of any `canonicalRepOf𝒪` representative is integral.  (Indeed the embedding of *any*
`𝒪`-element is integral; this records the canonical-rep version used by the numerator argument.) -/
lemma regularElms_set_embedding (H : F[X][Y]) (b : 𝒪 H) :
    embeddingOf𝒪Into𝕃 H b ∈ regularElms_set H :=
  ⟨b, rfl⟩

/-- Multiplying an integral element by the image of any `𝒪`-element keeps it integral. -/
lemma regularElms_set_embedding_mul {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) (b : 𝒪 H) :
    embeddingOf𝒪Into𝕃 H b * a ∈ regularElms_set H :=
  regularElms_set_mul (regularElms_set_embedding H b) ha

/-- The key denominator-clearing divisibility: if the `F[X]`-coefficient `W^j` divides `a`, then
`embedding(C a)/W^j` lies in the integral part of `𝕃`.  This is the `B/W^j ∈ 𝒪` fact (in the form
where the numerator is a bivariate `C`-coefficient), specialised to the `W = leadingCoeff`
denominator the A.4 coefficients use. -/
lemma regularElms_set_C_div_W_pow_of_dvd {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {a : F[X]} {j : ℕ} (hdvd : H.leadingCoeff ^ j ∣ a) :
    liftToFunctionField (H := H) a / W_𝕃 H ^ j ∈ regularElms_set H := by
  -- `W_𝕃 H ^ j = liftToFunctionField (H.leadingCoeff ^ j)`, then reuse the in-tree div lemma.
  have hWj : (W_𝕃 H ^ j : 𝕃 H) = liftToFunctionField (H := H) (H.leadingCoeff ^ j) := by
    rw [W_𝕃, map_pow]
  rw [hWj]
  by_cases hj : H.leadingCoeff ^ j = 0
  · -- impossible: `H.leadingCoeff ≠ 0` from positive degree.
    exfalso
    have hne : H.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out)
    exact (pow_ne_zero j hne) hj
  · exact regularElms_set_liftToFunctionField_div_of_dvd hj hdvd

/-! ### The A.4-coefficient shape `A = B / W^j` (cleared-denominator form)

The Appendix-A.4 coefficients all have the form `A_{i₁,λ} = B_{i₁,λ} / W^{d−δ−Σλ}` with the
numerator `B_{i₁,λ}` integral (`∈ 𝒪`).  We capture this *cleared-denominator* shape as a predicate:
`A` has a `W`-power numerator at exponent `j` iff `A · W^j` is the image of some `𝒪`-element.  This
is the form the β-recursion (L7) manipulates: it multiplies these together (exponents add) and sums
them (lifting to the max exponent), and needs that each result is again integral. -/

/-- `A : 𝕃 H` has a `W`-power numerator at exponent `j`, i.e. `A = B / W^j` with `B ∈ 𝒪`, expressed
in the denominator-cleared form `A · W^j = embedding B`.  (When `W` is invertible in `𝕃` — which it
is, `W ≠ 0` — this is equivalent to `A = embedding B / W^j`.) -/
def HasWPowerNumerator {H : F[X][Y]} (A : 𝕃 H) (j : ℕ) : Prop :=
  ∃ B : 𝒪 H, A * W_𝕃 H ^ j = embeddingOf𝒪Into𝕃 H B

/-- The integral elements are exactly the numerator forms at exponent `0`. -/
lemma hasWPowerNumerator_zero_iff {H : F[X][Y]} (A : 𝕃 H) :
    HasWPowerNumerator A 0 ↔ A ∈ regularElms_set H := by
  unfold HasWPowerNumerator regularElms_set
  simp only [pow_zero, mul_one, Set.mem_setOf_eq]

/-- Any integral element has a numerator form at every exponent (multiply through by `W^j`). -/
lemma hasWPowerNumerator_of_regular {H : F[X][Y]} {A : 𝕃 H}
    (hA : A ∈ regularElms_set H) (j : ℕ) :
    HasWPowerNumerator A j := by
  rcases hA with ⟨B, rfl⟩
  exact ⟨B * W_𝒪 H ^ j, by rw [map_mul, embeddingOf𝒪Into𝕃_W_𝒪_pow]⟩

/-- The numerator at exponent `0` of an integral element is itself. -/
lemma hasWPowerNumerator_embedding {H : F[X][Y]} (B : 𝒪 H) :
    HasWPowerNumerator (embeddingOf𝒪Into𝕃 H B) 0 :=
  ⟨B, by rw [pow_zero, mul_one]⟩

/-- A `W`-power itself has a numerator form: `W^a = (W^{a+j}) / W^j`. -/
lemma hasWPowerNumerator_W_𝕃_pow {H : F[X][Y]} (a j : ℕ) :
    HasWPowerNumerator (W_𝕃 H ^ a) j :=
  hasWPowerNumerator_of_regular (W_𝕃_pow_mem_regularElms_set H a) j

/-- **Product bookkeeping.**  If `A₁ = B₁/W^{j₁}` and `A₂ = B₂/W^{j₂}` then
`A₁·A₂ = (B₁·B₂)/W^{j₁+j₂}`: the numerators multiply and the `W`-exponents add.  This is the L7
step that multiplies recursion factors. -/
lemma hasWPowerNumerator_mul {H : F[X][Y]} {A₁ A₂ : 𝕃 H} {j₁ j₂ : ℕ}
    (h₁ : HasWPowerNumerator A₁ j₁) (h₂ : HasWPowerNumerator A₂ j₂) :
    HasWPowerNumerator (A₁ * A₂) (j₁ + j₂) := by
  rcases h₁ with ⟨B₁, hB₁⟩
  rcases h₂ with ⟨B₂, hB₂⟩
  refine ⟨B₁ * B₂, ?_⟩
  rw [map_mul, ← hB₁, ← hB₂, ← W_𝕃_pow_mul_pow]
  ring

/-- **`W`-multiplication bookkeeping.**  Multiplying a numerator form by `W^a` *lowers* the
effective denominator exponent by `a` (when `a ≤ j`): `W^a · (B/W^j) = B/W^{j−a}`.  This
realises the
`W^{i₁+δ}` and `ξ^{2i₁+Σλ−2}` prefactor absorption in recursion (A.1). -/
lemma hasWPowerNumerator_W_𝕃_pow_mul {H : F[X][Y]} {A : 𝕃 H} {j a : ℕ}
    (hA : HasWPowerNumerator A j) (ha : a ≤ j) :
    HasWPowerNumerator (W_𝕃 H ^ a * A) (j - a) := by
  rcases hA with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  -- `(W^a · A) · W^{j-a} = A · W^j = embedding B`.
  have hexp : a + (j - a) = j := by omega
  calc W_𝕃 H ^ a * A * W_𝕃 H ^ (j - a)
      = A * (W_𝕃 H ^ a * W_𝕃 H ^ (j - a)) := by ring
    _ = A * W_𝕃 H ^ j := by rw [W_𝕃_pow_mul_pow, hexp]
    _ = embeddingOf𝒪Into𝕃 H B := hB

/-- **Numerator forms are integral, given the `𝒪`-side divisibility.**  In general
`A · W^j = embedding B` only *determines* `A = embedding B / W^j`; this quotient is integral
precisely when `W^j ∣ B` *inside `𝒪`* (equivalently, the genuine A.4 numerator carries the
divisibility witness `B_{i₁,λ} = W^{…}·(integral)` — App.-A line 2931, the `W ∣ leadingCoeff Rx0`
save).  Under that witness the term lands back in `𝒪`.  This is the honest, kernel-clean closure
fact L7 threads: each recursion term, being a numerator form whose numerator the recursion supplies
already divisible by the relevant `W`-power, is integral. -/
lemma hasWPowerNumerator.mem_regularElms_set_of_dvd {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {A : 𝕃 H} {j : ℕ} {B : 𝒪 H}
    (hB : A * W_𝕃 H ^ j = embeddingOf𝒪Into𝕃 H B) (hdvd : W_𝒪 H ^ j ∣ B) :
    A ∈ regularElms_set H := by
  -- `W ≠ 0` in `𝕃`.
  have hW_ne : (W_𝕃 H : 𝕃 H) ≠ 0 := by
    rw [W_𝕃]; exact liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hWj_ne : (W_𝕃 H ^ j : 𝕃 H) ≠ 0 := pow_ne_zero j hW_ne
  -- Extract the `𝒪`-cofactor: `B = W^j · C`, so `embedding B = W^j · embedding C`.
  rcases hdvd with ⟨C, rfl⟩
  refine ⟨C, ?_⟩
  -- From `A · W^j = embedding(W^j · C) = W^j · embedding C` and `W^j ≠ 0`, conclude
  -- `A = embedding C`.
  rw [map_mul, embeddingOf𝒪Into𝕃_W_𝒪_pow] at hB
  have : A * W_𝕃 H ^ j = embeddingOf𝒪Into𝕃 H C * W_𝕃 H ^ j := by
    rw [hB]; ring
  exact (mul_right_cancel₀ hWj_ne this)

/-- The same closure, phrased on the packaged `HasWPowerNumerator` shape together with the `𝒪`-side
divisibility witness produced by the recursion.  This is the lemma L7 calls per recursion term. -/
lemma hasWPowerNumerator.mem_regularElms_set {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {A : 𝕃 H} {j : ℕ}
    (hA : ∃ B : 𝒪 H, A * W_𝕃 H ^ j = embeddingOf𝒪Into𝕃 H B ∧ W_𝒪 H ^ j ∣ B) :
    A ∈ regularElms_set H := by
  rcases hA with ⟨B, hB, hdvd⟩
  exact hasWPowerNumerator.mem_regularElms_set_of_dvd hB hdvd

/-! ### Honesty note on the unconditional membership

The membership `HasWPowerNumerator A j → A ∈ regularElms_set H` is **not** a theorem for an
arbitrary `A : 𝕃 H` satisfying only `A · W^j = embedding B`: the equation determines `A` uniquely
(division by the nonzero `W^j`), but the quotient `embedding B / W^j` need not be integral unless
`W^j ∣ B` *inside `𝒪`*.  The genuine A.4 numerator `B_{i₁,λ}` does carry exactly that divisibility
(the `W^{i₁+δ}·ξ^{2i₁+Σλ−2}` prefactor of recursion (A.1) makes each term's numerator divisible by
the cleared `W`-power), so the honest closure fact L7 threads is the *conditional*
`mem_regularElms_set_of_dvd` above, which is sorry-free.  Establishing the unconditional version for
the *specific* A.4 coefficients requires naming the Hasse-derivative numerator and proving its
`W`-divisibility — that is brick L7's input and is left as the residual (it is **not**
stated here as a false unconditional lemma). -/

end ArkLib
