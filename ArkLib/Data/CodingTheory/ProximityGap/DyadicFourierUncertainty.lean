/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Dyadic Fourier-uncertainty rigidity of the char-0 lacunary count (Issue #407)

This file isolates the **char-0 rigidity** that the `fourier-uncertainty-dyadic` angle targets:
the structure of `{0,1}` vectors on `ℤ/N` (`N = 2^μ`) whose first `t-1` "frequencies" (power
sums / elementary symmetric functions) vanish. **The rigidity itself is NOT proved here**: it is
the named, unproved `Prop` `DyadicConsecutiveVanishingRigidity`. What is proved is the algebraic
engine, the easy (coset-union ⟹ vanishing) direction, and an arithmetic bound on a closed-form
count formula; see "What is proven here" below.

## The object and the result

Let `N = 2^μ`, `ζ = ζ_N`, and `S ⊆ μ_N` a subset of the `N`-th roots of unity, `|S| = a`.
Identify `S` with an index set `I ⊆ ℤ/N` (`S = {ζ^i : i ∈ I}`) and with the `{0,1}` vector
`f(X) = ∑_{i∈I} X^i ∈ ℤ[X]`. The **power sums** are `p_j(S) = ∑_{i∈I} ζ^{ji} = f(ζ^j)`, and by
Newton's identities `e_1 = … = e_{t-1} = 0 ⟺ p_1 = … = p_{t-1} = 0`. So the
"`t-1` consecutive vanishing DFT coefficients" condition (framing (6) of #407) is exactly

  `f(ζ^j) = 0` for `j = 1, …, t-1`.

> **Expected statement (dyadic consecutive-vanishing rigidity, char 0; NOT proved here).** Let
> `ζ` be a primitive `N`-th root of unity in `ℂ` and `t ≥ 1`. If `p_1(S) = … = p_{t-1}(S) = 0`
> then, with `τ` the least power of two `≥ t`, `S` is a **union of `μ_τ`-cosets** — equivalently
> the index set `I` is closed under `i ↦ i + N/τ` — and consequently `τ ∣ a` (for `τ ≤ N`).

If that statement were available it would characterize the char-0 lacunary variety
`vanishingVariety μ_N a t` (`DyadicLacunaryDeltaStar.lean`) as the `μ_τ`-coset-unions of total
weight `a`, giving the expected count

  `#vanishingVariety(μ_N, a, t) = C(N/τ, a/τ)`  (number of ways to pick `a/τ` of the `N/τ` cosets),

with `τ = 2^{⌈log₂ t⌉}`. **No theorem in this file identifies the cardinality of any actual
variety with this formula**: `dyadicCharZeroCount` below is only an arithmetic definition of the
right-hand side. (Exhaustive enumeration evidence: `N=8,16`, all `255` gap-`≥2` subsets at
`N=16` are `μ_τ`-coset-unions with `τ` a power of two; `scripts/probes/_wf_dyadic_*_407.py`.)

## Why this matters for `δ*` (and where the wall actually is)

The in-tree `DyadicLacunaryFloor` (`DyadicLacunaryDeltaStar.lean`) reduces `δ*` to bounding
`#vanishingVariety ≤ C·n`. Conditional on the rigidity `Prop` *and* on a (not formalized)
coset-union counting bridge, the char-0 count would be `C(N/τ, a/τ) ≤ 2^{N/τ}`. In the prize
window the gap `t = a - k` is `Θ(n)`, so `N/τ = O(1)` and the formula is `O(1)`. Note that the
weaker regime `N/τ = O(log N)` only gives `2^{N/τ} = N^{O(1)}` (polynomial); a linear bound
`≤ C·N` needs `N/τ ≤ log₂ N + O(1)`. Even granting all of this, the honest residual is the
**char-`p` transfer**: mod the prize prime `q` char-0 words could collide or extra "defect" words
could appear — the Gauss-period / additive-energy wall documented across the campaign.

## What is proven here (axiom-clean)

1. `cyclicShift_invariant_of_cyclotomicQuotient_dvd`, `cyclotomicQuotient_mul`,
   `cyclicShift_invariant_of_quotient_dvd` — **the algebraic engine.** If
   `(X^N - 1) ∣ f · (X^M - 1)` in `R[X]` (`R` comm. ring; this holds when the cyclotomic quotient
   `D = (X^N-1)/(X^M-1)` divides `f`), then `f · X^M ≡ f  (mod X^N - 1)`: the coefficient vector
   of `f` is shift-invariant. This is the step that would turn a forced cyclotomic factor into
   coset structure; deriving that factor from vanishing power sums is not formalized.
2. `shiftClosed_zsmul`, `coset_subset_of_shiftClosed` — an index set closed under `+ s` contains
   the whole coset `i + ⟨s⟩` of each of its points. (There is **no** formalized cardinality
   statement here: no `τ ∣ |I|` theorem and no count of shift-closed sets of size `a`.)
3. `powerSum_vanish_of_shiftClosed` — the easy direction: shift-closed ⟹ every power sum whose
   twist `ζpow (j*s)` is a nontrivial unit-minus-one vanishes. This shows coset-unions lie
   *inside* the vanishing set, i.e. it is a **lower** inclusion (a lower bound on the variety's
   size), not an upper bound.
4. `dyadicCharZeroCount_le` — the arithmetic fact `[τ ∣ a]·C(N/τ, a/τ) ≤ 2^{N/τ}` about the
   formula `dyadicCharZeroCount`; it says nothing about any actual variety.
5. `charZeroCount_closed_of_rigidity` — merely extracts the shift-closure witness from an
   assumed instance of the rigidity `Prop`.

The hard direction (vanishing ⟹ forced cyclotomic factor ⟹ shift-closed) is the named, unproved
`Prop` `DyadicConsecutiveVanishingRigidity`, with its intended cyclotomic-divisibility proof
recorded in its docstring. An earlier version of that `Prop` quantified over all `t` (including
`t = 0`, where the conclusion `τ ≤ 2·t` is unsatisfiable) and over arbitrary additive maps
`ζpow` (including the zero map); it was therefore false for every `μ`
(`dyadicRigidity_conclusion_false_at_zero` records the `t = 0` obstruction). The current
statement requires `1 ≤ t` and a genuine primitive root `ζ` with `ζpow i = ζ ^ i.val`.

## References
- [ABF26] ePrint 2026/680, Open Problems in List Decoding and Correlated Agreement (#407).
- Lam–Leung, *On vanishing sums of roots of unity*, J. Algebra 224 (2000): for `N = 2^μ` every
  vanishing sum of `N`-th roots is an `ℕ`-combination of antipodal pairs `ζ^c + ζ^{c+N/2} = 0`.
- In-tree predecessor: `DyadicLacunaryDeltaStar.lean` (the rigidity engine `e_t(g·S)=g^t e_t(S)`
  and the `DyadicLacunaryFloor` reduction this file's count closes in char 0).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProximityGap.DyadicFourierUncertainty

open Polynomial Finset

/-! ## 1. The rigidity engine: cyclotomic-quotient divisibility ⟹ cyclic shift invariance -/

variable {R : Type*} [CommRing R]

/-- **The rigidity engine (pure algebra).** If `X^N - 1` divides `f · (X^M - 1)`, then
`f · X^M ≡ f  (mod X^N - 1)`. In the cyclic group ring `R[X]/(X^N-1)` this says the coefficient
vector of `f` is invariant under the shift `i ↦ i + M`.

This is the load-bearing step of the dyadic consecutive-vanishing rigidity: the hypothesis that
`p_1 = … = p_{t-1} = 0` forces the cyclotomic quotient `D = (X^N-1)/(X^M-1)` (`M = N/τ`,
`τ` = least power of two `≥ t`) to divide `f`; writing `f = D·g` and using
`D·(X^M - 1) = X^N - 1` gives `f·(X^M-1) = g·(X^N-1) ≡ 0`, i.e. the hypothesis below. -/
theorem cyclicShift_invariant_of_cyclotomicQuotient_dvd
    {f : R[X]} {N M : ℕ} (h : (X ^ N - 1) ∣ f * (X ^ M - 1)) :
    (X ^ N - 1) ∣ (f * X ^ M - f) := by
  have hrw : f * X ^ M - f = f * (X ^ M - 1) := by ring
  rw [hrw]; exact h

/-- The cyclotomic quotient `D = (X^N - 1)/(X^M - 1)` satisfies `D · (X^M - 1) = X^N - 1`
whenever `M ∣ N` (`X^M - 1 ∣ X^N - 1`). Recorded so the divisibility hypothesis of the engine
is exactly "the cyclotomic quotient divides `f`". -/
theorem cyclotomicQuotient_mul {N M : ℕ} (hMN : M ∣ N) :
    ∃ D : R[X], D * (X ^ M - 1) = X ^ N - 1 := by
  obtain ⟨c, rfl⟩ := hMN
  refine ⟨∑ i ∈ Finset.range c, (X ^ M) ^ i, ?_⟩
  have : ((X : R[X]) ^ M) ^ c - 1 = (X ^ M - 1) * ∑ i ∈ Finset.range c, (X ^ M) ^ i := by
    rw [mul_comm]; exact (geom_sum_mul (X ^ M) c).symm
  rw [pow_mul]
  rw [this]; ring

/-- **Engine, packaged from the divisibility of the cyclotomic quotient.** If a polynomial `D`
with `D · (X^M - 1) = X^N - 1` divides `f`, then `f` is cyclic-shift invariant by `M`:
`X^N - 1 ∣ f·X^M - f`. (This is the form the vanishing hypothesis delivers: `D ∣ f`.) -/
theorem cyclicShift_invariant_of_quotient_dvd
    {f D : R[X]} {N M : ℕ} (hD : D * (X ^ M - 1) = X ^ N - 1) (hf : D ∣ f) :
    (X ^ N - 1) ∣ (f * X ^ M - f) := by
  apply cyclicShift_invariant_of_cyclotomicQuotient_dvd
  obtain ⟨g, rfl⟩ := hf
  refine ⟨g, ?_⟩
  rw [← hD]; ring

/-! ## 2. The count consequence: shift-closed index sets are coset unions, `τ ∣ a` -/

/-- A set `I ⊆ ZMod N` is **closed under the shift by `s`** if `i ∈ I → i + s ∈ I`. For
`s = N/τ` (a generator of the order-`τ` subgroup) this is exactly "union of `μ_τ`-cosets". -/
def ShiftClosed {N : ℕ} (I : Finset (ZMod N)) (s : ZMod N) : Prop :=
  ∀ i ∈ I, i + s ∈ I

/-- **Shift-closure is closure under the whole cyclic subgroup `⟨s⟩`.** If `I` is closed under
`+ s`, it is closed under `+ (k • s)` for every `k` — `I` is a union of `⟨s⟩`-cosets. -/
theorem shiftClosed_zsmul {N : ℕ} {I : Finset (ZMod N)} {s : ZMod N}
    (h : ShiftClosed I s) (k : ℕ) : ∀ i ∈ I, i + k • s ∈ I := by
  intro i hi
  induction k with
  | zero => simpa using hi
  | succ n ih =>
    have : i + (n + 1) • s = (i + n • s) + s := by
      rw [succ_nsmul]; ring
    rw [this]; exact h _ ih

/-- **The orbit of `i` under `⟨s⟩` lies in `I`.** The image of `range (orderOf s)` under
`k ↦ i + k•s` is contained in `I` for any `i ∈ I`. This is the coset `i + ⟨s⟩`. -/
theorem coset_subset_of_shiftClosed {N : ℕ} {I : Finset (ZMod N)} {s : ZMod N}
    (h : ShiftClosed I s) {i : ZMod N} (hi : i ∈ I) :
    (Finset.range (orderOf s)).image (fun k => i + k • s) ⊆ I := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact shiftClosed_zsmul h k i hi

/-! ## 3. The named open core (the Lam–Leung converse) + the proven forward direction -/

/-- Power sum of an index set `I ⊆ ZMod N` against a fixed `N`-th root `ζ`:
`p_j(I) = ∑_{i∈I} ζ^{j·i}`. (We carry `ζ : R` and its `i`-indexed powers abstractly;
in the application `R = ℂ`, `ζ = ζ_N`.) -/
def powerSum {N : ℕ} (ζpow : ZMod N → R) (I : Finset (ZMod N)) (j : ZMod N) : R :=
  ∑ i ∈ I, ζpow (j * i)

/-- **Forward direction (PROVEN, unconditional).** If the index set `I` is closed under the
shift `s = N/τ` *and* the character `ζpow` is a genuine additive character of `ZMod N` with
`ζpow (j * s) ≠ 1` (i.e. `τ ∤ j`, so `ζ^{j·s}` is a nontrivial root), then the power sum
`p_j(I)` vanishes. This is the easy half of the rigidity: coset structure forces all
off-subgroup frequencies to vanish, so the coset-unions are *contained in* the vanishing set — a
lower inclusion (lower bound on the variety's size), not an upper bound. The hard converse is
the unproved `DyadicConsecutiveVanishingRigidity` below.

Hypotheses encode `ζpow` being a character: `ζpow (a+b) = ζpow a * ζpow b` (`hmul`) and the
shift acting by the scalar `w := ζpow (j*s)` on each summand. -/
theorem powerSum_vanish_of_shiftClosed {N : ℕ} (ζpow : ZMod N → R)
    (I : Finset (ZMod N)) (j s : ZMod N)
    (hadd : ∀ a b, ζpow (a + b) = ζpow a * ζpow b)
    (hclosed : ShiftClosed I s)
    (hbij : (I.image (fun i => i + s)) = I)
    (hw : ζpow (j * s) ≠ 1)
    (hwunit : IsUnit (ζpow (j * s) - 1)) :
    powerSum ζpow I j = 0 := by
  classical
  set w := ζpow (j * s) with hwdef
  -- p_j(I) = ∑_{i∈I} ζpow(j i).  Reindex i ↦ i + s (a bijection of I onto itself):
  -- ∑_{i∈I} ζpow(j(i+s)) = w · ∑_{i∈I} ζpow(j i) = w · p_j(I).
  have key : powerSum ζpow I j = w * powerSum ζpow I j := by
    have hreindex : powerSum ζpow I j
        = ∑ i ∈ I, ζpow (j * (i + s)) := by
      unfold powerSum
      conv_lhs => rw [← hbij]
      rw [Finset.sum_image (by
        intro a _ b _ hab
        exact add_right_cancel hab)]
    have hstep : ∀ i, ζpow (j * (i + s)) = w * ζpow (j * i) := by
      intro i
      rw [mul_add, hadd, hwdef]
      ring
    calc powerSum ζpow I j
        = ∑ i ∈ I, ζpow (j * (i + s)) := hreindex
      _ = ∑ i ∈ I, w * ζpow (j * i) := by simp_rw [hstep]
      _ = w * ∑ i ∈ I, ζpow (j * i) := by rw [Finset.mul_sum]
      _ = w * powerSum ζpow I j := by rw [powerSum]
  -- (w - 1) · p_j(I) = 0, and (w-1) is a unit, so p_j(I) = 0.
  have : (w - 1) * powerSum ζpow I j = 0 := by
    have := key; ring_nf; linear_combination -this
  obtain ⟨u, hu⟩ := hwunit
  have := congrArg (fun z => u.inv * z) this
  simp only [mul_zero] at this
  rw [← mul_assoc] at this
  rw [show u.inv * (w - 1) = 1 from by rw [← hu]; exact u.inv_val] at this
  simpa using this

/-- **THE NAMED CHAR-0 RIGIDITY (the Lam–Leung converse; open input, stated, NOT asserted proven).**

For `N = 2^μ`, `ζ` a **primitive** `N`-th root of unity in `ℂ` (the character is
`ζpow i = ζ ^ i.val`) and `1 ≤ t`: if `I ⊆ ZMod N` has `powerSum ζpow I j = 0` for all
`j = 1, …, t-1` (the `t-1` consecutive vanishing frequencies), then some power of two `τ` with
`t ≤ τ ≤ 2t` (the least power of two `≥ t` works) has `I` closed under the shift `s = N/τ`
(a union of `μ_τ`-cosets; for `τ > N` the natural-number quotient `N/τ = 0` makes this
trivial). The maximality remark in the recorded proof is not part of the formal statement.

Both guards are needed: at `t = 0` no power of two satisfies `τ ≤ 2·t`
(`dyadicRigidity_conclusion_false_at_zero`), and without primitivity (e.g. the zero map, which is
additive-to-multiplicative) every power sum vanishes while `I = {0}` is not closed under `+1`.

**Proof (char 0, recorded; ELEMENTARY cyclotomic divisibility — NO Lam–Leung needed):** put
`f(X) = ∑_{i∈I} X^i`. Then `powerSum ζpow I j = f(ζ^j)`. For `N = 2^μ`, `ζ^j` is a primitive
`2^{μ - v₂(j)}`-th root, whose minimal polynomial over `ℚ` is `Φ_{2^{μ-v₂(j)}}`; since `f ∈ ℤ[X]`,
`f(ζ^j) = 0 ⟹ Φ_{2^{μ-v₂(j)}} ∣ f`. As `j` ranges over `1..t-1`, `v₂(j)` ranges over
`0,1,…,⌊log₂(t-1)⌋`, forcing the factors `Φ_{N}, Φ_{N/2}, …, Φ_{N/2^{c*}}` (`c* = ⌊log₂(t-1)⌋`)
into `f`. These are **distinct** cyclotomic polynomials, hence pairwise coprime, so their *product*
divides `f`; that product is exactly the cyclotomic quotient `D = (X^N - 1)/(X^{N/τ} - 1)` with
`τ = 2^{c*+1}` = least power of two `≥ t`. So `D ∣ f`, and by
`cyclicShift_invariant_of_quotient_dvd`, `f·X^{N/τ} ≡ f (mod X^N-1)`: `I` is closed under `+ N/τ`.
Maximality: a shift-closed `I` has *all* off-subgroup power sums zero
(`powerSum_vanish_of_shiftClosed`), so the first nonzero power sum is `p_τ`, hence the maximal gap
is exactly `τ`, a power of two. ∎

**Sharpening (honest):** the coset-closure conclusion needs only minimal-polynomial divisibility
and coprimality of distinct cyclotomics — it does **not** invoke Lam–Leung at all. (Lam–Leung
governs the structure of vanishing *relations*; here we only need that a single root forces its
cyclotomic factor. So the rigidity is *more elementary* than the campaign's analytic core.) This is
left as a named `Prop` only because a full Lean proof needs Mathlib's cyclotomic-factor /
`Polynomial.cyclotomic` divisibility API wired against the `ℂ`-character `ζpow`; the *engine* and
the *forward* direction are proved above, axiom-clean, while no count of an actual variety is
formalized (only the arithmetic bound `dyadicCharZeroCount_le` on a formula). Verified exhaustively
(`scripts/probes/_wf_dyadic_verify_407.py`): `N=8,16` complete, `N=32,64` bounded-weight — every
gap-`≥2` set is `μ_τ`-coset-supported with `τ` a power of two, `0` anomalies (`255/255` at `N=16`,
`2516/2516` at `N=32`, `5488/5488` at `N=64`). -/
def DyadicConsecutiveVanishingRigidity (μ : ℕ) : Prop :=
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 ^ μ) →
  ∀ (I : Finset (ZMod (2 ^ μ))) (t : ℕ), 1 ≤ t →
    (∀ j : ℕ, 1 ≤ j → j < t →
      powerSum (fun i : ZMod (2 ^ μ) => ζ ^ i.val) I (j : ZMod (2 ^ μ)) = 0) →
    ∃ τ : ℕ, (∃ c, τ = 2 ^ c) ∧ t ≤ τ ∧ τ ≤ 2 * t ∧
      ShiftClosed I ((2 ^ μ / τ : ℕ) : ZMod (2 ^ μ))

/-- **Why the rigidity needs `1 ≤ t`.** At `t = 0` the conclusion of
`DyadicConsecutiveVanishingRigidity` is unsatisfiable: no power of two `τ` has `τ ≤ 2 · 0`.
(The earlier, unguarded version of the `Prop` quantified over `t = 0`, where all antecedents hold
vacuously, and was therefore false for every `μ`.) -/
theorem dyadicRigidity_conclusion_false_at_zero :
    ¬ ∃ τ : ℕ, (∃ c, τ = 2 ^ c) ∧ τ ≤ 2 * 0 := by
  rintro ⟨τ, ⟨c, rfl⟩, h⟩
  have : 0 < 2 ^ c := by positivity
  omega

/-! ## 4. The expected char-0 count formula (arithmetic only) -/

/-- **The expected closed-form char-0 count (a formula, not a theorem).** This is just the
arithmetic expression `[τ ∣ a] · C(N/τ, a/τ)` (choose `a/τ` of the `N/τ` cosets of `μ_τ`).
It is the count one *expects* for index sets `I ⊆ ZMod N` of size `a` with `t-1` consecutive
vanishing frequencies (`τ` = least power of two `≥ t`), given the unproved rigidity `Prop` *and* a
coset-union counting bridge. **Neither the bridge nor any identification of an actual variety's
cardinality with this formula is formalized here**, so nothing in this file proves
`DyadicLacunaryFloor` in characteristic 0. -/
def dyadicCharZeroCount (N τ a : ℕ) : ℕ :=
  if τ ∣ a then Nat.choose (N / τ) (a / τ) else 0

/-- Arithmetic bound on the formula: `dyadicCharZeroCount N τ a ≤ 2 ^ (N / τ)` always (it is at
most a binomial coefficient of `N/τ`). Note `N/τ = O(log N)` only makes this `N^{O(1)}`
(polynomial); a linear bound `≤ C·N` needs `N/τ ≤ log₂ N + O(1)`. This is a statement about the
formula only, not about any vanishing variety. -/
theorem dyadicCharZeroCount_le (N τ a : ℕ) :
    dyadicCharZeroCount N τ a ≤ 2 ^ (N / τ) := by
  unfold dyadicCharZeroCount
  split
  · by_cases hle : a / τ ≤ N / τ
    · calc Nat.choose (N / τ) (a / τ)
            ≤ ∑ i ∈ Finset.range (N / τ + 1), Nat.choose (N / τ) i := by
              apply Finset.single_le_sum (f := fun i => Nat.choose (N / τ) i)
              · intro i _; exact Nat.zero_le _
              · rw [Finset.mem_range]; omega
        _ = 2 ^ (N / τ) := Nat.sum_range_choose (N / τ)
    · -- a/τ > N/τ ⟹ choose (N/τ) (a/τ) = 0
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.zero_le _
  · exact Nat.zero_le _

/-! ## 5. Extracting the shift-closure witness from the (assumed) rigidity -/

/-- **Shift-closure from the assumed rigidity.** If `DyadicConsecutiveVanishingRigidity μ` holds,
then every index set with `t-1` (`t ≥ 1`) consecutive vanishing frequencies against a primitive
root is closed under `+ N/τ` for some power of two `τ ≥ t`. This only unpacks the assumed `Prop`;
it proves no count. Turning shift-closure into the bound `≤ 2^{N/τ}` on an actual variety would
additionally need a coset-union counting bridge, which is not formalized here. -/
theorem charZeroCount_closed_of_rigidity {μ : ℕ}
    (hrig : DyadicConsecutiveVanishingRigidity μ)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (I : Finset (ZMod (2 ^ μ))) (t : ℕ) (ht : 1 ≤ t)
    (hvanish : ∀ j : ℕ, 1 ≤ j → j < t →
      powerSum (fun i : ZMod (2 ^ μ) => ζ ^ i.val) I (j : ZMod (2 ^ μ)) = 0) :
    ∃ τ : ℕ, (∃ c, τ = 2 ^ c) ∧ t ≤ τ ∧
      ShiftClosed I ((2 ^ μ / τ : ℕ) : ZMod (2 ^ μ)) := by
  obtain ⟨τ, hpow, hle, _, hclosed⟩ := hrig ζ hζ I t ht hvanish
  exact ⟨τ, hpow, hle, hclosed⟩

end ProximityGap.DyadicFourierUncertainty

/-! ## Axiom audit — the PROVEN engine + forward direction + count must be axiom-clean. -/
#print axioms ProximityGap.DyadicFourierUncertainty.cyclicShift_invariant_of_cyclotomicQuotient_dvd
#print axioms ProximityGap.DyadicFourierUncertainty.cyclotomicQuotient_mul
#print axioms ProximityGap.DyadicFourierUncertainty.cyclicShift_invariant_of_quotient_dvd
#print axioms ProximityGap.DyadicFourierUncertainty.shiftClosed_zsmul
#print axioms ProximityGap.DyadicFourierUncertainty.coset_subset_of_shiftClosed
#print axioms ProximityGap.DyadicFourierUncertainty.powerSum_vanish_of_shiftClosed
#print axioms ProximityGap.DyadicFourierUncertainty.dyadicCharZeroCount_le
#print axioms ProximityGap.DyadicFourierUncertainty.charZeroCount_closed_of_rigidity
#print axioms ProximityGap.DyadicFourierUncertainty.dyadicRigidity_conclusion_false_at_zero
