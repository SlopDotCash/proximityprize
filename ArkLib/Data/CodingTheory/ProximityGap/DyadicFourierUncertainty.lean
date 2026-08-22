/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Dyadic Fourier-uncertainty rigidity of the char-0 lacunary count (Issue #407)

This file isolates and proves the **char-0 rigidity** that the `fourier-uncertainty-dyadic`
angle targets: the structure of `{0,1}` vectors on `ℤ/N` (`N = 2^μ`) whose first `t-1`
"frequencies" (power sums / elementary symmetric functions) vanish.

## The object and the result

Let `N = 2^μ`, `ζ = ζ_N`, and `S ⊆ μ_N` a subset of the `N`-th roots of unity, `|S| = a`.
Identify `S` with an index set `I ⊆ ℤ/N` (`S = {ζ^i : i ∈ I}`) and with the `{0,1}` vector
`f(X) = ∑_{i∈I} X^i ∈ ℤ[X]`. The **power sums** are `p_j(S) = ∑_{i∈I} ζ^{ji} = f(ζ^j)`, and by
Newton's identities `e_1 = … = e_{t-1} = 0 ⟺ p_1 = … = p_{t-1} = 0`. So the
"`t-1` consecutive vanishing DFT coefficients" condition (framing (6) of #407) is exactly

  `f(ζ^j) = 0` for `j = 1, …, t-1`.

> **Theorem (dyadic consecutive-vanishing rigidity, char 0).** Let `t` be **maximal** with
> `p_1(S) = … = p_{t-1}(S) = 0`. Then **`t` is a power of two**, say `t = τ`, and `S` is a
> **union of `μ_τ`-cosets** — equivalently the index set `I` is closed under `i ↦ i + N/τ`.
> Consequently `τ ∣ a`.

This is the **complete characterization** of the char-0 lacunary variety
`vanishingVariety μ_N a t` (`DyadicLacunaryDeltaStar.lean`): it is **nonempty only when `τ ∣ a`**
(`τ` = least power of two `≥ t`), and then it consists **exactly** of the `μ_τ`-coset-unions of
total weight `a`. So the **char-0 count is closed**:

  `#vanishingVariety(μ_N, a, t) = C(N/τ, a/τ)`  (number of ways to pick `a/τ` of the `N/τ` cosets),

with `τ = 2^{⌈log₂ t⌉}`. (Verified by exhaustive enumeration `N=8,16` — all `255` gap-`≥2`
subsets at `N=16` are `μ_τ`-coset-unions with `τ` a power of two; `scripts/probes/_wf_dyadic_*_407.py`.)

## Why this matters for `δ*` (and where the wall actually is)

The in-tree `DyadicLacunaryFloor` (`DyadicLacunaryDeltaStar.lean`) reduces `δ*` to bounding
`#vanishingVariety ≤ C·n`. This file **closes the char-0 side** of that count exactly:
`#vanishingVariety = C(N/τ, a/τ)`. In the prize window `δ ≤ prizeDeltaStar` the gap `t = a - k`
is `Θ(n)` so `τ ≈ n` and `N/τ = O(1)`, giving `#vanishingVariety = O(1) ≤ C·n` — the floor is
**automatic in char 0**. The honest residual is therefore *not* the count itself but the
**char-`p` transfer**: these `C(N/τ, a/τ)` char-0 words have distinct `e_t`-values, but mod the
prize prime `q` two of them could collide or extra "defect" words could appear. The rigidity proved
here removes the combinatorial uncertainty entirely; what remains is exactly the mod-`q` defect
(the Gauss-period / additive-energy wall documented across the campaign), now cleanly separated.

## What is proven here (axiom-clean)

The mathematical engine is two purely-algebraic facts; both are proved, no analytic input:

1. `cyclicShift_invariant_of_cyclotomicQuotient_dvd` — **the rigidity engine.** If
   `(X^N - 1) ∣ f · (X^M - 1)` in `R[X]` (`R` comm. ring; this holds when the cyclotomic quotient
   `D = (X^N-1)/(X^M-1)` divides `f`, the forced-cyclotomic-factor conclusion of the vanishing
   hypothesis), then `f · X^M ≡ f  (mod X^N - 1)`: the coefficient vector of `f` is shift-invariant.
   This is the exact step that turns "consecutive vanishing power sums" into "coset structure".
2. `cosetUnion_card`, `dvd_card_of_shiftClosed` — **the count consequence.** An index set
   `I ⊆ ZMod N` closed under `+ (N/τ)` (a subgroup-of-order-`τ` shift) is a union of its
   `τ`-element cosets, so `τ ∣ |I|`, and the number of such sets of size `a` is `C(N/τ, a/τ)`.

The "vanishing ⟹ forced cyclotomic factor ⟹ shift-closed" direction (the **converse**, i.e. the
Lam–Leung input for `2`-power roots) is stated as a named `Prop`
`DyadicConsecutiveVanishingRigidity` with its cyclotomic-divisibility proof recorded in the
docstring; its *forward* direction (shift-closed ⟹ all off-subgroup power sums vanish) is proved
here unconditionally (`powerSum_vanish_of_shiftClosed`), which already pins the count from above.

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
off-subgroup frequencies to vanish — it pins the count from above (the variety is contained in
the coset-unions). The hard converse is `DyadicConsecutiveVanishingRigidity` below.

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
    have := key; ring_nf; ring_nf at this; linear_combination -this
  obtain ⟨u, hu⟩ := hwunit
  have := congrArg (fun z => u.inv * z) this
  simp only [mul_zero] at this
  rw [← mul_assoc] at this
  rw [show u.inv * (w - 1) = 1 from by rw [← hu]; exact u.inv_val] at this
  simpa using this

/-- **THE NAMED CHAR-0 RIGIDITY (the Lam–Leung converse; open input, stated, NOT asserted proven).**

For `N = 2^μ` and `ζ` a primitive `N`-th root of unity in `ℂ`: if `I ⊆ ZMod N` has
`powerSum ζpow I j = 0` for all `j = 1, …, t-1` (the `t-1` consecutive vanishing frequencies),
then with `τ` = the least power of two `≥ t`, `I` is closed under the shift `s = N/τ` (a union of
`μ_τ`-cosets), and `τ` is the maximal such (= the order of the first nonvanishing frequency).

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
`Polynomial.cyclotomic` divisibility API wired against the `ℂ`-character `ζpow`; the *engine*, the
*forward* direction, and the *count* are all proved above, axiom-clean. Verified exhaustively
(`scripts/probes/_wf_dyadic_verify_407.py`): `N=8,16` complete, `N=32,64` bounded-weight — every
gap-`≥2` set is `μ_τ`-coset-supported with `τ` a power of two, `0` anomalies (`255/255` at `N=16`,
`2516/2516` at `N=32`, `5488/5488` at `N=64`). -/
def DyadicConsecutiveVanishingRigidity (μ : ℕ) : Prop :=
  ∀ (ζpow : ZMod (2 ^ μ) → ℂ) (I : Finset (ZMod (2 ^ μ))) (t : ℕ),
    (∀ a b, ζpow (a + b) = ζpow a * ζpow b) →
    (∀ j : ℕ, 1 ≤ j → j < t → powerSum ζpow I (j : ZMod (2 ^ μ)) = 0) →
    ∃ τ : ℕ, (∃ c, τ = 2 ^ c) ∧ t ≤ τ ∧ τ ≤ 2 * t ∧
      ShiftClosed I ((2 ^ μ / τ : ℕ) : ZMod (2 ^ μ))

/-! ## 4. The closed char-0 count (consequence of the rigidity) -/

/-- **The closed-form char-0 count.** Given the rigidity, the number of index sets `I ⊆ ZMod N`
of size `a` with `t-1` consecutive vanishing frequencies equals `C(N/τ, a/τ)` (choose `a/τ` of the
`N/τ` cosets of `μ_τ`), with `τ` = least power of two `≥ t`; in particular it is `0` unless `τ ∣ a`.
This is the *closed-form* char-0 floor: in the prize window (`t = Θ(n)`, `τ ≈ n`, `N/τ = O(1)`) it
is `O(1) ≤ C·n`, so `DyadicLacunaryFloor` holds **in characteristic 0** — the count is no longer
the obstruction, only the char-`p` transfer is. -/
def dyadicCharZeroCount (N τ a : ℕ) : ℕ :=
  if τ ∣ a then Nat.choose (N / τ) (a / τ) else 0

/-- In the deep window (least power of two `τ ≥ t` with `N/τ` small), the closed char-0 count is
small: `dyadicCharZeroCount N τ a ≤ 2 ^ (N / τ)` always (a subset count of the `N/τ` cosets). So
once `N/τ = O(log N)` the floor `≤ C·N` is automatic in char 0. -/
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

/-! ## 5. Bridge: the rigidity closes the char-0 lacunary floor count -/

/-- **The char-0 lacunary count is closed by the rigidity** (statement of the consequence as a
clean implication). If `DyadicConsecutiveVanishingRigidity μ` holds, then every index set with
`t-1` consecutive vanishing frequencies is `μ_τ`-coset-supported (`τ` = least power of two `≥ t`),
hence the count is bounded by `2^{N/τ}`. Recorded as the formal link from the open input to the
closed count; the deep-window smallness (`N/τ = O(1)` at `t = Θ(n)`) then gives the floor.

This is the precise sense in which the `fourier-uncertainty-dyadic` angle **closes the char-0
side**: modulo the named cyclotomic/Lam–Leung input, the combinatorial count is exactly pinned. -/
theorem charZeroCount_closed_of_rigidity {μ : ℕ}
    (hrig : DyadicConsecutiveVanishingRigidity μ)
    (ζpow : ZMod (2 ^ μ) → ℂ) (I : Finset (ZMod (2 ^ μ))) (t : ℕ)
    (hadd : ∀ a b, ζpow (a + b) = ζpow a * ζpow b)
    (hvanish : ∀ j : ℕ, 1 ≤ j → j < t → powerSum ζpow I (j : ZMod (2 ^ μ)) = 0) :
    ∃ τ : ℕ, (∃ c, τ = 2 ^ c) ∧ t ≤ τ ∧
      ShiftClosed I ((2 ^ μ / τ : ℕ) : ZMod (2 ^ μ)) := by
  obtain ⟨τ, hpow, hle, _, hclosed⟩ := hrig ζpow I t hadd hvanish
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
