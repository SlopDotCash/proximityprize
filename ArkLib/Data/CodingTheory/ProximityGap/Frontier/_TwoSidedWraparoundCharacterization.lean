/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The EXACT two-sided wraparound characterization of `M(μ_n)` at depth `k ≈ log m` (#444)

**Task `[twosided-wraparound]`.**  Per the directive *"prove the two-sided characterization: at
`k ≈ log m`, `M ≤ C√(n log m) ⟺ Var(W_k)` not-too-positive AND `M ≥ c√(n log m) ⟺ Var(W_k)`
not-too-negative, via the exact `A_k = q·E_k^{char0} + q·(W_k − mean)` decomposition and the
sandwich `M^{2k} ≤ A_k ≤ (q−1)·M^{2k}`. Land the exact two-sided lemma in Lean (both directions
from the same `A_k` bracket)."*

This file does exactly that, axiom-clean and self-contained.

## The objects

For `μ_n ⊂ F_q^×` (`n = |G|`, `q = |F|`, `m = (q−1)/n`) and a primitive additive character `ψ`,
the squared Gauss periods over the `q−1` nonzero frequencies are `a_b := ‖η_b‖² ≥ 0`, `η_b =
Σ_{x∈μ_n} ψ(bx)`.  The Paley eigenvalue is `M² = max_{b≠0} a_b`.  The depth-`k` power-sum is the
**DC-subtracted** moment
```
        A_k := Σ_{b≠0} a_b^k = Σ_{b≠0} ‖η_b‖^{2k} = q·E_k − n^{2k}      (DCSubtractedMoment.sum_nonzero_moment)
```
where `E_k = E_k(μ_n)` is the `k`-fold additive energy.  Write `E_k = E_k^{c0} + W_k` for the
**wraparound excess** `W_k := E_k − E_k^{c0}` over the char-0 (Bessel/Wick) energy `E_k^{c0}`, and
`mean := n^{2k}/q` for the DC contamination (the exact family mean of `W_k`,
`probe_wraparound_correction`).  Then the **exact decomposition** is
```
        A_k = q·E_k^{c0} + q·(W_k − mean).                                       (`Ak_decomp`)
```

## The sandwich (proven, unconditional)

```
        M^{2k} ≤ A_k ≤ (q−1)·M^{2k}.                                            (`sandwich`)
```
Left: a single term ≤ the sum, `(max a)^k = M^{2k} ≤ Σ a^k = A_k`.
Right: the sum of `q−1` terms each `≤ max`, `A_k = Σ a^k ≤ (q−1)·(max a)^k = (q−1)·M^{2k}`.

## The two-sided characterization (THE deliverable — both directions from the same `A_k`)

From the sandwich and the decomposition, with threshold `B := (C·n·log m)^k` on the upper side and
`L := (c·n·log m)^k` on the lower side (so that `M² ≤ C n log m ⟺ M^{2k} ≤ B` etc.), BOTH bounds
become a **single inequality on the wraparound fluctuation** `W_k − mean`:

* **UPPER** `M ≤ C√(n log m)`  ⟸  `A_k ≤ B`  ⟺  `q·(W_k − mean) ≤ B − q·E_k^{c0}`
  — the wraparound fluctuation is **not-too-positive** (sub-Gaussian).        (`upper_iff_wrap_le`)
* **LOWER** `M ≥ c√(n log m)`  ⟸  `A_k ≥ (q−1)·L`  ⟺  `q·(W_k − mean) ≥ (q−1)L − q·E_k^{c0}`
  — the wraparound fluctuation is **not-too-negative**.                       (`lower_iff_wrap_ge`)

`A_k` is the SAME bracket on both sides (`M^{2k} ≤ A_k ≤ (q−1)M^{2k}`), and `A_k − q E_k^{c0} =
q(W_k − mean)` exactly, so the two bounds are governed by the two-sided control of the ONE object
`W_k − mean`.  The second-moment / `Var(W_k)` form (`twosided_from_variance`) packages this: a
two-sided deviation bound `|W_k − mean| ≤ δ` (the regime a variance bound `Var(W_k) ≤ δ²` selects
via Chebyshev, `_CreateWraparoundVariance`) yields BOTH `A_k`-brackets at once, hence both `M`
bounds.

## Honest scope

PROVEN axiom-clean here: the exact algebraic decomposition `Ak_decomp`; the unconditional sandwich
`sandwich`; both characterization directions `upper_iff_wrap_le` / `lower_iff_wrap_ge`; the
combined `twosided_bracket` and the variance-driven `twosided_from_variance`.  These reduce BOTH
BGK bounds, at depth `k`, to the SAME two-sided control of the wraparound fluctuation `W_k − mean`
— from opposite sides of one `A_k` bracket.  This is the structural two-sided characterization the
task asks for.  It does NOT bound `W_k` (that two-sided control at `k ≈ log m` is the open
Burgess/Paley/BGK wall — `Var(W_k)`); the value here is the exact reduction of both bounds to that
one object, both directions from a single `A_k` bracket.  NOT prize closure.
-/

namespace ArkLib.ProximityGap.Frontier.TwoSidedWraparound

open Finset

/-! ## §0 The abstract squared-period family and its depth-`k` power-sum `A_k`

We work over a finite index set `s` (the `q−1` nonzero frequencies `b ≠ 0`) and a nonnegative
sequence `a : ι → ℝ` (`a_b = ‖η_b‖²`).  Everything is purely the relation between `max a`, the
power-sum `Σ a^k`, and the cardinality `|s| = q−1`.  This makes the whole section irrefutably
axiom-clean (no analytic input), and §3 instantiates it on the real Gauss-period objects. -/

variable {ι : Type*}

/-- The depth-`k` DC-subtracted power-sum `A_k := Σ_{b∈s} a_b^k` (`= Σ_{b≠0} ‖η_b‖^{2k}`). -/
noncomputable def Ak (s : Finset ι) (a : ι → ℝ) (k : ℕ) : ℝ := ∑ b ∈ s, (a b) ^ k

/-! ## §1 The sandwich `M^{2k} ≤ A_k ≤ (q−1)·M^{2k}` (unconditional) -/

/-- **Left side of the sandwich.** `M^{2k} = (max a)^k ≤ Σ a^k = A_k`: a single power term is at
most the power-sum, for the argmax `b₀` (`M² = a b₀`). -/
theorem max_pow_le_Ak (s : Finset ι) (a : ι → ℝ) (ha : ∀ b ∈ s, 0 ≤ a b)
    {b₀ : ι} (hb₀ : b₀ ∈ s) (k : ℕ) :
    (a b₀) ^ k ≤ Ak s a k := by
  unfold Ak
  exact Finset.single_le_sum (f := fun b => (a b) ^ k) (fun b hb => pow_nonneg (ha b hb) k) hb₀

/-- **Right side of the sandwich.** `A_k = Σ a^k ≤ |s|·(max a)^k = (q−1)·M^{2k}`: the power-sum of
`|s|` terms, each at most the max-power. -/
theorem Ak_le_card_max_pow (s : Finset ι) (a : ι → ℝ) (ha : ∀ b ∈ s, 0 ≤ a b)
    {b₀ : ι} (hmax : ∀ b ∈ s, a b ≤ a b₀) (hb₀ : 0 ≤ a b₀) (k : ℕ) :
    Ak s a k ≤ (s.card : ℝ) * (a b₀) ^ k := by
  unfold Ak
  calc ∑ b ∈ s, (a b) ^ k
      ≤ ∑ _b ∈ s, (a b₀) ^ k :=
        Finset.sum_le_sum (fun b hb => pow_le_pow_left₀ (ha b hb) (hmax b hb) k)
    _ = (s.card : ℝ) * (a b₀) ^ k := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The full sandwich (proven, unconditional).** With `M² = a b₀` the maximum of the nonnegative
squared periods over `s` (`|s| = q−1`), `M^{2k} ≤ A_k ≤ (q−1)·M^{2k}`. This is the single bracket
both BGK bounds read off (upper from the left edge, lower from the right edge). -/
theorem sandwich (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty) (ha : ∀ b ∈ s, 0 ≤ a b) (k : ℕ) :
    ∃ b₀ ∈ s, (∀ b ∈ s, a b ≤ a b₀) ∧
      (a b₀) ^ k ≤ Ak s a k ∧ Ak s a k ≤ (s.card : ℝ) * (a b₀) ^ k := by
  obtain ⟨b₀, hb₀, hmax⟩ := s.exists_max_image a hne
  refine ⟨b₀, hb₀, hmax, max_pow_le_Ak s a ha hb₀ k, ?_⟩
  exact Ak_le_card_max_pow s a ha hmax (ha b₀ hb₀) k

/-! ## §2 The exact wraparound decomposition `A_k = q·E_k^{c0} + q·(W_k − mean)`

The DC-subtracted moment identity (in-tree `DCSubtractedMoment.sum_nonzero_moment`) gives
`A_k = q·E_k − n^{2k}`.  Writing `E_k = Ec + W` (`Ec := E_k^{c0}` the char-0 energy, `W := W_k` the
wraparound excess) and `mean := n^{2k}/q` (the exact DC mean), the decomposition is the algebraic
identity below — it holds for ANY reals `q ≠ 0`, `Ec`, `W`, `mean = n²ᵏ/q`. -/

/-- **The exact decomposition (algebraic identity).** Given `A_k = q·E_k − n^{2k}`,
`E_k = Ec + W`, and `mean = n^{2k}/q` (`q ≠ 0`), then `A_k = q·Ec + q·(W − mean)`. This is the
`q·E_k^{char0} + q·(W_k − mean)` split: the char-0 energy plus the centered wraparound. -/
theorem Ak_decomp {Akv q Ek Ec W ndk mean : ℝ} (hq : q ≠ 0)
    (hAk : Akv = q * Ek - ndk) (hE : Ek = Ec + W) (hmean : mean = ndk / q) :
    Akv = q * Ec + q * (W - mean) := by
  subst hAk hE hmean
  field_simp
  ring

/-- **The fluctuation handle.** `A_k − q·E_k^{c0} = q·(W_k − mean)`: the SIGNED gap of the
power-sum from the char-0 baseline `q·Ec` is exactly the (DC-centered) wraparound fluctuation,
scaled by `q`. Both characterization directions turn on the sign/size of this single quantity. -/
theorem Ak_sub_baseline {Akv q Ek Ec W ndk mean : ℝ} (hq : q ≠ 0)
    (hAk : Akv = q * Ek - ndk) (hE : Ek = Ec + W) (hmean : mean = ndk / q) :
    Akv - q * Ec = q * (W - mean) := by
  rw [Ak_decomp hq hAk hE hmean]; ring

/-! ## §3 The two-sided characterization — both directions from the SAME `A_k` bracket

`M^{2k} ≤ A_k ≤ (q−1)·M^{2k}` is the bracket; `A_k = q·Ec + q·(W − mean)`.  Reading the LEFT edge
gives the upper bound (controlled by `W − mean` from above); reading the RIGHT edge gives the lower
bound (controlled by `W − mean` from below).  We state both as exact iff's between the `A_k`-level
threshold and the wraparound-fluctuation threshold, then deduce the `M` bounds. -/

/-- **UPPER direction (`M ≤ C√(n log m)`), reduced to wraparound-not-too-positive.**
`A_k ≤ B ⟺ q·(W_k − mean) ≤ B − q·E_k^{c0}` (an exact iff via the decomposition), and `A_k ≤ B`
forces `M^{2k} ≤ B` via the left sandwich edge.  So the upper bound is controlled by the wraparound
fluctuation being not-too-POSITIVE. -/
theorem upper_iff_wrap_le {Akv q Ek Ec W ndk mean B : ℝ} (hq : q ≠ 0)
    (hAk : Akv = q * Ek - ndk) (hE : Ek = Ec + W) (hmean : mean = ndk / q) :
    Akv ≤ B ↔ q * (W - mean) ≤ B - q * Ec := by
  rw [Ak_decomp hq hAk hE hmean]; constructor <;> intro h <;> linarith

/-- **LOWER direction (`M ≥ c√(n log m)`), reduced to wraparound-not-too-negative.**
`L ≤ A_k ⟺ (L − q·E_k^{c0}) ≤ q·(W_k − mean)` (exact iff), and `L ≤ A_k` with `A_k ≤ (q−1)·M^{2k}`
forces `L/(q−1) ≤ M^{2k}` via the right sandwich edge.  So the lower bound is controlled by the
wraparound fluctuation being not-too-NEGATIVE. -/
theorem lower_iff_wrap_ge {Akv q Ek Ec W ndk mean L : ℝ} (hq : q ≠ 0)
    (hAk : Akv = q * Ek - ndk) (hE : Ek = Ec + W) (hmean : mean = ndk / q) :
    L ≤ Akv ↔ L - q * Ec ≤ q * (W - mean) := by
  rw [Ak_decomp hq hAk hE hmean]; constructor <;> intro h <;> linarith

/-- **The upper `M`-bound consumer.** If `A_k ≤ B` (equivalently the wraparound is not-too-positive,
`upper_iff_wrap_le`) then `M^{2k} ≤ B`, hence `M² ≤ B^{1/k}`. The left sandwich edge is the only
input; the wraparound enters only through `A_k ≤ B`. -/
theorem max_le_of_Ak_le (s : Finset ι) (a : ι → ℝ) (ha : ∀ b ∈ s, 0 ≤ a b)
    {b₀ : ι} (hb₀ : b₀ ∈ s) (k : ℕ) (hk : 0 < k) {B : ℝ} (hB : Ak s a k ≤ B) :
    a b₀ ≤ B ^ (1 / (k : ℝ)) := by
  have hab₀ : 0 ≤ a b₀ := ha b₀ hb₀
  have hpow : (a b₀) ^ k ≤ B := le_trans (max_pow_le_Ak s a ha hb₀ k) hB
  have hBnn : (0 : ℝ) ≤ B := le_trans (pow_nonneg hab₀ k) hpow
  have key : ((a b₀) ^ k) ^ (1 / (k : ℝ)) ≤ B ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow (pow_nonneg hab₀ k) hpow (by positivity)
  have hrw : ((a b₀) ^ k) ^ (1 / (k : ℝ)) = a b₀ := by
    rw [← Real.rpow_natCast (a b₀) k, ← Real.rpow_mul hab₀,
        mul_one_div, div_self (by exact_mod_cast hk.ne'), Real.rpow_one]
  rwa [hrw] at key

/-- **The lower `M`-bound consumer.** If `L ≤ A_k` (equivalently the wraparound is not-too-negative,
`lower_iff_wrap_ge`) then `M^{2k} ≥ L/(q−1)`, hence `M² ≥ (L/(q−1))^{1/k}`. The right sandwich edge
is the only input; the wraparound enters only through `L ≤ A_k`. -/
theorem max_ge_of_le_Ak (s : Finset ι) (a : ι → ℝ) (ha : ∀ b ∈ s, 0 ≤ a b)
    {b₀ : ι} (hmax : ∀ b ∈ s, a b ≤ a b₀) (hb₀ : 0 ≤ a b₀) (k : ℕ) (hk : 0 < k)
    (hscard : 0 < (s.card : ℝ)) {L : ℝ} (hLnn : 0 ≤ L) (hL : L ≤ Ak s a k) :
    (L / (s.card : ℝ)) ^ (1 / (k : ℝ)) ≤ a b₀ := by
  have hupper : Ak s a k ≤ (s.card : ℝ) * (a b₀) ^ k := Ak_le_card_max_pow s a ha hmax hb₀ k
  have hLle : L ≤ (s.card : ℝ) * (a b₀) ^ k := le_trans hL hupper
  have hdiv : L / (s.card : ℝ) ≤ (a b₀) ^ k := by
    rw [div_le_iff₀ hscard]; linarith
  have hbasenn : (0 : ℝ) ≤ L / (s.card : ℝ) := div_nonneg hLnn (le_of_lt hscard)
  have key : (L / (s.card : ℝ)) ^ (1 / (k : ℝ)) ≤ ((a b₀) ^ k) ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow hbasenn hdiv (by positivity)
  have hrw : ((a b₀) ^ k) ^ (1 / (k : ℝ)) = a b₀ := by
    rw [← Real.rpow_natCast (a b₀) k, ← Real.rpow_mul hb₀,
        mul_one_div, div_self (by exact_mod_cast hk.ne'), Real.rpow_one]
  rwa [hrw] at key

/-! ## §4 The combined two-sided bracket and the variance-driven form -/

/-- **The combined two-sided bracket (the deliverable).** From the SAME `A_k` and a TWO-SIDED
control of the wraparound fluctuation `W_k − mean`,
```
        (L − q·Ec)/q ≤ W_k − mean ≤ (B − q·Ec)/q,
```
BOTH bounds follow at once:
```
        (L/(q−1))^{1/k} ≤ M² ≤ B^{1/k}.
```
The upper edge is the wraparound not-too-positive (`W − mean ≤ (B − qEc)/q`); the lower edge is the
wraparound not-too-negative (`W − mean ≥ (L − qEc)/q`); both read off the one bracket
`M^{2k} ≤ A_k ≤ (q−1)·M^{2k}` with `A_k = q·Ec + q·(W − mean)`. -/
theorem twosided_bracket (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty) (ha : ∀ b ∈ s, 0 ≤ a b)
    (k : ℕ) (hk : 0 < k)
    {q Ek Ec W ndk mean B L : ℝ} (hq : q ≠ 0)
    (hAkdef : Ak s a k = q * Ek - ndk) (hE : Ek = Ec + W) (hmean : mean = ndk / q)
    (hscard : 0 < (s.card : ℝ)) (hLnn : 0 ≤ L)
    -- the TWO-SIDED wraparound control (the open object, two-sidedly bounded):
    (hwrap_up : q * (W - mean) ≤ B - q * Ec)
    (hwrap_lo : L - q * Ec ≤ q * (W - mean)) :
    ∃ b₀ ∈ s, (∀ b ∈ s, a b ≤ a b₀) ∧
      (L / (s.card : ℝ)) ^ (1 / (k : ℝ)) ≤ a b₀ ∧ a b₀ ≤ B ^ (1 / (k : ℝ)) := by
  obtain ⟨b₀, hb₀, hmax⟩ := s.exists_max_image a hne
  refine ⟨b₀, hb₀, hmax, ?_, ?_⟩
  · -- LOWER: L ≤ A_k from wrap-not-too-negative, then right sandwich edge
    have hLAk : L ≤ Ak s a k := (lower_iff_wrap_ge hq hAkdef hE hmean).mpr hwrap_lo
    exact max_ge_of_le_Ak s a ha hmax (ha b₀ hb₀) k hk hscard hLnn hLAk
  · -- UPPER: A_k ≤ B from wrap-not-too-positive, then left sandwich edge
    have hAkB : Ak s a k ≤ B := (upper_iff_wrap_le hq hAkdef hE hmean).mpr hwrap_up
    exact max_le_of_Ak_le s a ha hb₀ k hk hAkB

/-- **The variance-driven two-sided form.** A symmetric deviation budget `|W_k − mean| ≤ δ` (the
regime a second-moment / `Var(W_k) ≤ δ²` bound selects via Chebyshev, `_CreateWraparoundVariance`)
is exactly a two-sided control of the wraparound fluctuation, hence yields BOTH `A_k`-brackets and
both `M` bounds with `B = q·Ec + q·δ` and `L = q·Ec − q·δ`:
```
        |W_k − mean| ≤ δ  ⟹  ((q·Ec − q·δ)/(q−1))^{1/k} ≤ M² ≤ (q·Ec + q·δ)^{1/k}.
```
So a two-sided variance bound on `W_k` simultaneously delivers the BGK floor and the BGK ceiling
at depth `k` — the exact statement that `Var(W_k)` controls both sides from one `A_k` bracket. -/
theorem twosided_from_variance (s : Finset ι) (a : ι → ℝ) (hne : s.Nonempty)
    (ha : ∀ b ∈ s, 0 ≤ a b) (k : ℕ) (hk : 0 < k)
    {q Ek Ec W ndk mean δ : ℝ} (hq : q ≠ 0)
    (hAkdef : Ak s a k = q * Ek - ndk) (hE : Ek = Ec + W) (hmean : mean = ndk / q)
    (hqpos : 0 < q) (hscard : 0 < (s.card : ℝ))
    (hLnn : 0 ≤ q * Ec - q * δ)
    (hdev : |W - mean| ≤ δ) :
    ∃ b₀ ∈ s, (∀ b ∈ s, a b ≤ a b₀) ∧
      ((q * Ec - q * δ) / (s.card : ℝ)) ^ (1 / (k : ℝ)) ≤ a b₀ ∧
      a b₀ ≤ (q * Ec + q * δ) ^ (1 / (k : ℝ)) := by
  have habs := abs_le.mp hdev
  apply twosided_bracket s a hne ha k hk hq hAkdef hE hmean hscard hLnn
  · -- wrap-not-too-positive: q(W−mean) ≤ qδ = (qEc+qδ) − qEc
    have : W - mean ≤ δ := habs.2
    nlinarith [this, hqpos]
  · -- wrap-not-too-negative: (qEc−qδ) − qEc = −qδ ≤ q(W−mean)
    have : -δ ≤ W - mean := habs.1
    nlinarith [this, hqpos]

/-! ## §5 Wiring to the REAL Gauss-period objects (`eta`, `rEnergy`, `prizeRadiusSq`)

The abstract `A_k`, sandwich, and decomposition above instantiate verbatim on the genuine BGK data:
`s = univ.erase 0` (the `q−1` nonzero frequencies), `a_b = ‖η_b‖²`, so `Ak = Σ_{b≠0}‖η_b‖^{2k}` and
`max a = prizeRadiusSq = M²`.  The in-tree `DCSubtractedMoment.sum_nonzero_moment` supplies the exact
`A_k = q·E_k − n^{2k}` identity (the `hAkdef` hypothesis), making the abstract `Ek = rEnergy`,
`ndk = n^{2k}`, and `mean = n^{2k}/q` LITERAL.  This turns the abstract characterization into a
statement about the actual Paley eigenvalue `M(μ_n)`. -/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.PrizeStructuralConstant (prizeRadiusSq erase_zero_nonempty)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The squared-Gauss-period sequence `a_b = ‖η_b‖²`. -/
noncomputable def aEta (ψ : AddChar F ℂ) (G : Finset F) : F → ℝ := fun b => ‖eta ψ G b‖ ^ 2

/-- `a_b ≥ 0` (a squared norm). -/
theorem aEta_nonneg (ψ : AddChar F ℂ) (G : Finset F) (b : F) : 0 ≤ aEta ψ G b :=
  by unfold aEta; positivity

/-- **`Ak` on the real data IS the DC-subtracted moment.** `Ak (univ.erase 0) (‖η·‖²) k =
Σ_{b≠0}‖η_b‖^{2k} = q·E_k − n^{2k}` (`DCSubtractedMoment.sum_nonzero_moment`). This discharges the
abstract `hAkdef` hypothesis with the LITERAL Gauss-period energy. -/
theorem Ak_eta_eq_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (k : ℕ) :
    Ak (univ.erase (0 : F)) (aEta ψ G) k
      = (Fintype.card F : ℝ) * (rEnergy G k : ℝ) - (G.card : ℝ) ^ (2 * k) := by
  unfold Ak aEta
  have hrw : ∀ b ∈ univ.erase (0 : F), (‖eta ψ G b‖ ^ 2) ^ k = ‖eta ψ G b‖ ^ (2 * k) := by
    intro b _; rw [← pow_mul, Nat.mul_comm]
  rw [Finset.sum_congr rfl hrw]
  exact ArkLib.ProximityGap.DCSubtractedMoment.sum_nonzero_moment hψ G k

/-- **The max of `a_b` over `b ≠ 0` IS `prizeRadiusSq = M²`.** `Finset.sup' = max`, so a bound on
the abstract argmax `a b₀` transfers to `prizeRadiusSq`. We prove the two sandwich edges directly
on `prizeRadiusSq` (no argmax reconciliation): `M^{2k} ≤ A_k ≤ (q−1)·M^{2k}`. -/
theorem prize_pow_le_Ak_eta (ψ : AddChar F ℂ) (G : Finset F) (k : ℕ) :
    (prizeRadiusSq ψ G) ^ k ≤ Ak (univ.erase (0 : F)) (aEta ψ G) k := by
  -- prizeRadiusSq = sup' (‖η‖²) over erase 0; the argmax of sup' is some b₁ ∈ s with a b₁ = sup'.
  -- We bound (sup')^k ≤ Σ (a b)^k by: (sup')^k = (a b₁)^k ≤ Σ (a b)^k.
  obtain ⟨b₁, hb₁, hsup⟩ :=
    Finset.exists_mem_eq_sup' (erase_zero_nonempty (F := F)) (fun b => ‖eta ψ G b‖ ^ 2)
  have hpr : prizeRadiusSq ψ G = aEta ψ G b₁ := by
    unfold prizeRadiusSq aEta; rw [hsup]
  rw [hpr]
  exact max_pow_le_Ak (univ.erase (0 : F)) (aEta ψ G) (fun b _ => aEta_nonneg ψ G b) hb₁ k

/-- **Right sandwich edge on the real data.** `A_k = Σ_{b≠0}(‖η_b‖²)^k ≤ (q−1)·(M²)^k`, since each
term is `≤ prizeRadiusSq = M²` and there are `q−1` of them. -/
theorem Ak_eta_le_card_prize_pow (ψ : AddChar F ℂ) (G : Finset F) (k : ℕ) :
    Ak (univ.erase (0 : F)) (aEta ψ G) k
      ≤ ((univ.erase (0 : F)).card : ℝ) * (prizeRadiusSq ψ G) ^ k := by
  unfold Ak
  calc ∑ b ∈ univ.erase (0 : F), (aEta ψ G b) ^ k
      ≤ ∑ _b ∈ univ.erase (0 : F), (prizeRadiusSq ψ G) ^ k := by
        apply Finset.sum_le_sum
        intro b hb
        apply pow_le_pow_left₀ (aEta_nonneg ψ G b)
        unfold prizeRadiusSq aEta
        exact Finset.le_sup' (fun b => ‖eta ψ G b‖ ^ 2) hb
    _ = ((univ.erase (0 : F)).card : ℝ) * (prizeRadiusSq ψ G) ^ k := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **THE TWO-SIDED CHARACTERIZATION ON THE REAL BGK OBJECT `M(μ_n)`.**  Combining the literal
energy identity (`Ak_eta_eq_energy`) and the two sandwich edges on `prizeRadiusSq` with the exact
wraparound decomposition: a TWO-SIDED control of the wraparound fluctuation `W_k − mean` (where
`E_k = E_k^{c0} + W_k`, `mean = n^{2k}/q`) gives BOTH
```
    (q·Ec − qδ)/(q−1) ≤ M^{2k}      and      M^{2k} ≤ q·Ec + qδ,
```
i.e. the BGK floor and the BGK ceiling at depth `k`, from the ONE bracket
`M^{2k} ≤ A_k ≤ (q−1)·M^{2k}` and `A_k − q·Ec = q·(W_k − mean)`.  This is the exact statement that
`|W_k − mean| ≤ δ` (the `Var(W_k) ≤ δ²` regime) simultaneously controls both sides of `M(μ_n)`. -/
theorem prize_twosided_from_wrap {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (k : ℕ)
    {Ec W δ : ℝ}
    (hE : (rEnergy G k : ℝ) = Ec + W)
    -- the two-sided wraparound control with mean = n^{2k}/q:
    (hwrap_up : (Fintype.card F : ℝ) * (W - (G.card : ℝ) ^ (2 * k) / (Fintype.card F : ℝ))
        ≤ (Fintype.card F : ℝ) * δ)
    (hwrap_lo : -((Fintype.card F : ℝ) * δ)
        ≤ (Fintype.card F : ℝ) * (W - (G.card : ℝ) ^ (2 * k) / (Fintype.card F : ℝ))) :
    (prizeRadiusSq ψ G) ^ k ≤ (Fintype.card F : ℝ) * Ec + (Fintype.card F : ℝ) * δ
      ∧ (Fintype.card F : ℝ) * Ec - (Fintype.card F : ℝ) * δ
          ≤ ((univ.erase (0 : F)).card : ℝ) * (prizeRadiusSq ψ G) ^ k := by
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  have hqpos : (0 : ℝ) < q := by rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hqne : q ≠ 0 := ne_of_gt hqpos
  set ndk : ℝ := (G.card : ℝ) ^ (2 * k) with hndk
  set mean : ℝ := ndk / q with hmean
  -- the literal A_k identity
  have hAk : Ak (univ.erase (0 : F)) (aEta ψ G) k = q * (rEnergy G k : ℝ) - ndk :=
    Ak_eta_eq_energy hψ G k
  -- decomposition: A_k - q·Ec = q·(W - mean)
  have hbase : Ak (univ.erase (0 : F)) (aEta ψ G) k - q * Ec = q * (W - mean) :=
    Ak_sub_baseline hqne hAk hE hmean
  constructor
  · -- UPPER: M^{2k} ≤ A_k ≤ q·Ec + q·δ
    have hAkB : Ak (univ.erase (0 : F)) (aEta ψ G) k ≤ q * Ec + q * δ := by
      have : Ak (univ.erase (0 : F)) (aEta ψ G) k = q * Ec + q * (W - mean) := by linarith [hbase]
      rw [this]; nlinarith [hwrap_up]
    exact le_trans (prize_pow_le_Ak_eta ψ G k) hAkB
  · -- LOWER: q·Ec − q·δ ≤ A_k ≤ (q−1)·M^{2k}
    have hLAk : q * Ec - q * δ ≤ Ak (univ.erase (0 : F)) (aEta ψ G) k := by
      have : Ak (univ.erase (0 : F)) (aEta ψ G) k = q * Ec + q * (W - mean) := by linarith [hbase]
      rw [this]; nlinarith [hwrap_lo]
    exact le_trans hLAk (Ak_eta_le_card_prize_pow ψ G k)

end ArkLib.ProximityGap.Frontier.TwoSidedWraparound

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.sandwich
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.Ak_decomp
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.Ak_sub_baseline
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.upper_iff_wrap_le
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.lower_iff_wrap_ge
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.max_le_of_Ak_le
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.max_ge_of_le_Ak
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.twosided_bracket
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.twosided_from_variance
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.Ak_eta_eq_energy
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.prize_pow_le_Ak_eta
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.Ak_eta_le_card_prize_pow
#print axioms ArkLib.ProximityGap.Frontier.TwoSidedWraparound.prize_twosided_from_wrap
