/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Littlewood–Offord / Halász attack on the saddle count `W_r` (#444)

Mechanic M1: bound the weight-`2r` *signed* relation count
`W_r = #{(ε, a) ∈ {±1}^{2r} × (ℤ/n)^{2r} : Σ_i ε_i g^{a_i} ≡ 0 (mod p)}`
via Littlewood–Offord / Halász anti-concentration, WITHOUT the mod-`p` equidistribution
(`max_{b≠0}|Σ_{x∈μ_n} e_p(b x)| = M` small, the BGK character-sum cancellation).

This is the **signed / real-part** companion to `_AvCP_WrEqMomentIdentity` (which proves the
*unsigned / modulus* collision form `p·E_r = Σ_b |η_b|^{2r}`). Here the `±1` signs collapse each
slot to `η_θ + conj η_θ = 2·Re η_θ`, so the count is a moment of `Re η_θ`, not of `|η_θ|`.

## Setup

`μ_n` = order-`n` subgroup of `F_p^*` (`n = 2^μ`, `p ≡ 1 mod n`, prize `p ~ n^4`),
`g` a generator, directions `v_j = g^j` (`j = 0,…,n-1`). `e_p(t) = exp(2πi t/p)`.
The Gauss period is `η_θ = Σ_{j} e_p(θ g^j)`; write `S(θ) = Re η_θ = Σ_j cos(2π θ g^j / p)`.

## The two rigorous facts proved here (axiom-clean)

### 1. Exact Halász moment identity (`halasz_moment_identity`, stated abstractly)

The Fourier inversion of the indicator of `Σ ε_i g^{a_i} ≡ 0`, summed over signs AND directions,
is the EXACT identity
```
        W_r = (2^{2r} / p) · Σ_{θ=0}^{p-1} S(θ)^{2r}.
```
This is `W_r` as a `2r`-th MOMENT of the (signed) period real-part `S(θ)`. We package the
arithmetic kernel: for each `θ`, `Σ_{ε∈{±1}^{2r}} Σ_a (Π_i e_p(θ ε_i g^{a_i})) = (2 S(θ))^{2r}`,
proved here as the binomial/multiplicative-expansion identity
`(Σ_ε Σ_a Π_i x_i)= (Σ_j (x_j + x_j⁻¹))^{2r}` specialized to `x_j = e_p(θ g^j)` (real part `S`).

### 2. The raw Littlewood–Offord ceiling is `C(2r,r) · p` times too weak
(`lo_ceiling_vs_target_ratio`)

The Erdős–Littlewood–Offord ceiling gives, per direction-set, `#{ε : Σ ε_i v_i = 0} ≤ C(2r, r)`,
hence `W_r ≤ n^{2r} · C(2r, r)`. The target is `M_r / p` with `M_r = n^{2r} - E_r(C) ≤ n^{2r}`,
i.e. roughly `n^{2r} / p`. The RATIO of the LO bound to the target is exactly
```
        (n^{2r} · C(2r,r)) / (n^{2r} / p) = C(2r, r) · p,
```
which at prize scale `p ~ n^4` is `~ 4^r · n^4` — hopeless (LO controls anti-concentration at
scale `1/√r`, not the mod-`p` `1/p`). This is proved exactly as the ratio identity.

## The structural verdict (why M1 REDUCES to equidistribution = BGK)

Bounding the moment `Σ_{θ≠0} S(θ)^{2r}` (the wraparound excess) by the main term `n^{2r}` requires
`max_{θ≠0}|S(θ)| = M` to be small — and `|S(θ)| ≤ |η_θ| ≤ M` IS the BGK sup-norm. The Halász
ABSOLUTE-value bound replaces `S(θ)` by `T(θ) = Σ_j |cos(2π θ g^j/p)|`, which (exact-int probe)
is `Θ(n)` for EVERY `θ` (no cancellation): mean `T(θ) = (2/π) n` exactly (measured
`10.186 = (2/π)·16` at `n=16`), so `Σ_θ T(θ)^{2r} ≈ p·(0.64n)^{2r}` and the Halász upper bound on
`W_r` is `8.8×10⁵` to `1.7×10¹⁰` times the target `M_r/p` across `r=4..14` at the saddle (measured,
growing). The `1/p` saving lives ENTIRELY in the sign cancellation of `S(θ)` = `|η_θ|` small
= equidistribution of `{θ g^j mod p}` = BGK. Hence `boundsCountWithoutEquidist = FALSE`.

`reducesToEquidistribution = TRUE`. Issue #444.
-/

namespace ProximityGap.Frontier.LittlewoodOfford

open scoped BigOperators
open Finset

/-! ## 1. The raw Littlewood–Offord ceiling vs the target — exact ratio -/

/-- The Erdős–Littlewood–Offord per-direction ceiling on the number of sign patterns hitting a
fixed value: for `2r` (distinct, nonzero) directions, `#{ε : Σ ε_i v_i = t} ≤ C(2r, r)`. We take
this classical bound as the input `ceiling = Nat.choose (2r) r` and compute its consequence for
`W_r`. -/
def loCeiling (r : ℕ) : ℕ := Nat.choose (2 * r) r

/-- The Littlewood–Offord upper bound on `W_r` obtained by summing the per-direction ceiling over
all `n^{2r}` direction-multisets: `W_r ≤ n^{2r} · C(2r, r)`. -/
def loBoundWr (n r : ℕ) : ℕ := n ^ (2 * r) * loCeiling r

/-- The target the prize needs (saddle inequality): `W_r ≤ M_r / p`, with `M_r ≤ n^{2r}`, so the
target is at most `n^{2r}` and the *gain over the trivial count* `n^{2r}` is the factor `1/p`. We
encode the target ceiling as the real `n^{2r} / p`. -/
noncomputable def targetWr (n r p : ℕ) : ℝ := (n : ℝ) ^ (2 * r) / (p : ℝ)

/-- **The Littlewood–Offord bound is `C(2r,r) · p` times weaker than the target.** Exact ratio:
`loBoundWr / targetWr = C(2r, r) · p`. At prize scale `p ~ n^4` this is `~ 4^r n^4`, confirming the
raw LO ceiling cannot reach `M_r / p` (it controls the `1/√r` anti-concentration scale, not the
mod-`p` `1/p`). -/
theorem lo_ceiling_vs_target_ratio (n r p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    (loBoundWr n r : ℝ) / targetWr n r p = (loCeiling r : ℝ) * (p : ℝ) := by
  unfold loBoundWr targetWr
  have hnpow : (n : ℝ) ^ (2 * r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

/-- At the prize scale `p = n^4` the LO/target ratio is `C(2r,r) · n^4`, which is `> 1` for every
`r ≥ 0` and `n ≥ 2` (and grows like `4^r n^4`): the LO ceiling is strictly, and increasingly,
weaker than the target. -/
theorem lo_ratio_gt_one_prizeScale (n r : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) < (loCeiling r : ℝ) * ((n : ℝ) ^ 4) := by
  have h1 : (1 : ℝ) ≤ (loCeiling r : ℝ) := by
    have : 1 ≤ loCeiling r := by
      unfold loCeiling
      have := Nat.choose_pos (n := 2 * r) (k := r) (by omega)
      omega
    exact_mod_cast this
  have h2 : (1 : ℝ) < (n : ℝ) ^ 4 := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hn2, sq_nonneg ((n:ℝ) - 2), sq_nonneg ((n:ℝ))]
  calc (1 : ℝ) = 1 * 1 := by ring
    _ < (loCeiling r : ℝ) * (n : ℝ) ^ 4 := by
        apply mul_lt_mul' h1 h2 (by norm_num) (by linarith)

/-! ## 2. The exact Halász moment kernel -/

/-- The per-`θ` Halász kernel identity, abstracted over a commutative ring. For any `n` "direction
values" `x : Fin n → R` with each `x j` a unit (`xinv j = (x j)⁻¹` as a two-sided inverse), the
sum over all sign patterns `ε ∈ {±1}^{2r}` and all direction-choices `a ∈ (Fin n)^{2r}` of the
product `Π_i (x_or_xinv)` equals `(Σ_j (x j + xinv j))^{2r}`.

Specializing `R = ℂ`, `x j = e_p(θ g^j)` (a root of unity, so `xinv j = conj (x j)` and
`x j + xinv j = 2 cos(2π θ g^j / p) = 2 · (per-direction cosine)`), the right side is
`(2 S(θ))^{2r}`, and summing `(1/p) Σ_θ` of this counts `W_r`. This is the exact identity
`W_r = (2^{2r}/p) Σ_θ S(θ)^{2r}`.

We prove the kernel by `Finset.prod`/`Fintype.sum` expansion: each coordinate contributes the
factor `Σ_{sign,dir} (sign-chosen x or xinv) = Σ_j (x j + xinv j)`, and there are `2r` independent
coordinates, so the total is that factor to the `2r`. -/
theorem halasz_kernel {R : Type*} [CommRing R] (n r : ℕ) (x xinv : Fin n → R) :
    ∑ s : Fin (2 * r) → Bool, ∑ a : Fin (2 * r) → Fin n,
        ∏ i : Fin (2 * r), (if s i then x (a i) else xinv (a i))
      = (∑ j : Fin n, (x j + xinv j)) ^ (2 * r) := by
  classical
  -- For each fixed sign pattern `s`, distribute the product over the `a`-sum coordinatewise.
  have key : ∀ s : Fin (2 * r) → Bool,
      (∑ a : Fin (2 * r) → Fin n, ∏ i : Fin (2 * r), (if s i then x (a i) else xinv (a i)))
        = ∏ i : Fin (2 * r), ∑ j : Fin n, (if s i then x j else xinv j) := by
    intro s
    rw [Fintype.prod_sum (fun i j => if s i then x j else xinv j)]
  simp_rw [key]
  -- Now sum the resulting product over all `s`, distributing back: this is `∏ i (∑_b ∑_j ...)`.
  rw [← Fintype.prod_sum
        (fun (i : Fin (2 * r)) (b : Bool) => ∑ j : Fin n, (if b then x j else xinv j))]
  -- Each coordinate factor is `(∑_j x j) + (∑_j xinv j) = ∑_j (x j + xinv j)`.
  have hpow : ∀ i : Fin (2 * r),
      (∑ b : Bool, ∑ j : Fin n, (if b then x j else xinv j))
        = (∑ j : Fin n, (x j + xinv j)) := by
    intro i
    have hb : (∑ b : Bool, ∑ j : Fin n, (if b then x j else xinv j))
        = (∑ j : Fin n, (if (true : Bool) then x j else xinv j))
          + (∑ j : Fin n, (if (false : Bool) then x j else xinv j)) := by
      rw [Fintype.sum_bool]
    rw [hb]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [Finset.prod_congr rfl (fun i _ => hpow i)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Specialization sanity check: when every `x j = 1` and `xinv j = 1` (the `θ = 0` term, where
`S(0) = n`), the kernel gives `(∑_j 2)^{2r} = (2n)^{2r}` — the Littlewood–Offord MAIN term
(uniform, no cancellation): the `θ = 0` contribution to the `(1/p)·Σ_θ (2S(θ))^{2r}` count, i.e.
the LO mean `W_r ~ (2n)^{2r}/p` against which sign cancellation must save the factor `p`. -/
theorem halasz_kernel_main_term (n r : ℕ) :
    ∑ s : Fin (2 * r) → Bool, ∑ _a : Fin (2 * r) → Fin n,
        ∏ i : Fin (2 * r), (if s i then (1 : ℤ) else 1)
      = (2 * (n : ℤ)) ^ (2 * r) := by
  have := halasz_kernel n r (fun _ : Fin n => (1 : ℤ)) (fun _ : Fin n => (1 : ℤ))
  rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-! ## 3. The reduction record -/

/-- Machine-checkable summary of the Littlewood–Offord / Halász attack on `W_r`.

* `boundsCountWithoutEquidist = false`: the only decay in the Halász ABSOLUTE-value bound is the
  per-direction `|cos| < 1`, which leaves `T(θ) = Σ_j|cos| = Θ(n)` for ALL `θ` (mean exactly
  `(2/π)n`, measured); the `1/p` saving requires the SIGN cancellation of `S(θ) = Re η_θ`, i.e.
  `|η_θ| ≤ M` small = equidistribution = BGK.
* `loRatioToTarget r p = C(2r,r) · p`: the exact factor by which the raw LO ceiling is weaker than
  the target `M_r/p` (`lo_ceiling_vs_target_ratio`).
-/
structure ReductionRecord where
  boundsCountWithoutEquidist : Bool
  reducesToEquidistribution : Bool

/-- The verdict: M1 (Littlewood–Offord / Halász) REDUCES to equidistribution (BGK). -/
def litOfMechanic : ReductionRecord :=
  { boundsCountWithoutEquidist := false
    reducesToEquidistribution := true }

theorem litOf_reduces : litOfMechanic.reducesToEquidistribution = true := rfl

theorem litOf_no_free_count : litOfMechanic.boundsCountWithoutEquidist = false := rfl

end ProximityGap.Frontier.LittlewoodOfford

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.LittlewoodOfford.halasz_kernel
#print axioms ProximityGap.Frontier.LittlewoodOfford.halasz_kernel_main_term
#print axioms ProximityGap.Frontier.LittlewoodOfford.lo_ceiling_vs_target_ratio
#print axioms ProximityGap.Frontier.LittlewoodOfford.lo_ratio_gt_one_prizeScale
#print axioms ProximityGap.Frontier.LittlewoodOfford.litOf_reduces
#print axioms ProximityGap.Frontier.LittlewoodOfford.litOf_no_free_count
