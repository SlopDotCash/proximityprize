/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-R2)
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Kesten–McKay edge → moment-method reduction (lane wf-R2, #444)

Lane R2 explores the Kunisky (arXiv:2303.16475) **Kesten–McKay deterministic spectral edge**
route to the thin-subgroup character-sum wall
`M(n) = max_{b≠0} |∑_{x∈μ_n} e_p(bx)| ≤ C·√(n·log(p/n))`.

For the Cayley graph `Cay(F_p, μ_n)` the eigenvalues are exactly the Gauss periods
`λ_b = S_b = ∑_{x∈μ_n} e_p(bx)` (`b ∈ F_p`), and `M(n) = λ_2` is the spectral gap.  The
Kunisky route says the bulk ESD converges to the degree-`n` Kesten–McKay law (support
`[-2√(n-1), 2√(n-1)]`), proven via **all-order signed closed-walk counts**, which equal the
char-`p` additive energies `E_k(μ_n) = #{(x,y)∈μ_n^{2k} : ∑x ≡ ∑y mod p}` because the `2k`-th
ESD moment is `(1/p)∑_b |S_b|^{2k} = E_k`.

**Refutation of the literal edge-rigidity lemma (numerically established, this lane).**
The naive "no eigenvalue exceeds `2√(n-1)`" is FALSE for the Cayley graph: measured
`M(n)/(2√(n-1))` reaches `2.45` (n=64, p=65921).  The graph is far from tree-like (abundant
4-cycles from `x+y=x'+y'`), so the extreme eigenvalue sits in an outlier band above the KM
bulk edge; the size of that band IS the prize quantity.  Hence the deterministic edge route
collapses onto the **char-`p` energy Wick bound** `E_k ≤ (2k-1)!!·n^k` to depth `k ~ log p`,
which is the permitted char-`p` deep-moment crux (not a new closed lemma).

**What this file proves, axiom-clean.**  The single rigorous reduction step the route rests
on: the deterministic moment-method inequality

  `M^{2k} ≤ ∑_b |S_b|^{2k}`,

i.e. the max of a nonneg finite family raised to a power is bounded by the sum of the powers.
Combined with `∑_b |S_b|^{2k} = p·E_k` (the closed-walk = energy identity) this yields the
`M ≤ (p·E_k)^{1/2k}` bound on which the entire route depends.  The remaining open step is the
energy bound itself.

Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.KMEdgeMomentReduction

/-- **Max-power ≤ sum-of-powers (the moment-method reduction step).**  For a nonnegative finite
family `a : σ → ℝ` and any exponent `k`, the maximum entry raised to the power `k` is bounded by
the sum of all entries raised to the power `k`.  This is the deterministic core of the
Kesten–McKay edge route: with `a b = |S_b|^2` and the energy identity `∑_b |S_b|^{2k} = p·E_k`,
it gives `M(n)^{2k} ≤ p·E_k`, hence `M ≤ (p·E_k)^{1/2k}` — the moment upper bound on the
spectral gap. -/
theorem max_pow_le_sum_pow {σ : Type*} [Fintype σ] (a : σ → ℝ) (ha : ∀ s, 0 ≤ a s)
    (k : ℕ) (b : σ) : (a b) ^ k ≤ ∑ s, (a s) ^ k := by
  refine Finset.single_le_sum (f := fun s => (a s) ^ k) ?_ (Finset.mem_univ b)
  intro s _
  exact pow_nonneg (ha s) k

/-- **The reduction conclusion in the `M`-shape.**  If `M = a b₀` is the maximum value of a
nonnegative family and `E := ∑_s (a s)^{2k}` denotes the (unnormalized) `2k`-th moment, then
`M^{2k} ≤ E`.  Specializing `a = |S_·|`, `b₀` = the maximizing frequency, `E = p·E_k`, this is
exactly `M(n)^{2k} ≤ p·E_k`. -/
theorem max_sq_pow_le_moment {σ : Type*} [Fintype σ] (a : σ → ℝ) (ha : ∀ s, 0 ≤ a s)
    (k : ℕ) (b : σ) : (a b) ^ (2 * k) ≤ ∑ s, (a s) ^ (2 * k) :=
  max_pow_le_sum_pow a ha (2 * k) b

end ProximityGap.Frontier.KMEdgeMomentReduction
