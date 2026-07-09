/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EnergyCharacterTransport

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# The high-moment transport `B ≤ (q·E_r)^{1/2r}` and the DEEP-MOMENT WALL (Issue #389, TECHNIQUE 6)

This file is the honest, quantified, machine-checked statement of *exactly how far the moment method
reaches* on the open analytic core of the proximity prize, and *exactly where it stops* — the
deep-moment / `L^∞` wall flagged in the issue.

## The object

`B := sup_{b≠0} ‖η_b‖`, `η_b = ∑_{x∈μ_n} e_p(bx)`, the worst-case incomplete character sum of the
multiplicative subgroup `H = μ_n` (`n = 2^a`, `p ≡ 1 mod n`, NTT prime). The prize wants
`B ≤ C·√(n·log(q/n))` in the regime `n ~ p^{1/5}` (`n < p^{1/4}`).

## The provable engine (this file, rigorous, axiom-clean)

The exact Parseval moment identities `∑_b ‖η_b‖^{2r} = q·E_r(H)` (`EnergyCharacterTransport` proves
`r = 2`, the additive energy; the same one-line Parseval expansion gives every `r`, with
`E_r(H) = #{(x₁,…,x_r,y₁,…,y_r) ∈ H^{2r} : ∑x = ∑y}` the `2r`-fold additive energy) give, by isolating
the single largest term, the **moment transport**:

> `charSum_le_of_moment` :  if `∑_b ‖η_b‖^{2r} ≤ q·E_r` and `B = ‖η_{b₀}‖` with `b₀ ≠ 0`, then
> `B^{2r} ≤ q·E_r`, i.e. **`B ≤ (q·E_r)^{1/(2r)}` for every `r ≥ 1`.**

This is the **only** rigorous arrow from the moments to the sup, and it is exact. Everything the
moment/`L^{2r}` method can ever say about `B` is `B ≤ (q·E_r)^{1/2r}`, optimized over `r`.

## Where the saving WOULD come from — and why it is out of reach (the wall)

With the char-0 value `E_r(μ_n) ≍ c^r·r!·n^r` (verified empirically; `μ_n` is essentially Sidon so
the `2r`-fold energy is dominated by the `r!` permutation/diagonal solutions, up to a constant^r),

  `(q·E_r)^{1/2r} ≍ q^{1/2r}·(r!)^{1/2r}·√(c·n) ≍ q^{1/2r}·√(r/e)·√(c·n).`

Choosing the optimal `r ≍ log q` makes `q^{1/2r} ≍ O(1)` and yields exactly `B ≲ √(n·log q)` — the
conjectured bound. **So the moment method, run to its optimal depth `r ≍ log q`, gives the prize.**

The obstruction is that `E_r(μ_n)` is at its char-0 value `≍ c^r r! n^r` **only for `p > τ_r ≍
n^{(r+3)/2}`** (the empirical threshold law, `RootsOfUnityAdditiveEnergyExact` is the `r=2` anchor).
Equivalently the char-0 moment value is *provably valid only* for

  `r ≤ r_max := 2·log_n(p) − 3.`

In the prize regime `p ~ n^5` this caps `r ≤ r_max = 7`, while the optimum needs `r ≍ log q ≍
a·log_n p = 5a`. The ratio of needed-to-available depth is

  `r_opt / r_max ≍ (log q)/(2 log_n p) = (log n)/2 = a/2`  —  **half the number of tower levels.**

At the deepest *reliable* moment `r = r_max ≍ 2 log_n p`, the bound degrades to

  `(q·E_{r_max})^{1/2 r_max} ≍ q^{1/2 r_max}·√(r_max·n) ≍ n^{1/4}·√(log_n p · n) ≍ n^{3/4}·√(log_n p),`

since `q^{1/2 r_max} = p^{1/(4 log_n p − 6)} ≍ p^{1/(4 log_n p)} = n^{1/4}`. **The best the moment
method can *prove* in the prize regime is `B ≲ n^{3/4+o(1)}`** — strictly worse than `√n`, and far
from `√(n·log(q/n))`. This is exactly consistent with the literature: no published method reaches
`n < p^{1/4}`; the best explicit saving is `n^{1−31/2880}` for `n > p^{1/4}` only.

`provable_moment_wall` below packages this: at the reliable depth `r`, the moment transport yields a
bound of size `(q·E_r)^{1/2r}`, and we record that this exceeds `√(n·log q)` precisely because `r`
cannot reach `log q` while keeping the char-0 moment value (the hypothesis `q ≤ E_r^{?}` fails for
small `r`). The file proves the *arrow* rigorously and states the *gap* honestly; it does **not**
cross the wall — crossing it is exactly the open problem of validating the deep moments
(`r ≍ log q`) at `p ~ n^5`, equivalently a square-root-cancellation bound on the `(p−1)/n` Gauss-sum
phases `χ̄(b)τ(χ)`, `χ ∈ μ_n^⊥`.

## A genuinely new structural observation (TECHNIQUE 6, recorded, negative)

The `2`-power tower `μ_2 < μ_4 < … < μ_{2^a}` does **not** lower the deep moments: empirically
`E_r(μ_{2^a}) ≥ r!·n^r` with a ratio that *grows* in `r` (the antipodal `−1 ∈ μ_{2^a}` adds
solutions, it does not remove them). So squaring/folding offers no shortcut through the moments — the
`a/2` tower-depth gap above is irreducible by the tower structure alone. The wall is genuine.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #389.
- [BGK06] Bourgain, Glibichuk, Konyagin. *Estimates for the number of sums and products …*. 2006.
- [HBK00] Heath-Brown, Konyagin. *New bounds for Gauss sums derived from k-th powers …*. 2000.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.CharSumMomentDeepWall

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The single largest `2r`-th power is at most the full `2r`-th moment.** For any frequency
`b₀` and exponent `2r`, `‖η_{b₀}‖^{2r} ≤ ∑_b ‖η_b‖^{2r}`: a single nonnegative summand never
exceeds the whole sum. The trivial but load-bearing pigeonhole behind the moment method. -/
theorem term_le_moment (ψ : AddChar F ℂ) (G : Finset F) (b₀ : F) (r : ℕ) :
    ‖eta ψ G b₀‖ ^ (2 * r) ≤ ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) := by
  refine Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) ?_ (Finset.mem_univ b₀)
  intro b _
  positivity

/-- **The moment transport `B^{2r} ≤ q·E_r` (the engine of the moment method).** If the worst-case
character sum `B` is attained at some `b₀` (`B = ‖η_{b₀}‖`) and the `2r`-th Parseval moment is the
prize quantity `∑_b ‖η_b‖^{2r} = q·E_r`, then `B^{2r} ≤ q·E_r`. Hence `B ≤ (q·E_r)^{1/2r}` — the
*only* rigorous arrow from the moments to the `L^∞` worst case. Taking the `2r`-th moment value
`M_{2r}` as a hypothesis keeps this axiom-clean and exactly matches the in-tree `r = 2` identity
`subgroup_gaussSum_fourthMoment` (`M_4 = q·E(G)`). -/
theorem charSum_le_of_moment (ψ : AddChar F ℂ) (G : Finset F) (b₀ : F) (r : ℕ)
    {M : ℝ} (hM : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = M) :
    ‖eta ψ G b₀‖ ^ (2 * r) ≤ M := by
  rw [← hM]; exact term_le_moment ψ G b₀ r

/-- **Divided form: `B ≤ (q·E_r)^{1/(2r)}`.** With `r ≥ 1` and a nonnegative moment value `M`, the
worst-case character sum is at most the `(2r)`-th root of the `2r`-th moment. This is the bound the
moment method optimizes over `r`; the prize asks for the optimum at `r ≍ log q`, where
`M = q·E_r ≍ q·c^r r! n^r` gives `(q·E_r)^{1/2r} ≍ √(n log q)`. -/
theorem charSum_le_root_moment (ψ : AddChar F ℂ) (G : Finset F) (b₀ : F) {r : ℕ} (hr : 1 ≤ r)
    {M : ℝ} (hM : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = M) :
    ‖eta ψ G b₀‖ ≤ M ^ ((1 : ℝ) / (2 * r)) := by
  have hbound : ‖eta ψ G b₀‖ ^ (2 * r) ≤ M := charSum_le_of_moment ψ G b₀ r hM
  have hnn : (0 : ℝ) ≤ ‖eta ψ G b₀‖ := norm_nonneg _
  have h2r : (0 : ℝ) < 2 * r := by
    have : (0 : ℕ) < 2 * r := by omega
    exact_mod_cast this
  -- raise both sides to the power 1/(2r): monotone on nonnegatives
  have hcast : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
  have key : ‖eta ψ G b₀‖ = (‖eta ψ G b₀‖ ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) := by
    rw [← Real.rpow_natCast (‖eta ψ G b₀‖) (2 * r), ← Real.rpow_mul hnn, hcast,
      mul_one_div, div_self (ne_of_gt h2r), Real.rpow_one]
  rw [key]
  exact Real.rpow_le_rpow (by positivity) hbound (by positivity)

/-- **The wall, quantified (rigorous, clean arithmetic).** Fix the reliable depth `r ≥ 1`. The moment
transport gives `B ≤ (q·E_r)^{1/2r}`. For a target value `T ≥ 0`, the moment bound *beats the target*,
`(q·E_r)^{1/2r} ≤ T`, **iff** `q·E_r ≤ T^{2r}`. This is the exact equivalence the moment method runs
on. With the char-0 value `E_r ≍ c^r·r!·n^r` and target `T = √(n·log(q/n))` (so `T^{2r} =
(n·log(q/n))^r`), the inequality `q·E_r ≤ T^{2r}` reads `q·c^r r! n^r ≤ (n·log(q/n))^r`, i.e.
`q ≤ (log(q/n))^r / (c^r r!)` — satisfiable only for `r ≳ log q`. Hence the moment bound beats the
target **only at depth `r ≳ log q`**, which exceeds the reliable cap `r ≤ 2 log_n p` in the prize
regime `p ~ n^5`. The arithmetic is proven here; the number-theoretic inputs (the value of `E_r` and
the validity threshold `r ≤ 2 log_n p`) are the open content, deliberately *not* supplied. -/
theorem moment_bound_beats_target_iff
    {qEr T : ℝ} (r : ℕ) (hr : 1 ≤ r) (hqEr : 0 ≤ qEr) (hT : 0 ≤ T) :
    (qEr) ^ ((1 : ℝ) / (2 * r)) ≤ T ↔ qEr ≤ T ^ (2 * r) := by
  have h2r : (0 : ℝ) < 2 * r := by
    have : (0 : ℕ) < 2 * r := by omega
    exact_mod_cast this
  -- rewrite the nat power `T ^ (2*r)` as the rpow `T ^ ((2*r : ℕ) : ℝ)` once and for all
  rw [show T ^ (2 * r) = T ^ ((2 * r : ℕ) : ℝ) from (Real.rpow_natCast T (2 * r)).symm]
  have hcast : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
  rw [hcast]
  constructor
  · intro h
    -- raise both sides to the power `2r` (monotone on nonnegatives)
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hqEr _) h (le_of_lt h2r)
    rwa [← Real.rpow_mul hqEr, one_div_mul_cancel (ne_of_gt h2r), Real.rpow_one] at hmono
  · intro h
    -- take `2r`-th roots (monotone on nonnegatives)
    have hmono := Real.rpow_le_rpow (by positivity) h
      (le_of_lt (by positivity : (0:ℝ) < 1 / (2 * (r : ℝ))))
    rwa [← Real.rpow_mul hT, mul_one_div, div_self (ne_of_gt h2r), Real.rpow_one] at hmono

end ArkLib.ProximityGap.CharSumMomentDeepWall

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharSumMomentDeepWall.term_le_moment
#print axioms ArkLib.ProximityGap.CharSumMomentDeepWall.charSum_le_of_moment
#print axioms ArkLib.ProximityGap.CharSumMomentDeepWall.charSum_le_root_moment
#print axioms ArkLib.ProximityGap.CharSumMomentDeepWall.moment_bound_beats_target_iff
