/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EnergyCharacterTransport

/-!
# The high-moment transport `B ≤ (q·E_r)^{1/2r}` and the DEEP-MOMENT WALL (Issue #389, TECHNIQUE 6)

This file machine-checks the single-term moment-to-sup arrow and the arithmetic equivalence the
moment method runs on, and records (as heuristic and empirical prose, not as theorems) where the
method appears to stop on the open analytic core of the proximity prize — the deep-moment / `L^∞`
wall flagged in the issue.

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

This single-term arrow is exact as an inequality, but it is **not** the only or the strongest
rigorous arrow, and on its own it is never better than the trivial bound. The raw moment
`∑_b ‖η_b‖^{2r}` includes the principal frequency `b = 0`, where `η_0 = n`; hence
`q·E_r ≥ n^{2r}` and `(q·E_r)^{1/2r} ≥ n` always. A strictly stronger valid arrow already in tree is
`GaussPeriodCosetReduction.cosetReduced_eta_pow_le`, which subtracts the principal mode and divides
by the orbit size: `‖η_{b₀}‖^{2r} ≤ (q·E_r − n^{2r})/n` for `b₀ ≠ 0` (all `r`; the all-order
Parseval identity is `SubgroupGaussSumMoment.subgroup_gaussSum_moment`).

## Where a saving would have to come from (heuristic, not proved here)

Heuristically one models the **principal-mode-subtracted** moment `q·E_r − n^{2r}` by a
"char-0" size `≍ q·c^r·r!·n^r`. The raw `E_r` cannot have that size once `n^r > q·c^r·r!`, because
`E_r ≥ n^{2r}/q`; any such model therefore concerns the DC-subtracted quantity (cf. PG-006). Under
that model,

  `(q·c^r·r!·n^r)^{1/2r} ≍ q^{1/2r}·√(r/e)·√(c·n),`

and choosing `r ≍ log q` makes `q^{1/2r} ≍ O(1)`, giving `B ≲ √(n·log q)`, the conjectured bound.
This is a heuristic consequence of an unproved model, not a theorem of this file.

## The empirical depth cap (unproved) and its correct fixed-regime exponent

The deep-moment obstruction recorded here is an **empirical** observation, not a proved law: in
numerical exploration the (DC-subtracted) energy of `μ_n` appeared to match its char-0 value only
for `p > τ_r ≍ n^{(r+3)/2}` (`RootsOfUnityAdditiveEnergyExact` is an exact `r = 2` anchor; no
general threshold law is proved in this file). If that empirical law were taken as the reliable
range, it would cap

  `r ≤ r_max := 2·log_n(p) − 3.`

In the regime `p ≈ n^5` this is the **fixed** depth `r_max = 7`, while the heuristic optimum needs
`r ≍ log q ≍ 5·log n`, which grows with `n`. Because `r_max` is fixed, the `−3` cannot be dropped
from the exponent: at `r = 7` the modelled bound is

  `(p·c^7·7!·n^7)^{1/14} ≍ (n^{12})^{1/14} = n^{6/7}`

(the coset reduction's extra `/n` improves this to `n^{11/14}` under the same model). So, under
the unproved empirical cap, the moment method at the capped depth gives `B ≲ n^{6/7}` (resp.
`n^{11/14}`) in the regime `p ≈ n^5`, strictly worse than `√n`. (An earlier version of this
docstring claimed `n^{3/4+o(1)}`; that figure silently used `r = 2·log_n p = 10`, beyond the cap.)
This is consistent with the literature: no published method reaches `n < p^{1/4}`; the best
explicit saving is `n^{1−31/2880}` for `n > p^{1/4}` only.

`moment_bound_beats_target_iff` below records the exact arithmetic equivalence the method runs on:
`(q·E_r)^{1/2r} ≤ T ↔ q·E_r ≤ T^{2r}`. The file proves the single-term arrow and this equivalence;
it does **not** prove the empirical cap, the char-0 model, or any bound on `E_r`, and it does not
cross the wall — that is the open problem of controlling the DC-subtracted deep moments
(`r ≍ log q`) at `p ~ n^5`, equivalently a square-root-cancellation bound on the `(p−1)/n`
Gauss-sum phases `χ̄(b)τ(χ)`, `χ ∈ μ_n^⊥`.

## Tower structure (recorded, negative, scope-limited)

The `2`-power tower `μ_2 < μ_4 < … < μ_{2^a}` was observed not to lower the deep moments in small
numerical samples (the antipodal `−1 ∈ μ_{2^a}` adds solutions). An unrestricted lower bound
`E_r ≥ r!·n^r` is **false**: the generic bound `E_r ≤ n^{2r}` already rules it out once
`r! > n^r`, and concretely for the proper `μ_4 = {1, 16, 241, 256} ⊆ 𝔽_257` at `r = 4` one has
`E_4 = 4900 < 24·4^4 = 6144`. The valid elementary lower bound counts only the permutation
solutions with pairwise distinct entries: `E_r ≥ r!·n(n−1)⋯(n−r+1)` for `r ≤ n`. The tower
observation is therefore only heuristic evidence that folding offers no shortcut.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #389.
- [BGK06] Bourgain, Glibichuk, Konyagin. *Estimates for the number of sums and products …*. 2006.
- [HBK00] Heath-Brown, Konyagin. *New bounds for Gauss sums derived from k-th powers …*. 2000.
-/

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false


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
prize quantity `∑_b ‖η_b‖^{2r} = q·E_r`, then `B^{2r} ≤ q·E_r`. Hence `B ≤ (q·E_r)^{1/2r}`. This
is the crudest moment-to-sup arrow: since the `b = 0` term alone is `n^{2r}`, its right side is
`≥ n^{2r}`; the stronger `GaussPeriodCosetReduction.cosetReduced_eta_pow_le` subtracts that
principal term and divides by `n`. Taking the `2r`-th moment value
`M_{2r}` as a hypothesis keeps this axiom-clean and exactly matches the in-tree `r = 2` identity
`subgroup_gaussSum_fourthMoment` (`M_4 = q·E(G)`). -/
theorem charSum_le_of_moment (ψ : AddChar F ℂ) (G : Finset F) (b₀ : F) (r : ℕ)
    {M : ℝ} (hM : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = M) :
    ‖eta ψ G b₀‖ ^ (2 * r) ≤ M := by
  rw [← hM]; exact term_le_moment ψ G b₀ r

/-- **Divided form: `B ≤ (q·E_r)^{1/(2r)}`.** With `r ≥ 1` and a nonnegative moment value `M`, the
worst-case character sum is at most the `(2r)`-th root of the `2r`-th moment. This is the bound the
moment method optimizes over `r`. With the raw moment `M = q·E_r ≥ n^{2r}` this root is always
`≥ n` (trivial); the heuristic `√(n log q)` at `r ≍ log q` needs the principal-mode-subtracted
moment `q·E_r − n^{2r}` to have char-0 size `≍ q·c^r r! n^r`, which is not proved here. -/
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
on. Heuristically, with a modelled char-0 value `c^r·r!·n^r` (for the raw `E_r` this model is
inconsistent once `n^r > q·c^r·r!`, since `q·E_r ≥ n^{2r}`; it must be read for the
principal-mode-subtracted moment) and target `T = √(n·log(q/n))`, the inequality reads
`q·c^r r! n^r ≤ (n·log(q/n))^r`, i.e. `q ≤ (log(q/n))^r / (c^r r!)` — satisfiable only for
`r ≳ log q`. That exceeds the fixed depth `r_max = 7` given by the *empirical, unproved* cap
`r ≤ 2 log_n p − 3` in the regime `p ≈ n^5`. Only the equivalence below is proven here; the value
of `E_r`, the char-0 model and the empirical cap are deliberately *not* supplied. -/
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
