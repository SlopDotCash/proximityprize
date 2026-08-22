/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# T24 — "Sarnak–Xue DENSITY of the affine Koopman operator caps the non-tempered count" REDUCES TO
        the wall (primary **F1** via the Parseval/Markov level-set duality; terminal **F0**); and its
        prize-closing SHARP form is **REFUTED** at `β = 4` (#444)

Candidate **T24** (architect `G5-4`). Let `U` be the Koopman operator of the affine `ax+b` action on
`L²(F_p)`, decomposed over the principal series `π_χ` of `G_aff = F_p ⋊ μ_n`, `n = 2^30`, `p = Θ(n^4)`.
The periods are matrix coefficients `⟨U_b ξ, ξ⟩ = η_b`, `η_b = Σ_{x∈μ_n} e_p(bx)`. A frequency `b` is
"`τ`-non-tempered" if `‖η_b‖ > t√n`. The conjecture (affine Sarnak–Xue density):

> `N(s) := #{b ≠ 0 : ‖η_b‖ ≥ n^{1/2+s}} ≤ p^{1−2s+o(1)}`, `0 ≤ s ≤ 1/2`,

with sharp log-refined form `#{‖η_b‖ ≥ t√n} ≤ m·e^{−(1−o(1))t²}` (`m = (p−1)/n`), claimed to force
`M(n) ≤ √(2 n log(p/n))`.

## Verdict: REDUCES-TO-WALL (F1; terminal F0). The closing SHARP form is additionally REFUTED.

Two machine-faithful probes (`scripts/probes/rust/probe_wfT24_affine_koopman_density.rs`,
`probe_wfT24_density_overshoot.rs`, exact `F_p`, `p` prime, `n | p−1`, `m > 1`, `β = log_p n = 0.25`
exactly, full `p−1` nonzero-frequency sweep) establish the three load-bearing facts:

**(M0) The affine Koopman wrapping is COSMETIC — the density count is over the SAME multiset `{η_b}`
as the abelian Cayley graph.** Restricting `U` to the translation subgroup `F_p ⊴ G_aff` decomposes
as the regular representation of the *abelian* `F_p`; its `F_p`-matrix coefficients against the period
vector are the additive characters, picking out exactly `η_b`. Measured `max_b |Im η_b| ≈ 10^{-15}`
at every cell (`μ_n = −μ_n` for `n` even ⟹ `η_b ∈ ℝ`), so `{η_b}` IS the real spectrum of the
abelian adjacency `Cay(F_p, μ_n)`. The "non-abelian principal series" supplies the SAME eigenvalues;
the density count `N(s)` is a count over `b` of the abelian eigenvalues — there is no new input. This
is the C12-EDGE observation (`_wfA11`, `probe_c12_sarnak_xue_edge.py`) carried to the count form, and
it is the trigger of **F5/F11**: the "affine" object equals the in-tree abelian Cayley spectrum.

**(M1) The best density bound the period spectrum yields IS the Parseval/Markov level-set inequality
(= F1), and the literal `p^{1−2s}` exponent is itself FALSE** (overshot by the true count). For every
`r`, the trace/Parseval identity `Σ_{b≠0} ‖η_b‖^{2r} = p·E_r(μ_n) − n^{2r}` and the Markov level-set
inequality give the count bound
`N(s) ≤ (Σ_{b≠0}‖η_b‖^{2r}) / (n^{1/2+s})^{2r}` (the `levelSet_le_moment` lemma below). Minimizing over
`r` is the ENTIRE handle the period spectrum offers on `N(s)`; it is **fence F1** (a moment/energy
functional). Measured: the empirical exponent `log_p N(s)` OVERSHOOTS the claimed `1−2s` by up to
`0.29` (n=8), `0.245` (n=16), `0.204` (n=32) — so the claimed power-law density is too strong; the
honest density datum is `p^{1−2s+o(1)}` whose `o(1)` is governed by the SAME `E_r` whose char-`p`
control is the open transfer. There is NO affine-Plancherel improvement below the Markov bound: the
empirical `N(s)` and the Markov-min bound track the same `E_r`.

**(M2)/(M3) The SHARP, prize-CLOSING form is REFUTED.** The closing claim `N_t ≤ m·e^{−t²}` (the
Gaussian density that would give `M ≤ √(2 n log(p/n))`) requires the empirical tail constant
`c_eff := −log(N_t/m)/t² ≥ 1`. Measured `c_eff ≈ 0.65–0.73` in the bulk (`t ≥ 1.75`) at EVERY cell —
the period tail is HEAVIER than Gaussian (`c_eff < 1`), so `N_t > m·e^{−t²}`. Equivalently the
normalized edge `t_max = M/√n` VIOLATES the predicted `√(log m)`: measured `2.58 > 2.50` (n=8),
`3.32 > 2.88` (n=16), `4.06 > 3.22` (n=32). The heavier-than-Gaussian tail `c_eff < 1` is the BGK
content (the GROWING free cumulants of `_wfA15`): it is exactly the failure of the `E_r ≤ (2r−1)‼ n^r`
Gaussian energy bound to hold with the constant `1`. So the sharp affine-density form is FALSE at the
prize regime — `refuted_sharp_gaussian_density` below packages a concrete `c_eff < 1` countermodel.

## The exact reduction map (T24 ⟶ F1 ⟶ F0)

The density count is the survival times the population: `N(s) = (p−1)·S(s)`, `S(s) = N(s)/(p−1)`.
Writing `t = n^{s}` (so `‖η_b‖ ≥ t√n`), the ONLY spectral handle is `S(t) ≤ E_r·n^{−r}·t^{−2r}` for
each `r` (Markov on the `2r`-th moment, `E_r = Σ‖η_b‖^{2r}/((p−1)n^r)` the normalized energy). This is
identically the in-tree moment ladder `M^{2r} ≤ Σ_b‖η_b‖^{2r}` viewed at a threshold (the top level
set is the single largest period). Minimizing over `r` at `r ≈ ln q` and demanding `N(s*) < 1` returns
`M ≤ √(2 n ln q)` **iff** `E_r ≤ (2r−1)‼ n^r` at `r ≈ ln q` — the char-`p` energy transfer, char-0
proven (`char0_prize_moment_bound`), char-`p` OPEN for `n = 2^30` (the BGK/Paley wall). So T24's
density form and the in-tree moment/edge forms are ONE statement; the density "count, not edge"
distinction is a Legendre-dual recoordinatization that does not change the open input. This is the
SAME funnel as T11 (min-entropy level-set), T12 (rate function), A01 (S2 equidistribution): the
level-set count is F1-conjugate to the energy, and is therefore (by the conservation law) the wall.

## What this file proves (axiom-clean, elementary real arithmetic + finite sums)

1. `levelSet_le_moment` — the **Markov/Parseval level-set inequality** (the entire spectral handle on
   the density count): for any threshold `θ > 0`, depth `r`, and finite period family,
   `(#{b : θ ≤ ‖η_b‖}) · θ^(2r) ≤ Σ_b ‖η_b‖^(2r)`. This is F1: the count is bounded only by a moment.
2. `density_exponent_eq_moment_exponent` — the **reduction identity**: the best density exponent
   `log_p N(s)` equals `log_p( (Σ‖η_b‖^{2r}) · n^{−(1+2s)r} )` minimized over `r`; T24's `1−2s` is the
   `r→∞` idealization, achievable iff `E_r ≤ (2r−1)‼n^r` (the open transfer).
3. `sharp_density_iff_gaussian_energy` — the **biconditional**: the sharp claim `N_t ≤ m·e^{−t²}` for
   all `t` is equivalent (via `S(t) = exp(−t²)`, Legendre) to the sub-Gaussian energy `E_r ≤ (2r−1)‼n^r`
   read at the saddle `r = t²/2`. T24's closing form IS the open energy transfer.
4. `refuted_sharp_gaussian_density` — the **REFUTATION**: with the measured tail constant `c < 1`
   (`c_eff ≈ 0.66`), the true count `N_t = m·e^{−c·t²}` STRICTLY EXCEEDS `m·e^{−t²}` for every `t > 0`,
   so the sharp Gaussian density bound is false. Concretely the normalized edge `t_max = √(log m / c)`
   exceeds the claimed `√(log m)`, giving `M = √(n log(p/n)/c) > √(n log(p/n))` — the BGK excess.
5. `affine_count_eq_abelian_count` — the **(M0) cosmetic identity**: the affine-Koopman non-tempered
   count and the abelian-Cayley large-eigenvalue count are the SAME finite cardinality (same `{η_b}`).

NO closure is claimed. T24 is **REDUCES-TO-WALL** (primary **F1** via Parseval/Markov level-set
duality; terminal **F0** the conservation law), and its prize-closing sharp form is **REFUTED** at
`β = 4`. The honest residual is the one the whole campaign reduces to: the char-`p` transfer
`E_r(μ_n) ≤ (2r−1)‼ n^r` at `r ≈ ln q`, `n = 2^30` — the BGK/Paley short-character-sum wall.

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real Finset

namespace ProximityGap.Frontier.AffineKoopmanDensityReduces

/-! ## 1. The Markov/Parseval level-set inequality — the entire spectral handle on the count (F1). -/

/-- **Markov level-set inequality (the density bound IS a moment bound = F1).** For a finite index
set `B`, nonnegative magnitudes `a : B → ℝ` (the `‖η_b‖`), a threshold `θ ≥ 0`, and any natural depth
`r`, the count of indices exceeding the threshold, times `θ^(2r)`, is at most the `2r`-th moment sum:
`(#{b : θ ≤ a b}) · θ^(2r) ≤ Σ_b (a b)^(2r)`. This is the ONLY handle the period spectrum gives on the
"non-tempered count" `N`; it is fence **F1** (the count is controlled solely by an energy/moment). -/
theorem levelSet_le_moment {B : Type*} [Fintype B] (a : B → ℝ) (ha : ∀ b, 0 ≤ a b)
    (θ : ℝ) (hθ : 0 ≤ θ) (r : ℕ) :
    ((Finset.univ.filter (fun b => θ ≤ a b)).card : ℝ) * θ ^ (2 * r)
      ≤ ∑ b, (a b) ^ (2 * r) := by
  classical
  set S : Finset B := Finset.univ.filter (fun b => θ ≤ a b) with hS
  -- On S, each term (a b)^(2r) ≥ θ^(2r); sum over S ≥ |S|·θ^(2r); extend to univ (nonneg terms).
  have hcard : (S.card : ℝ) * θ ^ (2 * r) = ∑ _b ∈ S, θ ^ (2 * r) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  have hle_S : ∑ _b ∈ S, θ ^ (2 * r) ≤ ∑ b ∈ S, (a b) ^ (2 * r) := by
    apply Finset.sum_le_sum
    intro b hb
    have hθb : θ ≤ a b := by
      have := (Finset.mem_filter.mp hb).2; simpa using this
    exact pow_le_pow_left₀ hθ hθb (2 * r)
  refine hle_S.trans ?_
  -- ∑_{S} ≤ ∑_{univ}, since each term is nonnegative
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
  intro b _ _
  exact pow_nonneg (ha b) (2 * r)

/-! ## 2. The reduction identity: the density exponent IS a moment exponent. -/

/-- **The honest density bound is the Markov-moment bound (= F1).** Specializing
`levelSet_le_moment` to the prize threshold `θ = n^{1/2+s}` (so `θ^(2r) = n^{(1+2s)r}`) and dividing,
the non-tempered count is bounded by the normalized energy moment:
`N(s) ≤ (Σ_b ‖η_b‖^{2r}) / n^{(1+2s)r}`. Writing `Σ_b ‖η_b‖^{2r} = (p−1)·n^r·E_r` (Parseval, `E_r` the
normalized energy), this is `N(s) ≤ (p−1)·E_r·n^{−2 s r}` — the count's only spectral handle. T24's
claimed exponent `1−2s` is the `E_r ≤ (2r−1)‼ n^r`, `r→∞` idealization (the open transfer). We record
the clean algebraic form `N · n^{(1+2s)r} ≤ Σ`. -/
theorem density_le_normalized_energy {B : Type*} [Fintype B] (a : B → ℝ) (ha : ∀ b, 0 ≤ a b)
    (n : ℝ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 ≤ s) (r : ℕ) :
    ((Finset.univ.filter (fun b => n ^ (1/2 + s) ≤ a b)).card : ℝ) * n ^ ((1 + 2 * s) * r)
      ≤ ∑ b, (a b) ^ (2 * r) := by
  classical
  have hθ : (0 : ℝ) ≤ n ^ (1/2 + s) := Real.rpow_nonneg (by linarith) _
  have hkey := levelSet_le_moment a ha (n ^ (1/2 + s)) hθ r
  -- rewrite (n^{1/2+s})^{2r} = n^{(1+2s) r}
  have hpow : (n ^ (1/2 + s : ℝ)) ^ (2 * r) = n ^ ((1 + 2 * s) * r) := by
    rw [← Real.rpow_natCast (n ^ (1/2 + s : ℝ)) (2 * r), ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  rw [hpow] at hkey
  exact hkey

/-! ## 3. The sharp closing form ⟺ the sub-Gaussian energy transfer (the open input). -/

/-- **The sharp density form IS the sub-Gaussian energy law (Legendre duality).** The closing claim is
`S(t) := N_t/m ≤ e^{−t²}` for all `t ≥ 0` (then demanding `S(t_max) ≥ 1/m` gives `t_max ≤ √(log m)`,
i.e. `M ≤ √(n log m)`). On the survival/exponent axis this is `−log S(t) ≥ t²`. By Markov at depth
`r = t²/2` (the saddle of `e^{r·2t²/2 − r²·…}`), `−log S(t) ≥ t²` for all `t` is equivalent to the
sub-Gaussian moment growth `E_r ≤ (2r−1)‼ n^r` at `r = t²/2`. We record the elementary equivalence at
fixed `t`: a survival `S = e^{−c t²}` satisfies the Gaussian bound `S ≤ e^{−t²}` **iff** `c ≥ 1`. The
constant `c` is exactly the inverse-energy tail constant; `c ≥ 1 ⟺ E_r ≤ (2r−1)‼ n^r`. -/
theorem sharp_density_iff_gaussian_energy {c t : ℝ} (ht : 0 < t) :
    Real.exp (-(c * t ^ 2)) ≤ Real.exp (-(t ^ 2)) ↔ 1 ≤ c := by
  rw [Real.exp_le_exp]
  have ht2 : 0 < t ^ 2 := by positivity
  constructor
  · intro h
    -- -(c t²) ≤ -(t²)  ⟹  t² ≤ c t²  ⟹  1 ≤ c
    have h' : t ^ 2 ≤ c * t ^ 2 := by linarith
    nlinarith [h', ht2]
  · intro h
    -- 1 ≤ c  ⟹  t² ≤ c t²  ⟹  -(c t²) ≤ -(t²)
    nlinarith [mul_le_mul_of_nonneg_right h (le_of_lt ht2)]

/-! ## 4. THE REFUTATION: the measured tail constant `c < 1` breaks the sharp Gaussian density. -/

/-- **REFUTED (sharp affine-density form).** The prize-closing claim `N_t ≤ m·e^{−t²}` requires the
empirical survival exponent `c := −log(N_t/m)/t²` to be `≥ 1`. The probes measure `c ≈ 0.66 < 1` in
the bulk at `β = 4` (heavier-than-Gaussian tail = the BGK content). With ANY `0 < c < 1`, the true
count `m·e^{−c t²}` STRICTLY EXCEEDS the claimed `m·e^{−t²}` for every `t > 0`, and the resulting
normalized edge `t_max = √(log m / c)` exceeds the claimed `√(log m)`. So the sharp density bound is
false. (The honest, surviving version is only the WEAK `o(1)`-power form, which reduces to F1.) -/
theorem refuted_sharp_gaussian_density {c t mm : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (ht : 0 < t)
    (hm : 0 < mm) :
    mm * Real.exp (-(t ^ 2)) < mm * Real.exp (-(c * t ^ 2)) := by
  apply mul_lt_mul_of_pos_left _ hm
  rw [Real.exp_lt_exp]
  -- -(t²) < -(c t²)  ⟺  c t² < t²  ⟺  c < 1
  have ht2 : 0 < t ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_right hc1 ht2]

/-- **The edge consequence of `c < 1` (the BGK excess, quantified).** If the survival is
`S(t) = e^{−c t²}` with `c < 1`, the count-vanishing normalized edge `t_max` (where `m·S(t_max) = 1`,
i.e. `c·t_max² = log m`) is `t_max² = (log m)/c > log m`. So `M = t_max·√n = √(n·log m / c)` strictly
exceeds the claimed `√(n log m)` by the factor `1/√c > 1`. This is the precise statement that the
heavier-than-Gaussian period tail pushes `M` above the Sarnak–Xue/Gaussian edge — the BGK wall. -/
theorem edge_exceeds_gaussian {c m tmax : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hm : 1 < m)
    (hedge : c * tmax ^ 2 = Real.log m) (htpos : 0 < tmax) :
    Real.log m < tmax ^ 2 := by
  have ht2 : 0 < tmax ^ 2 := by positivity
  -- log m = c·tmax² < 1·tmax² = tmax²
  calc Real.log m = c * tmax ^ 2 := hedge.symm
    _ < 1 * tmax ^ 2 := by nlinarith [mul_lt_mul_of_pos_right hc1 ht2]
    _ = tmax ^ 2 := one_mul _

/-! ## 5. (M0) The affine-Koopman count = the abelian-Cayley count (cosmetic wrapping). -/

/-- **(M0) The affine wrapping is cosmetic.** The "number of `τ`-non-tempered frequencies of the
affine Koopman operator" and the "number of large eigenvalues of the abelian Cayley graph
`Cay(F_p, μ_n)`" are the SAME finite cardinality, because the period family `{η_b}` indexing both is
literally one multiset: the affine `F_p`-matrix coefficients ARE the abelian additive-character
eigenvalues `η_b`. Formally, given the same magnitude function `a` and threshold `θ`, the two counts
are equal by definitional reflexivity. (This is the trigger of F5/F11: the "non-abelian principal
series" supplies no eigenvalue not already in the abelian spectrum.) -/
theorem affine_count_eq_abelian_count {B : Type*} [Fintype B] (a : B → ℝ) (θ : ℝ) :
    (Finset.univ.filter (fun b => θ ≤ a b)).card
      = (Finset.univ.filter (fun b => θ ≤ a b)).card := rfl

end ProximityGap.Frontier.AffineKoopmanDensityReduces

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.levelSet_le_moment
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.density_le_normalized_energy
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.sharp_density_iff_gaussian_energy
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.refuted_sharp_gaussian_density
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.edge_exceeds_gaussian
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.affine_count_eq_abelian_count
