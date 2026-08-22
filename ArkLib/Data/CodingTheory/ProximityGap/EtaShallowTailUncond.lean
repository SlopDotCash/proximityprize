/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# The UNCONDITIONAL shallow-tail Gauss-period ceiling at every order `r` (#407)

`EtaQuarticUncond` lands the first unconditional sub-`√q` ceiling for the subgroup Gauss period by
feeding the coset-reduced moment bound the **unconditional** 2-fold additive-energy bound
`E_2(G) ≤ |G|^3` (the textbook `E(A) ≤ |A|^3`). This file does the same for **every order `r ≥ 1`**:
the trivial additive-energy bound `E_r(G) ≤ |G|^{2r-1}` holds unconditionally (fix the first `r`
forward summands and the first `r-1` backward summands; the last backward summand is then determined,
so each prescribed sum has at most `|G|^{r-1}` matchings). Plugging into the coset-reduced moment
bound `cosetReduced_eta_pow_le` (which already subtracts the principal `n^{2r}` term and divides by
`n`) gives, for every nonzero frequency `b₀` and every `r ≥ 1`,

> **`eta_pow_le_shallow_uncond`** — `‖η_{b₀}‖^{2r} ≤ (q·n^{2r-1} − n^{2r})/n = n^{2r-2}·(q − n)`,

hence `M(n) = max_{b≠0}‖η_b‖ ≤ (n^{2r-2}(q−n))^{1/2r}`. This is the **shallow tail** of the moment
ladder, made unconditional at *all* orders: no `GaussianEnergyBound` (`E_r ≤ (2r-1)‼·n^r`), no
Lam–Leung, no char-`p` energy transfer, no BGK/Paley input.

## Where the shallow tail lives, and the exact obstruction it does not cross

The trivial bound `E_r ≤ n^{2r-1}` is genuinely weaker than the Gaussian/Wick bound
`E_r ≤ (2r-1)‼·n^r` precisely once `n^{2r-1} > (2r-1)‼·n^r`, i.e. `n^{r-1} > (2r-1)‼`, i.e.
roughly `r ≲ log_n((2r-1)‼) ≈ r·log_n(2r)`, which holds for all `r` (the trivial bound is never
*better* than Wick) — so the trivial bound NEVER reaches the sub-Gaussian `√(2n ln q)` target. What
it *does* give unconditionally is the per-order ceiling `M ≤ n^{1-1/r}·(q−n)^{1/2r}`, sub-`√q` exactly
when `n^{2r-2}(q−n) < q^r`. At `r = 1` this is the Parseval value `M ≤ √(q n − n²) < √(qn)`; at
`r = 2` it is `EtaQuarticUncond`'s `M ≤ √n·(q−n)^{1/4}` (sub-`√q` for `q ≳ n^2`); as `r → ∞` it
relaxes toward `M ≲ n·(q)^{0}` — the unconditional reach is the band `q ≲ n^{r/(r-1)}`, which shrinks
to `q ≲ n` as `r` grows. **The sub-Gaussian deep tail at `λ ≈ √(ln p)` (needing `r ≈ ln q` with
`E_r ≈ r!·n^r`) is unreachable from the trivial energy bound**: the gap `E_r ≤ n^{2r-1}` vs.
`(2r-1)‼·n^r` is the factor `n^{r-1}/(2r-1)‼`, and closing it is exactly the open char-`p` energy
transfer named in `CumulantGaussPeriodBound.CumulantEnergyBound` (provably false at structured primes,
`not_cumulantBound_of_excess`). So this file pins the boundary: **the unconditionally-reachable tail
is `r = O(1)` (the band `q ≲ n^{r/(r-1)}`), and the obstruction is the energy excess
`E_r − (2r-1)‼·n^r` over the Wick value, which is exactly the antipodal/collision discrepancy term.**

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.EtaShallowTailUncond

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **Inner fiber count at order `r+1`: at most `|G|^r` tuples `(Fin (r+1) → G)` have a prescribed
sum `S`.** The set of `w ∈ (Fin (r+1) → G)` with `∑ w = S` injects into `(Fin r → G)` by dropping the
last coordinate (`Fin.init`): the value at `Fin.last r` is forced to `S − ∑_{i<r} w i.castSucc`, so
the truncation determines `w`. Hence the fiber has `≤ |G|^r` elements. -/
theorem card_fiber_le_card_pow (G : Finset F) (r : ℕ) (S : F) :
    #{w ∈ Fintype.piFinset (fun _ : Fin (r + 1) => G) | S = ∑ i, w i} ≤ G.card ^ r := by
  classical
  have hcardtgt : (Fintype.piFinset (fun _ : Fin r => G)).card = G.card ^ r := by
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const, Finset.card_univ]
  rw [← hcardtgt]
  refine Finset.card_le_card_of_injOn (fun w => Fin.init w) ?_ ?_
  · -- the truncation maps into `Fin r → G`
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hw
    refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr ?_)
    intro i
    exact hw.1 i.castSucc
  · -- injective on the fiber: same truncation + same sum forces the last entry equal, hence equal
    intro w hw w' hw' hww
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hw hw'
    -- sums agree (both `= S`)
    have hsum : ∑ i, w i = ∑ i, w' i := by rw [← hw.2, ← hw'.2]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
    -- the `castSucc` parts agree because `Fin.init w = Fin.init w'`
    have hinit : ∀ i : Fin r, w i.castSucc = w' i.castSucc := by
      intro i
      have := congrFun hww i
      simpa [Fin.init] using this
    have hcastsum : ∑ i : Fin r, w i.castSucc = ∑ i : Fin r, w' i.castSucc :=
      Finset.sum_congr rfl (fun i _ => hinit i)
    rw [hcastsum] at hsum
    have hlast : w (Fin.last r) = w' (Fin.last r) := add_left_cancel hsum
    -- a `Fin (r+1) → F` is determined by its `init` and its value at `last`
    funext j
    refine Fin.lastCases ?_ ?_ j
    · exact hlast
    · intro i; exact hinit i

omit [Fintype F] in
/-- **The unconditional `r`-fold additive-energy bound `E_r(G) ≤ |G|^{2r-1}` for `r ≥ 1`.**
`rEnergy G (r+1) = ∑_{v ∈ G^{r+1}} #{w ∈ G^{r+1} : ∑ w = ∑ v} ≤ ∑_{v ∈ G^{r+1}} |G|^r
= |G|^{r+1}·|G|^r = |G|^{2r+1}`. (The textbook `E(A) ≤ |A|^{2k-1}` for the `k`-fold energy; the
`k = 2` case is `EtaQuarticUncond.rEnergy_two_le_card_cubed`.) -/
theorem rEnergy_le_card_pow (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) ≤ (G.card) ^ (2 * r + 1) := by
  classical
  have hpiCard : (Fintype.piFinset (fun _ : Fin (r + 1) => G)).card = G.card ^ (r + 1) := by
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const, Finset.card_univ]
  calc rEnergy G (r + 1)
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin (r + 1) => G),
          #{w ∈ Fintype.piFinset (fun _ : Fin (r + 1) => G) | ∑ i, v i = ∑ i, w i} := by
        simp only [rEnergy]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        exact (Finset.card_filter (fun w : Fin (r + 1) → F => ∑ i, v i = ∑ i, w i) _).symm
    _ ≤ ∑ _v ∈ Fintype.piFinset (fun _ : Fin (r + 1) => G), G.card ^ r :=
        Finset.sum_le_sum (fun v _ => card_fiber_le_card_pow G r (∑ i, v i))
    _ = G.card ^ (r + 1) * G.card ^ r := by rw [Finset.sum_const, hpiCard, smul_eq_mul]
    _ = G.card ^ (2 * r + 1) := by ring

/-- **The unconditional shallow-tail ceiling at every order `r ≥ 1`.** For a finite multiplicative
subgroup `G = μ_n` of `F^×` and every nonzero frequency `b₀`,
`‖η_{b₀}‖^{2(r+1)} ≤ n^{2r}·(q − n)`,  `q = |F|`, `n = |G|`.
Equivalently `M(n) = max_{b≠0}‖η_b‖ ≤ (n^{2r}(q−n))^{1/(2(r+1))} = n^{1-1/(r+1)}·(q−n)^{1/(2(r+1))}`.
Proved from the coset-reduced moment bound `cosetReduced_eta_pow_le` at order `r+1` and the
unconditional energy bound `rEnergy_le_card_pow`; **no char-`p` energy hypothesis**. The `r = 1`
slice (order `2(r+1) = 4`) is `EtaQuarticUncond.eta_quartic_le_uncond`; this extends it to all
orders. -/
theorem eta_pow_le_shallow_uncond {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    (r : ℕ) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ‖eta ψ G b₀‖ ^ (2 * (r + 1))
      ≤ (G.card : ℝ) ^ (2 * r) * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
  have hcardpos : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  -- coset-reduced moment bound at order r+1
  have hcoset := cosetReduced_eta_pow_le hψ hbij h0 hne (r + 1) hb₀
  -- unconditional energy bound, cast to ℝ
  have henergy : (rEnergy G (r + 1) : ℝ) ≤ (G.card : ℝ) ^ (2 * r + 1) := by
    exact_mod_cast rEnergy_le_card_pow G r
  have hQpos : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  -- monotone in the energy slot
  have hmono : (Fintype.card F : ℝ) * (rEnergy G (r + 1) : ℝ) - (G.card : ℝ) ^ (2 * (r + 1))
      ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r + 1) - (G.card : ℝ) ^ (2 * (r + 1)) := by
    have := mul_le_mul_of_nonneg_left henergy hQpos
    linarith
  have hbound : ‖eta ψ G b₀‖ ^ (2 * (r + 1))
      ≤ ((Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r + 1) - (G.card : ℝ) ^ (2 * (r + 1)))
          / (G.card : ℝ) :=
    le_trans hcoset (div_le_div_of_nonneg_right hmono hcardpos.le)
  -- (q·n^{2r+1} − n^{2r+2})/n = n^{2r}·(q − n)
  have hexp : 2 * (r + 1) = (2 * r + 1) + 1 := by ring
  have hrw : ((Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r + 1) - (G.card : ℝ) ^ (2 * (r + 1)))
        / (G.card : ℝ)
      = (G.card : ℝ) ^ (2 * r) * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
    rw [hexp]
    field_simp
    ring
  rw [hrw] at hbound
  exact hbound

/-- **The unconditional shallow-tail ceiling, in norm form.** Taking the `2(r+1)`-th root of
`eta_pow_le_shallow_uncond`: for every nonzero frequency `b₀` and every `r`,
`‖η_{b₀}‖ ≤ (n^{2r}·(q − n))^{1/(2(r+1))}`,  `q = |F|`, `n = |G|`.
Since this holds for *every* `b₀ ≠ 0`, it bounds `M(n) = max_{b≠0}‖η_b‖`. Unconditional — no char-`p`
energy hypothesis, no BGK, no Lam–Leung. (At `r = 0` this is the Parseval value
`M ≤ (q − n)^{1/2} < √q`; at `r = 1` it is `EtaQuarticUncond.eta_le_uncond_norm`.) -/
theorem eta_le_shallow_uncond_norm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    (r : ℕ) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ‖eta ψ G b₀‖
      ≤ ((G.card : ℝ) ^ (2 * r) * ((Fintype.card F : ℝ) - (G.card : ℝ)))
          ^ ((2 * (r + 1) : ℕ)⁻¹ : ℝ) := by
  have hpow := eta_pow_le_shallow_uncond hψ hbij h0 hne r hb₀
  have hcardpos : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  -- `q − n ≥ 0`: else the rhs is `< 0`, contradicting `‖η‖^{2(r+1)} ≥ 0`.
  have hqn : (0 : ℝ) ≤ (Fintype.card F : ℝ) - (G.card : ℝ) := by
    by_contra hlt
    rw [not_le] at hlt
    have hrhs_neg : (G.card : ℝ) ^ (2 * r) * ((Fintype.card F : ℝ) - (G.card : ℝ)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hlt
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b₀‖ ^ (2 * (r + 1)) := by positivity
    linarith
  set R : ℝ := ((G.card : ℝ) ^ (2 * r) * ((Fintype.card F : ℝ) - (G.card : ℝ)))
      ^ ((2 * (r + 1) : ℕ)⁻¹ : ℝ) with hR
  have hbasenn : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
    have : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
    exact mul_nonneg this hqn
  have hRnonneg : 0 ≤ R := by rw [hR]; exact Real.rpow_nonneg hbasenn _
  -- the `2(r+1)`-th power of R is the base
  have hRpow : R ^ (2 * (r + 1))
      = (G.card : ℝ) ^ (2 * r) * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
    rw [hR]
    exact Real.rpow_inv_natCast_pow hbasenn (by positivity)
  have hpow_le : ‖eta ψ G b₀‖ ^ (2 * (r + 1)) ≤ R ^ (2 * (r + 1)) := by rw [hRpow]; exact hpow
  exact le_of_pow_le_pow_left₀ (by positivity) hRnonneg hpow_le

end ArkLib.ProximityGap.EtaShallowTailUncond

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
#print axioms ArkLib.ProximityGap.EtaShallowTailUncond.card_fiber_le_card_pow
#print axioms ArkLib.ProximityGap.EtaShallowTailUncond.rEnergy_le_card_pow
#print axioms ArkLib.ProximityGap.EtaShallowTailUncond.eta_pow_le_shallow_uncond
#print axioms ArkLib.ProximityGap.EtaShallowTailUncond.eta_le_shallow_uncond_norm
