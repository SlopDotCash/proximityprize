/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# R389: C-inflated Wick energy budget ⇒ the corrected `√(C·n·log q)` sup bound

Session 2026-07-09 (#466), route **wick-excess-tower**, companion to
`_R341CAZACCosetEquivalence` (the exact Mellin ⟺ coset dictionary) and successor to the
r304 refutation of the C = 1 Wick chain.

## What this brick is

r304 refuted exact Wick at prize depth (`E₃ ≤ 15n³` is FALSE at `n = 32`; the excess is an
exact cyclotomic difference-class sum), so the in-tree C = 1 chain
(`GaussPeriodMomentBound.GaussianEnergyBound` → `eta_pow_le_of_energyBound`, and its
DC-subtracted correction `DCEnergyCorrection.DCEnergyBound` → `eta_pow_le_of_dcEnergyBound`)
cannot be the carrier.  The 2026-07-09 excess-theory round showed the non-Wick excess is
**bounded-ratio, not a blow-up**: a constant `C`-inflation of the Wick budget absorbs every
measured cell.  This brick installs that `C`-inflated budget as the named hypothesis and
proves, axiom-clean, the full real-arithmetic consumer chain down to the corrected
`√(m log q)` CAZAC/PAPR constant of the r341 dictionary.

## PROVEN here (machine-checked, axiom-clean)

* `GaussianEnergyBudget` / `DCEnergyBudget` — the `C`-inflated budgets
  (`E_r ≤ C^r·(2r−1)‼·n^r`, resp. `q·E_r − n^{2r} ≤ q·C^r·(2r−1)‼·n^r`), with welds
  `gaussianEnergyBudget_one_iff` / `dcEnergyBudget_one_iff` to the in-tree C = 1 predicates
  and monotonicity `DCEnergyBudget.mono` in `C`.
* `doubleFactorial_le_pow` — the AM-GM calibration `(2k−1)‼ ≤ k^k` (all `k`), via the
  Bernoulli step `two_mul_pow_le_succ_pow : 2·k^k ≤ (k+1)^k` for `k ≥ 1`.
* `eta_pow_le_of_energyBudget` / `eta_pow_le_of_dcEnergyBudget` — the per-frequency power
  bounds `‖η_b‖^{2r} ≤ q·C^r·(2r−1)‼·n^r` (the C = 1 in-tree proofs with `C^r` carried).
* `sup_le_of_dcEnergyBudget` — **moment-to-sup at any calibrated depth**: if
  `log q ≤ 2r` and `DCEnergyBudget G r C`, then `‖η_b‖ ≤ e·√(C·r·n)` for every `b ≠ 0`.
  Purely elementary: `‖η‖^{2r} ≤ q·C^r·k^k·n^r ≤ (e·√(Crn))^{2r}`, take `2r`-th roots.
* `sup_le_three_sqrt_of_dcEnergyBudget` — **the headline instantiation** at the single
  depth `k* = wickDepth q = ⌈(log q)/2⌉₊`: for `q ≥ 5`,
  `DCEnergyBudget G k* C  ⟹  ∀ b ≠ 0, ‖η_b‖ ≤ 3·√(C·n·log q)`.
  (The task-level claim quoted constant `3` via the coset `/d` saving at `q ≥ 3`; here the
  constant `3` is proven WITHOUT the coset saving for `q ≥ 5`, using
  `e²·(log q/2 + 1) ≤ 9·log q` for `log q ≥ 3/2` and `log 5 > 3/2` from `e³ < 25`.)
* `sup_le_of_uniformSubgroupWickBudget` — the packaged consumer of the named open Prop.
* `mellin_papr_transfer` — **the r341 Mellin/CAZAC transfer, abstract arithmetic form**:
  from the r341 identity's bound `Mₙ ≤ (m·S + 1)/√q` (`norm_mellinSum_le_coset`, restated
  as a hypothesis per lane hygiene — frontier files do not import frontier oleans) and
  `S ≤ 3√(C·d·log q)` with `m·d ≤ q`, conclude `Mₙ ≤ 3·√(C·m·log q) + 1` — the corrected
  `√(m log p)` CAZAC/PAPR bound (the literal `√(m log m)` claim was conditionally refuted
  2026-07-09).
* `charZeroEnergy_two_d8` — **kernel-decided anchor**: the char-0 depth-2 energy of
  `μ₈ ⊂ ℤ[ζ₈]` is exactly `V₂(8) = 168` (counted in the integral basis `1,ζ,ζ²,ζ³`,
  `ζ⁴ = −1`), matching the 2026-07-09 probe suite bit-exact, with
  `charZeroEnergy_two_d8_le_wick : 168 ≤ 3·8² = 192` — a concrete machine-checked instance
  of char-0 Wick domination (`V_k(d) ≤ (2k−1)‼·d^k`, proven on paper for all `d = 2^j`).

## NAMED OPEN (do not discharge — this is the wall in energy coordinates)

* `UniformSubgroupWickBudget C` — `DCEnergyBudget (μ_d) (wickDepth q) C` for every finite
  field `F` and every `d`, at one absolute `C`.  Census evidence (2026-07-09,
  verifier-audited): over 14,693 dense-census primes (`d ∈ {12,…,64}`, `k ≤ 12`), a
  513-cell 2-adically-rich ladder, and the complete chain-family scan `p ≤ 1.2·10⁶`, the
  observed `C_needed = (moment/Wick)^{1/k}` is `≤ 3.47` globally; in the route-relevant
  regime `β = log p/log d ≥ 2.3` the max over all depths is `2.61` and the max at route
  depth `k*` is `2.07`, both attained at the pure-2-chain cell `(p,d) = (279073, 108)`
  (NOT the Fermat prime — the corrected worst cell); dense-census `q95 ≤ 1.06`.  All
  numerics live at `k* ≤ 7`, `β ∈ [1.5, 5.3]`, `p ≤ 2.15·10⁷`; the deep-window `k* ≥ 8`
  regime is beyond FFT reach and is supported only by the exact structure theory (support
  cutoff `N_k = V_k` for `p > (2k)^{φ(d)}`, peak-and-decay, per-vector bounds).  The
  hypothesis is OPEN in both directions throughout the honest window; already its `k = 2`
  instance gives `E₊(H) ≤ 3C²d² + d⁴/p` uniformly in `p` (note the mandatory `+ d⁴/p` DC
  main term), beyond the Heath-Brown–Konyagin `d^{5/2}` and Shkredov-school `~d^{32/13}`
  additive-energy bounds.  Numerics are evidence, not proof.

Everything proven below consumes exactly this ONE named hypothesis (or none).  Known-dead
routes NOT retreaded here: aggregate fixed-depth exact Wick (r304), resonance refutation,
two-generator refuters, metaplectic at growing `m`.

Issue #466, round 389, route wick-excess-tower.
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCMomentSupBound

namespace ArkLib.ProximityGap.R389WickBudgetSupBound

/-! ## The C-inflated budgets and welds to the refuted C = 1 predicates -/

section Budgets

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The C-inflated full-energy Wick budget**: `E_r(G) ≤ C^r·(2r−1)‼·|G|^r`.  At `C = 1`
this is exactly the in-tree `GaussPeriodMomentBound.GaussianEnergyBound` (DC-included form,
false past the DC crossover at prize depth). -/
def GaussianEnergyBudget (G : Finset F) (r : ℕ) (C : ℝ) : Prop :=
  (rEnergy G r : ℝ) ≤ C ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- **The C-inflated DC-subtracted energy budget** (the prize-relevant form):
`q·E_r(G) − |G|^{2r} ≤ q·C^r·(2r−1)‼·|G|^r`.  At `C = 1` this is exactly the in-tree
`DCEnergyCorrection.DCEnergyBound`, whose exactness r304 refuted; the census-supported
inflation is `C ≈ 3.5` globally (`≈ 2.7` for `β ≥ 2.3`, all measured depths). -/
def DCEnergyBudget (G : Finset F) (r : ℕ) (C : ℝ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ)
        * (C ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)

/-- At `C = 1` the full-energy budget is literally the in-tree `GaussianEnergyBound`. -/
theorem gaussianEnergyBudget_one_iff (G : Finset F) (r : ℕ) :
    GaussianEnergyBudget G r 1
      ↔ ArkLib.ProximityGap.GaussPeriodMomentBound.GaussianEnergyBound G r := by
  simp [GaussianEnergyBudget,
    ArkLib.ProximityGap.GaussPeriodMomentBound.GaussianEnergyBound]

/-- At `C = 1` the DC-subtracted budget is literally the in-tree `DCEnergyBound`. -/
theorem dcEnergyBudget_one_iff (G : Finset F) (r : ℕ) :
    DCEnergyBudget G r 1 ↔ ArkLib.ProximityGap.DCEnergyCorrection.DCEnergyBound G r := by
  simp [DCEnergyBudget, ArkLib.ProximityGap.DCEnergyCorrection.DCEnergyBound]

/-- The budget is monotone in the inflation constant. -/
theorem DCEnergyBudget.mono {G : Finset F} {r : ℕ} {C C' : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (h : DCEnergyBudget G r C) : DCEnergyBudget G r C' := by
  refine h.trans ?_
  have hpow : C ^ r ≤ C' ^ r := pow_le_pow_left₀ hC hCC r
  have hinner : C ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
      ≤ C' ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) r)
    exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)

end Budgets

/-! ## The AM-GM calibration `(2k−1)‼ ≤ k^k` -/

/-- Bernoulli's inequality, nonneg case (self-contained induction):
`1 + n·x ≤ (1+x)^n` for `x ≥ 0`. -/
theorem one_add_nsmul_le_pow_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    1 + (n : ℝ) * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (1 + (n : ℝ) * x) * (1 + x) ≤ (1 + x) ^ n * (1 + x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h3 : 1 + ((n : ℝ) + 1) * x ≤ (1 + (n : ℝ) * x) * (1 + x) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hx hx)]
    push_cast
    rw [pow_succ]
    linarith [h2, h3]

/-- Bernoulli step: `2·k^k ≤ (k+1)^k` for `k ≥ 1` (first two binomial terms,
via `(1 + 1/k)^k ≥ 1 + k·(1/k) = 2`). -/
theorem two_mul_pow_le_succ_pow {k : ℕ} (hk : 1 ≤ k) :
    2 * (k : ℝ) ^ k ≤ ((k : ℝ) + 1) ^ k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hbern := one_add_nsmul_le_pow_of_nonneg (x := 1 / (k : ℝ)) (by positivity) k
  have h1 : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
    rw [one_div, mul_inv_cancel₀ hkne]
  have h2 : (2 : ℝ) ≤ (1 + 1 / (k : ℝ)) ^ k := by
    rw [h1] at hbern
    linarith [hbern]
  have h3 : 2 * (k : ℝ) ^ k ≤ (1 + 1 / (k : ℝ)) ^ k * (k : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right h2 (pow_nonneg hk0.le k)
  have h4 : (1 + 1 / (k : ℝ)) * (k : ℝ) = (k : ℝ) + 1 := by
    rw [add_mul, one_mul, one_div, inv_mul_cancel₀ hkne]
  have h5 : (1 + 1 / (k : ℝ)) ^ k * (k : ℝ) ^ k = ((k : ℝ) + 1) ^ k := by
    rw [← mul_pow, h4]
  linarith [h3, h5]

/-- **AM-GM for the double factorial**: `(2k−1)‼ ≤ k^k` for every `k` (the product of
`1, 3, …, 2k−1` has arithmetic mean `k`).  This is the exact calibration that turns the
Wick budget `C^k·(2k−1)‼·n^k` into `(C·k·n)^k`, i.e. `M_k^{1/2k} ≈ √(k·n)`. -/
theorem doubleFactorial_le_pow (k : ℕ) :
    (Nat.doubleFactorial (2 * k - 1) : ℝ) ≤ (k : ℝ) ^ k := by
  induction k with
  | zero => norm_num [Nat.doubleFactorial]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; norm_num [Nat.doubleFactorial]
    · have hidx : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
      have hrecN : Nat.doubleFactorial (2 * (k + 1) - 1)
          = (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) := by
        rw [hidx, Nat.doubleFactorial_add_two]
        congr 1
        omega
      have hstep := two_mul_pow_le_succ_pow hkpos
      have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      push_cast
      rw [hrecN]
      push_cast
      calc (2 * (k : ℝ) + 1) * (Nat.doubleFactorial (2 * k - 1) : ℝ)
          ≤ (2 * (k : ℝ) + 1) * (k : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ ((k : ℝ) + 1) * (2 * (k : ℝ) ^ k) := by nlinarith [pow_nonneg hkR k]
        _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ k := by
            apply mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = ((k : ℝ) + 1) ^ (k + 1) := by rw [pow_succ]; ring

/-! ## Per-frequency power bounds with the `C^r` carried -/

section PowerBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Per-frequency power bound from the full-energy budget (every `b`, DC included):
`‖η_b‖^{2r} ≤ q·C^r·(2r−1)‼·|G|^r`.  Same proof as the in-tree C = 1
`eta_pow_le_of_energyBound`, with the inflation carried. -/
theorem eta_pow_le_of_energyBudget {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {r : ℕ} {C : ℝ} (h : GaussianEnergyBudget G r C) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * (C ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) (Finset.mem_univ b)
  rw [subgroup_gaussSum_moment hψ G r] at hterm
  exact hterm.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

/-- Per-frequency power bound from the DC-subtracted budget (`b ≠ 0`, non-vacuous at prize
depth): `‖η_b‖^{2r} ≤ q·C^r·(2r−1)‼·|G|^r`.  Chains the unconditional `eta_pow_le_dc`
with the budget. -/
theorem eta_pow_le_of_dcEnergyBudget {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {r : ℕ} {C : ℝ} (h : DCEnergyBudget G r C) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * (C ^ r * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
  (eta_pow_le_dc hψ G r hb).trans h

/-! ## Moment-to-sup: the calibrated-depth theorems -/

/-- **Moment-to-sup at any calibrated depth.**  If the depth `r ≥ 1` satisfies
`log q ≤ 2r` and the DC-subtracted budget holds at `(r, C)`, then every nontrivial Gauss
period obeys `‖η_b‖ ≤ e·√(C·r·|G|)`.  Proof: `‖η_b‖^{2r} ≤ q·C^r·(2r−1)‼·|G|^r ≤
q·(C·r·|G|)^r ≤ e^{2r}·(C·r·|G|)^r = (e·√(C·r·|G|))^{2r}`, then take `2r`-th roots. -/
theorem sup_le_of_dcEnergyBudget {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {r : ℕ} {C : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hlog : Real.log (Fintype.card F) ≤ 2 * (r : ℝ))
    (h : DCEnergyBudget G r C) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ Real.exp 1 * Real.sqrt (C * (r : ℝ) * (G.card : ℝ)) := by
  have hcard : 0 < Fintype.card F := Fintype.card_pos
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hcard
  have hn0 : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hCr : (0 : ℝ) ≤ C ^ r := pow_nonneg hC r
  have hqe : (Fintype.card F : ℝ) ≤ Real.exp (2 * (r : ℝ)) := by
    calc (Fintype.card F : ℝ)
        = Real.exp (Real.log (Fintype.card F)) := (Real.exp_log hq0).symm
      _ ≤ Real.exp (2 * (r : ℝ)) := Real.exp_le_exp.mpr hlog
  have hpow1 : ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (C ^ r * (r : ℝ) ^ r * (G.card : ℝ) ^ r) := by
    refine (eta_pow_le_of_dcEnergyBudget hψ h hb).trans ?_
    apply mul_le_mul_of_nonneg_left _ hq0.le
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hn0 r)
    exact mul_le_mul_of_nonneg_left (doubleFactorial_le_pow r) hCr
  have hCrn : (0 : ℝ) ≤ C * (r : ℝ) * (G.card : ℝ) := mul_nonneg (mul_nonneg hC hr0) hn0
  have hpow2 : ‖eta ψ G b‖ ^ (2 * r)
      ≤ Real.exp (2 * (r : ℝ)) * (C ^ r * (r : ℝ) ^ r * (G.card : ℝ) ^ r) := by
    refine hpow1.trans ?_
    apply mul_le_mul_of_nonneg_right hqe
    exact mul_nonneg (mul_nonneg hCr (pow_nonneg hr0 r)) (pow_nonneg hn0 r)
  have hrhs : Real.exp (2 * (r : ℝ)) * (C ^ r * (r : ℝ) ^ r * (G.card : ℝ) ^ r)
      = (Real.exp 1 * Real.sqrt (C * (r : ℝ) * (G.card : ℝ))) ^ (2 * r) := by
    have hexp : Real.exp (2 * (r : ℝ)) = Real.exp 1 ^ (2 * r) := by
      rw [Real.exp_one_pow]
      congr 1
      push_cast
      ring
    have hsqrt : Real.sqrt (C * (r : ℝ) * (G.card : ℝ)) ^ (2 * r)
        = (C * (r : ℝ) * (G.card : ℝ)) ^ r := by
      rw [pow_mul, Real.sq_sqrt hCrn]
    rw [mul_pow, hexp, hsqrt, mul_pow, mul_pow]
  have hbase : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (C * (r : ℝ) * (G.card : ℝ)) :=
    mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _)
  have h2r : 2 * r ≠ 0 := by omega
  exact le_of_pow_le_pow_left₀ h2r hbase (hrhs ▸ hpow2)

end PowerBounds

/-- The calibrated Wick depth `k* = ⌈(log q)/2⌉₊` — the single moment order at which the
budget is consumed (`2k* ≥ log q` makes `q^{1/2k*} ≤ e`; `k* ≤ log q/2 + 1` keeps
`√k* ≲ √log q`). -/
noncomputable def wickDepth (q : ℕ) : ℕ := ⌈Real.log (q : ℝ) / 2⌉₊

section Headline

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The headline `√(C·n·log q)` sup bound at the single depth `k*`.**  For `q ≥ 5`:
`DCEnergyBudget G (wickDepth q) C  ⟹  ∀ b ≠ 0, ‖η_b‖ ≤ 3·√(C·|G|·log q)`.
Constants: `e²·(log q/2 + 1) ≤ 9·log q` as soon as `log q ≥ 3/2`, and `log 5 > 3/2`
(from `e³ < 25`).  Via the r341 dictionary this is the corrected-CAZAC `√(m log p)` shape
with constant `3√C`. -/
theorem sup_le_three_sqrt_of_dcEnergyBudget {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {C : ℝ} (hC : 0 ≤ C) (hq5 : 5 ≤ Fintype.card F)
    (h : DCEnergyBudget G (wickDepth (Fintype.card F)) C) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ 3 * Real.sqrt (C * (G.card : ℝ) * Real.log (Fintype.card F)) := by
  have hq5R : (5 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq5
  -- e-numerics: e·e < 7.3890560990 and e³ < 25
  have he := Real.exp_one_lt_d9
  have hepos := (Real.exp_pos 1).le
  have he2 : Real.exp 1 * Real.exp 1 < 7.39 := by nlinarith [he, hepos]
  have he3 : Real.exp 1 * Real.exp 1 * Real.exp 1 < 25 := by
    nlinarith [he, he2, hepos, mul_nonneg hepos hepos]
  -- log 5 > 3/2, hence log q ≥ 3/2
  have hexp3 : Real.exp (3 / 2 : ℝ) * Real.exp (3 / 2 : ℝ)
      = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hlog5 : (3 : ℝ) / 2 < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)]
    nlinarith [Real.exp_pos (3 / 2 : ℝ), hexp3, he3]
  have hlogq : (3 : ℝ) / 2 ≤ Real.log (Fintype.card F) := by
    calc (3 : ℝ) / 2 ≤ Real.log 5 := hlog5.le
      _ ≤ Real.log (Fintype.card F) := Real.log_le_log (by norm_num) hq5R
  have hlogpos : (0 : ℝ) < Real.log (Fintype.card F) := by linarith
  -- depth facts for k* = ⌈log q / 2⌉₊
  have hk1 : 1 ≤ wickDepth (Fintype.card F) := by
    unfold wickDepth
    exact Nat.ceil_pos.mpr (by linarith)
  have hklog : Real.log (Fintype.card F) ≤ 2 * (wickDepth (Fintype.card F) : ℝ) := by
    have hceil := Nat.le_ceil (Real.log (Fintype.card F) / 2)
    unfold wickDepth
    linarith [hceil]
  have hkle : (wickDepth (Fintype.card F) : ℝ) < Real.log (Fintype.card F) / 2 + 1 := by
    unfold wickDepth
    exact Nat.ceil_lt_add_one (by linarith)
  -- general bound at depth k*
  have hmain := sup_le_of_dcEnergyBudget hψ hC hk1 hklog h hb
  refine hmain.trans ?_
  -- calibrate: e·√(C·k*·n) ≤ 3·√(C·n·log q)
  have hn0 : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (wickDepth (Fintype.card F) : ℝ) := Nat.cast_nonneg _
  have hCkn : (0 : ℝ) ≤ C * (wickDepth (Fintype.card F) : ℝ) * (G.card : ℝ) :=
    mul_nonneg (mul_nonneg hC hk0) hn0
  have hcal : Real.exp 1 ^ 2 * (wickDepth (Fintype.card F) : ℝ)
      ≤ 9 * Real.log (Fintype.card F) := by
    have hesq : Real.exp 1 ^ 2 < 7.39 := by rw [sq]; exact he2
    have hstep1 : Real.exp 1 ^ 2 * (wickDepth (Fintype.card F) : ℝ)
        ≤ Real.exp 1 ^ 2 * (Real.log (Fintype.card F) / 2 + 1) :=
      mul_le_mul_of_nonneg_left hkle.le (sq_nonneg _)
    have hstep2 : Real.exp 1 ^ 2 * (Real.log (Fintype.card F) / 2 + 1)
        ≤ 7.39 * (Real.log (Fintype.card F) / 2 + 1) := by
      apply mul_le_mul_of_nonneg_right hesq.le
      linarith
    linarith [hstep1, hstep2, hlogq]
  have hglue : Real.exp 1 ^ 2 * (C * (wickDepth (Fintype.card F) : ℝ) * (G.card : ℝ))
      ≤ 9 * (C * (G.card : ℝ) * Real.log (Fintype.card F)) := by
    have hcn : (0 : ℝ) ≤ C * (G.card : ℝ) := mul_nonneg hC hn0
    nlinarith [mul_le_mul_of_nonneg_left hcal hcn]
  have hleft : Real.exp 1 * Real.sqrt (C * (wickDepth (Fintype.card F) : ℝ) * (G.card : ℝ))
      = Real.sqrt (Real.exp 1 ^ 2
          * (C * (wickDepth (Fintype.card F) : ℝ) * (G.card : ℝ))) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos 1).le]
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hright : 3 * Real.sqrt (C * (G.card : ℝ) * Real.log (Fintype.card F))
      = Real.sqrt (9 * (C * (G.card : ℝ) * Real.log (Fintype.card F))) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9), h9]
  calc Real.exp 1 * Real.sqrt (C * (wickDepth (Fintype.card F) : ℝ) * (G.card : ℝ))
      = Real.sqrt (Real.exp 1 ^ 2
          * (C * (wickDepth (Fintype.card F) : ℝ) * (G.card : ℝ))) := hleft
    _ ≤ Real.sqrt (9 * (C * (G.card : ℝ) * Real.log (Fintype.card F))) :=
        Real.sqrt_le_sqrt hglue
    _ = 3 * Real.sqrt (C * (G.card : ℝ) * Real.log (Fintype.card F)) := hright.symm

end Headline

/-! ## The named open Prop and its packaged consumer -/

/-- The `d`-torsion set `μ_d = {y : F | y^d = 1}` as a finset (the substrate's smooth
domain; self-contained here so this lane stays frontier-import-free). -/
def torsionSet (F : Type*) [Fintype F] [DecidableEq F] [Monoid F] (d : ℕ) : Finset F :=
  Finset.univ.filter (fun y => y ^ d = 1)

/-- **NAMED OPEN (do not discharge) — the wall in energy coordinates.**  One absolute
inflation constant `C` such that the DC-subtracted Wick budget holds for every finite
field and every torsion subgroup at the calibrated depth `k* = ⌈(log q)/2⌉₊`.  Census
evidence (2026-07-09, verifier-corrected): observed `C_needed ≤ 3.47` globally, `≤ 2.61`
in the route regime `β ≥ 2.3` (worst cell `(279073, d = 108)`, `C(k*) = 2.07` there);
open in both directions in the honest window — its `k = 2` instance already implies
`E₊(H) ≤ 3C²d² + d⁴/p`, beyond Heath-Brown–Konyagin.  Numerics are evidence, not proof. -/
def UniformSubgroupWickBudget (C : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (d : ℕ),
    DCEnergyBudget (torsionSet F d) (wickDepth (Fintype.card F)) C

section UniformConsumer

variable {F0 : Type} [Field F0] [Fintype F0] [DecidableEq F0]

/-- **Packaged consumer of the named open Prop**: under `UniformSubgroupWickBudget C`,
every nontrivial Gauss period of every torsion subgroup of every finite field with
`q ≥ 5` obeys the corrected bound `‖η_b‖ ≤ 3·√(C·|μ_d|·log q)`. -/
theorem sup_le_of_uniformSubgroupWickBudget {C : ℝ}
    (hbudget : UniformSubgroupWickBudget C) (hC : 0 ≤ C)
    {ψ : AddChar F0 ℂ} (hψ : ψ.IsPrimitive) (hq5 : 5 ≤ Fintype.card F0) (d : ℕ)
    {b : F0} (hb : b ≠ 0) :
    ‖eta ψ (torsionSet F0 d) b‖
      ≤ 3 * Real.sqrt (C * ((torsionSet F0 d).card : ℝ) * Real.log (Fintype.card F0)) :=
  sup_le_three_sqrt_of_dcEnergyBudget hψ hC hq5 (hbudget F0 d) hb

end UniformConsumer

/-! ## The r341 Mellin/CAZAC transfer (abstract arithmetic form) -/

/-- **r341 transfer**: from the exact coset identity's bound `Mₙ ≤ (m·S + 1)/√q`
(r341 `norm_mellinSum_le_coset`, normalized by `√q`; restated as a hypothesis per lane
hygiene) and the budget-route coset bound `S ≤ 3·√(C·d·log q)`, with `m·d ≤ q` (true for
`m = (q−1)/d`, `d = |μ_d|`), the normalized Mellin/CAZAC phase sum obeys
`Mₙ ≤ 3·√(C·m·log q) + 1` — the corrected `√(m log p)` PAPR bound with constant `3√C`. -/
theorem mellin_papr_transfer {Mn S q d m C : ℝ} (hq1 : 1 ≤ q)
    (hm : 0 ≤ m) (hC : 0 ≤ C) (hmd : m * d ≤ q)
    (hMn : Mn ≤ (m * S + 1) / Real.sqrt q)
    (hSb : S ≤ 3 * Real.sqrt (C * d * Real.log q)) :
    Mn ≤ 3 * Real.sqrt (C * m * Real.log q) + 1 := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hsq1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hq1
  have hsqpos : (0 : ℝ) < Real.sqrt q := lt_of_lt_of_le one_pos hsq1
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  -- m·√(C·d·L) ≤ √q·√(C·m·L)
  have h2 : m * Real.sqrt (C * d * Real.log q)
      = Real.sqrt (m ^ 2 * (C * d * Real.log q)) := by
    rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hm]
  have h3 : m ^ 2 * (C * d * Real.log q) ≤ q * (C * m * Real.log q) := by
    have hmd2 : m * d * (m * (C * Real.log q)) ≤ q * (m * (C * Real.log q)) :=
      mul_le_mul_of_nonneg_right hmd (mul_nonneg hm (mul_nonneg hC hlogq))
    nlinarith [hmd2]
  have hchain : m * Real.sqrt (C * d * Real.log q)
      ≤ Real.sqrt q * Real.sqrt (C * m * Real.log q) := by
    calc m * Real.sqrt (C * d * Real.log q)
        = Real.sqrt (m ^ 2 * (C * d * Real.log q)) := h2
      _ ≤ Real.sqrt (q * (C * m * Real.log q)) := Real.sqrt_le_sqrt h3
      _ = Real.sqrt q * Real.sqrt (C * m * Real.log q) := Real.sqrt_mul hq0.le _
  have hnum : m * S + 1 ≤ 3 * (Real.sqrt q * Real.sqrt (C * m * Real.log q)) + 1 := by
    have hms := mul_le_mul_of_nonneg_left hSb hm
    nlinarith [hchain, hms]
  have hfin : (m * S + 1) / Real.sqrt q
      ≤ 3 * Real.sqrt (C * m * Real.log q) + 1 := by
    rw [div_le_iff₀ hsqpos]
    have hexp : (3 * Real.sqrt (C * m * Real.log q) + 1) * Real.sqrt q
        = 3 * (Real.sqrt q * Real.sqrt (C * m * Real.log q)) + Real.sqrt q := by ring
    rw [hexp]
    linarith [hnum, hsq1]
  exact hMn.trans hfin

/-! ## Kernel-decided anchor: `V₂(8) = 168 < 192` (char-0 Wick domination at d = 8) -/

/-- The eight 8th roots of unity in `ℤ[ζ₈] ≅ ℤ⁴` (integral basis `1, ζ, ζ², ζ³`, with
`ζ⁴ = −1`): `octRoot j = ζ^j` as an integer 4-tuple. -/
def octRoot : Fin 8 → ℤ × ℤ × ℤ × ℤ
  | ⟨0, _⟩ => (1, 0, 0, 0)
  | ⟨1, _⟩ => (0, 1, 0, 0)
  | ⟨2, _⟩ => (0, 0, 1, 0)
  | ⟨3, _⟩ => (0, 0, 0, 1)
  | ⟨4, _⟩ => (-1, 0, 0, 0)
  | ⟨5, _⟩ => (0, -1, 0, 0)
  | ⟨6, _⟩ => (0, 0, -1, 0)
  | ⟨7, _⟩ => (0, 0, 0, -1)
  | ⟨n + 8, h⟩ => absurd h (by omega)

/-- **Kernel-decided**: the char-0 depth-2 energy of `μ₈` is exactly
`V₂(8) = #{(a,b,c,d) : ζ^a + ζ^b = ζ^c + ζ^d in ℤ[ζ₈]} = 168`, counted in autocorrelation
form `∑_{(a,b)} #{(c,d) : ζ^a+ζ^b = ζ^c+ζ^d}` (bit-exact match with the 2026-07-09 probe
suite; independently rederivable from Lam–Leung: `3·8² − 24 = 168`). -/
theorem charZeroEnergy_two_d8 :
    (∑ p : Fin 8 × Fin 8, ((Finset.univ : Finset (Fin 8 × Fin 8)).filter
      (fun t => octRoot p.1 + octRoot p.2 = octRoot t.1 + octRoot t.2)).card)
      = 168 := by
  decide

/-- The Wick-domination instance `V₂(8) = 168 ≤ (2·2−1)‼·8² = 192`: the concrete `C = 1`
char-0 grounding of the budget shape (char-0 never exceeds real Wick for `d = 2^j`). -/
theorem charZeroEnergy_two_d8_le_wick :
    ((∑ p : Fin 8 × Fin 8, ((Finset.univ : Finset (Fin 8 × Fin 8)).filter
      (fun t => octRoot p.1 + octRoot p.2 = octRoot t.1 + octRoot t.2)).card : ℕ) : ℝ)
      ≤ (Nat.doubleFactorial (2 * 2 - 1) : ℝ) * (8 : ℝ) ^ 2 := by
  have h3 : Nat.doubleFactorial (2 * 2 - 1) = 3 := rfl
  rw [charZeroEnergy_two_d8, h3]
  norm_num

end ArkLib.ProximityGap.R389WickBudgetSupBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/

#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.gaussianEnergyBudget_one_iff
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.dcEnergyBudget_one_iff
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.DCEnergyBudget.mono
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.one_add_nsmul_le_pow_of_nonneg
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.two_mul_pow_le_succ_pow
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.doubleFactorial_le_pow
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.eta_pow_le_of_energyBudget
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.eta_pow_le_of_dcEnergyBudget
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.sup_le_of_dcEnergyBudget
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.sup_le_three_sqrt_of_dcEnergyBudget
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.sup_le_of_uniformSubgroupWickBudget
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.mellin_papr_transfer
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.charZeroEnergy_two_d8
#print axioms ArkLib.ProximityGap.R389WickBudgetSupBound.charZeroEnergy_two_d8_le_wick
