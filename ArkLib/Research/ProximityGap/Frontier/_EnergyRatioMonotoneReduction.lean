/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion

/-!
# Energy-Ratio Monotonicity: a closed recursive reduction of the prize moment input (#444)

**The result.** The prize per-frequency bound `B = max_{b≠0}‖η_b‖ ≤ √(2 n ln q)` follows (via the
in-tree `GaussPeriodMomentBound` consumer chain) from the single named input
`GaussianEnergyBound G r : E_r(G) ≤ (2r-1)‼·n^r` at depth `r ≈ ln q` — the char-`p` transfer of the
char-0 (Lam–Leung) Gaussian energy bound. The open core is that transfer at deep `r`.

This file **reduces that entire family of deep-order bounds to one closed recursive inequality** on the
additive energies, with NO analytic sub-lemma and NO appeal to an external conjecture as a black box:

  **Energy-Ratio Monotonicity (ERM).**  `E_{r+1}(G) ≤ (2r+1)·|G|·E_r(G)`  for every `r ≥ 1`.

**Why ERM closes it.** From the base `E_1(G) = |G|` (= the diagonal energy, trivial Parseval, so
`GaussianEnergyBound G 1` holds with equality), ERM steps the Gaussian bound up one order at a time via
the double-factorial recursion `(2r+1)‼ = (2r+1)·(2r-1)‼`:

  `E_{r+1} ≤ (2r+1)|G|·E_r ≤ (2r+1)|G|·(2r-1)‼|G|^r = (2r+1)‼·|G|^{r+1}`.

So **ERM ⟹ `GaussianEnergyBound G r` for ALL `r`**, hence (by the in-tree consumer) the prize bound at
the optimizing depth. `gaussianEnergyBound_of_ERM` and `worstCaseIncompleteSumBound_of_ERM` below are the
axiom-clean reduction.

**Status of ERM (HONESTY — REFUTED as a global claim).** ERM `∀ r ≥ 1` is **FALSE**, by exact
arbitrary-precision computation (NOT the earlier float64 numerics, which were a catastrophic-cancellation
artifact). At `n = 32`, `p = 1048609` (prize geometry `p = n⁴`, and confirmed at a generic prime
`p = 1051649`), the energy ratio `R_r = E_r / [(2r-1)‼·n^r]` is **non-monotone** — it dips to `0.711` at
`r = 6` then **rebounds through 1** (`R_9 = 1.27`, `R_10 = 1.85`). ERM first fails at the `r = 6→7` step
(`E_7/(n·E_6) = 13.60 > 13`), inside the shallow window `r < (n-1)/2 = 15.5`. Two consequences:
- The base case `r = 1` is still PROVEN (`E_2 = 3n²−3n ≤ 3n·n`), and `r = 2` holds (slack `1−1/n`), but
  **past `r ≈ n/4` the per-step ratio `E_{r+1}/(n·E_r)` exceeds `2r+1`** (it → `max_c‖η_c‖²/n`).
- The companion `GaussianEnergyBound` (`E_r ≤ (2r-1)‼·n^r`) is itself **not uniform in `r`** at finite `n`:
  it holds only for `r ≲ n/4` and rebounds above `1` for larger `r` (e.g. fails at `n=32`, `r ≥ 9`).

**What this file still proves (valid, axiom-clean — these are IMPLICATIONS, they never assert ERM is true):**
`gaussianEnergyBound_of_ERM`, `worstCaseIncompleteSumBound_of_ERM` (ERM ⇒ the prize bound), the
`doubleFactorial_step` recursion, and `energyRatioMonotone_at_deep` (ERM is automatic for the deep band
`|G| ≤ 2r+1`, i.e. `r ≥ (n-1)/2` — but that band is exactly where it is vacuous for the prize).

**Why no escape (sharp).** ERM-at-`r` ⟺ `R(r) := E_{r+1}/(n·E_r) ≤ 2r+1`, and `R(r)` is monotone increasing
in `r` with limit `max_c‖η_c‖²/n`. So ERM-at-`r` *presupposes* `max‖η‖² ≤ (2r+1)·n` = the BGK/Paley
sup-norm bound. **Prize-scale nuance (a clarification, not a rescue):** the `n=32` failure sits at `r ≈ n/4`;
for the prize `n = 2³⁰` the optimal depth `r ≈ ln q ≈ 110 ≪ n/4 = 2²⁸`, so the counterexample does *not*
reach the prize-relevant range — but ERM restricted to `r ≪ n/4` is then exactly the sup-norm wall. ERM-as-
a-route is therefore DEAD globally and equals the wall when restricted. Kept as the honest negative record;
the implication lemmas remain because they are mathematically correct and document the (failed) strategy.
Issue #444.
-/

open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ProximityGap.Frontier.EnergyRatioMonotone

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Energy-Ratio Monotonicity (ERM).** The `(r+1)`-st additive energy is at most `(2r+1)·|G|` times
the `r`-th, for every `r ≥ 1`. The single closed recursive input that — with the trivial base
`E_1 = |G|` — implies the Gaussian energy bound at every order (and hence the prize per-frequency bound).
**REFUTED as a global claim** (exact bigint: fails at `n=32`, `r=6`, inside `r<(n-1)/2`); see the module
docstring. Kept only as the hypothesis of the (valid) implication lemmas below — it is NOT true `∀ r`. -/
def EnergyRatioMonotone (G : Finset F) : Prop :=
  ∀ k : ℕ, 1 ≤ k → (rEnergy G (k + 1) : ℝ) ≤ (2 * (k : ℝ) + 1) * (G.card : ℝ) * (rEnergy G k : ℝ)

/-- **The double-factorial step.** `(2(k+1)-1)‼ = (2k+1)·(2k-1)‼` in `ℝ`, for `k ≥ 1` (the recursion
that turns one factor of `(2k+1)` from ERM into the next double factorial). -/
theorem doubleFactorial_step (k : ℕ) (hk : 1 ≤ k) :
    (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ)
      = (2 * (k : ℝ) + 1) * (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
  have h1 : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
  rw [h1, Nat.doubleFactorial_add_two]
  have h2 : ((2 * k - 1 : ℕ) : ℝ) + 2 = 2 * (k : ℝ) + 1 := by
    have hle : 1 ≤ 2 * k := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  push_cast
  rw [h2]

/-- **The deep half of ERM is UNCONDITIONAL (the dichotomy).** For every order `r` with
`|G| ≤ 2r+1`, the ERM inequality at `r` holds with no hypothesis at all — it follows from the in-tree
*weak* recursion `E_{r+1} ≤ |G|²·E_r` (`rEnergy_succ_le`), since `|G|² ≤ (2r+1)·|G|` when `|G| ≤ 2r+1`.
Hence **`EnergyRatioMonotone` is automatically true for all deep `r ≥ (|G|−1)/2`**, and its only open
content is the SHALLOW regime `r < (|G|−1)/2`. Sharp localization: the prize moment depth `r ≈ ln q`
is `≪ |G|/2 = n/2` (for the prize `n = 2^30`, `ln q ≈ 110 ≪ 2^29`), so the prize lives squarely in the
open shallow part — this theorem proves the (large) complementary deep part for free. -/
theorem energyRatioMonotone_at_deep (G : Finset F) (r : ℕ) (hdeep : G.card ≤ 2 * r + 1) :
    (rEnergy G (r + 1) : ℝ) ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ) * (rEnergy G r : ℝ) := by
  have hnat : rEnergy G (r + 1) ≤ G.card ^ 2 * rEnergy G r :=
    ArkLib.ProximityGap.CharPMomentRecursion.rEnergy_succ_le G r
  have hcast : (rEnergy G (r + 1) : ℝ) ≤ (G.card : ℝ) ^ 2 * (rEnergy G r : ℝ) := by exact_mod_cast hnat
  have hcard : (G.card : ℝ) ^ 2 ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ) := by
    have h1 : (G.card : ℝ) ≤ 2 * (r : ℝ) + 1 := by exact_mod_cast hdeep
    have h2 : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
    nlinarith [h2]
  calc (rEnergy G (r + 1) : ℝ)
      ≤ (G.card : ℝ) ^ 2 * (rEnergy G r : ℝ) := hcast
    _ ≤ (2 * (r : ℝ) + 1) * (G.card : ℝ) * (rEnergy G r : ℝ) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **ERM ⟹ the Gaussian energy bound at every order.** Given the trivial base `GaussianEnergyBound G 1`
(`E_1 = |G|`, Parseval) and ERM, the bound `E_r(G) ≤ (2r-1)‼·|G|^r` holds for ALL `r ≥ 1` — by induction
on `r`, stepping with `doubleFactorial_step`. This is the whole open-core family collapsed to ERM. -/
theorem gaussianEnergyBound_of_ERM {G : Finset F}
    (hbase : GaussianEnergyBound G 1) (hERM : EnergyRatioMonotone G) :
    ∀ r : ℕ, 1 ≤ r → GaussianEnergyBound G r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
    have ihbound : (rEnergy G k : ℝ) ≤ (Nat.doubleFactorial (2 * k - 1) : ℝ) * (G.card : ℝ) ^ k := ih
    have hstep := hERM k hk
    have hnn : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) * (G.card : ℝ) := by positivity
    show (rEnergy G (k + 1) : ℝ)
      ≤ (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) * (G.card : ℝ) ^ (k + 1)
    calc (rEnergy G (k + 1) : ℝ)
        ≤ (2 * (k : ℝ) + 1) * (G.card : ℝ) * (rEnergy G k : ℝ) := hstep
      _ ≤ (2 * (k : ℝ) + 1) * (G.card : ℝ)
            * ((Nat.doubleFactorial (2 * k - 1) : ℝ) * (G.card : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ihbound hnn
      _ = ((2 * (k : ℝ) + 1) * (Nat.doubleFactorial (2 * k - 1) : ℝ)) * (G.card : ℝ) ^ (k + 1) := by
          rw [pow_succ]; ring
      _ = (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) * (G.card : ℝ) ^ (k + 1) := by
          rw [doubleFactorial_step k hk]

/-- **ERM ⟹ the prize per-frequency bound at every depth.** Combining `gaussianEnergyBound_of_ERM` with
the in-tree consumer `worstCaseIncompleteSumBound_of_energyBound`: under ERM (and the trivial base),
for every `r ≥ 1` the worst-case incomplete-sum bound holds at scale `M_r = (q·(2r-1)‼·|G|^r)^{1/r}`.
Minimizing `M_r` over `r` (optimum `r ≈ ln q`) yields `B ≤ √(2 n ln q)` — the prize bound `C = √2`. The
entire open analytic core is now carried by the single recursive inequality `EnergyRatioMonotone`. -/
theorem worstCaseIncompleteSumBound_of_ERM {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hbase : GaussianEnergyBound G 1) (hERM : EnergyRatioMonotone G)
    {r : ℕ} (hr : 1 ≤ r) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹)) :=
  worstCaseIncompleteSumBound_of_energyBound hψ hr (gaussianEnergyBound_of_ERM hbase hERM r hr)

end ProximityGap.Frontier.EnergyRatioMonotone

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.EnergyRatioMonotone.doubleFactorial_step
#print axioms ProximityGap.Frontier.EnergyRatioMonotone.energyRatioMonotone_at_deep
#print axioms ProximityGap.Frontier.EnergyRatioMonotone.gaussianEnergyBound_of_ERM
#print axioms ProximityGap.Frontier.EnergyRatioMonotone.worstCaseIncompleteSumBound_of_ERM
