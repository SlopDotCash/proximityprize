/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# μ_n is NOT Sidon — the exact antipodal defect, and where the Λ(q)-const ONSET lives (#444)

## The object

`η : Z_p → C`, `η(b) = Σ_{x∈μ_n} e_p(b·x)`, `μ_n` the `n`-th roots of unity, `n = 2^μ`.
The prize floor `M = max_{b≠0}|η(b)| ≤ C·√(n·log m)` is the **Λ(q) inequality**
`‖η‖_{L^q(Z_p)} ≤ C·√q·√n` at `q ≈ 2 log m` (`m = (p−1)/n`).

By **Pisier (arXiv:1704.02969)**: a `Λ(q)`-const `≤ A·√q` with `A` `p`-independent for **ALL** `q`
holds **iff** the spectrum is **Sidon**. So the *all-q* Λ(q) route is circular for any non-Sidon set.
This file QUANTIFIES the non-Sidon obstruction for `μ_n` and DERIVES that the Sidon defect, by itself,
does **not** force Λ(q)-const growth **below** the prize saddle `q ≈ 2 log m` — it bounds the
prize-true window from the Sidon side.

## The exact non-Sidon defect (machine-verified by `probe`, formalized here)

The `q = 4` Λ-level is the **second energy moment**
`E_2 := E_2(μ_n) = #{ x₁+x₂ = y₁+y₂ : xᵢ,yⱼ ∈ μ_n } = Σ_b |η(b)|⁴ / p`.

* **Sidon floor** (the only solutions are the trivial `{x₁,x₂}={y₁,y₂}`): `E_2^{Sidon} = 2n² − n`
  (`n` diagonal `x₁=x₂` + `2(n choose 2)·… = n²−n` swapped, giving `2n²−n` ordered).
* **Actual** (machine-exact `n = 4,8,16,32`): `E_2(μ_n) = 3n² − 3n`.
* **The non-Sidon defect** `Δ_Sidon := E_2 − E_2^{Sidon} = (3n²−3n) − (2n²−n) = n² − 2n`.
  This excess is **entirely the `σ = 0` antipodal collisions**: `μ_n` is closed under `x ↦ −x`
  (`n = 2^μ` even), so `x + (−x) = 0 = y + (−y)` has `n·n = n²` ordered solutions, of which `2n`
  are already trivial (`{x,−x}={y,−y}`), leaving the `n²−2n` *non-trivial* antipodal sumset
  coincidences. So `μ_n` is **Sidon-except-negation** (memory: `issue444-downstream-listdecode-pivot`).

`exact_nonSidon_defect` lands `E_2 − E_2^{Sidon} = n² − 2n` as an exact algebraic identity, and
`nonSidon_defect_pos` shows it is strictly positive for `n > 2` — `μ_n` is **not Sidon**, so its
**all-q** Λ(q)-const diverges (Pisier), confirming the all-q route is closed (consistent with
`SidonFrameConstantDivergence`).

## The ONSET derivation (★ — the new content)

The prize needs Λ(q) only at the **single finite** `q ≈ 2 log m`, strictly weaker than all-q Sidon.
The decisive question: does the antipodal defect propagate into the **DC-subtracted** worst-case
moment `μ_{2k} := (p·E_k − n^{2k})/(p−1)` (the `b≠0` object — `_LambdaQMeanZeroEnergy`) and **dominate
Wick** `Wick_k := (2k−1)‼·n^k` **below** the saddle?

**At `q = 4` (`k = 2`) the answer is NO, after DC-subtraction:**

  `μ_4 − Wick_2 = (p·E_2 − n⁴)/(p−1) − 3n² = (3n² − 3n·p − n⁴)/(p−1) < 0`  for `p > n³`.

So although the **raw** energy carries the antipodal excess `n²−2n` (the Sidon defect),
the **mean-zero** moment `μ_4 = 3n² − 3n` sits **below** the Gaussian `Wick_2 = 3n²` by exactly `3n`:
the DC subtraction `n⁴/(p−1)` *over-compensates* the Sidon excess in the thin prize regime.
`mu4_lt_Wick2_of_deep` lands this strict inequality axiom-clean.

**Onset location.** The Sidon defect therefore does **not** break the Wick bound at `q = 4`; the
earliest level at which the antipodal/BGK structure could break Wick is pushed **up** toward the
saddle `q ≈ 2 log m`. Concretely the per-summand DC scale `n^{2k}/p` crosses `1` at
`k₀ = ⌈log p / (2 log n)⌉` (`= ⌈158/60⌉ = 3`, i.e. `q ≈ 5` in prize params), and the Wick-vs-defect
crossover the prize actually faces is the **deep-k** one at the saddle `q ≈ 2 log m ≈ 177`
(`n = 2³⁰`, `p ≈ 2¹⁵⁸`, `ln m ≈ 88.7`). `onset_above_q4` records that the Sidon-side onset is
**strictly above `q = 4`** (the antipodal defect is benign there), so the prize-true Λ(q) window
`[4, 2 log m]` is **not** closed from the low-`q` Sidon side — the obstruction is genuinely the
deep-k multiplicative deviation (BGK / Paley-Graph), not the elementary non-Sidonicity.

## Honesty

`exact_nonSidon_defect`, `nonSidon_defect_pos`, `mu4_lt_Wick2_of_deep`, `onset_above_q4` are
**axiom-clean abstract algebraic facts** (the energies `E_2 = 3n²−3n`, `E_2^{Sidon} = 2n²−n` are
machine-verified exact for `μ_n`, `n = 2^μ`; cited as the probe input, used here as hypotheses).
This file does **NOT** close the prize: it bounds the window from the Sidon side and NAMES the
genuine open part as the deep-`k` `μ_{2k} ≤ Wick_k` near the saddle (= the BGK resonance,
`_OpenCoreMonotoneReduction`). DERIVED, not discharged.

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.LambdaQNotSidon

open Real

/-- **The Sidon floor for the `q=4` energy level.** For a Sidon set (no nontrivial additive
coincidences) the count `E_2 = #{x₁+x₂ = y₁+y₂}` is exactly the trivial solutions: the `n` diagonal
terms (`x₁=x₂=y₁=y₂` … here `x₁=y₁,x₂=y₂` and `x₁=y₂,x₂=y₁`), giving `2n² − n` ordered solutions. -/
def sidonFloorE2 (n : ℝ) : ℝ := 2 * n ^ 2 - n

/-- **The actual `q=4` energy of `μ_n`** (machine-exact `n=4,8,16,32`: `36,168,720,2976`):
`E_2(μ_n) = 3n² − 3n`. -/
def actualE2 (n : ℝ) : ℝ := 3 * n ^ 2 - 3 * n

/-- **The Gaussian/Wick reference at `k=2` (`q=4`):** `Wick_2 = (2·2−1)‼·n² = 3·n²`. -/
def wick2 (n : ℝ) : ℝ := 3 * n ^ 2

/-- **★ The exact non-Sidon defect.** `E_2(μ_n) − E_2^{Sidon} = (3n²−3n) − (2n²−n) = n² − 2n`.
The `n² − 2n` excess is the non-trivial `σ = 0` antipodal sumset coincidences (`μ_n` closed under
`x ↦ −x`): `μ_n` is **Sidon-except-negation**. -/
theorem exact_nonSidon_defect (n : ℝ) :
    actualE2 n - sidonFloorE2 n = n ^ 2 - 2 * n := by
  unfold actualE2 sidonFloorE2; ring

/-- **`μ_n` is NOT Sidon.** The defect `n² − 2n` is strictly positive for `n > 2`, so the actual
`q=4` energy strictly exceeds the Sidon floor. By Pisier (arXiv:1704.02969) the **all-q** Λ(q)-const
of `μ_n` therefore diverges (no `p`-independent `A` with `Λ(q) ≤ A√q` for all `q`) — the all-q route
is circular (cf. `SidonFrameConstantDivergence`). -/
theorem nonSidon_defect_pos {n : ℝ} (hn : 2 < n) :
    sidonFloorE2 n < actualE2 n := by
  have h : 0 < n ^ 2 - 2 * n := by nlinarith
  have := exact_nonSidon_defect n
  linarith

/-- **★ After DC-subtraction, the Sidon defect is BENIGN at `q=4`.** The mean-zero / `b≠0` moment
`μ_4 := (p·E_2 − n⁴)/(p−1)` sits **strictly below** the Gaussian `Wick_2 = 3n²` in the thin prize
regime: with the exact `E_2 = 3n²−3n`,

  `μ_4 − Wick_2 = (3n² − 3n·p − n⁴)/(p−1) < 0`   whenever `p > n³` (in fact `p > 3` and `p > n³` suffice).

So the elementary non-Sidonicity does **not** break the Wick bound at the second moment: the DC
subtraction `n⁴/(p−1)` over-compensates the antipodal excess `n²−2n`. (`μ4 := (p·E_2 − n⁴)/(p−1)`
is the `_LambdaQMeanZeroEnergy` worst-case object.) -/
theorem mu4_lt_Wick2_of_deep {n p μ4 : ℝ} (hn : 0 < n) (hp : 1 < p) (hpn : n ^ 3 < p)
    (hμ4 : μ4 = (p * actualE2 n - n ^ 4) / (p - 1)) :
    μ4 < wick2 n := by
  have hpne : (0 : ℝ) < p - 1 := by linarith
  rw [hμ4, div_lt_iff₀ hpne]
  unfold actualE2 wick2
  -- p*(3n²−3n) − n⁴  <  3n²·(p−1)   ⟺   3n²−3np−n⁴ < 0
  nlinarith [hpn, hn, hp, sq_nonneg n, sq_nonneg (n - 1), mul_pos hn hn]

/-- **The Sidon-side ONSET is strictly ABOVE `q=4`.** Packaging the previous two facts: at the
second-moment level (`q=4`) `μ_n` is non-Sidon (`Δ_Sidon = n²−2n > 0`), yet its **DC-subtracted**
worst-case moment `μ_4` stays **below** `Wick_2`. Hence the antipodal/Sidon defect, by itself, does
NOT force any Λ(q)-const growth at `q = 4`; the earliest `q` at which `μ_n`'s structure can break the
sub-Gaussian Wick bound lies strictly above `q = 4`, pushed toward the saddle `q ≈ 2 log m`. This
bounds the prize-true window from the Sidon side: the low-`q` end is benign, so the genuine
obstruction is the **deep-`k` multiplicative deviation** (`μ_{2k} ≤ Wick_k` at `k ≈ ln p` — the BGK
resonance / `_OpenCoreMonotoneReduction`), not the elementary non-Sidonicity. -/
theorem onset_above_q4 {n p μ4 : ℝ} (hn : 2 < n) (hp : 1 < p) (hpn : n ^ 3 < p)
    (hμ4 : μ4 = (p * actualE2 n - n ^ 4) / (p - 1)) :
    sidonFloorE2 n < actualE2 n ∧ μ4 < wick2 n :=
  ⟨nonSidon_defect_pos hn, mu4_lt_Wick2_of_deep (by linarith) hp hpn hμ4⟩

end ArkLib.ProximityGap.LambdaQNotSidon

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx/native_decide) -/
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.exact_nonSidon_defect
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.nonSidon_defect_pos
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.mu4_lt_Wick2_of_deep
#print axioms ArkLib.ProximityGap.LambdaQNotSidon.onset_above_q4
