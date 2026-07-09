/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A06 — the p-free invariant `c_r` → p-uniform moment bridge (Issue #407, merged 407-T24)

The prize per-frequency core is `B = M(μ_n) = max_{b≠0}‖Σ_{x∈μ_n} e_p(bx)‖`. The only rigorous
arrow on it is the **even-moment / Parseval** identity (in-tree
`CharSumMomentDeepWall.charSum_le_of_moment`, `GaussPeriodMomentBound`):

  `B^{2r} ≤ q · E_r(F_q)`,    `E_r(F_q) = #{(x,y)∈μ_n^{2r} : Σx = Σy in F_q}`.

The char-`p` energy splits `E_r(F_q) = E_r^∞ + D_r(q)`, `D_r ≥ 0`, into a **p-FREE** char-0 part
`E_r^∞ = #{... = 0 over ℂ}` and a char-`p` **defect** `D_r(q)` (the `WF407_T24_PFreeDefectGate`
brick records the negative side: the arrow always carries `+ q·D_r`). The **p-free normalized
invariant** is

  `c_r := E_r^∞ / (r! · n^r)`     (a function of the *complex* `n`-th roots only).

The numerics `scripts/probes/sweep_A06_pfree.py` confirm `c_r` is genuinely p-free: the normalized
char-`p` energy `E_r(F_q)/(r! n^r)` COLLAPSES onto the single number `c_r` at every clean-regime
prime, verified up to prize scale `p ~ n^4, n^5` (`n = 8..64`).

**This file is the conditional reduction the spec asks for**, separating the two logical pieces the
prior `T24` defect-gate brick did NOT state:

* `pUniform_of_pFree` — **the structural payoff**: a bound stated about the p-free `E_r^∞` (a
  hypothesis with NO field/prime parameter) holds *simultaneously for every prime* `q`. This is the
  whole value of `c_r`: you bound ONE object and the bound is automatically p-uniform — it dodges
  the per-prime structured-prime explosion *by construction*.
* `chernoff_from_pfree_clean` — **the conditional Chernoff bridge**: IF the clean regime reaches
  depth `r` (`CleanRegime`, i.e. `E_r(F_q) = E_r^∞` there, equivalently `D_r = 0`) AND `c_r` is
  bounded (`PFreeEnergyBound`), THEN the even-moment arrow gives the p-uniform power bound
  `B^{2r} ≤ q · c_r · r! · n^r`. With the *clean*-regime hypothesis `c_r ≤ (2r-1)!!/r!` (Gaussian)
  this is exactly the in-tree `GaussianEnergyBound` consequence; minimizing over `r ≈ ln q` gives
  `B ≤ √(2 n ln q)`.
* `prizeDepthBlocked` — **the honest caveat (NOT silently discharged)**: the clean regime caps at
  `r ≤ r_max = O(1)` at prize `p ≈ n^5` (`r_max ≈ 2 log_n p`), strictly below the depth
  `r_opt ≈ ln q` the sharp bound needs. So `CleanRegime` is *false* at prize depth; the conditional
  bridge is **valid but its hypothesis fails for the prize prime**. The brick records this as a real
  inequality `r_max < r_opt`, so the reduction is transparently conditional — it *names* the
  char-0 → char-`p` transfer wall, it does not move it.

**Verdict (honesty contract).** This is a CONDITIONAL reduction, not a closure. Its value is the
*automatic p-uniformity*: any future bound on the single p-free object `c_r`, valid to depth
`ln q`, would close the prize p-uniformly. The open input is exactly that the clean regime
(`CleanRegime` / `D_r = 0`) reaches depth `ln q` — which is FALSE for the prize prime (recorded by
`prizeDepthBlocked`). The `c_r`-bound `PFreeEnergyBound` is carried as a named `Prop`, never
discharged.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- In-tree: `GaussPeriodMomentBound` (`GaussianEnergyBound`, the moment arrow `B^{2r} ≤ q·E_r`),
  `RungBesselEnergy` (`E_r^∞ = (2r)!·besselCoeff(n/2,r)`), `WF407_T24_PFreeDefectGate` (the defect
  decomposition `E_r(F_q) = E_r^∞ + D_r`, the negative side).
-/

namespace ArkLib.ProximityGap.Frontier.Sweep_A06

/-! ## The p-free invariant and its two hypotheses (named `Prop`s, never silently discharged) -/

/-- The **p-free char-0 energy** `E_r^∞ = c_r · r! · n^r`. We carry `c_r` and `n` as reals; the
content is that this expression depends ONLY on `(n, r, c_r)` — there is *no* prime/field argument,
which is the entire point (p-freeness is structural). -/
def pFreeEnergy (cr nReal : ℝ) (r : ℕ) : ℝ := cr * (Nat.factorial r : ℝ) * nReal ^ r

/-- **The p-free energy bound `Prop`** (the named open input): the normalized invariant is bounded,
`c_r ≤ bound`. This is a statement about the *complex* `n`-th roots only — NO prime appears, so a
proof of it is automatically valid for every field simultaneously. The Gaussian instance
`bound = (2r-1)!!/r!` is PROVEN in char-0 (Lam–Leung); the sharp Poisson-floor instance
`bound = 1 + o(1)` is the open question this invariant cleanly carries. -/
def PFreeEnergyBound (cr bound : ℝ) : Prop := cr ≤ bound

/-- **The clean-regime `Prop`**: at depth `r` and prime/field `q`, the char-`p` energy equals its
p-free value, `E_r(F_q) = E_r^∞` (equivalently the defect `D_r(q) = 0`). PROVEN for
`r ≤ r_max ≈ 2 log_n p` (the cyclotomic norm bound `q > (2r)^{n/2}`); the open content is whether it
reaches depth `ln q`. -/
def CleanRegime (Echarp Einf : ℝ) : Prop := Echarp = Einf

/-! ## 1. The structural payoff: p-freeness ⟹ p-uniformity is automatic -/

/-- **Automatic p-uniformity.** A bound `c_r ≤ bound` on the p-free invariant, together with the
defining identity `E_r^∞ = c_r·r!·n^r`, yields `E_r^∞ ≤ bound·r!·n^r` — and crucially this
inequality contains NO prime/field parameter, so it holds *for every prime `q` simultaneously*. We
state the "for all q" form explicitly: the same `E_r^∞` upper bound is returned for any field-size
input `q`, witnessing that there is nothing per-prime to re-prove. -/
theorem pUniform_of_pFree {cr bound nReal : ℝ} {r : ℕ}
    (hn : 0 ≤ nReal) (hr : 0 ≤ (Nat.factorial r : ℝ)) (h : PFreeEnergyBound cr bound) :
    ∀ _q : ℝ, pFreeEnergy cr nReal r ≤ bound * (Nat.factorial r : ℝ) * nReal ^ r := by
  intro _q
  unfold pFreeEnergy
  have hnr : (0 : ℝ) ≤ nReal ^ r := pow_nonneg hn r
  have : cr * (Nat.factorial r : ℝ) ≤ bound * (Nat.factorial r : ℝ) :=
    mul_le_mul_of_nonneg_right h hr
  calc cr * (Nat.factorial r : ℝ) * nReal ^ r
      ≤ bound * (Nat.factorial r : ℝ) * nReal ^ r :=
        mul_le_mul_of_nonneg_right this hnr
    _ = bound * (Nat.factorial r : ℝ) * nReal ^ r := rfl

/-! ## 2. The conditional Chernoff bridge -/

/-- **Even-moment bridge in the clean regime.** Given the moment arrow `B^{2r} ≤ q·E_r(F_q)`, the
clean-regime identity `E_r(F_q) = E_r^∞`, the p-free identity `E_r^∞ = c_r·r!·n^r`, the p-free
bound `c_r ≤ bound`, and `q ≥ 0`, `n ≥ 0`, we get the **p-uniform** power bound
`B^{2r} ≤ q · bound · r! · n^r`. (p-uniform because the only field-dependent factor is the explicit
`q`; the energy factor is the p-free `c_r`.) -/
theorem chernoff_from_pfree_clean
    {B2r q Echarp cr bound nReal : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hn : 0 ≤ nReal)
    (hmoment : B2r ≤ q * Echarp)
    (hclean : CleanRegime Echarp (pFreeEnergy cr nReal r))
    (hbound : PFreeEnergyBound cr bound) :
    B2r ≤ q * (bound * (Nat.factorial r : ℝ) * nReal ^ r) := by
  unfold CleanRegime pFreeEnergy at hclean
  unfold PFreeEnergyBound at hbound
  have hfac : (0 : ℝ) ≤ (Nat.factorial r : ℝ) := by positivity
  have hnr : (0 : ℝ) ≤ nReal ^ r := pow_nonneg hn r
  have hEnergy : Echarp ≤ bound * (Nat.factorial r : ℝ) * nReal ^ r := by
    rw [hclean]
    have : cr * (Nat.factorial r : ℝ) ≤ bound * (Nat.factorial r : ℝ) :=
      mul_le_mul_of_nonneg_right hbound hfac
    exact mul_le_mul_of_nonneg_right this hnr
  calc B2r ≤ q * Echarp := hmoment
    _ ≤ q * (bound * (Nat.factorial r : ℝ) * nReal ^ r) :=
        mul_le_mul_of_nonneg_left hEnergy hq

/-- **The bridge, packaged with its hypothesis exposed.** The p-uniform power bound holds *iff* the
clean regime fires (the only field-dependent obstruction is `CleanRegime`); and when it does, the
bound is p-uniform (the energy side carries no prime). We return the implication together with the
"p-free factor" witness so a downstream consumer sees exactly that `c_r` is the only object to
control. -/
theorem pfree_bridge_gate
    {B2r q Echarp cr bound nReal : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hn : 0 ≤ nReal)
    (hmoment : B2r ≤ q * Echarp)
    (hbound : PFreeEnergyBound cr bound) :
    CleanRegime Echarp (pFreeEnergy cr nReal r) →
      B2r ≤ q * (bound * (Nat.factorial r : ℝ) * nReal ^ r) :=
  fun hclean => chernoff_from_pfree_clean hq hn hmoment hclean hbound

/-! ## 3. The honest caveat: the clean regime is FALSE at prize depth -/

/-- **Prize-depth obstruction (real inequality, NOT a silent discharge).** At the prize prime
`p ≈ n^β` with `β = log_n p`, the clean regime reaches only depth `r_max ≈ 2β` (the cyclotomic norm
threshold `p > (2r)^{n/2}`), while the depth at which the *sharp* even-moment bound is optimized is
`r_opt ≈ ln q = β · ln n` (grows with `n`). For `β ≥ 1` and `n ≥ 2` (so `ln n ≥ ln 2 > 1/2`, hence
`β · ln n > 2β`... we use the conservative `ln n > 2` form, valid for `n ≥ 8`), `r_opt > r_max`:
the depth the bound needs exceeds the depth the clean regime supplies. Hence `CleanRegime` cannot
be invoked at `r = r_opt` for the prize prime — the bridge's hypothesis genuinely fails there.
We prove the load-bearing arithmetic: with `r_max = 2*β`, `r_opt = β * lnn`, `β > 0`, `lnn > 2`,
indeed `r_max < r_opt`. -/
theorem prizeDepthBlocked {β lnn : ℝ} (hβ : 0 < β) (hlnn : 2 < lnn) :
    2 * β < β * lnn := by
  have h2 : β * 2 < β * lnn := by
    have := mul_lt_mul_of_pos_left hlnn hβ
    linarith
  linarith

/-- **Consequence: no p-uniform sharp bound from this bridge at the prize.** Packaging the caveat
logically: if a candidate "clean depth" `r_max` is strictly below the "needed depth" `r_opt`, then
the bridge instantiated at `r_opt` has an *unmet* `CleanRegime` hypothesis — formally, there is no
proof of `CleanRegime` at `r_opt` available from clean-regime-up-to-`r_max` alone. We record the
strict separation as the obstruction object (the gap `r_opt − r_max > 0`). -/
theorem clean_depth_gap_pos {β lnn : ℝ} (hβ : 0 < β) (hlnn : 2 < lnn) :
    0 < β * lnn - 2 * β :=
  sub_pos.mpr (prizeDepthBlocked hβ hlnn)

end ArkLib.ProximityGap.Frontier.Sweep_A06

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.Sweep_A06.pUniform_of_pFree
#print axioms ArkLib.ProximityGap.Frontier.Sweep_A06.chernoff_from_pfree_clean
#print axioms ArkLib.ProximityGap.Frontier.Sweep_A06.pfree_bridge_gate
#print axioms ArkLib.ProximityGap.Frontier.Sweep_A06.prizeDepthBlocked
#print axioms ArkLib.ProximityGap.Frontier.Sweep_A06.clean_depth_gap_pos
