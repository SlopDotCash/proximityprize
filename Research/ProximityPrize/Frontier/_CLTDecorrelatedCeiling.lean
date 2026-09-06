/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungBesselEnergy

/-!
# The effective-CLT decorrelated ceiling for the Gauss-period energy (#407, ★ structural)

This file records the outcome of the **effective-CLT-with-dependence** analysis of the prize
energy bracket `E_r(μ_n) ≤ (2r−1)‼·n^r` at depth `r ≈ ln q`, thin regime `q = n^β` (`β ≈ 4–5`).
The per-frequency object is `η_b = ∑_{x∈μ_n} ψ(b·x) = ∑_{j=1}^{N} 2cos(2π b x_j/q)` (`N = n/2`,
one rep per `±`-pair), a sum of `N` bounded summands `Y_j(b) = 2cos(2π b x_j/q)`, each a
deterministic function of the single source `b`.

## The decorrelated (i.i.d.) model and the structural decomposition

Replace the shared-source family `{Y_j(b)}_b` by the **decorrelated model**: `N` i.i.d. copies of
`Z = 2cos(2πU)`, `U ~ Unif`.  Its `2r`-th moment is, by the multinomial expansion plus
`E[Z^{2k}] = C(2k,k)` (central binomial),

> `M_iid(2r) = ∑_{|β|=r} (2r)!/∏_j(2β_j)! · ∏_j C(2β_j,β_j) = (2r)!·besselCoeff N r`,

verified numerically (`probe_407_clt_dependence_structure.py` + `/tmp/probe_iid_bessel.py`,
exact match for `N = 2,3,4`, all `r ≤ 6`).  This is **exactly** the in-tree Bessel constant term
`besselCoeff` (`RungBesselEnergy.besselCoeff`).  And `M_iid(2r)` coincides with the **char-0
additive energy** `E_r^∞(μ_n)` (both count the b-independent / formal zero-sum relations).

The numerics (`/tmp/probe_clt_decisive.py`, `/tmp/probe_gap_structure.py`) give the clean
two-piece decomposition of the Wick slack at every measured `(n, β≥4, r≤12)`:

> `Wick − A_r  =  (Wick − M_iid)  +  (M_iid − A_r)`,
>   • `(Wick − M_iid) ≥ 0` — the **decorrelated Gaussian deficit**, ~97–99% of the slack,
>     and **PROVABLE** in char 0: it is exactly `bessel_energy_le_gaussian`
>     (`besselCoeff N r ≤ gaussianCoeff N r`, the coefficientwise `I₀(2x) ≤ e^{x²}`).
>   • `(M_iid − A_r) ≥ 0` — the **arithmetic remainder**, ~1–3% and *sign-definite* `≥ 0` in the
>     thin regime: the dependence **lowers** the moment below the decorrelated model
>     (`true/iid ≤ 1`, never crossing `1` for `β ≥ 4` up to `r = 12`).

## The honest verdict (is the CLT angle a lever or the moment problem?)

* **The decorrelated ceiling `M_iid ≤ Wick` is a genuine, already-proven char-0 lever**
  (`bessel_energy_le_gaussian`): the i.i.d. summand model is sub-Gaussian-dominated at the *sharp*
  Gaussian constant with **no `2^r` Hoeffding loss** (`/tmp/probe_iid_sum_wick.py`: `M_iid(2r) ≤
  (2r−1)‼·n^r` for all `r ≤ 40`, all `N`).  So the "CLT-with-INdependence" baseline closes the
  bound for the decorrelated model.
* **The remaining target is `A_r ≤ M_iid`** (dependent moment `≤` decorrelated), which is
  sign-definite `≥ 0` and tiny in the thin regime — *not* the full open core.  But it is **NOT a
  moment-free handle**: `A_r` and `M_iid` differ exactly on the **extra mod-`p` zero-sum relations**
  `∑±x_{j_i} ≡ 0 (mod p)` that are not char-0 relations (`/tmp/probe_circularity_final.py`:
  char-`p` energy `=` char-0 energy to `~10⁻⁴` in thin until the norm bound `q > (2r)^{n/2}` lapses,
  where the first extra relation appears — at `n=16` this is `r=4`).  Bounding those extra relations
  is precisely the **char-`p` transfer of the Lam–Leung energy bound** — the same named residual as
  `GaussPeriodMomentBound.GaussianEnergyBound` and `WorstPeriodMomentAvgLower.WickEnergyLowerBound`.
* **Stein / Berry-Esseen with a dependency graph is vacuous here**: the shared source `b` makes the
  dependency neighborhood of each `Y_j` the *entire* index set (`/tmp` probe: Stein error scale is
  `Θ(n²)`, not `Θ(n)` → 0), so there is no locality to exploit.

**Net (constraint lemma).**  The effective CLT is a *lever for the 97–99% decorrelated part*
(already proven in char 0 by the Bessel route) but **reduces the residual 1–3% to the same
char-`p` extra-relation count = BGK/Paley** — it confirms, rather than bypasses, the open core.
This file packages the provable half as a clean, importable theorem and names the residual.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #407.
-/

set_option linter.style.longLine false

open Finset BigOperators
open ProximityGap.PrizeWorkbench

namespace ProximityGap.Frontier.CLTDecorrelatedCeiling

/-- **The decorrelated (i.i.d.) model `2r`-th moment**, as the in-tree Bessel constant term scaled
by `(2r)!`.  `M_iid(2r) = (2r)!·besselCoeff N r`, where `N = n/2` is the number of `±`-paired
summands `Y_j = 2cos(2π b x_j/q)`.  Numerically equal to the char-0 additive energy `E_r^∞(μ_n)`
(`/tmp/probe_iid_bessel.py`, exact).  This is the moment of the **CLT-with-INdependence** baseline:
the sum of `N` i.i.d. copies of `Z = 2cos(2πU)`, `E[Z^{2k}] = C(2k,k)`. -/
noncomputable def iidModelMoment (N r : ℕ) : ℚ := (Nat.factorial (2 * r) : ℚ) * besselCoeff N r

/-- **The Gaussian (Wick) `2r`-th moment** for variance `n = 2N`, as the in-tree Gaussian constant
term scaled by `(2r)!`.  `Wick(2r) = (2r)!·gaussianCoeff N r = (2r−1)‼·n^r` (the real-Gaussian
`2r`-th moment at variance `n`). -/
noncomputable def wickMoment (N r : ℕ) : ℚ := (Nat.factorial (2 * r) : ℚ) * gaussianCoeff N r

/-- **The decorrelated ceiling is the Gaussian moment — PROVEN (char 0).**  The i.i.d.-summand
model moment is at most the Wick / Gaussian value, `M_iid(2r) ≤ Wick(2r)`, with the *sharp*
Gaussian constant and no `2^r` loss.  This is the in-tree `bessel_energy_le_gaussian`
(`besselCoeff ≤ gaussianCoeff`, the coefficientwise `I₀(2x) ≤ e^{x²}`) multiplied through by the
nonnegative factor `(2r)!`.

This is the affirmative content of the effective-CLT angle: the *decorrelated* model (CLT with
independence) provably satisfies the prize Wick bound.  The numerics confirm it carries
97–99% of the Wick slack and the dependent moment sits **below** it in the thin prize regime. -/
theorem iidModelMoment_le_wick (N r : ℕ) :
    iidModelMoment N r ≤ wickMoment N r := by
  unfold iidModelMoment wickMoment
  have hfac : (0 : ℚ) ≤ (Nat.factorial (2 * r) : ℚ) := by positivity
  exact mul_le_mul_of_nonneg_left (bessel_energy_le_gaussian N r) hfac

/-- **The arithmetic-remainder residual (the named open input).**  The genuinely open piece left
after the decorrelated ceiling is whether the *dependent* energy `A_r = E_r(μ_n) − n^{2r}/q` sits
below the decorrelated model: `A_r ≤ M_iid(2r)`.  Numerically this holds (sign-definite, ~1–3% of
the Wick slack) for `β ≥ 4` to `r = 12` (`/tmp/probe_gap_structure.py`), but proving it is the
**char-`p` extra-relation count** — the same wall as the char-`p` transfer of the Lam–Leung energy
bound (`GaussianEnergyBound`).  Stated here as an explicit named hypothesis, *not* silently
discharged. `Ar` is the caller-supplied dependent energy at order `r`. -/
def ArithmeticRemainderBelowIid (N r : ℕ) (Ar : ℚ) : Prop := Ar ≤ iidModelMoment N r

/-- **The effective-CLT bracket (the consumer chain).**  IF the arithmetic remainder is controlled
(`A_r ≤ M_iid`, the named residual) THEN the prize Wick bound holds on the dependent energy,
`A_r ≤ Wick(2r)`, via the proven decorrelated ceiling.  This is the precise sense in which the
effective CLT "closes" the bound: the only open input is the dependent-vs-decorrelated comparison,
the proven part (`M_iid ≤ Wick`) is supplied by the Bessel route.  Confirms the open core is the
char-`p` extra-relation count, with the 97–99% Gaussian-deficit part discharged. -/
theorem energy_le_wick_of_remainder (N r : ℕ) (Ar : ℚ)
    (h : ArithmeticRemainderBelowIid N r Ar) :
    Ar ≤ wickMoment N r :=
  le_trans h (iidModelMoment_le_wick N r)

end ProximityGap.Frontier.CLTDecorrelatedCeiling

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CLTDecorrelatedCeiling.iidModelMoment_le_wick
#print axioms ProximityGap.Frontier.CLTDecorrelatedCeiling.energy_le_wick_of_remainder
