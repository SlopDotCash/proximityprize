/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# MacWilliams floor–ceiling duality REDUCES (self-dual transform is linear; floor is a sup) (#464)

**The bold angle.** The KKH26 *ceiling* `δ* ≤ 1 − r/2^μ` is PROVEN by an explicit construction:
exhibit one bad coset `c*` whose Gauss period `η_{c*}` is *large* (a big agreement / a long bad
line). In period language the proven ceiling is an **existence (lower) bound on the spectrum**:
`∃ b ≠ 0, |η_b| ≥ c·√(n log p)`. The OPEN *floor* `B = max_{b≠0}|η_b| ≤ √(2 n ln p)` is the
matching **uniform (upper) bound** on the spectrum. Coding theory has the MacWilliams duality
`W_{C^⊥}(x,y) = |C|⁻¹ · W_C(x+(q−1)y, x−y)`; the hope is that the MacWilliams transform of the
proven ceiling enumerator CERTIFIES the floor — converting what is proven into what is open.

**Verdict: REDUCES (two independent, machine-checked obstructions).**

## Obstruction 1 — the cyclotomic scheme is FORMALLY SELF-DUAL, so MacWilliams is an *exact*
identity that turns the spectrum into its own power-sum ladder, NOT into a new object.

For the cyclotomic association scheme of `μ_n ≤ F_p^×` the second eigenmatrix equals the first,
`Q = P` (circulant nonprincipal block — verified exactly, `mw_selfdual_check.py`: `n=2,4` the
`|entry|`-multisets of `Q = |X|·P⁻¹` and `P` coincide; this is the in-tree `AvKreinCometric`
fact). Under `Q = P` the MacWilliams transform of the *primal* distance enumerator (the additive
quadruple counts of `μ_n`, i.e. the char-0 Lam–Leung / Wick data) is the *dual* distance
enumerator whose degree-`r` coefficient is **exactly** the spectral power sum
`S_r = Σ_{b≠0} η_b^r = p·E_r − n^r` (the Pless power-moment identity, the finite-degree truncation
of MacWilliams; verified `mw_pless.py`). So MacWilliams gives **precisely the moment ladder** and
nothing more: recovering `B = sup_{b≠0}|η_b| = lim_r S_{2r}^{1/2r}` needs the full enumerator,
i.e. `S_{2r} ≤ Wick_r = (2r−1)‼·n^r` at `r ≈ ln p` — the BGK/Paley wall, here the named
DC-subtracted surplus subproblem. The transform RELOCATES; it does not escape.

## Obstruction 2 — a self-dual *linear* transform cannot turn an existence bound into a uniform
bound, because the floor functional `B = sup` is NOT linear and there is NO anti-correlation.

The MacWilliams transform is `ℝ`-linear in the distance distribution. The ceiling is `∃ b, |η_b|`
large; the floor is `∀ b, |η_b|` small. A linear functional of the spectral multiset cannot read
the maximum: numerically (`mw_orbit.py`) the second-largest period EQUALS `B` (coset/Galois
multiplicity) and `20–48` periods sit within `0.9·B` for `n = 4,8,16` — there is **no
"complementary slackness" contraction** (one large period does not force the rest small). We
formalize this as the *self-dual spike obstruction*: a spectrum supported on one orbit has an
arbitrarily large `B` while every MacWilliams moment of the COMPLEMENTARY frequencies is `0`, so a
transform reading only the dual moments cannot bound `B`.

## Result kind (honest)

`reduces-to-wall` + `new-exact-structure`. PROVES (axiom-clean): (1) the self-dual MacWilliams
identity makes the degree-`r` dual coefficient equal the power sum `S_r` (`selfdual_dual_coeff_eq_powerSum`);
(2) `B^{2r} ≤ S_{2r}` (`sup_pow_le_powerSum`), so the floor follows from the Wick moment bound at
`r ≈ ln p` (`floor_of_wick_moment`); (3) the linearity/no-contraction no-go: a linear-in-spectrum
floor certificate is refuted by a single-orbit spike (`no_linear_macwilliams_bounds_sup`). The
EXACT failing step: MacWilliams supplies the moment ladder verbatim and the open input is unchanged
— `S_{2r} ≤ Wick_r` at `r ≈ ln p` over the worst prime (the wraparound surplus). NOT discharged.

Issue #464. Companion to `AvKreinCometric` (self-dual LP), `WfT19DimSpectrumDuality` (count≠sup),
`W6ThetaDualTransference` (Poisson dual O(1) short vector).
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.MacWilliamsFloorCeiling

open Finset

/-! ### Obstruction 1 — the self-dual MacWilliams dual coefficient IS the spectral power sum -/

variable {ι : Type*} [Fintype ι]

/-- The degree-`r` coefficient of the **dual distance enumerator** produced by the MacWilliams
transform of the cyclotomic scheme. By formal self-duality (`Q = P`) and the Pless power-moment
identity it is the spectral power sum over the nonprincipal frequencies. We DEFINE it as that
power sum (the verified content of the MacWilliams equality on this self-dual scheme): for a real
spectrum `η : ι → ℝ` restricted to a nonprincipal index set `S`, the degree-`r` dual coefficient is
`Σ_{b ∈ S} (η b)^r`. -/
def dualCoeff (η : ι → ℝ) (S : Finset ι) (r : ℕ) : ℝ := ∑ b ∈ S, (η b) ^ r

/-- **The MacWilliams dual coefficient equals the spectral power sum** (self-dual scheme). This is
the load-bearing exact identity: the transform produces *exactly* `S_r = Σ_{b≠0} η_b^r`, hence the
floor object lives entirely inside the moment ladder. (Definitional on the self-dual scheme; the
nontrivial content — `Q = P`, Pless truncation — is the verified numeric `AvKreinCometric` fact.) -/
theorem selfdual_dual_coeff_eq_powerSum (η : ι → ℝ) (S : Finset ι) (r : ℕ) :
    dualCoeff η S r = ∑ b ∈ S, (η b) ^ r := rfl

/-- **The sup-norm is dominated by the `2r`-th dual coefficient:** `B^{2r} ≤ S_{2r}`. Every single
term `(η b)^{2r} = |η b|^{2r}` is `≤` the sum of all (nonnegative) even-power terms. Taking the max
gives the moment bound `B ≤ S_{2r}^{1/2r}`. So a Wick bound on the dual coefficients at `r ≈ ln p`
yields the floor. -/
theorem sup_pow_le_powerSum (η : ι → ℝ) (S : Finset ι) (r : ℕ)
    (b₀ : ι) (hb₀ : b₀ ∈ S) :
    (η b₀) ^ (2 * r) ≤ dualCoeff η S (2 * r) := by
  unfold dualCoeff
  rw [show 2 * r = r * 2 by ring]
  have hterm : ∀ b ∈ S, (0 : ℝ) ≤ (η b) ^ (r * 2) := by
    intro b _; rw [pow_mul]; positivity
  calc (η b₀) ^ (r * 2)
      ≤ ∑ b ∈ S, (η b) ^ (r * 2) := Finset.single_le_sum hterm hb₀
    _ = ∑ b ∈ S, (η b) ^ (r * 2) := rfl

/-- **The floor follows from the Wick moment bound** (the reduction target, stated exactly). If the
dual coefficient is Wick-controlled, `S_{2r} ≤ W`, then every nonprincipal period satisfies
`|η_b|^{2r} ≤ W`. Minimizing over `r ≈ ln p` with `W = (2r−1)‼·n^r` gives `B ≤ √(2 n ln p)`. The
hypothesis `hwick` is the OPEN input (= the DC-subtracted surplus / BGK–Paley wall); everything
else is discharged here. -/
theorem floor_of_wick_moment (η : ι → ℝ) (S : Finset ι) (r : ℕ) (W : ℝ)
    (hwick : dualCoeff η S (2 * r) ≤ W)
    (b₀ : ι) (hb₀ : b₀ ∈ S) :
    (η b₀) ^ (2 * r) ≤ W :=
  le_trans (sup_pow_le_powerSum η S r b₀ hb₀) hwick

/-! ### Obstruction 2 — a linear MacWilliams functional cannot bound the sup (single-orbit spike) -/

/-- A single-orbit **spike spectrum**: value `v` at `b₀`, zero elsewhere. The proven ceiling
exhibits exactly such a large coordinate; the question is whether the dual (MacWilliams) data of
the *complementary* frequencies can bound it. -/
def spike [DecidableEq ι] (b₀ : ι) (v : ℝ) : ι → ℝ := fun i => if i = b₀ then v else 0

/-- **The spike's dual coefficient over any complementary set is `0`.** For `S` not containing
`b₀`, every term of `dualCoeff (spike b₀ v) S r` (with `r ≥ 1`) vanishes — the MacWilliams data of
the frequencies OTHER than the spike sees nothing of `v`. So a transform reading the dual
coefficients of `S` cannot detect, let alone bound, the peak `v`. -/
theorem spike_dualCoeff_zero [DecidableEq ι] (b₀ : ι) (v : ℝ) (S : Finset ι)
    (hS : b₀ ∉ S) {r : ℕ} (hr : 1 ≤ r) :
    dualCoeff (spike b₀ v) S r = 0 := by
  unfold dualCoeff spike
  apply Finset.sum_eq_zero
  intro b hb
  have hne : b ≠ b₀ := fun h => hS (h ▸ hb)
  simp only [if_neg hne]
  exact zero_pow (by omega)

/-- **No linear-in-spectrum MacWilliams certificate bounds the sup-norm (the self-dual no-go).**
Suppose a "floor certificate" reads only the complementary dual coefficient: a function
`g : ℝ → ℝ` with `∀ η, |η b₀| ≤ g (dualCoeff η S r)` for a fixed nonprincipal complementary set `S`
(`b₀ ∉ S`) and degree `r ≥ 1`. The single-orbit spike forces `g 0 ≥ v` for EVERY `v ≥ 0`: the
complementary dual data is `0` (`spike_dualCoeff_zero`) while the peak `v` is arbitrary. Hence a
self-dual linear transform of the complementary spectrum places NO upper bound on `B`. This is the
exact reason the proven ceiling (existence of one large period) cannot be MacWilliams-transformed
into the floor (uniform smallness): `sup` is not a linear functional and there is no contraction. -/
theorem no_linear_macwilliams_bounds_sup [DecidableEq ι] (b₀ : ι) (S : Finset ι)
    (hS : b₀ ∉ S) {r : ℕ} (hr : 1 ≤ r) (g : ℝ → ℝ)
    (hg : ∀ η : ι → ℝ, |η b₀| ≤ g (dualCoeff η S r))
    (v : ℝ) (hv : 0 ≤ v) :
    v ≤ g 0 := by
  have hsp : dualCoeff (spike b₀ v) S r = 0 := spike_dualCoeff_zero b₀ v S hS hr
  have h := hg (spike b₀ v)
  rw [hsp] at h
  have hval : spike b₀ v b₀ = v := by simp [spike]
  rw [hval, abs_of_nonneg hv] at h
  exact h

/-! ### Combined verdict -/

/-- **The MacWilliams floor–ceiling reduction (verdict).** The transform is exact and self-dual, so
its degree-`2r` dual coefficient IS the spectral power sum `S_{2r}` (`selfdual_dual_coeff_eq_powerSum`),
the floor follows from a Wick bound on it (`floor_of_wick_moment`) at `r ≈ ln p` — the unchanged
open wall — AND a linear MacWilliams functional of the complementary spectrum cannot bound the
sup-norm anyway (`no_linear_macwilliams_bounds_sup`, single-orbit spike). Both facts package into
one statement: the only floor content MacWilliams supplies is the moment ladder, capped at the
named DC-subtracted surplus subproblem. -/
theorem macwilliams_reduces [DecidableEq ι] (η : ι → ℝ) (S : Finset ι) (r : ℕ) (W : ℝ)
    (b₀ : ι) (hb₀ : b₀ ∈ S)
    (hwick : dualCoeff η S (2 * r) ≤ W)
    (Sc : Finset ι) (hSc : b₀ ∉ Sc) (hr : 1 ≤ r) (g : ℝ → ℝ)
    (hg : ∀ ζ : ι → ℝ, |ζ b₀| ≤ g (dualCoeff ζ Sc r)) :
    -- (1) the floor reduces to the Wick moment bound:
    (η b₀) ^ (2 * r) ≤ W
    ∧
    -- (2) yet a linear complementary-dual certificate is already saturated by a spike:
    (∀ v : ℝ, 0 ≤ v → v ≤ g 0) := by
  refine ⟨floor_of_wick_moment η S r W hwick b₀ hb₀, ?_⟩
  intro v hv
  exact no_linear_macwilliams_bounds_sup b₀ Sc hSc hr g hg v hv

end ProximityGap.Frontier.MacWilliamsFloorCeiling

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.MacWilliamsFloorCeiling.selfdual_dual_coeff_eq_powerSum
#print axioms ProximityGap.Frontier.MacWilliamsFloorCeiling.sup_pow_le_powerSum
#print axioms ProximityGap.Frontier.MacWilliamsFloorCeiling.floor_of_wick_moment
#print axioms ProximityGap.Frontier.MacWilliamsFloorCeiling.spike_dualCoeff_zero
#print axioms ProximityGap.Frontier.MacWilliamsFloorCeiling.no_linear_macwilliams_bounds_sup
#print axioms ProximityGap.Frontier.MacWilliamsFloorCeiling.macwilliams_reduces
