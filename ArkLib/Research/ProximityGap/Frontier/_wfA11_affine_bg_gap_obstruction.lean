/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# wf-A11 (#444): the Bourgain–Gamburd / superstrong-approximation affine envelope and `M(n)` — an (informal) abelianness obstruction

**Angle.** The prize object `M(n) = max_{b≠0}‖η_b‖`, `η_b = ∑_{x∈μ_n} e_p(bx)`, is the
non-principal eigenvalue of the *additive* Cayley graph `Cay(F_p, μ_n)` (the generalized Paley
graph). The additive Cayley route is recorded dead (`_AttackR2_AbelianCayleyNonRamanujan`):
abelian Cayley graphs of growing degree are not Ramanujan. **This file attacks the orthogonal
hope**: package the *multiplicative dilation* action `x ↦ ux` (`u ∈ μ_n`) as a NON-abelian
envelope — the affine group `G = F_p ⋊ μ_n` — and ask whether a Bourgain–Gamburd /
superstrong-approximation spectral gap there bounds `M(n)`.

**The governing theorem (Lindenstrauss–Varjú, AFST 2016 "Spectral gap in the group of affine
transformations over prime fields", Thm 1):** for `G = F_p^d ⋊ SL_d(F_p)` and a lift `S` of a
linear generating set `S' ⊂ SL_d(F_p)`,
  `gap(G, S) ≥ c_d · min{ gap(SL_d(F_p), S'), |S|⁻¹ }`.
The Bourgain–Gamburd input `gap(SL_d(F_p), S') ≥ c` (Thm A) requires `S'` to be the reduction of
a **Zariski-dense subgroup of the PERFECT group `SL_d`, `d ≥ 2`** (quasirandomness: smallest
non-trivial irrep of `SL_2(F_p)` has dimension `(p−1)/2`).

**The obstruction (audit-corrected).** The dilation action of `μ_n` is the `d = 1` case. There
the linear part is `SL_1 = {1}` and the group controlling the dilation is the **abelian torus**
`μ_n ≤ F_p^*`.  LV Thm 1 is stated for `SL_d`, `d ≥ 2`; at `d = 1` it is simply **not applicable**
(it does not "give 0").  Abelian groups have only `1`-dimensional irreducibles (no
quasirandomness), so BG Thm A has no analogue.  The honest obstruction is: (a) bounded-degree
Cayley families of abelian groups (e.g. `μ_n ≅ ℤ/n` with the `{±1}` generator) are never uniform
expanders; (b) if one instead takes the full dilation set `S = μ_n`, the abelian Cayley operator
is the averaging operator (gap `1`), but then `|S|⁻¹ = 1/n → 0`, so an LV-shaped bound
`c·min{gap, |S|⁻¹}` would still decay.  Either way no uniform BG-type input appears.

Moreover the BG *non-concentration / Fourier-flatness* input on the additive factor `F_p` is, for
the uniform measure `u` on `μ_n`, exactly `\hat u(b) = η_b/n`; its sup over `b≠0` is `M(n)/n`. So
even the input one would feed to a hypothetical affine gap **is the prize object itself** — the
route is circular.

## What this file lands (axiom-clean `ℝ`/`ℂ`-arithmetic, no Weil, no char-`p`):

1. `affine_fourier_input_eq_period` : the BG additive non-concentration input
   `\hat u(b) = (∑_{x∈μ_n} e_p(bx)) / n = η_b / n` is **definitionally** the prize Gauss period
   over `n`. So `‖\hat u(b)‖ = ‖η_b‖ / n`, and `sup_{b≠0}‖\hat u(b)‖ = M(n)/n`. (Circularity.)
2. `abelian_dilation_gap_le`        : the spectral gap of `Cay(ℤ/n, {±1})` (`= 1 − cos(2π/n)`,
   one particular bounded-degree generator choice) satisfies `1 − cos(2π/n) ≤ 2π²/n²` → `0`.
3. `abelian_dilation_no_uniform_gap`: for every `c > 0` there is `n` with that gap `< c` — the
   `{±1}` Cayley family of `ℤ/n` is not a uniform expander family.  (This is specific to the
   bounded generator; with `S = μ_n` the gap is `1`, see the obstruction paragraph.)
4. `lv_envelope_vacuous`            : arithmetic only — the expression `c·min{0, s}` is `0` for
   `s ≥ 0`.  This does NOT model LV Thm 1 at `d = 1` (which is not applicable there).

**Verdict: OBSTRUCTION (informal).** The Bourgain–Gamburd / superstrong-approximation machinery
does not apply to the multiplicative dilation action: the natural envelope (the affine group) has an
*abelian* linear part `μ_n` (LV Thm 1 is not applicable at `d = 1`, and abelian Cayley families give
no uniform BG-type input — bounded degree gives gap → 0, full `S = μ_n` gives `|S|⁻¹ → 0`); and the
only quantity it would control is `M(n)/n` itself. No new control on `M(n)` is produced.  The Lean
content is items 1–4 above; the verdict is their informal reading.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset Real Complex

namespace ArkLib.ProximityGap.Frontier.AffineBGGapObstruction

/-! ## 1. Circularity: the affine Fourier-flatness input IS the prize period. -/

/-- The additive character `e_p(t) = exp(2πi t / p)` as a unit complex number. -/
noncomputable def ep (p : ℕ) (t : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ))

/-- The Gauss period `η_b = ∑_{x ∈ S} e_p(b·x)` over a finite multiplicative-subgroup support `S`. -/
noncomputable def period (p : ℕ) (S : Finset ℕ) (b : ℕ) : ℂ := ∑ x ∈ S, ep p (b * x)

/-- The Fourier transform of the **uniform measure** `u` on the dilation support `S` (`|S| = n`),
evaluated at frequency `b`, is exactly the prize period divided by `n`. This is the additive
non-concentration / Fourier-flatness input the Bourgain–Gamburd machine reads on the `F_p` factor.
-/
noncomputable def affineFourierInput (p : ℕ) (S : Finset ℕ) (b : ℕ) : ℂ :=
  (period p S b) / (S.card : ℂ)

/-- **Circularity (definitional identity).** The BG additive non-concentration input
`\hat u(b)` equals the prize Gauss period `η_b` divided by `n = |S|`. Hence
`‖\hat u(b)‖ = ‖η_b‖ / n`, and the worst-case input `sup_{b≠0}‖\hat u(b)‖ = M(n)/n`: bounding the
quantity a hypothetical affine spectral gap would feed back is *exactly* bounding the prize
object. No new control is created by passing to the affine envelope. -/
theorem affine_fourier_input_eq_period (p : ℕ) (S : Finset ℕ) (b : ℕ) :
    affineFourierInput p S b * (S.card : ℂ) = period p S b := by
  unfold affineFourierInput
  by_cases h : (S.card : ℂ) = 0
  · simp only [h, mul_zero]
    -- card S = 0 ⟹ S = ∅ ⟹ period = 0
    have hcard : S.card = 0 := by exact_mod_cast h
    have hS : S = (∅ : Finset ℕ) := Finset.card_eq_zero.mp hcard
    simp [period, hS]
  · field_simp

/-- The norm form of the circularity: `‖\hat u(b)‖ = ‖η_b‖ / |S|`. The sup over `b ≠ 0` of the
LHS is `M(n)/n`; so the affine input's worst case is the prize wall over `n`. -/
theorem affine_fourier_input_norm (p : ℕ) (S : Finset ℕ) (b : ℕ) :
    ‖affineFourierInput p S b‖ = ‖period p S b‖ / (S.card : ℝ) := by
  unfold affineFourierInput
  rw [norm_div, Complex.norm_natCast]

/-! ## 2. The abelian dilation gap collapses (no Bourgain–Gamburd input). -/

/-- The spectral gap of the **cyclic** dilation group `μ_n ≅ ℤ/n` with the symmetric generator
`{±1}`: its non-trivial Cayley-graph eigenvalues are `cos(2πk/n)`, the largest being `cos(2π/n)`,
so the gap is `1 − cos(2π/n)`.  This is ONE generator choice (bounded degree 2), not a best-possible
gap: with the full dilation set `S = μ_n` the normalized Cayley operator is averaging and the gap
is `1`.  There is no `d = 1` instance of LV Thm 1 for this to enter. -/
noncomputable def abelianDilationGap (n : ℕ) : ℝ := 1 - Real.cos (2 * Real.pi / n)

/-- **The abelian linear-part gap collapses as `n → ∞`.** Using `1 − cos θ ≤ θ²/2`, the cyclic
dilation gap is bounded by `2π²/n²`, hence tends to `0`. There is therefore NO uniform spectral
gap for the multiplicative-dilation linear part — the Bourgain–Gamburd input
`gap(linear part) ≥ c > 0` is unavailable for the abelian torus `μ_n`. -/
theorem abelian_dilation_gap_le (n : ℕ) (hn : 0 < n) :
    abelianDilationGap n ≤ 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by
  unfold abelianDilationGap
  -- 1 - cos θ ≤ θ²/2  with  θ = 2π/n, from  1 - θ²/2 ≤ cos θ
  have hcos : 1 - Real.cos (2 * Real.pi / n) ≤ (2 * Real.pi / n) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi / (n : ℝ))
    linarith
  refine hcos.trans ?_
  -- (2π/n)²/2 = 2π²/n²
  have heq : (2 * Real.pi / (n : ℝ)) ^ 2 / 2 = 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq]

/-- **No uniform gap for the `{±1}` family.** For every target `c > 0` there is `n` with
`abelianDilationGap n < c`: the Cayley family `Cay(ℤ/n, {±1})` is not a uniform expander family
(as for any bounded-degree abelian family).  This is about that generator choice only; it is not a
general failure statement for every generating set of `μ_n`. -/
theorem abelian_dilation_no_uniform_gap :
    ∀ c : ℝ, 0 < c → ∃ n : ℕ, 0 < n ∧ abelianDilationGap n < c := by
  intro c hc
  -- choose n with 2π²/n² < c, i.e. n > π√(2/c); take n ≥ that
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt (2 * Real.pi ^ 2 / c))
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  have hn : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hbound : abelianDilationGap (N + 1) ≤ 2 * Real.pi ^ 2 / ((N + 1 : ℕ) : ℝ) ^ 2 :=
    abelian_dilation_gap_le (N + 1) (Nat.succ_pos N)
  refine hbound.trans_lt ?_
  -- 2π²/n² < c  ⟺  n² > 2π²/c  ⟺  n > √(2π²/c)
  rw [div_lt_iff₀ (by positivity)]
  have hsqrt : Real.sqrt (2 * Real.pi ^ 2 / c) < ((N + 1 : ℕ) : ℝ) := by
    push_cast
    have : Real.sqrt (2 * Real.pi ^ 2 / c) < (N : ℝ) := hN
    linarith
  have hpos : 0 ≤ Real.sqrt (2 * Real.pi ^ 2 / c) := Real.sqrt_nonneg _
  -- square both sides:  2π²/c < n²
  have hsq : 2 * Real.pi ^ 2 / c < (((N + 1 : ℕ) : ℝ)) ^ 2 := by
    have h1 : (Real.sqrt (2 * Real.pi ^ 2 / c)) ^ 2 = 2 * Real.pi ^ 2 / c :=
      Real.sq_sqrt (by positivity)
    calc 2 * Real.pi ^ 2 / c = (Real.sqrt (2 * Real.pi ^ 2 / c)) ^ 2 := h1.symm
      _ < (((N + 1 : ℕ) : ℝ)) ^ 2 := by
          apply sq_lt_sq' <;> [linarith; linarith]
  -- 2π² < c · n²
  rw [div_lt_iff₀ hc] at hsq
  linarith [hsq]

/-! ## 3. The Lindenstrauss–Varjú envelope is vacuous for the abelian linear part. -/

/-- The *shape* of the Lindenstrauss–Varjú Theorem 1 lower bound, `c · min{gLin, sInv}`, as a bare
real expression.  LV Thm 1 itself requires `SL_d` with `d ≥ 2`; this expression is not an instance
of it at `d = 1`. -/
noncomputable def lvLowerBound (c gLin sInv : ℝ) : ℝ := c * min gLin sInv

/-- **Arithmetic: `c·min{0, sInv} = 0` for `sInv ≥ 0`.**  This only evaluates the expression
`lvLowerBound` at `gLin = 0`.  It is NOT a consequence of LV Thm 1 at `d = 1` (not applicable
there), and `abelianDilationGap n` is positive for `n ≥ 2`, so `gLin = 0` is not its value. -/
theorem lv_envelope_vacuous (c sInv : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ sInv) :
    lvLowerBound c 0 sInv = 0 := by
  unfold lvLowerBound
  rw [min_eq_left (le_trans (le_refl 0) hs)]
  · ring

/-- **Bundle of 2+3.** Conjoins `abelian_dilation_no_uniform_gap` (the `{±1}` Cayley family of
`ℤ/n` has no uniform gap) and `lv_envelope_vacuous` (the arithmetic `c·min{0, s} = 0`).  The
informal reading — BG / superstrong approximation gives no control on `M(n)` because LV Thm 1 is
not applicable at `d = 1`, abelian Cayley families give no uniform BG input, and the only fed-back
quantity is `M(n)/n` (`affine_fourier_input_norm`) — is NOT itself proven by this conjunction. -/
theorem bg_route_no_bound_on_M :
    (∀ c₀ : ℝ, 0 < c₀ → ∃ n : ℕ, 0 < n ∧ abelianDilationGap n < c₀) ∧
    (∀ c sInv : ℝ, 0 ≤ c → 0 ≤ sInv → lvLowerBound c 0 sInv = 0) :=
  ⟨abelian_dilation_no_uniform_gap, lv_envelope_vacuous⟩

end ArkLib.ProximityGap.Frontier.AffineBGGapObstruction

open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms affine_fourier_input_eq_period
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms affine_fourier_input_norm
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms abelian_dilation_gap_le
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms abelian_dilation_no_uniform_gap
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms lv_envelope_vacuous
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms bg_route_no_bound_on_M
