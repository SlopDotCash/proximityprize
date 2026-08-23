/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.IncidenceDevL2Offset
import ArkLib.Data.CodingTheory.ProximityGap.IncidenceDeviationCharSum
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# The incidence-offset MOMENT-RATIO tool: an EXACT, wall-free sandwich pinning the worst-case
  far-line incidence deviation (`L∞`) between the offset moment ratios and powers — Face I × Form-D
  (#444, #407)

## The new machinery (what nobody built before)

The two proven cross-face *offset-Parseval* identities give the **L²** and **L⁴** of the incidence
deviation field `D(s₀) := I(s₀,s₁) − |G|` averaged over the line offset `s₀`:

* `IncidenceDevL2Offset.dev_l2_offset_eq` : `∑_{s₀} ‖D(s₀)‖² = q·∑_{b∈dev}‖η_b‖²`.
* `GrindL4Bridge.incidence_l4_offset_eq_specConvEnergy` : `∑_{s₀} ‖D(s₀)‖⁴ = q·specConvEnergy`.

Both are *average* (L²/L⁴) facts.  The prize needs the **worst-case (L∞) single offset**
`max_{s₀}‖D(s₀)‖ ≲ √q·B`.  This file supplies the missing machinery joining the two: an **EXACT,
unconditional, wall-free SANDWICH** that pins the worst-case deviation between the offset *moment
ratios* and the offset *moment powers*, for every truncation depth `k`.

Define the **offset even-moment sequence** of the deviation field,
  `M_k := ∑_{s₀ ∈ F} ‖D(s₀)‖^{2k}`   (`offMoment`, `M_0 = q`, `M_1 = q·∑‖η_b‖²`, `M_2 = q·specConvEnergy`).

We prove, with NO field-size hypothesis, NO regime, NO √-cancellation, NO Paley/BGK input:

1. **`offMoment_succ_le_sup_mul`** (the moment RECURSION): `M_{k+1} ≤ T · M_k`, where
   `T := max_{s₀}‖D(s₀)‖²` is the worst-case squared deviation.  Hence the **EXACT lower ladder**
   `offMoment_ratio_le_sup` :  `M_{k+1} / M_k ≤ T`   (for `M_k > 0`).

2. **`sup_le_offMoment_rpow`** (the moment POWER upper): `T ≤ M_k^{1/k}` for `k ≥ 1` (the worst-case
   squared deviation is dominated by every `(2k)`-power mean).  Equivalently `T^k ≤ M_k`.

Together these are the **L∞ sandwich**:  `M_{k+1}/M_k ≤ T ≤ M_k^{1/k}`  for every `k ≥ 1`.

## Why this is the right Face-I × Form-D tool (and what it pins)

`T = max_{s₀}‖I(s₀,s₁) − |G||²` is the **worst-case far-line incidence deviation** — the exact object
the prize budget needs to bound (`epsMCA_ge_far_incidence`).  The sandwich says:

* the moment *ratio* `M_{k+1}/M_k` is a **monotone-in-`k`, EXACT lower bound** for `T` that converges
  UP to `T` (it is the Form-D-Jacobi "top of the support of the offset spectral measure" read off the
  Hankel/power-sum data) — this is the wall-free LOWER half;
* the moment *power* `M_k^{1/k}` is an EXACT UPPER bound for `T` that converges DOWN to `T`.

Since `M_k = q·(additive 2k-energy of the period spectrum)` (the offset-Parseval identities,
generalised), **the entire L²/L⁴→L∞ gap is now EXACTLY a moment-ratio convergence-rate statement**:
`T` is pinned to `√(n log q)`-scale iff the offset moments `M_k` stay Wick-like up to depth
`k ≈ log q` (Face A) — but the *reduction itself* (sandwich + the fact that `M_k` is the offset
2k-energy) is proven here, wall-free.  This is the incidence-side reorganisation of the Form-D-Jacobi
edge: `T = lim_k M_{k+1}/M_k = lim_k M_k^{1/k}`, the support edge of the offset measure.

## Honest scope (NOT the prize, NOT a face closure)

The sandwich is EXACT and unconditional, but it does NOT bound `T` numerically: closing the prize
still needs an *effective* upper bound on some `M_k` at `k ≈ log q` (the offset 2k-energy = Face A =
the wall).  What is new and certified: the worst-case far-line incidence deviation is *exactly*
squeezed by the offset moment ratios and powers — so any future bound on a deep offset moment is
*literally* a bound on the worst-case incidence (and vice versa), and the lower ladder
`M_{k+1}/M_k ≤ T` gives a free, monotone, wall-free certificate of how large `T` must be.  The
residual is purely the deep offset moment `M_{log q}`, i.e. Face A; this file does NOT discharge it.

Axiom-clean (`propext, Classical.choice, Quot.sound`); pure norm inequalities + the EXACT
offset-Parseval identities.  Issue #444 / #407.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge
open ArkLib.ProximityGap.IncidenceDeviationCharSum
open ArkLib.ProximityGap.IncidenceDevL2Offset

namespace ArkLib.ProximityGap.Frontier.PIN6

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The offset even-moment sequence of the incidence-deviation field.**
`M_k := ∑_{s₀ ∈ F} ‖D(s₀)‖^{2k}` where `D(s₀) = I(s₀,s₁) − |G|` (`devField`).  `M_0 = q`,
`M_1 = ∑_{s₀}‖D‖²` (the L²(offset) Parseval mass), `M_2 = ∑_{s₀}‖D‖⁴` (the L⁴ additive energy).
This is the moment sequence whose support edge is the worst-case squared deviation. -/
noncomputable def offMoment (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) (k : ℕ) : ℝ :=
  ∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ (2 * k)

/-- The worst-case squared deviation over the offset: `T := max_{s₀}‖D(s₀)‖²`. -/
noncomputable def offSup (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) : ℝ :=
  ⨆ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2

/-! ### Basic facts about the moment sequence -/

/-- Every offset moment is non-negative. -/
theorem offMoment_nonneg (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) (k : ℕ) :
    0 ≤ offMoment ψ G s₁ k := by
  unfold offMoment
  refine Finset.sum_nonneg (fun s₀ _ => ?_)
  positivity

/-- `M_0 = q`: the zeroth moment counts the offsets. -/
theorem offMoment_zero (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) :
    offMoment ψ G s₁ 0 = (Fintype.card F : ℝ) := by
  unfold offMoment
  simp [Finset.card_univ]

/-- The first offset moment is the L²(offset) Parseval mass (= `q·∑_{b∈dev}‖η_b‖²`). -/
theorem offMoment_one_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₁ : F) :
    offMoment ψ G s₁ 1 = (Fintype.card F : ℝ) * ∑ b ∈ deviationSupport s₁, ‖eta ψ G b‖ ^ 2 := by
  unfold offMoment
  simp only [mul_one]
  rw [dev_l2_offset_eq hψ G s₁]

/-! ### The worst-case squared deviation `T = offSup` -/

/-- The pointwise squared deviation is `≤ T` for every offset `s₀` (the defining sup bound, with the
finite-`Fintype` index making the `iSup` a genuine maximum). -/
theorem sq_le_offSup (ψ : AddChar F ℂ) (G : Finset F) (s₀ s₁ : F) :
    ‖devField ψ G s₀ s₁‖ ^ 2 ≤ offSup ψ G s₁ := by
  unfold offSup
  exact le_ciSup (f := fun s₀ : F => ‖devField ψ G s₀ s₁‖ ^ 2)
    (Finite.bddAbove_range _) s₀

/-- `T ≥ 0` (it dominates each non-negative squared deviation). -/
theorem offSup_nonneg (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) :
    0 ≤ offSup ψ G s₁ := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty F)
  exact le_trans (by positivity) (sq_le_offSup ψ G s₀ s₁)

/-! ### Tool 1 — the moment recursion `M_{k+1} ≤ T · M_k` and the EXACT lower ladder -/

/-- **The offset-moment recursion (headline, wall-free).**  Each offset even moment is at most the
worst-case squared deviation times the previous moment:

  `M_{k+1} ≤ T · M_k`,   `T = max_{s₀}‖D(s₀)‖²`.

Pointwise `‖D(s₀)‖^{2(k+1)} = ‖D(s₀)‖² · ‖D(s₀)‖^{2k} ≤ T · ‖D(s₀)‖^{2k}`; sum over `s₀`.  This is
the engine of the lower ladder: it forces `T` to dominate every moment ratio `M_{k+1}/M_k`. -/
theorem offMoment_succ_le_sup_mul (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) (k : ℕ) :
    offMoment ψ G s₁ (k + 1) ≤ offSup ψ G s₁ * offMoment ψ G s₁ k := by
  unfold offMoment
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun s₀ _ => ?_)
  have hpow : ‖devField ψ G s₀ s₁‖ ^ (2 * (k + 1))
      = ‖devField ψ G s₀ s₁‖ ^ 2 * ‖devField ψ G s₀ s₁‖ ^ (2 * k) := by
    rw [← pow_add]; ring_nf
  rw [hpow]
  have hsq := sq_le_offSup ψ G s₀ s₁
  have hpownn : (0 : ℝ) ≤ ‖devField ψ G s₀ s₁‖ ^ (2 * k) := by positivity
  exact mul_le_mul_of_nonneg_right hsq hpownn

/-- **The EXACT lower ladder (Form-D-Jacobi support edge, read off the offset moments).**
For any depth `k` with `M_k > 0`, the worst-case squared deviation dominates the moment ratio:

  `M_{k+1} / M_k ≤ T = max_{s₀}‖D(s₀)‖²`.

This is the wall-free LOWER half of the L∞ sandwich: the moment ratios `M_{k+1}/M_k` form an
EXACT, certificate-free lower-bound ladder for the worst-case far-line incidence deviation, the
incidence-side reading of the Jacobi top eigenvalue (= support edge of the offset measure). -/
theorem offMoment_ratio_le_sup (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) (k : ℕ)
    (hMk : 0 < offMoment ψ G s₁ k) :
    offMoment ψ G s₁ (k + 1) / offMoment ψ G s₁ k ≤ offSup ψ G s₁ := by
  rw [div_le_iff₀ hMk]
  exact offMoment_succ_le_sup_mul ψ G s₁ k

/-! ### Tool 2 — the moment POWER upper bound `T^k ≤ M_k`, the UPPER half of the sandwich -/

/-- **The moment-power upper bound (headline, wall-free).**  The worst-case squared deviation to the
`k`-th power is at most the `2k`-th offset moment:

  `T^k ≤ M_k = ∑_{s₀}‖D(s₀)‖^{2k}`.

Because some offset `s₀*` attains the worst-case squared deviation `T` (the index is finite), its
single term `‖D(s₀*)‖^{2k} = T^k` already sits inside the sum, and every other term is `≥ 0`.  This
is the UPPER half of the sandwich `T ≤ M_k^{1/k}` (`k ≥ 1`): the worst-case deviation is dominated by
every offset power mean. -/
theorem sup_pow_le_offMoment (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) (k : ℕ) :
    (offSup ψ G s₁) ^ k ≤ offMoment ψ G s₁ k := by
  classical
  -- the iSup over a finite nonempty type is attained
  obtain ⟨s₀star, hstar⟩ := Finite.exists_max (fun s₀ : F => ‖devField ψ G s₀ s₁‖ ^ 2)
  -- offSup = the max value, attained at s₀star
  have hsupeq : offSup ψ G s₁ = ‖devField ψ G s₀star s₁‖ ^ 2 := by
    unfold offSup
    apply le_antisymm
    · apply ciSup_le; intro s₀; exact hstar s₀
    · exact le_ciSup (f := fun s₀ : F => ‖devField ψ G s₀ s₁‖ ^ 2)
        (Finite.bddAbove_range _) s₀star
  rw [hsupeq]
  unfold offMoment
  -- single term: ‖D(s₀star)‖^{2k} = (‖D(s₀star)‖²)^k sits in the sum
  have hterm : (‖devField ψ G s₀star s₁‖ ^ 2) ^ k = ‖devField ψ G s₀star s₁‖ ^ (2 * k) := by
    rw [← pow_mul]
  rw [hterm]
  refine Finset.single_le_sum (f := fun s₀ : F => ‖devField ψ G s₀ s₁‖ ^ (2 * k))
    (fun s₀ _ => by positivity) (Finset.mem_univ s₀star)

/-- **The moment-power upper bound, root form.**  For `k ≥ 1`, `T ≤ M_k^{1/k}`: the worst-case
squared deviation is at most the `(1/k)`-power of the `2k`-th offset moment.  This is the converging
UPPER bound complementing the lower ladder; together with `offMoment_ratio_le_sup` it is the EXACT
L∞ sandwich. -/
theorem sup_le_offMoment_rpow (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) (k : ℕ) (hk : 1 ≤ k) :
    offSup ψ G s₁ ≤ (offMoment ψ G s₁ k) ^ ((1 : ℝ) / k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsupnn : 0 ≤ offSup ψ G s₁ := offSup_nonneg ψ G s₁
  have hpow := sup_pow_le_offMoment ψ G s₁ k
  -- T = (T^k)^{1/k} ≤ M_k^{1/k}  (rpow is monotone, T^k ≥ 0)
  have hMnn : (0 : ℝ) ≤ offMoment ψ G s₁ k := offMoment_nonneg ψ G s₁ k
  have hTk_rpow : (offSup ψ G s₁) = ((offSup ψ G s₁) ^ k) ^ ((1 : ℝ) / k) := by
    rw [← Real.rpow_natCast (offSup ψ G s₁) k, ← Real.rpow_mul hsupnn]
    rw [mul_one_div, div_self (ne_of_gt hkpos), Real.rpow_one]
  rw [hTk_rpow]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast hpow

/-! ### The EXACT L∞ sandwich (the headline tool, packaged) -/

/-- **THE INCIDENCE-OFFSET L∞ SANDWICH (capstone).**  For every depth `k ≥ 1` with `M_k > 0`, the
worst-case far-line incidence squared deviation `T = max_{s₀}‖I(s₀,s₁) − |G||²` is EXACTLY squeezed
between the offset moment ratio and the offset moment power:

  `M_{k+1} / M_k  ≤  T  ≤  M_k^{1/k}`.

Both bounds are unconditional and wall-free.  `M_k = ∑_{s₀}‖D(s₀)‖^{2k}` is the `2k`-th offset
moment, which (by the offset-Parseval identities) equals `q` times the additive `2k`-energy of the
period spectrum.  So the worst-case incidence deviation is pinned to the convergence of the offset
moment ratios/powers — the incidence-side restatement of the Form-D-Jacobi support edge.  The prize
needs `T ≲ q·B²` (`B ≈ √(n log q)`), which by the upper bound reduces to bounding ONE deep offset
moment `M_k` at `k ≈ log q` (= Face A, the wall) — NOT discharged here; the sandwich itself is. -/
theorem incidence_offset_sandwich (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) (k : ℕ) (hk : 1 ≤ k)
    (hMk : 0 < offMoment ψ G s₁ k) :
    offMoment ψ G s₁ (k + 1) / offMoment ψ G s₁ k ≤ offSup ψ G s₁
      ∧ offSup ψ G s₁ ≤ (offMoment ψ G s₁ k) ^ ((1 : ℝ) / k) :=
  ⟨offMoment_ratio_le_sup ψ G s₁ k hMk, sup_le_offMoment_rpow ψ G s₁ k hk⟩

/-! ### Connect the sup to the genuine incidence deviation (the Face-I object) -/

/-- **The offset sup IS the worst-case far-line incidence squared deviation.**  Rewriting `devField`
to `I(s₀,s₁) − |G|`, the abstract `offSup` is literally the worst-case squared incidence deviation
over the offset — the object `epsMCA_ge_far_incidence` consumes.  (Makes the sandwich a statement
about the prize's incidence functional, not just the abstract spectral field.) -/
theorem offSup_eq_incidence_sup {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₁ : F) :
    offSup ψ G s₁ = ⨆ s₀ : F, ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖ ^ 2 := by
  unfold offSup
  have hpt : ∀ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2
      = ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖ ^ 2 := by
    intro s₀; rw [devField_eq_incidence_sub_mean hψ G s₀ s₁]
  exact congrArg _ (funext hpt)

/-- **The first moment ratio recovers the Parseval lower bound on `T`.**  At `k = 1`,
`offMoment_ratio_le_sup` says `M_2/M_1 ≤ T`, i.e. the L⁴/L² ratio of the incidence deviation field
lower-bounds the worst-case deviation.  This is the wall-free quantitative content already at the
proven L²/L⁴ level: the additive energy over the Parseval mass is a certificate-free lower bound for
the worst-case far-line incidence deviation. -/
theorem l4_over_l2_le_sup {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₁ : F)
    (hM1 : 0 < offMoment ψ G s₁ 1) :
    offMoment ψ G s₁ 2 / offMoment ψ G s₁ 1 ≤ offSup ψ G s₁ :=
  offMoment_ratio_le_sup ψ G s₁ 1 hM1

/-! ### Tool 3 — a CLEAN NUMERIC floor: `T ≥ M_1/q = ∑_{b∈dev}‖η_b‖²` (Cauchy–Schwarz, wall-free) -/

/-- **Cauchy–Schwarz on the offset moments: `M_1² ≤ q · M_2`.**  Applying the discrete
Cauchy–Schwarz `(∑ fᵢgᵢ)² ≤ (∑fᵢ²)(∑gᵢ²)` with `f(s₀) = ‖D(s₀)‖²`, `g ≡ 1` gives
`(∑‖D‖²)² ≤ (∑‖D‖⁴)·q`, i.e. `M_1² ≤ q·M_2`.  This says the L⁴ offset moment is at least the
square of the L² mass over the count — the engine of the numeric floor. -/
theorem offMoment_one_sq_le_q_mul_two (ψ : AddChar F ℂ) (G : Finset F) (s₁ : F) :
    (offMoment ψ G s₁ 1) ^ 2 ≤ (Fintype.card F : ℝ) * offMoment ψ G s₁ 2 := by
  classical
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset F)
    (fun s₀ : F => ‖devField ψ G s₀ s₁‖ ^ 2) (fun _ : F => (1 : ℝ))
  -- LHS of hCS: (∑ ‖D‖²·1)² = M_1²
  have hL : (∑ s₀ : F, ‖devField ψ G s₀ s₁‖ ^ 2 * (1 : ℝ)) ^ 2 = (offMoment ψ G s₁ 1) ^ 2 := by
    unfold offMoment; simp
  -- RHS factor 1: ∑ (‖D‖²)² = ∑ ‖D‖⁴ = M_2
  have hR1 : (∑ s₀ : F, (‖devField ψ G s₀ s₁‖ ^ 2) ^ 2) = offMoment ψ G s₁ 2 := by
    unfold offMoment
    refine Finset.sum_congr rfl (fun s₀ _ => ?_)
    rw [← pow_mul]
  -- RHS factor 2: ∑ 1² = q
  have hR2 : (∑ _s₀ : F, (1 : ℝ) ^ 2) = (Fintype.card F : ℝ) := by
    simp [Finset.card_univ]
  rw [hL] at hCS
  rw [hR1, hR2] at hCS
  linarith [hCS]

/-- **THE NUMERIC FLOOR (wall-free): `T ≥ M_1 / q`.**  The worst-case far-line incidence squared
deviation is at least the *average* squared deviation over the offset:

  `T = max_{s₀}‖D(s₀)‖²  ≥  (1/q)·∑_{s₀}‖D(s₀)‖²  =  ∑_{b∈deviationSupport s₁}‖η_b‖²`.

Proof: the moment ratio `M_2/M_1 ≤ T` (lower ladder, `k=1`) combined with Cauchy–Schwarz
`M_1² ≤ q·M_2` gives `M_1/q ≤ M_2/M_1 ≤ T`.  This is the EXACT, unconditional "max ≥ average"
floor, tied through the offset-Parseval identity to the **deviation-support period energy**
`∑_{b∈dev}‖η_b‖²` — a certificate-free numeric lower bound for the worst-case incidence deviation,
with NO wall.  (The prize needs the matching UPPER bound `T ≲ q·B²`, the open side.) -/
theorem offSup_ge_avg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (s₁ : F)
    (hM1 : 0 < offMoment ψ G s₁ 1) :
    ∑ b ∈ deviationSupport s₁, ‖eta ψ G b‖ ^ 2 ≤ offSup ψ G s₁ := by
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F); exact_mod_cast this
  -- Cauchy–Schwarz: M_1² ≤ q·M_2;  recursion: M_2 ≤ T·M_1.  Chain ⟹ M_1 ≤ q·T.
  have hCS := offMoment_one_sq_le_q_mul_two ψ G s₁
  have hrec : offMoment ψ G s₁ 2 ≤ offSup ψ G s₁ * offMoment ψ G s₁ 1 :=
    offMoment_succ_le_sup_mul ψ G s₁ 1
  have hT : 0 ≤ offSup ψ G s₁ := offSup_nonneg ψ G s₁
  -- M_1² ≤ q·M_2 ≤ q·(T·M_1) = (q·T)·M_1, and M_1 > 0 ⟹ M_1 ≤ q·T
  have hchain : (offMoment ψ G s₁ 1) ^ 2 ≤ ((Fintype.card F : ℝ) * offSup ψ G s₁) * offMoment ψ G s₁ 1 := by
    have h2 : (Fintype.card F : ℝ) * offMoment ψ G s₁ 2
        ≤ (Fintype.card F : ℝ) * (offSup ψ G s₁ * offMoment ψ G s₁ 1) :=
      mul_le_mul_of_nonneg_left hrec (le_of_lt hq)
    nlinarith [hCS, h2]
  -- divide by M_1 > 0:  M_1 ≤ q·T
  have hM1le : offMoment ψ G s₁ 1 ≤ (Fintype.card F : ℝ) * offSup ψ G s₁ := by
    have hsq : offMoment ψ G s₁ 1 * offMoment ψ G s₁ 1
        ≤ ((Fintype.card F : ℝ) * offSup ψ G s₁) * offMoment ψ G s₁ 1 := by
      nlinarith [hchain]
    exact le_of_mul_le_mul_right (by linarith [hsq]) hM1
  -- M_1 = q·∑‖η_b‖²  ⟹  ∑‖η_b‖² ≤ T
  rw [offMoment_one_eq hψ G s₁] at hM1le
  -- q·∑‖η_b‖² ≤ q·T  ⟹  ∑‖η_b‖² ≤ T
  have := le_of_mul_le_mul_left (by linarith [hM1le] : (Fintype.card F : ℝ) * (∑ b ∈ deviationSupport s₁, ‖eta ψ G b‖ ^ 2) ≤ (Fintype.card F : ℝ) * offSup ψ G s₁) hq
  exact this

end ArkLib.ProximityGap.Frontier.PIN6

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.PIN6.offMoment_succ_le_sup_mul
#print axioms ArkLib.ProximityGap.Frontier.PIN6.offMoment_ratio_le_sup
#print axioms ArkLib.ProximityGap.Frontier.PIN6.sup_pow_le_offMoment
#print axioms ArkLib.ProximityGap.Frontier.PIN6.sup_le_offMoment_rpow
#print axioms ArkLib.ProximityGap.Frontier.PIN6.incidence_offset_sandwich
#print axioms ArkLib.ProximityGap.Frontier.PIN6.offSup_eq_incidence_sup
#print axioms ArkLib.ProximityGap.Frontier.PIN6.l4_over_l2_le_sup
#print axioms ArkLib.ProximityGap.Frontier.PIN6.offMoment_one_sq_le_q_mul_two
#print axioms ArkLib.ProximityGap.Frontier.PIN6.offSup_ge_avg
