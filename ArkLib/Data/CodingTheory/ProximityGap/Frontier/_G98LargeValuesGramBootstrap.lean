/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# G98 (#466): Guth–Maynard large-values / Halász–Montgomery Gram bootstrap for the period sup

**Lane G98 [virgin angle].** Transfer of the Guth–Maynard (arXiv 2405.20552, "New large value
estimates for Dirichlet polynomials") large-values machinery to the Gauss-period sup problem

  `M(μ_n) = max_{b ≠ 0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, target `M ≤ C√(n log(p/n))`, `p ≈ n⁴`.

GM's innovation for Dirichlet polynomials `Σ b_n n^{it}` is to reformulate large values as a
matrix problem: for a set `B` of `r` frequencies where the polynomial is `≥ V`, study the
**large-values (Gram) matrix** of phases between the large-value points, and exploit
cancellation/structure in that matrix rather than in individual sums.

## The exact analogue for the period family (formalized here)

For the family `v_b = (e_p(bx))_{x∈μ_n}` the transfer is *exact and self-referential*:

> **The large-values matrix IS the period field at difference frequencies**:
> `G_{b,b'} = Σ_{x∈μ_n} e_p((b−b')x) = η_{b−b'}` (`gram_eq_period_diff` below).

The classical Halász–Montgomery inequality then reads (`large_values_gram_bound`):

> if `|η_b| ≥ V` for all `b ∈ B`, `|B| = r`, and `|η_{b−b'}| ≤ M'` for `b ≠ b' ∈ B`, then
> `r·V² ≤ n·(n + (r−1)·M')`.

This is **quadratic in the extremizer set** — a genuinely different functional from the G80
signed-`l1` certificate (`_G80SignedL1CertificatePinnedToWall.lean`), which is *linear* in the
spectrum (`Σ c_b η_b ≤ ‖c‖₁·M`). It is an axiom-clean, `r`-uniform inequality connecting the
sup `M`, the large-value count `r`, and the field at difference frequencies.

## Probe (scripts: `probe_g98_gram_bootstrap.py`, `probe_g98_gram_signs.py`; β = 4, n = 8..64, real primes p = 4129, 65537, 1048609, 16777601)

1. **The self-referential bootstrap is VACUOUS, not merely degenerate.** Measured off-diagonal
   Gram mass at the extremal set: `M'_max/√n ≈ 2.4–3.5`, `M'_mean ≈ 2.0–2.5·√n` — the differences
   of extremizers are themselves large-value frequencies (value percentile 0.88–0.99 ≫ 0.5).
   The informativeness ratio `V²/(n·M')` is **0.32–0.94 < 1 at every scale and every level
   tested** (target level and 0.7M level, r = 4..147): the HM inequality holds for ALL r and
   constrains nothing. Formalized as `selfref_vacuous`: whenever `M' ≥ V²/n` (and `M' ≤ n`),
   the HM inequality is implied by trivial bounds.
2. **The bootstrap fixed point degenerates to the trivial interval.** The self-application
   (`V = M' = M`) admits EVERY `M ≤ n` as a fixed point (`selfref_bootstrap_all_fixed_points`);
   measured `f(V) = √(n²/r + nM')` sits at 8.0–8.5 (n=8, target 7.07), 15.1–15.4 (n=16, target
   11.5), 27.7–30.9 (n=32, target 18.2), 47.2–50.9 (n=64, target 28.3) — strictly ABOVE the
   `√(n log(p/n))` scale and drifting toward the trivial `n`. NOT at √(n log p) scale.
3. **Count-vs-sup: the Gram route certifies emptiness only above the trivial level.** The HM
   count cap `r ≤ n(n−M')/(V²−nM')` drops below 1 **iff `V > n`** — for any off-diagonal bound
   `M'` whatsoever (`hm_certifies_empty_iff_above_trivial`, `hm_count_ge_one_below_trivial`).
   Composed with the recorded F0 fence (`_wfH47_SelbergLargerSieveLargeValues.lean`,
   `sup_le_iff_levelset_card_zero`: only an EMPTY level set bounds the sup), the GM/HM count
   machinery cannot bound `M` below the trivial `n`. Moreover the truth itself has a LARGE
   level set at the target scale (measured: 3/13/26/77 cosets ≥ `√(n log(p/n))` at n = 8/16/32/64,
   growing with n, since C ≈ 1.07–1.36 > 1) — a count argument can never operate at the target.
4. **GM's matrix-cancellation IS present but already priced in.** The extremal Gram has near-total
   sign cancellation (|mean signed off-diag|/mean|off-diag| = 0.7%–4.6%) and low effective rank
   (1.4–17 of r), exactly the structure GM exploit. But the SPECTRAL form of HM is measured
   SATURATED: `n·λ_max(G_B)/Σ_{b∈B}|η_b|² = 1.02–1.08`. This is forced: `λ_max(G_B) ≥ Σ_B|η_b|²/n`
   is a theorem (`period_quadratic_form_floor` / `no_independent_spectral_handle`: any
   operator-norm-style bound `Q ≤ Λ·Σ|η_b|²` on the Gram quadratic form forces `Σ|η_b|² ≤ n·Λ`,
   i.e. `Λ ≥ rV²/n`) — the top of the Gram spectrum is pinned from below by the large values
   themselves, so no spectral upper bound can create a contradiction without already knowing `M`.
5. **Additive structure of `B`:** essentially NONE beyond the forced `±` symmetry (`−1 ∈ μ_n`
   makes `b−b'` and `b'−b` coset-equal): distinct-coset counts of `B−B` are 5/6, 28/28, 113/120,
   491/496 of the maximum `r(r−1)/2`. The level set is NOT approximately difference-closed
   (only 0.7%–16% of `B−B` cosets lie back in the level set, decreasing in n). The GM dichotomy's
   "structured" horn fails; its "few large values" horn is vacuous by (3). The set falls in the
   gap between the horns.

## Moment-disguise verdict (mandated by the dossier §2 no-go `θ(r,β) > 1/2`)

The GM/HM bootstrap is **NOT a moment bound in disguise — it is a COUNT bound in disguise**.
The row-sum functional `max_b Σ_{b'∈B} |η_{b−b'}|` is an `ℓ^∞→ℓ¹` mixed functional on the
extremizer set, not a global `2r`-th moment; it only becomes Parseval (fence F1) if one estimates
the row `ℓ¹` mass by Cauchy–Schwarz against the global energy — a step this file never takes.
The transfer dies by the F0 fence (count-vs-sup, K1 of H47), not by the moment-ladder no-go:
GM's machinery outputs *cardinality* bounds on level sets (sufficient for zero-density theorems,
their application), while the prize demands *emptiness* at a level where the true level set is
large. Distinct death, now recorded. The one residual escape — an INDEPENDENT upper bound on
`λ_max(G_B)` not routed through `|η|` row sums — is exactly an upper bound on the period field
again (the Gram IS the field), i.e. the open core itself: circular, per (4).

## What is proven here (all axiom-clean; no sorry, no new axioms)

* `gram_eq_period_diff` — the transfer identity: the large-values Gram matrix of the period
  family IS the period field at difference frequencies (for any unimodular character `e` on any
  `CommRing`, in particular `e_p` on `F_p`).
* `halasz_montgomery_rowsum` — the abstract finite Halász–Montgomery inequality
  `Σ_{b∈B} |⟨1_s, v_b⟩|² ≤ |s|·max-row-sum(|Gram|)`, by the PSD/duality double-counting proof
  (Cauchy–Schwarz through the domain side + symmetric bilinear row-sum bound).
* `large_values_gram_bound` — the instantiated `r`-uniform large-values inequality
  `r·V² ≤ n·(n + (r−1)·M')` for the period family.
* `hm_count_bound_of_informative` — the count form `r ≤ n(n−M')/(V²−nM')` when `V² > nM'`.
* `selfref_vacuous`, `selfref_bootstrap_all_fixed_points` — the honest obstruction: with the
  measured off-diagonal mass (`M' ≥ V²/n`) the inequality is vacuous, and the self-referential
  bootstrap `M ≤ f(M)` admits the whole trivial interval `[0, n]` as fixed points.
* `hm_certifies_empty_iff_above_trivial`, `hm_count_ge_one_below_trivial`,
  `hm_empty_certificate_needs_trivial_level` — the count route certifies an empty level set only
  above the trivial level `V > n`, for EVERY off-diagonal bound `M'`.
* `period_quadratic_form_floor`, `no_independent_spectral_handle` — the spectral saturation pin:
  the Gram quadratic form at the extremal weights is `≥ (Σ|η_b|²)²/n`, so any spectral handle
  tight enough to help must already bound the field.

## Verdict

`REDUCES-TO-FENCE F0` (count-vs-sup; the GM large-values output type is a cardinality cap, blind
to the pointwise sup below the trivial level) **and** `VACUOUS-AT-PRIZE` (the measured extremal
Gram off-diagonal mass `M' ≈ 2–3.5·√n ≫ log(p/n) = V²_target/n` sits far above the
informativeness threshold; the Gram of the extremizers is the field at near-extremal
frequencies — the self-reference saturates rather than bootstraps). The positive bricks
(`gram_eq_period_diff`, `halasz_montgomery_rowsum`, `large_values_gram_bound`) are new in-tree,
`r`-uniform, quadratic-in-`B` inequalities — NOT wrappers on the linear G80 certificate.
The `√log` excess remains the open BGK/Paley wall, untouched.

Issue #466, lane G98 (Guth–Maynard large-values transfer).
-/

namespace ProximityGap.Frontier.G98LargeValuesGramBootstrap

open Finset ComplexConjugate

variable {α ι : Type*}

/-! ## §1 The abstract large-values Gram machinery (any finite family of ℂ-vectors) -/

/-- The correlation of family member `b` against the all-ones weight on the domain `s`:
for the period family `v b x = e_p(bx)` on `s = μ_n` this is exactly the Gauss period `η_b`. -/
noncomputable def corr (s : Finset α) (v : ι → α → ℂ) (b : ι) : ℂ := ∑ x ∈ s, v b x

/-- The **large-values (Gram) matrix** of the family: `gram s v b b' = ⟨v_b, v_{b'}⟩` as vectors
on the domain `s`. This is the object at the heart of the Guth–Maynard reformulation. -/
noncomputable def gram (s : Finset α) (v : ι → α → ℂ) (b b' : ι) : ℂ :=
  ∑ x ∈ s, v b x * conj (v b' x)

/-- Hermitian symmetry of the Gram matrix. -/
theorem gram_conj_swap (s : Finset α) (v : ι → α → ℂ) (b b' : ι) :
    gram s v b' b = conj (gram s v b b') := by
  rw [gram, gram, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

/-- The absolute Gram matrix is symmetric. -/
theorem norm_gram_swap (s : Finset α) (v : ι → α → ℂ) (b b' : ι) :
    ‖gram s v b b'‖ = ‖gram s v b' b‖ := by
  rw [gram_conj_swap s v b' b, Complex.norm_conj]

/-- **Quadratic-form expansion**: the weighted `L²` mass of the family on the domain equals the
Gram quadratic form. This is the exact mechanism by which "cancellation in matrices" (GM) and
"cancellation in sums" are the same object for this family. -/
theorem weighted_normSq_expand (s : Finset α) (v : ι → α → ℂ) (B : Finset ι) (w : ι → ℂ) :
    ((∑ x ∈ s, ‖∑ b ∈ B, w b * v b x‖ ^ 2 : ℝ) : ℂ)
      = ∑ b ∈ B, ∑ b' ∈ B, w b * conj (w b') * gram s v b b' := by
  push_cast
  have step1 : ∀ x : α, ((‖∑ b ∈ B, w b * v b x‖ : ℂ) ^ 2)
      = ∑ b ∈ B, ∑ b' ∈ B, (w b * v b x) * conj (w b' * v b' x) := by
    intro x
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun x _ => step1 x]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [gram, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul]
  ring

/-- **The Rayleigh/self-referential floor** (steps A–C of the Halász–Montgomery proof, isolated):
the square of the total large-value mass is at most `|s|` times the Gram quadratic form at the
extremal weight vector `w_b = conj(corr b)`. Consequence: the top of the Gram spectrum is pinned
from BELOW by the large values themselves — measured saturated to within 2–8% at the extremal
sets (probe §4 of the module doc). -/
theorem sq_sum_corr_le_card_mul_quadratic (s : Finset α) (v : ι → α → ℂ) (B : Finset ι) :
    (∑ b ∈ B, ‖corr s v b‖ ^ 2) ^ 2
      ≤ (s.card : ℝ) * ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2 := by
  set T : ℝ := ∑ b ∈ B, ‖corr s v b‖ ^ 2 with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA : (∑ x ∈ s, ∑ b ∈ B, conj (corr s v b) * v b x) = (T : ℂ) := by
    rw [Finset.sum_comm, hTdef]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum]
    exact Complex.conj_mul' (corr s v b)
  have hTle : T ≤ ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ := by
    calc T = ‖(T : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hT0]
    _ = ‖∑ x ∈ s, ∑ b ∈ B, conj (corr s v b) * v b x‖ := by rw [hA]
    _ ≤ ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ := norm_sum_le _ _
  calc T ^ 2 ≤ (∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖) ^ 2 :=
        pow_le_pow_left₀ hT0 hTle 2
  _ ≤ (s.card : ℝ) * ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq

/-- Symmetric-bilinear row-sum bound: for a nonneg symmetric kernel `c` with row sums `≤ R` on
`B`, the bilinear form `Σ a_b a_{b'} c_{bb'}` is at most `(Σ a_b²)·R`. Pure finite arithmetic. -/
theorem bilinear_rowsum_bound (B : Finset ι) (a : ι → ℝ) (c : ι → ι → ℝ) (R : ℝ)
    (hc : ∀ b b', 0 ≤ c b b') (hsym : ∀ b b', c b b' = c b' b)
    (hrow : ∀ b ∈ B, ∑ b' ∈ B, c b b' ≤ R) :
    ∑ b ∈ B, ∑ b' ∈ B, a b * a b' * c b b' ≤ (∑ b ∈ B, a b ^ 2) * R := by
  have half : ∑ b ∈ B, ∑ b' ∈ B, a b * a b' * c b b'
      ≤ ∑ b ∈ B, ∑ b' ∈ B, (a b ^ 2 * c b b' + a b' ^ 2 * c b b') / 2 := by
    refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => ?_
    have h1 : a b * a b' ≤ (a b ^ 2 + a b' ^ 2) / 2 := by nlinarith [sq_nonneg (a b - a b')]
    have := mul_le_mul_of_nonneg_right h1 (hc b b')
    nlinarith [this]
  have expand : ∑ b ∈ B, ∑ b' ∈ B, (a b ^ 2 * c b b' + a b' ^ 2 * c b b') / 2
      = ∑ b ∈ B, ∑ b' ∈ B, a b ^ 2 * c b b' := by
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => add_div _ _ 2]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
    have s2 : ∑ b ∈ B, ∑ b' ∈ B, a b' ^ 2 * c b b' / 2
        = ∑ b ∈ B, ∑ b' ∈ B, a b ^ 2 * c b b' / 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      rw [hsym]
    rw [s2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  calc ∑ b ∈ B, ∑ b' ∈ B, a b * a b' * c b b'
      ≤ ∑ b ∈ B, ∑ b' ∈ B, (a b ^ 2 * c b b' + a b' ^ 2 * c b b') / 2 := half
  _ = ∑ b ∈ B, ∑ b' ∈ B, a b ^ 2 * c b b' := expand
  _ = ∑ b ∈ B, a b ^ 2 * ∑ b' ∈ B, c b b' := by
      refine Finset.sum_congr rfl fun b _ => ?_; rw [Finset.mul_sum]
  _ ≤ ∑ b ∈ B, a b ^ 2 * R := by
      refine Finset.sum_le_sum fun b hb => ?_
      exact mul_le_mul_of_nonneg_left (hrow b hb) (sq_nonneg _)
  _ = (∑ b ∈ B, a b ^ 2) * R := by rw [← Finset.sum_mul]

/-- **The finite Halász–Montgomery inequality** (abstract form): the total large-value mass of
the family against the all-ones weight is controlled by `|s|` times the maximal absolute row sum
of the large-values Gram matrix. The proof is the classical PSD double-counting: Cauchy–Schwarz
through the domain side, then the symmetric bilinear row-sum bound. Quadratic in the extremizer
set — NOT the linear `l1` pairing of G80, and NOT a global moment. -/
theorem halasz_montgomery_rowsum (s : Finset α) (v : ι → α → ℂ) (B : Finset ι) (R : ℝ)
    (hR0 : 0 ≤ R)
    (hrow : ∀ b ∈ B, ∑ b' ∈ B, ‖gram s v b b'‖ ≤ R) :
    ∑ b ∈ B, ‖corr s v b‖ ^ 2 ≤ (s.card : ℝ) * R := by
  set T : ℝ := ∑ b ∈ B, ‖corr s v b‖ ^ 2 with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ0 : 0 ≤ ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ : ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2 ≤ T * R := by
    have habs : ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2
        ≤ ∑ b ∈ B, ∑ b' ∈ B, ‖corr s v b‖ * ‖corr s v b'‖ * ‖gram s v b b'‖ := by
      calc ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2
          = ‖((∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2 : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg hQ0]
      _ = ‖∑ b ∈ B, ∑ b' ∈ B,
            conj (corr s v b) * conj (conj (corr s v b')) * gram s v b b'‖ := by
            rw [weighted_normSq_expand s v B (fun b => conj (corr s v b))]
      _ ≤ ∑ b ∈ B, ‖∑ b' ∈ B,
            conj (corr s v b) * conj (conj (corr s v b')) * gram s v b b'‖ :=
            norm_sum_le _ _
      _ ≤ ∑ b ∈ B, ∑ b' ∈ B,
            ‖conj (corr s v b) * conj (conj (corr s v b')) * gram s v b b'‖ :=
            Finset.sum_le_sum fun b _ => norm_sum_le _ _
      _ = ∑ b ∈ B, ∑ b' ∈ B, ‖corr s v b‖ * ‖corr s v b'‖ * ‖gram s v b b'‖ := by
            refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
            simp
    refine le_trans habs ?_
    exact bilinear_rowsum_bound B (fun b => ‖corr s v b‖) (fun b b' => ‖gram s v b b'‖) R
      (fun b b' => norm_nonneg _) (fun b b' => norm_gram_swap s v b b') hrow
  have hsq := sq_sum_corr_le_card_mul_quadratic s v B
  have hcard0 : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hTT : T ^ 2 ≤ (s.card : ℝ) * (T * R) :=
    le_trans hsq (mul_le_mul_of_nonneg_left hQ hcard0)
  rcases eq_or_lt_of_le hT0 with h0 | hpos
  · rw [← h0]; exact mul_nonneg hcard0 hR0
  · have h2 : T * T ≤ ((s.card : ℝ) * R) * T := by nlinarith [hTT]
    exact le_of_mul_le_mul_right h2 hpos

/-- **No independent spectral handle**: any operator-norm-style bound `Λ` on the Gram quadratic
form at the extremal weights (`Q ≤ Λ·Σ|corr|²`, e.g. `Λ = λ_max(G_B)`) already forces
`Σ_{b∈B}|corr b|² ≤ |s|·Λ`, i.e. `Λ ≥ r·V²/|s|`. The probe measures this SATURATED
(`|s|·λ_max/Σ|η_b|² = 1.02–1.08`): the Gram spectrum cannot be bounded above — by ANY method —
tightly enough to contradict the large values, unless that method already bounds the period
field itself (the Gram IS the field, `gram_eq_period_diff`). This is the precise sense in which
the GM matrix-cancellation step is circular for the period family. -/
theorem no_independent_spectral_handle (s : Finset α) (v : ι → α → ℂ) (B : Finset ι) (Λ : ℝ)
    (hΛ0 : 0 ≤ Λ)
    (hQ : ∑ x ∈ s, ‖∑ b ∈ B, conj (corr s v b) * v b x‖ ^ 2
      ≤ Λ * ∑ b ∈ B, ‖corr s v b‖ ^ 2) :
    ∑ b ∈ B, ‖corr s v b‖ ^ 2 ≤ (s.card : ℝ) * Λ := by
  set T : ℝ := ∑ b ∈ B, ‖corr s v b‖ ^ 2 with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcard0 : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hTT : T ^ 2 ≤ (s.card : ℝ) * (Λ * T) :=
    le_trans (sq_sum_corr_le_card_mul_quadratic s v B) (mul_le_mul_of_nonneg_left hQ hcard0)
  rcases eq_or_lt_of_le hT0 with h0 | hpos
  · rw [← h0]; exact mul_nonneg hcard0 hΛ0
  · have h2 : T * T ≤ ((s.card : ℝ) * Λ) * T := by nlinarith [hTT]
    exact le_of_mul_le_mul_right h2 hpos

/-! ## §2 The period-family instantiation: the Gram matrix IS the field -/

section Period

variable {Rg : Type*} [CommRing Rg]

/-- The (incomplete) period sum of a unimodular additive character `e` over a domain `s` at
frequency `d`: for `Rg = ZMod p`, `e = e_p`, `s = μ_n` this is the Gauss period `η_d`. -/
noncomputable def period (e : Rg → ℂ) (s : Finset Rg) (d : Rg) : ℂ := ∑ x ∈ s, e (d * x)

/-- A multiplicative-on-addition, unimodular map sends `0` to `1`. -/
theorem char_map_zero (e : Rg → ℂ) (he : ∀ y z, e (y + z) = e y * e z)
    (hnorm : ∀ y, ‖e y‖ = 1) : e 0 = 1 := by
  have hne : e 0 ≠ 0 := by
    intro h0
    have := hnorm 0
    rw [h0, norm_zero] at this
    norm_num at this
  have h : e 0 * e 0 = e 0 * 1 := by rw [mul_one, ← he, add_zero]
  exact mul_left_cancel₀ hne h

/-- For a unimodular character, `e(−y) = conj(e y)`. -/
theorem char_neg_eq_conj (e : Rg → ℂ) (he : ∀ y z, e (y + z) = e y * e z)
    (hnorm : ∀ y, ‖e y‖ = 1) (y : Rg) : e (-y) = conj (e y) := by
  have h1 : e y * e (-y) = 1 := by
    rw [← he, add_neg_cancel, char_map_zero e he hnorm]
  have h2 : conj (e y) * e y = 1 := by
    rw [Complex.conj_mul', hnorm y]
    norm_num
  calc e (-y) = (conj (e y) * e y) * e (-y) := by rw [h2, one_mul]
  _ = conj (e y) * (e y * e (-y)) := by ring
  _ = conj (e y) := by rw [h1, mul_one]

/-- The correlation of the period family against the all-ones weight is the period itself. -/
theorem corr_eq_period (e : Rg → ℂ) (s : Finset Rg) (b : Rg) :
    corr s (fun b x => e (b * x)) b = period e s b := rfl

/-- **THE TRANSFER IDENTITY (headline): the large-values matrix IS the period field at
difference frequencies.** For the period family `v_b = (e(bx))_{x∈s}`, the Guth–Maynard
large-values Gram matrix is exactly `G_{b,b'} = η_{b−b'}`. The object controlling the
extremizer geometry is the object being bounded: the transfer is self-referential by an exact
identity, not by analogy. -/
theorem gram_eq_period_diff (e : Rg → ℂ) (he : ∀ y z, e (y + z) = e y * e z)
    (hnorm : ∀ y, ‖e y‖ = 1) (s : Finset Rg) (b b' : Rg) :
    gram s (fun b x => e (b * x)) b b' = period e s (b - b') := by
  rw [gram, period]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← char_neg_eq_conj e he hnorm, ← he]
  congr 1
  ring

/-- The period at frequency `0` is the domain size (the Gram diagonal). -/
theorem period_zero (e : Rg → ℂ) (he : ∀ y z, e (y + z) = e y * e z)
    (hnorm : ∀ y, ‖e y‖ = 1) (s : Finset Rg) : period e s 0 = (s.card : ℂ) := by
  simp [period, char_map_zero e he hnorm]

/-- Trivial bound: every period value is at most the domain size in absolute value. -/
theorem norm_period_le (e : Rg → ℂ) (hnorm : ∀ y, ‖e y‖ = 1) (s : Finset Rg) (d : Rg) :
    ‖period e s d‖ ≤ (s.card : ℝ) := by
  calc ‖period e s d‖ ≤ ∑ x ∈ s, ‖e (d * x)‖ := norm_sum_le _ _
  _ = (s.card : ℝ) := by simp [hnorm]

/-- Row sums of the absolute Gram matrix of the period family: diagonal `= |s|`, off-diagonal
bounded by the field at difference frequencies. -/
theorem period_gram_rowsum_le [DecidableEq Rg] (e : Rg → ℂ)
    (he : ∀ y z, e (y + z) = e y * e z) (hnorm : ∀ y, ‖e y‖ = 1)
    (s B : Finset Rg) (M' : ℝ)
    (hoff : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ‖period e s (b - b')‖ ≤ M')
    (b : Rg) (hb : b ∈ B) :
    ∑ b' ∈ B, ‖gram s (fun b x => e (b * x)) b b'‖
      ≤ (s.card : ℝ) + ((B.card : ℝ) - 1) * M' := by
  rw [← Finset.add_sum_erase B _ hb]
  have hdiag : ‖gram s (fun b x => e (b * x)) b b‖ = (s.card : ℝ) := by
    rw [gram_eq_period_diff e he hnorm, sub_self, period_zero e he hnorm,
      Complex.norm_natCast]
  have herase : ∑ b' ∈ B.erase b, ‖gram s (fun b x => e (b * x)) b b'‖
      ≤ ((B.card : ℝ) - 1) * M' := by
    have hstep : ∑ b' ∈ B.erase b, ‖gram s (fun b x => e (b * x)) b b'‖
        ≤ (B.erase b).card • M' := by
      refine Finset.sum_le_card_nsmul _ _ _ fun b' hb' => ?_
      rw [gram_eq_period_diff e he hnorm]
      exact hoff b hb b' (Finset.mem_of_mem_erase hb')
        (Ne.symm (Finset.ne_of_mem_erase hb'))
    rw [nsmul_eq_mul, Finset.cast_card_erase_of_mem hb] at hstep
    exact hstep
  rw [hdiag]
  linarith [herase]

/-- **The `r`-uniform large-values inequality for the period family (main positive brick).**
If `|η_b| ≥ V ≥ 0` on a nonempty set `B` of `r` frequencies and the field at the (nonzero)
difference frequencies `B − B` is bounded by `M'`, then

  `r·V² ≤ n·(n + (r−1)·M')`,  `n = |s|`.

This is the exact Halász–Montgomery / Guth–Maynard base inequality for the Gauss-period sup:
the count of large values is controlled by the field at difference frequencies — and by
`gram_eq_period_diff` this control is intrinsically self-referential. -/
theorem large_values_gram_bound [DecidableEq Rg] (e : Rg → ℂ)
    (he : ∀ y z, e (y + z) = e y * e z) (hnorm : ∀ y, ‖e y‖ = 1)
    (s B : Finset Rg) (hB : B.Nonempty) (V M' : ℝ) (hV0 : 0 ≤ V) (hM'0 : 0 ≤ M')
    (hlarge : ∀ b ∈ B, V ≤ ‖period e s b‖)
    (hoff : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ‖period e s (b - b')‖ ≤ M') :
    (B.card : ℝ) * V ^ 2 ≤ (s.card : ℝ) * ((s.card : ℝ) + ((B.card : ℝ) - 1) * M') := by
  have hcard1 : (1 : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero_of_mem hB.choose_spec)
  have hR0 : 0 ≤ (s.card : ℝ) + ((B.card : ℝ) - 1) * M' :=
    add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) hM'0)
  have hm := halasz_montgomery_rowsum s (fun b x => e (b * x)) B
    ((s.card : ℝ) + ((B.card : ℝ) - 1) * M') hR0
    (fun b hb => period_gram_rowsum_le e he hnorm s B M' hoff b hb)
  have hlow : (B.card : ℝ) * V ^ 2
      ≤ ∑ b ∈ B, ‖corr s (fun b x => e (b * x)) b‖ ^ 2 := by
    have hcs := Finset.card_nsmul_le_sum B
      (fun b => ‖corr s (fun b x => e (b * x)) b‖ ^ 2) (V ^ 2)
      (fun b hb => pow_le_pow_left₀ hV0 (hlarge b hb) 2)
    rwa [nsmul_eq_mul] at hcs
  linarith [hm, hlow]

/-- The Rayleigh floor in period language: the Gram quadratic form at the extremal weights is
at least `(Σ_{b∈B}|η_b|²)²/n` — the spectral saturation pin, measured tight to 2–8%. -/
theorem period_quadratic_form_floor (e : Rg → ℂ) (s B : Finset Rg) :
    (∑ b ∈ B, ‖period e s b‖ ^ 2) ^ 2
      ≤ (s.card : ℝ) * ∑ x ∈ s, ‖∑ b ∈ B, conj (period e s b) * e (b * x)‖ ^ 2 :=
  sq_sum_corr_le_card_mul_quadratic s (fun b x => e (b * x)) B

end Period

/-! ## §3 The honest obstruction: vacuity, fixed-point degeneration, and the count-vs-sup fence

Pure ℝ-arithmetic no-go lemmas quantifying exactly where the GM/HM bootstrap dies for the
period family. Measured inputs (probe): at the extremal sets, `M' ≈ 2–3.5·√n` while
informativeness requires `M' < V²/n ≈ log(p/n)`; and the target-level set is nonempty
(3/13/26/77 cosets at n = 8/16/32/64). -/

/-- **Vacuity of the self-referential bootstrap.** If the off-diagonal field level satisfies
`M' ≥ V²/n` (measured: `M' ≈ 2–3.5·√n ≫ V²/n ≈ log(p/n)` at every tested scale) and the trivial
`M' ≤ n`, then the Halász–Montgomery inequality `r·V² ≤ n(n + (r−1)M')` holds for EVERY count
`r ≥ 1`: it constrains nothing. The Gram off-diagonal mass assumption that fails is exactly
`M' < V²/n`. -/
theorem selfref_vacuous {n V M' r : ℝ} (hn0 : 0 ≤ n) (hM'n : M' ≤ n)
    (hVM : V ^ 2 ≤ n * M') (hr : 1 ≤ r) :
    r * V ^ 2 ≤ n * (n + (r - 1) * M') := by
  have h1 : r * V ^ 2 ≤ r * (n * M') := mul_le_mul_of_nonneg_left hVM (by linarith)
  have h2 : n * M' ≤ n * n := mul_le_mul_of_nonneg_left hM'n hn0
  nlinarith [h1, h2]

/-- **Fixed-point degeneration of the bootstrap `M ≤ f(M)`.** In the fully self-referential
instantiation (`V = M' = M`: the extremizers' differences are themselves near-extremal, as
measured — value percentile 0.88–0.99), EVERY `M ∈ [0, n]` satisfies the HM inequality at every
count `r ≥ 1`. The fixed-point set of the bootstrap is the whole trivial interval: the
self-improvement collapses, and the fixed point does NOT sit at the `√(n log(p/n))` scale. -/
theorem selfref_bootstrap_all_fixed_points {n M r : ℝ} (h0 : 0 ≤ M) (hMn : M ≤ n)
    (hr : 1 ≤ r) :
    r * M ^ 2 ≤ n * (n + (r - 1) * M) :=
  selfref_vacuous (le_trans h0 hMn) hMn (by nlinarith) hr

/-- The count form of Halász–Montgomery: when informative (`V² > n·M'`), the number of
`V`-large frequencies is at most `n(n−M')/(V²−nM')`. -/
theorem hm_count_bound_of_informative {n V M' r : ℝ} (hden : n * M' < V ^ 2)
    (hhm : r * V ^ 2 ≤ n * (n + (r - 1) * M')) :
    r ≤ n * (n - M') / (V ^ 2 - n * M') := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hhm]

/-- **The count route certifies an empty level set only above the trivial level.** The HM count
cap drops below `1` (the only way a count bound can force `A_V = ∅`, hence — by the F0 fence,
`_wfH47_SelbergLargerSieveLargeValues.sup_le_iff_levelset_card_zero` — the only way it can bound
the sup) **iff `V² > n²`**, i.e. only above the trivial bound, for EVERY off-diagonal level
`M'`. -/
theorem hm_certifies_empty_iff_above_trivial {n V M' : ℝ} (hden : n * M' < V ^ 2) :
    n * (n - M') / (V ^ 2 - n * M') < 1 ↔ n ^ 2 < V ^ 2 := by
  rw [div_lt_one (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- Below the trivial level the HM count cap is `≥ 1`: it is consistent with a nonempty level
set, hence (F0) places no bound on the sup `M`. This composes the G98 route with the recorded
count-vs-sup fence: the Guth–Maynard output type (a cardinality cap on the large-value set)
cannot decide the prize inequality. -/
theorem hm_count_ge_one_below_trivial {n V M' : ℝ} (hden : n * M' < V ^ 2)
    (hVn : V ^ 2 ≤ n ^ 2) :
    1 ≤ n * (n - M') / (V ^ 2 - n * M') := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Certifying emptiness through the HM count forces `V > n`: the Gram/GM route cannot bound the
period sup below the trivial level, regardless of how strong an off-diagonal estimate `M'` is
fed to it. -/
theorem hm_empty_certificate_needs_trivial_level {n V M' : ℝ} (hn0 : 0 ≤ n) (hV0 : 0 ≤ V)
    (hden : n * M' < V ^ 2)
    (hcert : n * (n - M') / (V ^ 2 - n * M') < 1) : n < V := by
  have h2 : n ^ 2 < V ^ 2 := (hm_certifies_empty_iff_above_trivial hden).mp hcert
  nlinarith

end ProximityGap.Frontier.G98LargeValuesGramBootstrap

/-! ## Axiom audit -/

#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.gram_conj_swap
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.norm_gram_swap
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.weighted_normSq_expand
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.sq_sum_corr_le_card_mul_quadratic
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.bilinear_rowsum_bound
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.halasz_montgomery_rowsum
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.no_independent_spectral_handle
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.char_map_zero
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.char_neg_eq_conj
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.corr_eq_period
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.gram_eq_period_diff
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.period_zero
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.norm_period_le
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.period_gram_rowsum_le
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.large_values_gram_bound
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.period_quadratic_form_floor
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.selfref_vacuous
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.selfref_bootstrap_all_fixed_points
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.hm_count_bound_of_informative
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.hm_certifies_empty_iff_above_trivial
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.hm_count_ge_one_below_trivial
#print axioms ProximityGap.Frontier.G98LargeValuesGramBootstrap.hm_empty_certificate_needs_trivial_level
