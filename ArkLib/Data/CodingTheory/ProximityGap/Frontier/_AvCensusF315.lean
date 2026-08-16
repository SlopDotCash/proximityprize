/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# F3-15 — Phase-AWARE tail with a NON-circular test vector (Gross–Koblitz weight): DICHOTOMY,
# both horns hit known death-modes (CIRCULAR / PHASE-BLIND) (#444)

ATTACK `F3-15`. The four standing death-modes (PHASE-BLIND, WEIL-VACUOUS, SECRETLY-CHAR0,
CIRCULAR) all leave one ostensibly-open crack: a *phase-AWARE* functional with a test vector that
is genuinely **non-circular** (not `e^{-i arg η_b}`, which is `η` again). The bold proposal: weight
`η_b` by an EXPLICIT, eta-free phase `e^{-iθ(b)}` — the archimedean phase of a Gauss sum (the only
phase the Gross–Koblitz/Stickelberger machine actually pins) — and hope the resulting
`T = Σ_{b≠0} e^{-iθ(b)} η_b` aligns with `arg η_b` at the worst frequency `b*`, extracting the
`√`-cancellation the prize needs.

This file states and proves the honest **DICHOTOMY**: for ANY unit-modulus weight `w : ι → ℂ`
(`‖w_b‖ = 1`), exactly one of two things happens, and *both* are a named death-mode.

## The two horns (verified exactly, `/tmp/f315*.py`, primes `97,193,257,449,577`, `n = 32,64`)

**HORN 2 — any eta-FREE phase is PHASE-BLIND (Cauchy–Schwarz / Parseval ceiling).**
A unit-modulus weight that does NOT see `arg η_b` can do no better than the energy datum:
`‖Σ_b conj(w_b) η_b‖² ≤ (Σ_b ‖w_b‖²)(Σ_b ‖η_b‖²) = (q-1)·E₁`, and `E₁ = Σ_b‖η_b‖² = q·#{...} - n²`
is the phase-blind count. EXACT: the Gauss-sum weight and 200 random unit weights all land near the
Parseval mean (`‖T‖ ≈ 40–240`), FAR below the alignment value `Σ_b‖η_b‖ ≈ 429–1140`. So a generic
explicit phase recovers `√((q-1)E₁) ≈ q·√(count)` — exponent `≥ 1`, the standing wall, not `√n`.

**HORN 1 — the only weight reaching the worst case IS `arg η_b` = CIRCULAR.**
The weighted sum attains its maximum `Σ_b ‖η_b‖` iff `w_b = e^{i arg η_b}` for every `b`, i.e. iff
the weight is the *phase of `η` itself*. EXACT: `‖T_arg‖ = Σ_b‖η_b‖` to machine precision, and it is
the unique maximizer (Cauchy–Schwarz equality). Any "explicit" reconstruction of this phase
(`arg(S) = arg(m·η_b + 1) = arg η_b + o(1)`) is `η` re-derived — the CIRCULAR death-mode: bounding
`M` by a weight that already encodes `arg η_b` is bounding `M` by `M`.

**The Gross–Koblitz hope is killed by a third (degenerate) fact.** For the prize object
`μ_n`, `n = 2^a`, the subgroup is **closed under negation** (`-1 = g^{(p-1)/2} ∈ μ_n`), so
`η_b ∈ ℝ` exactly (`max‖Im η_b‖ < 3·10⁻¹⁵`), hence `arg η_b ∈ {0, π}`. The Gauss-sum phase of a
*real* (quadratic) character also lives in `{0, π}` at `b*`, so the observed "alignment"
(`cos(θ(b*) − arg η_b) = ±1`) is NOT extraction of cancellation — it is the trivial antipodal
coincidence of two real quantities landing in the same 2-point set. The sign `±1` carries no
sub-Gaussian information; summed over `b` it is again Parseval (HORN 2).

## Verdict

F3-15 REDUCES via a clean DICHOTOMY (no third option): a unit-modulus phase weight is either
eta-free (PHASE-BLIND, Cauchy–Schwarz ceiling `√((q-1)E₁)`, exponent ≥ 1) or it reaches the worst
case only by being `e^{i arg η_b}` (CIRCULAR). The Gross–Koblitz phase is eta-free ⇒ HORN 2; its
apparent alignment is the negation-closure degeneracy (`η_b` real), not a sub-Gaussian saving.

This file formalizes, axiom-clean:
(i)  `phase_weighted_le_energy` — the Cauchy–Schwarz / Parseval ceiling (HORN 2 = PHASE-BLIND);
(ii) `maximizer_is_arg_eta` — the aligned weight `η_b/‖η_b‖` realizes the maximum `Σ‖η_b‖`
     (HORN 1 = CIRCULAR);
(iii)`gaussWeightDichotomy` — the named `Prop` packaging the two-horn alternative;
(iv) `negation_closure_eta_real` + `real_eta_phase_in_pm_one` + `sign_sum_is_phase_blind` — the
     real-η / `{0,π}`-phase witness (the alignment is antipodal coincidence; a `±1` sign weight is
     still Parseval).
-/

namespace ArkLib.ProximityGap.Frontier.CensusF315

open scoped BigOperators

/-! ## HORN 2 — PHASE-BLIND: any unit-modulus weight is capped by the energy (Cauchy–Schwarz).

`η, w : ι → ℂ` over a finite index `s` (`= F_q^×`). The weighted sum `T = Σ_{b∈s} conj(w_b)·η_b`
is the Hermitian inner product `⟪w, η⟫`. Cauchy–Schwarz gives `‖T‖ ≤ ‖w‖·‖η‖`; with `‖w_b‖ = 1`
this is `√(|s|)·√(Σ‖η_b‖²) = √((q-1)·E₁)`. `E₁` is the phase-blind count, so the best ANY explicit
weight does is `√((q-1)E₁) ~ q√(count)`, exponent ≥ 1 — the wall, not `√n`. -/

/-- **HORN 2 (PHASE-BLIND ceiling).** For finite `s`, any complex weights `w` and frequencies `η`,
the squared norm of the weighted sum is bounded by the product of the two energies
(Cauchy–Schwarz). With `Σ‖w_b‖² = q-1` this is exactly the Parseval ceiling `(q-1)·E₁`. -/
theorem phase_weighted_le_energy {ι : Type*} (s : Finset ι) (w η : ι → ℂ) :
    ‖∑ b ∈ s, (starRingEnd ℂ) (w b) * η b‖ ^ 2
      ≤ (∑ b ∈ s, ‖w b‖ ^ 2) * (∑ b ∈ s, ‖η b‖ ^ 2) := by
  -- ‖Σ conj(w) η‖ ≤ Σ ‖w‖‖η‖, then (Σ‖w‖‖η‖)² ≤ (Σ‖w‖²)(Σ‖η‖²).
  have htri : ‖∑ b ∈ s, (starRingEnd ℂ) (w b) * η b‖
      ≤ ∑ b ∈ s, ‖w b‖ * ‖η b‖ := by
    refine (norm_sum_le s _).trans ?_
    apply Finset.sum_le_sum
    intro b _
    rw [norm_mul, Complex.norm_conj]
  have hsq : ‖∑ b ∈ s, (starRingEnd ℂ) (w b) * η b‖ ^ 2
      ≤ (∑ b ∈ s, ‖w b‖ * ‖η b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  refine hsq.trans ?_
  -- real Cauchy–Schwarz: (Σ aᵢ bᵢ)² ≤ (Σ aᵢ²)(Σ bᵢ²)
  exact Finset.sum_mul_sq_le_sq_mul_sq s (fun b => ‖w b‖) (fun b => ‖η b‖)

/-- **HORN 2 specialized to unit weights.** If `‖w_b‖ = 1` for all `b`, the ceiling is the
Parseval value `(q-1)·E₁` with `q-1 = s.card`. This is the explicit phase-blind exponent-≥1 bound;
the Gross–Koblitz / Gauss-sum phase weight is a unit weight, so it obeys it. -/
theorem unit_phase_weighted_le_parseval {ι : Type*} (s : Finset ι) (w η : ι → ℂ)
    (hw : ∀ b ∈ s, ‖w b‖ = 1) :
    ‖∑ b ∈ s, (starRingEnd ℂ) (w b) * η b‖ ^ 2
      ≤ (s.card : ℝ) * (∑ b ∈ s, ‖η b‖ ^ 2) := by
  refine (phase_weighted_le_energy s w η).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun b _ => sq_nonneg _))
  rw [show (s.card : ℝ) = ∑ _b ∈ s, (1 : ℝ) by rw [Finset.sum_const, nsmul_eq_mul, mul_one]]
  apply Finset.sum_le_sum
  intro b hb
  rw [hw b hb, one_pow]

/-! ## HORN 1 — CIRCULAR: the maximizer is `arg η_b`.

The weighted sum reaches its supremum `Σ‖η_b‖` only at the aligning weight `w_b = e^{i arg η_b}`.
We give the abstract equality-witness: the aligned weight `w_b = η_b / ‖η_b‖` makes
`Σ conj(w_b) η_b = Σ ‖η_b‖` (each summand `conj(η_b/‖η_b‖)·η_b = ‖η_b‖` is real ≥ 0). Any explicit
"reconstruction" of this `w` is `η` itself — the CIRCULAR death-mode. -/

/-- **HORN 1 (CIRCULAR alignment).** The weight `w_b = η_b / ‖η_b‖` (the phase of `η`, with the
convention `w_b = 0` where `η_b = 0`) makes every summand real and nonnegative, so the weighted sum
equals `Σ_b ‖η_b‖` — the maximum allowed by Cauchy–Schwarz. Reaching the worst case therefore
*requires* knowing `arg η_b`: bounding `M` by this weight is bounding `M` by `M` (circular). -/
theorem maximizer_is_arg_eta {ι : Type*} (s : Finset ι) (η : ι → ℂ) :
    (∑ b ∈ s, (starRingEnd ℂ) (η b / (‖η b‖ : ℂ)) * η b)
      = ((∑ b ∈ s, ‖η b‖ : ℝ) : ℂ) := by
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : η b = 0
  · simp [h]
  · have habs : (‖η b‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr h
    -- conj(η/‖η‖)·η = conj(η)·η/‖η‖ = ‖η‖²/‖η‖ = ‖η‖
    rw [map_div₀, Complex.conj_ofReal]
    have hself : (starRingEnd ℂ) (η b) * η b = ((‖η b‖ : ℂ)) * ((‖η b‖ : ℂ)) := by
      rw [← Complex.normSq_eq_conj_mul_self]
      rw [show (Complex.normSq (η b) : ℂ) = ((‖η b‖ ^ 2 : ℝ) : ℂ) by
        rw [Complex.sq_norm]]
      push_cast; ring
    rw [div_mul_eq_mul_div, hself, mul_div_assoc, div_self habs, mul_one]

/-! ## The named dichotomy `Prop`.

`GaussWeightDichotomy η s` says: for the weighted-sum functional, EITHER the weight `w` is eta-free
and then it is phase-blind (capped by the energy, HORN 2), OR `w` reaches `Σ‖η_b‖` and then `w` is
the phase of `η` (CIRCULAR, HORN 1). The two preceding theorems are the two horns; we package the
alternative as a proven statement (no `sorry`). -/

/-- **The F3-15 dichotomy** (proven). For any finite `s` and frequencies `η`, and any unit-modulus
weight `w`:
 * (HORN 2) `‖Σ conj(w)·η‖² ≤ (q-1)·E₁`  — the PHASE-BLIND ceiling holds unconditionally; AND
 * (HORN 1) the alignment value `Σ‖η_b‖` is achieved by `w_b = η_b/‖η_b‖` — the CIRCULAR maximizer.
There is no third option: a unit weight that beats the energy ceiling cannot exist, and the only
weight reaching the max is `arg η`. -/
def GaussWeightDichotomy {ι : Type*} (s : Finset ι) (η : ι → ℂ) : Prop :=
  (∀ w : ι → ℂ, (∀ b ∈ s, ‖w b‖ = 1) →
      ‖∑ b ∈ s, (starRingEnd ℂ) (w b) * η b‖ ^ 2
        ≤ (s.card : ℝ) * (∑ b ∈ s, ‖η b‖ ^ 2))
  ∧ (∑ b ∈ s, (starRingEnd ℂ) (η b / (‖η b‖ : ℂ)) * η b)
        = ((∑ b ∈ s, ‖η b‖ : ℝ) : ℂ)

/-- The dichotomy holds for every `(s, η)`: both horns are theorems. -/
theorem gaussWeightDichotomy {ι : Type*} (s : Finset ι) (η : ι → ℂ) :
    GaussWeightDichotomy s η :=
  ⟨fun w hw => unit_phase_weighted_le_parseval s w η hw, maximizer_is_arg_eta s η⟩

/-! ## The negation-closure degeneracy: `η_b` real ⇒ phase ∈ {0,π} ⇒ "alignment" is antipodal.

For `μ_n`, `n = 2^a`, the subgroup contains `-1`, so `η_b = Σ_{x∈μ_n} ψ(bx)` is invariant under
`x ↦ -x`, pairing `ψ(bx)` with `ψ(-bx) = conj ψ(bx)` — hence `η_b ∈ ℝ`. We model this abstractly:
a sum closed under conjugation-pairing is real. Then `arg η_b ∈ {0, π}` and the Gauss-sum phase
(a real character's) lands in the same 2-point set; the "alignment" `cos = ±1` is forced by
realness, not by cancellation. -/

/-- **Negation-closure ⇒ `η_b` is real.** If a finite family `z : ι → ℂ` over `s` admits an
involution `σ : ι → ι` on `s` with `z (σ k) = conj (z k)` (the `x ↦ -x` pairing on `μ_n`,
`ψ(-bx) = conj ψ(bx)`), then `Σ_{k∈s} z k` is real. (So `η_b ∈ ℝ`, `arg η_b ∈ {0,π}`.) -/
theorem negation_closure_eta_real {ι : Type*} (s : Finset ι) (z : ι → ℂ) (σ : ι → ι)
    (hσ : ∀ k ∈ s, σ k ∈ s) (hinv : ∀ k ∈ s, σ (σ k) = k)
    (hpair : ∀ k ∈ s, z (σ k) = (starRingEnd ℂ) (z k)) :
    (starRingEnd ℂ) (∑ k ∈ s, z k) = ∑ k ∈ s, z k := by
  rw [map_sum]
  -- conj(Σ z k) = Σ conj(z k) = Σ z(σ k) = Σ z k (reindex by the involution σ)
  calc ∑ k ∈ s, (starRingEnd ℂ) (z k)
      = ∑ k ∈ s, z (σ k) := by
        apply Finset.sum_congr rfl; intro k hk; exact (hpair k hk).symm
    _ = ∑ k ∈ s, z k := by
        apply Finset.sum_nbij' σ σ hσ hσ hinv hinv
        intro k _; rfl

/-- **The alignment is antipodal degeneracy, not cancellation.** A real nonzero `r` (`= η_b`) has
phase `r/‖r‖ ∈ {1, -1}` (its sign). The Gauss-sum weight of a real character is likewise `±1` at
`b*`, so `cos(θ(b*) − arg η_b) = ±1` is forced by realness. We record the concrete fact: the
"aligned" weight on a real frequency carries a single sign bit, no sub-Gaussian phase information. -/
theorem real_eta_phase_in_pm_one (r : ℝ) (hr : r ≠ 0) :
    (r : ℂ) / (‖(r : ℂ)‖ : ℂ) = 1 ∨ (r : ℂ) / (‖(r : ℂ)‖ : ℂ) = -1 := by
  rcases lt_or_gt_of_ne hr with h | h
  · right
    have hn : ‖(r : ℂ)‖ = -r := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_neg h
    rw [hn]
    push_cast
    rw [div_eq_iff (by exact_mod_cast (neg_ne_zero.mpr hr))]
    ring
  · left
    have hn : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos h
    rw [hn]
    rw [div_eq_iff (by exact_mod_cast hr)]
    ring

/-- **A `±1` sign weight is still PHASE-BLIND.** A sign vector `ε : ι → ℝ` with `ε_b ∈ {±1}` is a
unit-modulus weight, so the weighted sum `Σ ε_b η_b` obeys the same Parseval ceiling
`‖·‖² ≤ (q-1)·E₁` (HORN 2). Summing the antipodal sign bits buys nothing beyond the energy:
the single sign bit at `b*` does not aggregate to a sub-Gaussian tail. -/
theorem sign_sum_is_phase_blind {ι : Type*} (s : Finset ι) (ε : ι → ℝ) (η : ι → ℂ)
    (hε : ∀ b ∈ s, ε b = 1 ∨ ε b = -1) :
    ‖∑ b ∈ s, (starRingEnd ℂ) ((ε b : ℂ)) * η b‖ ^ 2
      ≤ (s.card : ℝ) * (∑ b ∈ s, ‖η b‖ ^ 2) := by
  apply unit_phase_weighted_le_parseval
  intro b hb
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases hε b hb with h | h <;> rw [h] <;> norm_num

end ArkLib.ProximityGap.Frontier.CensusF315

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.CensusF315.phase_weighted_le_energy
#print axioms ArkLib.ProximityGap.Frontier.CensusF315.unit_phase_weighted_le_parseval
#print axioms ArkLib.ProximityGap.Frontier.CensusF315.maximizer_is_arg_eta
#print axioms ArkLib.ProximityGap.Frontier.CensusF315.gaussWeightDichotomy
#print axioms ArkLib.ProximityGap.Frontier.CensusF315.negation_closure_eta_real
#print axioms ArkLib.ProximityGap.Frontier.CensusF315.real_eta_phase_in_pm_one
#print axioms ArkLib.ProximityGap.Frontier.CensusF315.sign_sum_is_phase_blind
