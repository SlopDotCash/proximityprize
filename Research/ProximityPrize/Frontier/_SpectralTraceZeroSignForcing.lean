/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The Cayley TRACE-ZERO (no-self-loop) identity and the sign-forcing of the Paley spectrum (#444)

ANGLE 4 (generalized-Paley spectral-moment handle). `B = max_{b≠0}‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b·x)`,
is the non-principal eigenvalue of the Cayley graph `Cay(F_p, μ_n)` (`A = Σ_{x∈μ_n} P^x`, eigenvalues
`{η_b}_{b∈F_p}`, the additive characters the eigenbasis). The prize floor `M = ‖A‖_{non-principal}`.

Every in-tree spectral brick works with the **even** power-sums `S_r = Σ_{b≠0}‖η_b‖^{2r} = tr(A^{2r}) − n^{2r}`
(`DCSubtractedMoment.sum_nonzero_moment`), i.e. with `tr(A^{2r})` for `r ≥ 1` (the second moment
`Σ_b‖η_b‖² = q·n = tr(A²)` is `SubgroupGaussSumSecondMoment`). This file lands the ONE structural
spectral invariant that the entire even-moment hierarchy is **blind** to: the **FIRST** power-sum, the
bare **trace** `tr(A) = Σ_b η_b`.

## The trace-zero identity (the graph fact `0 ∉ μ_n` = no self-loops)

> **`spectral_trace_zero`** : `Σ_{b∈F} η_b = 0`   when `0 ∉ G`.

Proof (orthogonality only, no Weil): `Σ_b η_b = Σ_b Σ_{x∈G} ψ(b·x) = Σ_{x∈G} Σ_b ψ(b·x)
= Σ_{x∈G} (q·[x=0]) = 0`, because `0 ∉ G` kills every term. This is `tr(A) = Σ_b η_b = 0`: the Cayley
graph has NO self-loops precisely because the connection set `μ_n` excludes the identity vertex `0`
(`0 ∉ μ_n` as a subset of `F_p`). This is a genuinely new structural fact: it is the FIRST eigenvalue
moment, completely independent of the energy hierarchy `S_r` (which is built from squared norms
`‖η_b‖^{2r}`, all nonnegative).

## The non-principal form and the sign-forcing consequence

Splitting off the DC term `η_0 = n` (`eta_zero`, the Perron/degree eigenvalue):

> **`sum_nonzero_eta_eq_neg_degree`** : `Σ_{b≠0} η_b = -(n : ℂ)`.

The `m = q−1` non-principal eigenvalues sum to exactly `-n`. Taking real parts:

> **`sum_nonzero_re_eq_neg_degree`** : `Σ_{b≠0} Re(η_b) = -(n : ℝ)`,

so the average non-principal eigenvalue has real part `-n/(q−1) < 0`. The decisive structural
consequence the positive-moment method cannot see:

> **`exists_nonzero_eta_re_neg`** : `∃ b ≠ 0, Re(η_b) < 0`.

GENUINE SIGN CANCELLATION is FORCED: the non-principal spectrum cannot lie in the closed right
half-plane. The even-moment hierarchy `S_r = Σ_{b≠0}‖η_b‖^{2r}` is a sum of NONNEGATIVE terms and is
invariant under `η_b ↦ -η_b` (and under any phase rotation), so it is **provably blind** to this signed
structure (`specMoment_phase_blind`). The √(log p) sup-excess that the prize must rule out is exactly an
`L^∞`/phase rare-event invisible to bulk `L²`/moment functionals (the in-tree conservation-law fence
`F0`); trace-zero is the cleanest exact witness that the signed first moment carries information the
moment ladder discards.

## A clean trace-zero LOWER bound on M (honest, weak, NOT wall-circular)

> **`M_ge_degree_div_pred`** : `(n : ℝ)/(q−1) ≤ max_{b≠0}‖η_b‖`,

from `n = ‖Σ_{b≠0} η_b‖ ≤ (q−1)·max‖η_b‖` (triangle inequality on `sum_nonzero_eta_eq_neg_degree`). This is a
`Θ(n/q) = Θ(n^{1−β})`-scale floor — far below the Parseval `√n` floor and FAR below the prize
`√(n·log p)`. It does NOT advance the upper-bound wall; it is the honest content the FIRST moment alone
supplies, recorded so the next agent knows the trace gives only an `n/q` floor (the `√n` floor needs the
SECOND moment, the prize needs depth `r ∼ log p`).

## Honesty (project §6)

POSITIVE structural brick, NOT a closure and NOT a refutation. The trace-zero identity and the
sign-forcing are exact and axiom-clean (orthogonality only). They prove a genuinely NEW spectral fact
(`tr(A)=0` ⟹ forced cancellation) that the even-moment hierarchy omits, and a weak `n/q` lower bound.
They do NOT bound `M` from above: the core `M ≤ C√(n·log p)` (the char-`p` energy saddle / BGK wall)
stays OPEN. This is the spectral first-moment companion of the in-tree second-moment
`SubgroupGaussSumSecondMoment` and the even-moment `DCSubtractedMoment` / `_CirculantTraceEnergy`
bricks. Issue #444 / #407.

## References
- `SubgroupGaussSumSecondMoment` (`tr(A²) = Σ_b‖η_b‖² = q·n`); `DCSubtractedMoment` (`tr(A^{2r}) − n^{2r}`).
- `Frontier/_PaleyCayleyEigenvalue`, `Frontier/_CirculantTraceEnergy` (the eigen-equation, `tr=energy`).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.SpectralTraceZeroSignForcing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Part 1 — the trace-zero identity (no self-loops, `tr(A) = 0`) -/

/-- **The DC (`b=0`) eigenvalue is the degree:** `η_0 = Σ_{y∈G} ψ(0) = |G|` (the Perron/principal
eigenvalue, the regular degree `n = |G|`). -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  unfold eta; simp

/-- **★ The Cayley TRACE-ZERO identity: `Σ_b η_b = 0` when `0 ∉ G`.**

`tr(A) = Σ_b η_b = Σ_b Σ_{x∈G} ψ(b·x) = Σ_{x∈G} Σ_b ψ(b·x) = Σ_{x∈G} (q·[x=0]) = 0`, because the
connection set `G = μ_n` excludes the identity vertex `0` (no self-loops). Pure additive-character
orthogonality (`AddChar.sum_mulShift`), no Weil, no open input. This is the FIRST eigenvalue moment of
the Paley graph — a structural invariant the even power-sums `S_r = Σ‖η_b‖^{2r}` cannot encode. -/
theorem spectral_trace_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (h0 : (0 : F) ∉ G) :
    ∑ b : F, eta ψ G b = 0 := by
  classical
  calc ∑ b : F, eta ψ G b
      = ∑ b : F, ∑ x ∈ G, ψ (b * x) := rfl
    _ = ∑ x ∈ G, ∑ b : F, ψ (b * x) := Finset.sum_comm
    _ = ∑ x ∈ G, ((if x = 0 then Fintype.card F else 0 : ℕ) : ℂ) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        exact AddChar.sum_mulShift x hψ
    _ = ∑ x ∈ G, (0 : ℂ) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [if_neg (by rintro rfl; exact h0 hx)]
        simp
    _ = 0 := by simp

/-! ### Part 2 — the non-principal trace and the forced sign cancellation -/

/-- **★ The non-principal eigenvalues sum to `-n`: `Σ_{b≠0} η_b = -(|G| : ℂ)`.** Splitting the
trace-zero identity at the DC term `η_0 = |G|`: `0 = Σ_b η_b = η_0 + Σ_{b≠0} η_b = n + Σ_{b≠0} η_b`, so
the `m = q−1` non-principal eigenvalues sum to exactly the negative degree `-n`. -/
theorem sum_nonzero_eta_eq_neg_degree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (h0 : (0 : F) ∉ G) :
    ∑ b ∈ univ.erase (0 : F), eta ψ G b = -(G.card : ℂ) := by
  have hsplit : ∑ b : F, eta ψ G b
      = eta ψ G 0 + ∑ b ∈ univ.erase (0 : F), eta ψ G b :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ 0)).symm
  rw [spectral_trace_zero hψ G h0, eta_zero] at hsplit
  -- 0 = (n : ℂ) + Σ_{b≠0} η_b ⟹ Σ_{b≠0} η_b = -(n : ℂ)
  linear_combination -hsplit

/-- **The real-part form: `Σ_{b≠0} Re(η_b) = -(|G| : ℝ)`.** Taking real parts of
`sum_nonzero_eta_eq_neg_degree`: the average non-principal eigenvalue has real part `-n/(q−1) < 0`. -/
theorem sum_nonzero_re_eq_neg_degree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (h0 : (0 : F) ∉ G) :
    ∑ b ∈ univ.erase (0 : F), (eta ψ G b).re = -(G.card : ℝ) := by
  have h := sum_nonzero_eta_eq_neg_degree hψ G h0
  have hre : (∑ b ∈ univ.erase (0 : F), eta ψ G b).re = (-(G.card : ℂ)).re := by rw [h]
  rw [Complex.re_sum] at hre
  simpa using hre

/-- **★ FORCED SIGN CANCELLATION: `∃ b ≠ 0, Re(η_b) < 0`.** If the smooth domain is nonempty
(`0 < |G|`), the non-principal spectrum cannot lie in the closed right half-plane: some nontrivial
eigenvalue has strictly negative real part. Else `Σ_{b≠0} Re(η_b) ≥ 0`, contradicting the trace-zero
sum `-n < 0`. The even-moment hierarchy `S_r = Σ_{b≠0}‖η_b‖^{2r}` (sums of nonnegative, phase-invariant
terms) is structurally BLIND to this — the precise sense in which the FIRST moment carries information
the moment ladder discards. -/
theorem exists_nonzero_eta_re_neg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (h0 : (0 : F) ∉ G) (hG : 0 < G.card) :
    ∃ b : F, b ≠ 0 ∧ (eta ψ G b).re < 0 := by
  classical
  by_contra h
  push Not at h
  have hge : (0 : ℝ) ≤ ∑ b ∈ univ.erase (0 : F), (eta ψ G b).re := by
    refine Finset.sum_nonneg (fun b hb => ?_)
    have hbne : b ≠ 0 := (Finset.mem_erase.mp hb).1
    exact h b hbne
  rw [sum_nonzero_re_eq_neg_degree hψ G h0] at hge
  have : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hG
  linarith

/-! ### Part 3 — the trace-zero LOWER bound on `M` (honest, weak `n/q` floor) -/

/-- **The trace-zero floor `M ≥ n/(q−1)`.** From `n = ‖Σ_{b≠0} η_b‖ ≤ Σ_{b≠0}‖η_b‖ ≤ (q−1)·max`
(triangle inequality on `sum_nonzero_eta_eq_neg_degree`): the non-principal spectral radius is at least
`n/(q−1)`. This is the honest FIRST-moment lower content — a `Θ(n^{1−β})` floor, far below the Parseval
`√n` (which needs the SECOND moment) and the prize `√(n·log p)`. Recorded so the trace route's reach is
explicit: the bare trace gives only `n/q`, NOT the wall. -/
theorem M_ge_degree_div_pred {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (h0 : (0 : F) ∉ G) (hq : (1 : ℝ) < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧ (G.card : ℝ) / ((Fintype.card F : ℝ) - 1) ≤ ‖eta ψ G b‖ := by
  classical
  set S : Finset F := univ.erase (0 : F) with hS
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : F)
    exact ⟨x, by rw [hS, Finset.mem_erase]; exact ⟨hx, Finset.mem_univ x⟩⟩
  have hcard : (S.card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Nat.cast_sub hq1]; simp
  have hq1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  -- pick the maximizer of ‖η_b‖ over S
  obtain ⟨b₀, hb₀S, hb₀max⟩ := S.exists_max_image (fun b => ‖eta ψ G b‖) hSne
  refine ⟨b₀, (Finset.mem_erase.mp hb₀S).1, ?_⟩
  -- n = ‖-(n)‖ = ‖Σ_{b≠0} η_b‖ ≤ Σ_{b≠0} ‖η_b‖ ≤ (q-1)·‖η_{b₀}‖
  have htrace : ∑ b ∈ S, eta ψ G b = -(G.card : ℂ) := sum_nonzero_eta_eq_neg_degree hψ G h0
  have hnormtrace : (G.card : ℝ) = ‖∑ b ∈ S, eta ψ G b‖ := by
    rw [htrace, norm_neg]; simp
  have htri : ‖∑ b ∈ S, eta ψ G b‖ ≤ ∑ b ∈ S, ‖eta ψ G b‖ := norm_sum_le _ _
  have hbound : ∑ b ∈ S, ‖eta ψ G b‖ ≤ (S.card : ℝ) * ‖eta ψ G b₀‖ := by
    calc ∑ b ∈ S, ‖eta ψ G b‖ ≤ ∑ _b ∈ S, ‖eta ψ G b₀‖ :=
          Finset.sum_le_sum (fun b hb => hb₀max b hb)
      _ = (S.card : ℝ) * ‖eta ψ G b₀‖ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hcard] at hbound
  -- combine: n ≤ (q-1)·‖η_{b₀}‖, so n/(q-1) ≤ ‖η_{b₀}‖
  rw [div_le_iff₀ hq1]
  calc (G.card : ℝ) = ‖∑ b ∈ S, eta ψ G b‖ := hnormtrace
    _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ := htri
    _ ≤ ((Fintype.card F : ℝ) - 1) * ‖eta ψ G b₀‖ := hbound
    _ = ‖eta ψ G b₀‖ * ((Fintype.card F : ℝ) - 1) := by ring

/-! ### Part 4 — the phase-blindness of the even-moment hierarchy (the structural punchline) -/

/-- **The even-moment hierarchy is PHASE-BLIND.** For any phase `u : F → ℂ` with `‖u b‖ = 1` (a pure
rotation of each eigenvalue, in particular sign flips `u b = -1`), the even power-sum
`Σ_{b≠0} ‖(u b)·η_b‖^{2r} = Σ_{b≠0} ‖η_b‖^{2r}` is UNCHANGED. So the entire energy ladder `S_r` is a
function of the magnitudes `{‖η_b‖}` alone, discarding all sign/phase information — exactly the signed
structure the trace-zero identity `Σ_{b≠0} η_b = -n` exhibits and `exists_nonzero_eta_re_neg` forces.
This is the structural statement of WHY a first-moment (trace) fact is independent content. -/
theorem specMoment_phase_blind (ψ : AddChar F ℂ) (G : Finset F) (u : F → ℂ)
    (hu : ∀ b, ‖u b‖ = 1) (r : ℕ) :
    ∑ b ∈ univ.erase (0 : F), ‖u b * eta ψ G b‖ ^ (2 * r)
      = ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) := by
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [norm_mul, hu b, one_mul]

end ProximityGap.Frontier.SpectralTraceZeroSignForcing

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.SpectralTraceZeroSignForcing.spectral_trace_zero
#print axioms ProximityGap.Frontier.SpectralTraceZeroSignForcing.sum_nonzero_eta_eq_neg_degree
#print axioms ProximityGap.Frontier.SpectralTraceZeroSignForcing.sum_nonzero_re_eq_neg_degree
#print axioms ProximityGap.Frontier.SpectralTraceZeroSignForcing.exists_nonzero_eta_re_neg
#print axioms ProximityGap.Frontier.SpectralTraceZeroSignForcing.M_ge_degree_div_pred
#print axioms ProximityGap.Frontier.SpectralTraceZeroSignForcing.specMoment_phase_blind
