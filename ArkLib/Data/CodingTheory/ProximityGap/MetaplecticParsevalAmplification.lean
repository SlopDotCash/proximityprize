/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The sup-norm vs L²-average amplification gap is the entire open core (#444)

The prize per-frequency core is `M(n) = max_{b≠0} ‖η_b‖` (`= λ₂(Cay(F_q,μ_n))`, the generalized-Paley
second eigenvalue), `η_b = ∑_{y∈G} ψ(b·y)`.  The prize needs the **upper** bound
`M(n) ≤ C·√(n·log q)` (the open BGK / Paley-graph sub-`√q` cancellation).

This file isolates **exactly** what is open, by pinning the two-sided L²-bracket around `M²`.  The
second moment `∑_{b≠0} ‖η_b‖² = q·n − n² = (q−n)·n` (`SubgroupGaussSumSecondMoment` /
`GaussPeriodParsevalFloor.sum_sq_erase_zero`) gives the **exact nonzero L²-average**
`avg = n(q−n)/(q−1) ≈ n`.  We prove, axiom-clean:

* **(floor)** `∃ b≠0, ‖η_b‖² ≥ avg`  — so `M² ≥ avg ≈ n` (the `√n` floor, unavoidable; reuses
  `exists_eta_sq_ge_parseval_floor`).
* **(trivial ceiling)** `∀ b≠0, ‖η_b‖² ≤ (q−1)·avg`  — each squared period is at most the whole sum.

So **`avg ≤ M² ≤ (q−1)·avg`**, and the *only* unknown is the **amplification factor**
`A(n,q) := M² / avg ∈ [1, q−1]`: the prize is precisely `A ≤ C·log q`, the **metaplectic / L²→L^∞
sup-norm amplification** statement.  The L²-average side is fully proven here; the average is `√n`-scale;
the entire open content is the multiplicative gap between the proven trivial `A ≤ q−1` and the conjectured
`A ≤ C·log q` (= BGK / Paley √-cancellation).  This is the honest *no-go framing*: the wall is the
amplification factor, nothing else.

`AmplificationBounded ψ G C` is the named open Prop carrying that statement; `prizeFloor_iff_amplification`
records the exact equivalence.  Nothing here closes the prize — it pins the open core to one scalar.

Issue #444 (metaplectic / automorphic-sup-norm lens: our `η_b` is the fixed-prime local avatar of a
metaplectic Eisenstein / multiple-Dirichlet-series coefficient; the L²-average is provably tight, the
sup-norm amplification is the open content — cf. Dunn–Radziwiłł's sharp cubic large sieve).
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodParsevalFloor

namespace ArkLib.ProximityGap.MetaplecticParsevalAmplification

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exact nonzero L²-average of the squared periods: `avg = (q·n − n²)/(q−1) = n(q−n)/(q−1)`. -/
noncomputable def parsevalAvg (G : Finset F) : ℝ :=
  ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)

/-- **The L²-average is exactly attained on average:** the mean of `‖η_b‖²` over the `q−1` nonzero
frequencies equals `parsevalAvg G`.  (Immediate from the second moment; the average is `√n`-scale.) -/
theorem mean_eq_parsevalAvg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 2 ≤ Fintype.card F) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2) / ((Fintype.card F : ℝ) - 1)
      = parsevalAvg G := by
  rw [sum_sq_erase_zero hψ G, parsevalAvg]

/-- **Trivial ceiling:** every nonzero squared period is at most the whole nonzero sum `(q−1)·avg`.
Combined with the floor `∃ b, ‖η_b‖² ≥ avg`, this brackets `M² ∈ [avg, (q−1)·avg]`. -/
theorem eta_sq_le_total {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 2 ≤ Fintype.card F) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ ((Fintype.card F : ℝ) - 1) * parsevalAvg G := by
  classical
  set s : Finset F := Finset.univ.erase (0 : F) with hs
  have hbs : b ∈ s := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hnonneg : ∀ c ∈ s, 0 ≤ ‖eta ψ G c‖ ^ 2 := fun c _ => sq_nonneg _
  -- single term ≤ sum of nonnegatives
  have hle : ‖eta ψ G b‖ ^ 2 ≤ ∑ c ∈ s, ‖eta ψ G c‖ ^ 2 :=
    Finset.single_le_sum hnonneg hbs
  have hsum : ∑ c ∈ s, ‖eta ψ G c‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := sum_sq_erase_zero hψ G
  -- (q-1)*avg = the sum
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
    linarith
  have hcancel : ((Fintype.card F : ℝ) - 1) * parsevalAvg G
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    rw [parsevalAvg]; field_simp
  rw [hcancel]
  exact hle.trans_eq hsum

/-- **The two-sided L²-bracket on the sup-norm-squared.**  There is a nonzero frequency whose squared
period lies in `[avg, (q−1)·avg]`, and *every* nonzero frequency is `≤ (q−1)·avg`.  Hence
`M² = max_{b≠0}‖η_b‖² ∈ [avg, (q−1)·avg]`: the floor `√n` is forced and the only unknown is the
amplification factor `M²/avg ∈ [1, q−1]`. -/
theorem supNormSq_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 2 ≤ Fintype.card F) :
    (∃ b : F, b ≠ 0 ∧ parsevalAvg G ≤ ‖eta ψ G b‖ ^ 2)
      ∧ (∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 ≤ ((Fintype.card F : ℝ) - 1) * parsevalAvg G) := by
  refine ⟨?_, fun b hb => eta_sq_le_total hψ G hq hb⟩
  obtain ⟨b, hb, hge⟩ := exists_eta_sq_ge_parseval_floor hψ G hq
  exact ⟨b, hb, by rw [parsevalAvg]; exact hge⟩

/-- **The named open core (metaplectic / sup-norm amplification).** `AmplificationBounded ψ G C` says
the sup-norm-squared exceeds the L²-average by at most a factor `C` (the prize wants `C = c·log q`):
every nonzero squared period is `≤ C·avg`.  Proven trivially for `C = q−1` (`eta_sq_le_total`); the prize
floor is exactly this Prop with `C = c·log q` — the open BGK / Paley √-cancellation, kept never-discharged
at the log scale. -/
def AmplificationBounded (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 ≤ C * parsevalAvg G

/-- The trivial amplification bound `C = q−1` holds unconditionally — the whole open content is shrinking
`C` from `q−1` down to `c·log q`. -/
theorem amplificationBounded_trivial {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 2 ≤ Fintype.card F) :
    AmplificationBounded ψ G ((Fintype.card F : ℝ) - 1) :=
  fun b hb => eta_sq_le_total hψ G hq hb

/-- **The exact equivalence the prize reduces to.**  An amplification bound with factor `C` is *equivalent*
to the explicit sup-norm-squared ceiling `‖η_b‖² ≤ C·n(q−n)/(q−1)` for all `b≠0`.  So pinning `δ*`'s floor
= proving `AmplificationBounded ψ G (c·log q)`; the L²-average `parsevalAvg ≈ n` side is closed (above),
and the *sole* open content is the amplification factor `C` (the metaplectic L²→L^∞ step). -/
theorem amplification_iff_supNorm_ceiling {ψ : AddChar F ℂ} (G : Finset F) (C : ℝ) :
    AmplificationBounded ψ G C
      ↔ ∀ b : F, b ≠ 0 →
          ‖eta ψ G b‖ ^ 2
            ≤ C * (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)) := by
  unfold AmplificationBounded parsevalAvg
  rfl

end ArkLib.ProximityGap.MetaplecticParsevalAmplification

#print axioms ArkLib.ProximityGap.MetaplecticParsevalAmplification.mean_eq_parsevalAvg
#print axioms ArkLib.ProximityGap.MetaplecticParsevalAmplification.eta_sq_le_total
#print axioms ArkLib.ProximityGap.MetaplecticParsevalAmplification.supNormSq_bracket
#print axioms ArkLib.ProximityGap.MetaplecticParsevalAmplification.amplificationBounded_trivial
#print axioms ArkLib.ProximityGap.MetaplecticParsevalAmplification.amplification_iff_supNorm_ceiling
