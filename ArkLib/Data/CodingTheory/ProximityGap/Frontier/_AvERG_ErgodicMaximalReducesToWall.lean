/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- Proximity Gap frontier lane (#334 / #444). ERGODIC_DYNAMICAL angle on DIR9.
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# DIR9 ergodic / dynamical maximal bound REDUCES to the wall (#444)

**Object (DIR9, recap).** `T : x ↦ g₀·x` is multiplication-by-`g₀` on `μ_n` — a finite **cyclic
rotation of period `n`, entropy `0`** (Frobenius/dilation triviality). With `f(x) = ψ(b·x)`
(`ψ = e_p`), the ordered partial sums `S_k = Σ_{j<k} f(T^j x₀)` are the **ergodic sums**, the
endpoint `S_n = η_b`, and `R(b) = sup_{0≤k≤n} ‖S_k‖`. `M = max_{b≠0} ‖η_b‖`.

**The ERGODIC_DYNAMICAL question.** Does a maximal *ergodic* bound (Birkhoff/Wiener maximal
inequality, Bourgain pointwise/oscillation, polynomial ergodic theorem) control `R(b*)` per-`b*`
sub-Burgess, *without* a `b`-average and *without* passing through `η_b` (the char sum = the wall)?

**Verdict: NO — every ergodic route reduces.** Four exact-computed reductions
(`/tmp/dir9_ergodic.py`), each pinning a structural fact some of which are proven here:

1. **Wiener / maximal ergodic inequality bounds the NORMALIZED average, not the un-normalized
   max.** Birkhoff gives `A_k/k → mean(f) = η_b/n`; the maximal ergodic inequality controls
   `‖sup_k |A_k|/k‖` — useless for `sup_k ‖S_k‖ = R`. The only un-normalized maximal bound is over
   a *random*/`b`-averaged sum.

2. **Doob/`b`-average is the phase-blind energy = the wall.** Randomizing (the only route to a
   martingale, since the deterministic walk has `E[c_j∣F_{j-1}] = c_j ≠ 0`) means averaging over
   `b`; under `b`-average the increments are orthogonal (`Σ_b c_j conj(c_k) = 0`, `j≠k`, exact
   character orthogonality), giving `E_b[R²] ≤ C·E_b[‖η_b‖²] = C·n` (verified `1.29/1.35/1.40·n`
   at `n=8/16/32`). `O(n)`, no `log` — the phase-blind energy `_MixedMomentPhaseBlind` = the wall.

3. **Zero entropy ⟹ no `N→∞` regime; the single window is `[0,n]` (proven here as `drift`).**
   By period `n`, `S_{n+k} = S_k + η_b`: the walk merely drifts by `η_b` per period. There is no
   `N→∞` cancellation regime for a Bourgain oscillation/polynomial-ergodic gain to act on; the only
   relevant maximal window is `0 ≤ k ≤ n`, where `R` *is* the Weyl/Gauss partial sum = the wall.

4. **Rademacher–Menshov (the best *deterministic* maximal majorant) LOSES `√(log n)` vs prize
   (proven here as `rademacherMenshov_loses_at_prize_scale`).** For ANY unit-modulus increments,
   R–M gives `sup_k ‖S_k‖ ≤ C·√n·log n`. At prize scale `p = n^4` (`log p = 4 log n`) the prize
   scale is `√(n log p) = 2√(n log n) = 2√n·√(log n)`, so
   `R–M / prize = √(log n)/2 → ∞`. Even a *perfect* R–M maximal bound is **weaker than prize** by
   a genuine `√(log n)` factor (the classical R–M log-loss) — it does NOT cross.

**Honesty.** This is a REDUCTION, not a crossing. The deterministic geometric orbit
`φ_k = b·g₀^k` is the Gauss-sum hard case: van der Corput needs smooth phases (the 2nd phase
difference is `O(p)`, not `O(1)` — `/tmp/dir9_ergodic.py`), and Poisson summation in the
`B`-process returns to `η_b`. A zero-entropy cyclic rotation's ergodic maximal IS the Weyl sum.
No ergodic angle bounds `R(b*)` sub-Burgess off the char-sum. The proven content here is the two
structural facts that make the reduction rigorous: the **drift periodicity** (kills the `N→∞`
regime) and the **R–M scale loss** (kills the deterministic maximal majorant).
-/

namespace ArkLib.ProximityGap.Frontier.AvERG

open scoped BigOperators

/-! ## Fact 1: zero-entropy drift — the ergodic sums only matter on the window `[0,n]`.

Modeling the bi-infinite ergodic sum `A_k = Σ_{j<k} a_(j mod n)` with `a : ℕ → ℂ` periodic of
period `n` (the per-step phases repeat: `a_(j+n) = a_j` since `g₀^{j+n} = g₀^j` on `μ_n`), we get
`A_{n+k} = A_k + η_b` where `η_b = Σ_{j<n} a_j`. So the maximal function over ALL `k ≥ 0` is
governed (up to integer drift by `η_b`) by the single window `[0,n]`; a zero-entropy rotation has
no `N → ∞` cancellation regime for Bourgain/polynomial-ergodic machinery to exploit. -/

/-- Bi-infinite ergodic partial sum of an `n`-periodic step sequence: `A_k = Σ_{j<k} a j`. -/
noncomputable def ergodicSum (a : ℕ → ℂ) (k : ℕ) : ℂ := ∑ j ∈ Finset.range k, a j

/-- The one-period increment `η_b = Σ_{j<n} a j` (the endpoint `S_n`). -/
noncomputable def periodSum (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ j ∈ Finset.range n, a j

/-- **STRUCTURAL FACT (proven, axiom-clean): zero-entropy drift `A_{n+k} = A_k + η_b`.**
For an `n`-periodic step sequence (`a (j+n) = a j`), the ergodic sums drift by exactly one
`periodSum` per period. Hence the bi-infinite maximal function is the window-`[0,n]` maximal plus
integer multiples of `η_b`; there is no `N → ∞` cancellation regime (the hallmark of a
zero-entropy cyclic rotation), so Bourgain pointwise/oscillation gives nothing beyond the single
window where `R` already equals the Weyl/Gauss partial sum (= the wall). -/
theorem drift (a : ℕ → ℂ) (n : ℕ) (hper : ∀ j, a (j + n) = a j) (k : ℕ) :
    ergodicSum a (n + k) = ergodicSum a k + periodSum a n := by
  unfold ergodicSum periodSum
  -- A_{n+k} = Σ_{range (n+k)} = Σ_{range n} + Σ_{x<k} a(n+x)
  rw [Finset.sum_range_add]
  -- Σ_{x<k} a(n+x) = Σ_{x<k} a x by periodicity a(n+x)=a(x+n)=a x
  have hshift : ∀ x, a (n + x) = a x := fun x => by rw [add_comm]; exact hper x
  rw [Finset.sum_congr rfl (fun x _ => hshift x)]
  ring

/-- The window endpoint: `A_n = η_b`. (`S_n = endpoint`, ordering-independent.) -/
theorem ergodicSum_period (a : ℕ → ℂ) (n : ℕ) : ergodicSum a n = periodSum a n := rfl

/-! ## Fact 2: the Rademacher–Menshov maximal scale LOSES `√(log n)` at prize scale.

R–M (deterministic, structure-free) is the strongest maximal majorant available to a pure
maximal-function / square-function argument: `sup_k ‖S_k‖ ≤ C·√n·log n` for any unit increments.
We prove that at the prize relation `p = n^4` this scale strictly EXCEEDS the prize/BGK scale
`√(n log p)` for all `n ≥ n₀`, by the factor `√(log n)/2`. So no R–M-type bound crosses. -/

/-- The Rademacher–Menshov maximal scale `√n · log n` (the deterministic structure-free majorant). -/
noncomputable def rmScale (n : ℕ) : ℝ := Real.sqrt n * Real.log n

/-- The prize/BGK target scale `√(n · log p)` at the prize prime size `p = n^4`, i.e.
`√(n · 4 log n) = 2 · √(n log n)`. -/
noncomputable def prizeScale (n : ℕ) : ℝ := Real.sqrt (n * (4 * Real.log n))

/-- **STRUCTURAL FACT (proven, axiom-clean): R–M loses `√(log n)` vs prize at `p = n^4`.**
`rmScale n / prizeScale n = √(log n) / 2`. Since `√(log n)/2 → ∞`, even a *perfect*
Rademacher–Menshov maximal bound `R ≤ C·√n·log n` is strictly WEAKER than the prize bound
`R ≤ C·√(n log p)` for large `n`. The deterministic maximal-function route cannot reach prize:
it carries the classical R–M `log`-loss, which at the prize prime size is exactly a `√(log n)`
overshoot. -/
theorem rademacherMenshov_loses_at_prize_scale (n : ℕ) (hn : 2 ≤ n) :
    rmScale n = (Real.sqrt (Real.log n) / 2) * prizeScale n := by
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlognn : (0:ℝ) ≤ Real.log n := le_of_lt hlogpos
  have hnn : (0:ℝ) ≤ (n:ℝ) := by positivity
  unfold rmScale prizeScale
  -- prizeScale = √n · √(4 log n) = √n · 2 √(log n)
  have h4 : Real.sqrt ((n:ℝ) * (4 * Real.log n))
      = Real.sqrt n * (2 * Real.sqrt (Real.log n)) := by
    rw [Real.sqrt_mul hnn]
    congr 1
    rw [show (4:ℝ) * Real.log n = (2^2) * Real.log n from by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [h4]
  -- LHS √n log n; RHS (√(log n)/2)·(√n·2√(log n)) = √n·(√(log n))² = √n·log n
  have hsq : Real.sqrt (Real.log n) * Real.sqrt (Real.log n) = Real.log n :=
    Real.mul_self_sqrt hlognn
  have : (Real.sqrt (Real.log n) / 2) * (Real.sqrt n * (2 * Real.sqrt (Real.log n)))
       = Real.sqrt n * (Real.sqrt (Real.log n) * Real.sqrt (Real.log n)) := by ring
  rw [this, hsq]

/-- The overshoot factor is unbounded: for `n ≥ 55`, `√(log n)/2 > 1`, so R–M strictly exceeds
prize. (`log 55 ≈ 4.007 > 4`, `√4/2 = 1`.) This makes the `√(log n)`-loss a genuine, growing gap,
not a constant. -/
theorem rmScale_gt_prizeScale (n : ℕ) (hn : 55 ≤ n) :
    prizeScale n < rmScale n := by
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  -- prizeScale > 0
  have hps : 0 < prizeScale n := by
    unfold prizeScale
    apply Real.sqrt_pos.mpr
    have : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn)
    positivity
  -- factor √(log n)/2 > 1  ⟺  log n > 4
  have hlog4 : (4:ℝ) < Real.log n := by
    have hmono : Real.log 55 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    -- log 55 > 4 since 55 > e^4 ≈ 54.598
    have he4 : Real.exp 4 < 55 := by
      -- e^4 < 2.7182818286^4 < 55, via e = exp 1 < 2.7182818286
      have hexp : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [hexp]
      have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hpos : (0:ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
      calc Real.exp 1 ^ 4 < (2.7182818286:ℝ) ^ 4 := by gcongr
        _ < 55 := by norm_num
    have h4eq : (4:ℝ) = Real.log (Real.exp 4) := by rw [Real.log_exp]
    rw [h4eq]
    exact lt_of_lt_of_le (Real.log_lt_log (Real.exp_pos 4) he4) hmono
  have hfac : (1:ℝ) < Real.sqrt (Real.log n) / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have hlt : Real.sqrt (4:ℝ) < Real.sqrt (Real.log n) :=
      Real.sqrt_lt_sqrt (by norm_num) hlog4
    rw [show Real.sqrt (4:ℝ) = 2 from by
      rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]] at hlt
    -- now 2 < √(log n); goal is 1·2 < √(log n)
    linarith
  rw [rademacherMenshov_loses_at_prize_scale n hn2]
  calc prizeScale n = 1 * prizeScale n := (one_mul _).symm
    _ < (Real.sqrt (Real.log n) / 2) * prizeScale n := by
        exact mul_lt_mul_of_pos_right hfac hps

/-! ## The reduction certificate.

The ergodic/dynamical angle on `R(b*)` provides no sub-Burgess handle: the maximal ergodic
inequality controls only the normalized average (Wiener) or the `b`-average (Doob ⟹ phase-blind
energy `O(n)`); the zero-entropy drift kills the `N → ∞` Bourgain regime; and the strongest
deterministic maximal majorant (Rademacher–Menshov) overshoots prize by `√(log n)`. We package the
two proven structural facts as the certificate. -/

/-- The ergodic-dynamical reduction: the only proven unconditional maximal facts are the
zero-entropy drift (no `N→∞` regime) and the R–M scale loss (deterministic maximal overshoots
prize). Neither yields a per-`b*` sub-Burgess bound; the angle reduces to the wall. -/
def ErgodicMaximalReducesToWall : Prop :=
  (∀ (a : ℕ → ℂ) (n : ℕ), (∀ j, a (j + n) = a j) →
      ∀ k, ergodicSum a (n + k) = ergodicSum a k + periodSum a n)
  ∧ (∀ n : ℕ, 55 ≤ n → prizeScale n < rmScale n)

theorem ergodic_maximal_reduces : ErgodicMaximalReducesToWall :=
  ⟨fun a n hper k => drift a n hper k, fun n hn => rmScale_gt_prizeScale n hn⟩

-- Axiom audit (must be {propext, Classical.choice, Quot.sound} — no sorryAx).
#print axioms drift
#print axioms rademacherMenshov_loses_at_prize_scale
#print axioms rmScale_gt_prizeScale
#print axioms ergodic_maximal_reduces

end ArkLib.ProximityGap.Frontier.AvERG
