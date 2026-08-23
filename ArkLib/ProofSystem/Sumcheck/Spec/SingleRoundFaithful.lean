/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# The single-round sum-check **round-polynomial faithfulness** identity (`hRoundFaithful`, issue #13)

`Sumcheck.Spec.SingleRound.coh_of` (`SimpleRoundCoherent.lean`) reduces the whole per-round
`LiftContextCoherent` routing coherence `(★)` — the last structural residual of issue #13's
LogUp Protocol 2 keystone chain — to one genuinely-deep, value-level (monad-free) residual:

  `hRoundFaithful` : for round `i`, outer round statement `os` and honest outer oracles `oos`, the
  `|D|^(n-1)`-fold fold of the *outer multivariate* oracle polynomial `(oos ()).1` over the
  boolean/domain subcube at `sumPoint i pt os y` equals the *inner round univariate* oracle answer
  `OracleInterface.answer (((sumcheckOracleLens …).toLens.proj (os, oos)).2 ()) pt`.

This file **discharges the mechanical layers** of that identity and **isolates its one genuinely
combinatorial residual** as the single explicit named hypothesis `hCubeFiber` (no `sorry`/`admit`):

* The fold collapses to a `Finset.sum` via `foldl_add_eq_sum` (the same brick used by
  `SimpleRoundCoherent.simOStmt_run_simOracle`).
* The inner round univariate oracle answer is, definitionally, `Polynomial.eval pt` of the round
  polynomial `oStmtLens.toFunA`. In the genuine `n = n' + 1` round shape, that round polynomial is
  `∑ x ∈ (univ.map D) ^ᶠ (n' - i), poly ⸨X ⦃i⦄, challenges, x⸩`, so by `Polynomial.eval_finset_sum`
  and the `finSuccEquivNth` partial-evaluation bridge `eval_eq_eval_mv_eval_finSuccEquivNth`, its
  evaluation at `pt` equals
  `∑ x ∈ (univ.map D) ^ᶠ (n' - i), eval (Fin.insertNth i pt (Fin.append challenges x ∘ Fin.cast _)) poly`.

The **only** content not discharged here is the equality of the two cube summations — the
`|D|^(n-1)`-fold `sumPoint` fold over `Fin (n-1) → R` versus the `|D|^(n'-i)`-fold round-polynomial
sum over `Fin (n'-i) → R` (the fiber/coordinate-bookkeeping matching prior `challenges` against the
dummy summation slots `k < i` of `sumPoint`). It is carried as the explicit named hypothesis
`hCubeFiber`, exactly mirroring how LogUp carries `logupSumcheckPolynomial_finalEval` and Spartan
carries `zeroCheckEval_simOracle`. The main theorem `roundFaithful_of_cubeFiber` then produces the
`hRoundFaithful` shape consumed verbatim by `SimpleRoundCoherent.coh_of`, and
`coh_of_cubeFiber` packages the resulting `∀ i` coherence.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec Finset Polynomial MvPolynomial

set_option linter.unusedSectionVars false

namespace Sumcheck.Spec.SingleRound

noncomputable section

variable {R : Type} [CommSemiring R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [DecidableEq R] [SampleableType R]

/-- A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
(Local copy of `SimpleRoundCoherent.foldl_add_eq_sum`, restated to avoid importing the coherence
module.) -/
private theorem foldl_add_eq_sum {S : Type} [AddCommMonoid S] {β : Type} (g : β → S) :
    ∀ (l : List β) (acc : S),
      l.foldl (fun a y => a + g y) acc = acc + (l.map g).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons y ys ih =>
      intro acc
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]; abel

/-- **The fold collapses to a finite sum.** The `|D|^(n-1)`-fold left fold over the domain subcube,
accumulating `acc + (oos ()).1.eval (sumPoint i pt os y)`, equals the `Finset.sum` over the subcube
of the same summand. Purely structural (`foldl_add_eq_sum` + `Finset.sum_to_list`). -/
theorem foldl_sumPoint_eq_finsetSum (i : Fin n) (os : StatementRound R n i.castSucc)
    (oos : ∀ i, OracleStatement R n deg i) (pt : R) :
    (((univ.map D) ^ᶠ (n - 1 - i)).toList).foldl
        (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y)) (0 : R)
      = ∑ y ∈ (univ.map D) ^ᶠ (n - 1 - i), (oos ()).1.eval (sumPoint R n i pt os y) := by
  rw [foldl_add_eq_sum (fun y => (oos ()).1.eval (sumPoint R n i pt os y)), zero_add]
  rw [Finset.sum_map_toList]

/-- **The inner round univariate oracle answer is `Polynomial.eval pt` of the round polynomial.**
`OracleInterface.answer` on the bounded univariate type `R⦃≤ deg⦄[X]` (instance
`instPolynomialDegreeLE`) is exactly evaluation of the underlying polynomial. So the right-hand side
of `hRoundFaithful` is `Polynomial.eval pt` of the second (oracle) component of `oStmtLens.toFunA`
applied to `(os, oos)`. This holds definitionally. -/
theorem answer_proj_eq_eval (i : Fin n) (os : StatementRound R n i.castSucc)
    (oos : ∀ i, OracleStatement R n deg i) (pt : R) :
    OracleInterface.answer
        (((sumcheckOracleLens R n deg D oSpec i).toLens.proj (os, oos)).2 ()) pt
      = Polynomial.eval pt
          ((((oStmtLens R n deg D i).toFunA (os, oos)).2 ()).val) := rfl

/-- **The round-polynomial evaluation as a survivor-cube sum (genuine `n = n' + 1` round).**

For a real round (`n = n' + 1`), the inner round univariate oracle answer at `pt` unfolds, via the
`finSuccEquivNth` partial-evaluation bridge `eval_eq_eval_mv_eval_finSuccEquivNth` and
`Polynomial.eval_finset_sum`, to the survivor-cube sum

  `∑ x ∈ (univ.map D) ^ᶠ (n' - i),
      eval (Fin.insertNth i pt (Fin.append os.challenges x ∘ Fin.cast _)) (oos ()).val`.

This is the canonical "evaluating the round polynomial at the round challenge equals summing the
multivariate polynomial over the remaining cube with the round coordinate fixed to the challenge"
identity (the value-level core of the sum-check round reduction). -/
theorem answer_proj_eval_succ {n' : ℕ} (i : Fin (n' + 1))
    (os : StatementRound R (n' + 1) i.castSucc)
    (oos : ∀ i, OracleStatement R (n' + 1) deg i) (pt : R) :
    OracleInterface.answer
        (((sumcheckOracleLens R (n' + 1) deg D oSpec i).toLens.proj (os, oos)).2 ()) pt
      = ∑ x ∈ (univ.map D) ^ᶠ (n' - i),
          MvPolynomial.eval
            (Fin.insertNth i pt (Fin.append os.challenges x ∘ Fin.cast (by simp; omega)))
            (oos ()).val := by
  rw [answer_proj_eq_eval]
  -- `oStmtLens.toFunA`'s oracle component in the `n' + 1` branch is the survivor-sum round poly.
  show Polynomial.eval pt
      (∑ x ∈ (univ.map D) ^ᶠ (n' - i),
        (oos ()).val ⸨X ⦃i⦄, os.challenges, x⸩'(by simp; omega)) = _
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  -- Each summand is `Polynomial.eval pt (Polynomial.map (eval _) (finSuccEquivNth _ i poly))`,
  -- which by the bridge lemma is the multivariate evaluation at the `insertNth` point.
  rw [← eval_eq_eval_mv_eval_finSuccEquivNth]

/-- **The single named combinatorial residual.** The `|D|^(n-1)`-fold `sumPoint` sum over
`Fin (n-1) → R` equals the round-polynomial survivor-cube sum over `Fin (n'-i) → R` with the round
coordinate fixed to `pt`. This is the genuine coordinate / fiber bookkeeping: `sumPoint` reads the
prior `challenges` into the slots `k < i` and the running summation index `y k` into the remaining
slots `k ≥ i`, so the effective evaluation point matches `Fin.insertNth i pt (Fin.append challenges
x ∘ …)` — but only on the `n' - i` "free" tail coordinates. The `i` slots `k < i` of the summation
index `y` are *ignored* by `sumPoint` (it uses `challenges` there), so the `Fin (n-1) → R` fold ranges
over `i` extra dummy coordinates relative to the `Fin (n'-i) → R` round-polynomial cube. This fiber
collapse (and any `|D|^i` multiplicity it carries) is the substantive content; it is the direct
analogue of LogUp's `logupSumcheckPolynomial_finalEval` closed-form identity, and is carried here as
an explicit named hypothesis rather than asserted — it is exactly the genuinely-deep value-level
core that `SimpleRoundCoherent.lean` already factored out as `hRoundFaithful`. -/
abbrev CubeFiber (i : Fin n) : Prop :=
  ∀ (os : StatementRound R n i.castSucc) (oos : ∀ i, OracleStatement R n deg i) (pt : R),
    ∑ y ∈ (univ.map D) ^ᶠ (n - 1 - i), (oos ()).1.eval (sumPoint R n i pt os y)
      = Polynomial.eval pt
          ((((oStmtLens R n deg D i).toFunA (os, oos)).2 ()).val)

/-- **Round-polynomial faithfulness from the cube-fiber residual.** Combining the structural
fold-collapse (`foldl_sumPoint_eq_finsetSum`), the definitional answer-as-eval identity
(`answer_proj_eq_eval`), and the named combinatorial residual `hCubeFiber`, the fold value equals the
inner round univariate oracle answer — exactly the `hRoundFaithful` hypothesis consumed by
`SimpleRoundCoherent.coh_of`. -/
theorem roundFaithful_of_cubeFiber (i : Fin n) (hCubeFiber : CubeFiber (R := R) (deg := deg) (D := D) i)
    (os : StatementRound R n i.castSucc) (oos : ∀ i, OracleStatement R n deg i) (pt : R) :
    (((univ.map D) ^ᶠ (n - 1 - i)).toList).foldl
        (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y)) (0 : R)
      = OracleInterface.answer
          (((sumcheckOracleLens R n deg D oSpec i).toLens.proj (os, oos)).2 ()) pt := by
  rw [foldl_sumPoint_eq_finsetSum, answer_proj_eq_eval, hCubeFiber os oos pt]

/-- **The `∀ i`-form round faithfulness, modulo the per-round cube-fiber residual.** This is exactly
the `hRoundFaithful` shape that `SimpleRoundCoherent.coh_of` consumes; supplying it discharges the
last structural residual `(★)` of issue #13's per-round `LiftContextCoherent`. -/
theorem coh_of_cubeFiber
    (hCubeFiber : ∀ i : Fin n, CubeFiber (R := R) (deg := deg) (D := D) i)
    (i : Fin n) (os : StatementRound R n i.castSucc)
    (oos : ∀ i, OracleStatement R n deg i) (pt : R) :
    (((univ.map D) ^ᶠ (n - 1 - i)).toList).foldl
        (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y)) (0 : R)
      = OracleInterface.answer
          (((sumcheckOracleLens R n deg D oSpec i).toLens.proj (os, oos)).2 ()) pt :=
  roundFaithful_of_cubeFiber (oSpec := oSpec) i (hCubeFiber i) os oos pt

/-- The `Fin.cast` / `succAbove` commutation needed to evaluate `sumPoint` at `i.succAbove k`. -/
theorem cast_succAbove_comm (n' : ℕ) (i : Fin (n'+1)) (k : Fin n')
    (h : n' + 1 = (n' + 1 - 1) + 1) (hk : n' = (n' + 1 - 1)) :
    Fin.cast h (i.succAbove k) = (Fin.cast h i).succAbove (Fin.cast hk k) := by
  by_cases hlt : k.castSucc < i
  · have hlt' : (Fin.cast hk k).castSucc < Fin.cast h i := by
      rw [Fin.lt_def] at hlt ⊢; simpa [Fin.coe_cast, Fin.val_castSucc] using hlt
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt, Fin.succAbove_of_castSucc_lt _ _ hlt']
    apply Fin.ext; simp [Fin.coe_cast, Fin.val_castSucc]
  · have hle : i ≤ k.castSucc := not_lt.mp hlt
    have hle' : Fin.cast h i ≤ (Fin.cast hk k).castSucc := by
      rw [Fin.le_def] at hle ⊢; simpa [Fin.coe_cast, Fin.val_castSucc] using hle
    rw [Fin.succAbove_of_le_castSucc _ _ hle, Fin.succAbove_of_le_castSucc _ _ hle']
    apply Fin.ext; simp [Fin.coe_cast, Fin.val_succ]

/-- **`sumPoint` is exactly the `insertNth`-`append` evaluation point** used by the round
polynomial: prior `challenges` in the `k < i` slots, `pt` at slot `i`, the survivor index `y` in the
`k > i` slots. (This is what makes `CubeFiber` true now that the lens sums over the `n-1-i` survivor
cube.) -/
theorem sumPoint_eq_insertNth (n' : ℕ) (i : Fin (n'+1)) (pt : R)
    (os : StatementRound R (n'+1) i.castSucc) (y : Fin (n' + 1 - 1 - i) → R) :
    sumPoint R (n'+1) i pt os y
      = Fin.insertNth i pt (Fin.append os.challenges y ∘ Fin.cast (by simp; omega)) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp only [sumPoint, Function.comp_apply, Fin.insertNth_apply_same]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [sumPoint, Function.comp_apply, Fin.insertNth_apply_succAbove]
    rw [cast_succAbove_comm n' i k (by omega) (by omega), Fin.insertNth_apply_succAbove]
    simp only [Fin.coe_cast]
    by_cases hc : (k:ℕ) < (i:ℕ)
    · rw [dif_pos hc]
      have he : (Fin.cast (by simp; omega) k : Fin (↑(i.castSucc) + (n' + 1 - 1 - ↑i)))
          = Fin.castAdd _ ⟨k, by simp [Fin.val_castSucc]; omega⟩ := by
        apply Fin.ext; simp [Fin.coe_cast]
      rw [he, Fin.append_left]
    · rw [dif_neg hc]
      have he : (Fin.cast (by simp; omega) k : Fin (↑(i.castSucc) + (n' + 1 - 1 - ↑i)))
          = Fin.natAdd _ ⟨(k:ℕ) - ↑i, by simp [Fin.val_castSucc]; omega⟩ := by
        apply Fin.ext; simp only [Fin.coe_cast, Fin.val_natAdd, Fin.val_castSucc]; omega
      rw [he, Fin.append_right]

/-- **`CubeFiber` is PROVEN** — no longer a hypothesis. The `|D|^{n-1-i}`-fold `sumPoint` sum equals
`Polynomial.eval pt` of the round polynomial `oStmtLens.toFunA`, because (after the survivor-cube
fix) each `sumPoint i pt os y` is exactly the `insertNth`-`append` point at which the round
polynomial's survivor sum is evaluated (`sumPoint_eq_insertNth`). This discharges the last
combinatorial residual `hCubeFiber`. The proof is `oSpec`-free (works directly on `oStmtLens.toFunA`,
mirroring `answer_proj_eval_succ`'s internals without the oracle wrapper). -/
theorem cubeFiber_holds (i : Fin n) : CubeFiber (R := R) (deg := deg) (D := D) i := by
  cases n with
  | zero => exact i.elim0
  | succ n' =>
    intro os oos pt
    show (∑ y ∈ (univ.map D) ^ᶠ (n' + 1 - 1 - i), (oos ()).1.eval (sumPoint R (n'+1) i pt os y))
      = Polynomial.eval pt (∑ x ∈ (univ.map D) ^ᶠ (n' - i),
          (oos ()).val ⸨X ⦃i⦄, os.challenges, x⸩'(by simp; omega))
    rw [Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← eval_eq_eval_mv_eval_finSuccEquivNth]
    exact congrArg (fun p => (MvPolynomial.eval p) ((oos ()).val))
      (sumPoint_eq_insertNth n' i pt os y)

/-- **Per-round round-polynomial faithfulness, UNCONDITIONALLY** — `coh_of_cubeFiber` with the
now-proven `cubeFiber_holds`. This is exactly the `hRoundFaithful` shape `SimpleRoundCoherent.coh_of`
consumes, with NO residual hypothesis, discharging `hPerRound` and making the per-round
`LiftContextCoherent` (hence the multi-round sum-check oracle bridge of issue #13) unconditional. -/
theorem coh_proven (i : Fin n) (os : StatementRound R n i.castSucc)
    (oos : ∀ i, OracleStatement R n deg i) (pt : R) :
    (((univ.map D) ^ᶠ (n - 1 - i)).toList).foldl
        (fun (acc : R) y => acc + (oos ()).1.eval (sumPoint R n i pt os y)) (0 : R)
      = OracleInterface.answer
          (((sumcheckOracleLens R n deg D oSpec i).toLens.proj (os, oos)).2 ()) pt :=
  coh_of_cubeFiber (fun j => cubeFiber_holds j) i os oos pt

end

end Sumcheck.Spec.SingleRound

#print axioms Sumcheck.Spec.SingleRound.foldl_sumPoint_eq_finsetSum
#print axioms Sumcheck.Spec.SingleRound.answer_proj_eq_eval
#print axioms Sumcheck.Spec.SingleRound.answer_proj_eval_succ
#print axioms Sumcheck.Spec.SingleRound.roundFaithful_of_cubeFiber
#print axioms Sumcheck.Spec.SingleRound.coh_of_cubeFiber
