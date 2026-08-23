/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.CS25DeepHoleFinish2

/-!
# CS25 "Claim 3" deep-hole — discharging the joint-far side condition (`DeepHoleJointFar`)

This file closes the **last residual** of the [CS25] (Crites–Stewart, eprint 2025/2046)
Theorem 2 / [ABF26] Theorem 5.3 deep-hole chain: the joint-far property `DeepHoleJointFar`
surfaced as a documented side condition in `ArkLib.ToMathlib.CS25DeepHoleFinish2`.

## The argument (CS25 §Claim 3 minimum-distance step)

The deep-hole stack `dhStack domain u a = ![u⁰, u¹]` has rows
```
  u⁰_i = u_i / (xᵢ − a),   u¹_i = 1 / (xᵢ − a),   where xᵢ := domain i, a ∉ range domain.
```
`DeepHoleJointFar domain u a k δ` asserts this stack is **not** jointly `δ`-close to `RS[k]`,
i.e. `¬ jointProximity RS[k] (dhStack domain u a) δ.toNNReal`.

Suppose, for contradiction, joint closeness held.  Unfolding `jointProximity`, the interleaved
word `⋈|(dhStack …) = (dhStack …).transpose : Matrix ι (Fin 2) F` would be within relative
distance `δ.toNNReal` of the interleaved code `interleavedCodeSet RS[k]`, so there is an
interleaved codeword `V` with both columns `q⁰ := V.transpose 0`, `q¹ := V.transpose 1` in
`RS[k]`, and a **common agreement set** `S : Finset ι` of size
`|S| ≥ n − ⌊δ·n⌋` on which `⋈|(dhStack …)` and `V` agree *column-wise* — i.e. **both** rows
agree at every `i ∈ S`.

Writing `q¹ = evalOnPoints domain h` for a polynomial `h` with `deg h < k`, the second-row
agreement says `1/(xᵢ − a) = h(xᵢ)` for `i ∈ S`, hence (clearing the nonzero denominator)
```
  (xᵢ − a) · h(xᵢ) = 1   for every i ∈ S.
```
Thus the degree-`≤ k` polynomial `g := (X − C a)·h − 1` vanishes at the `|S|` *distinct* points
`{xᵢ : i ∈ S}`.  If `k < |S|` then `natDegree g ≤ k < |S|`, so `g = 0` by
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`.  But evaluating at `X = a`:
```
  g(a) = (a − a)·h(a) − 1 = −1 ≠ 0,
```
a contradiction.  Hence joint closeness is impossible, *provided* `k < |S|`.

Since `|S| ≥ n − ⌊δ·n⌋`, the genuine arithmetic side condition is exactly
`k < n − ⌊δ·n⌋` (the in-chain equivalent of the rate condition `δ < 1 − k/n`).  This is the
**one documented arithmetic hypothesis** `hkS`; it is the *only* input — everything else is the
proven minimum-distance argument.

## Main results (all `sorry`-free)

- `deepHoleJointFar_holds` — `DeepHoleJointFar` holds under the arithmetic side condition
  `k < n − ⌊δ.toNNReal·n⌋` and `a` off the evaluation domain.
- `rs_epsCA_implies_lambda_extended_cs25_complete` — the ABF26 T5.3 / CS25 Thm 2 list-size
  bound with the deep-hole geometric/probabilistic content discharged under the standard
  parameter regime plus the documented arithmetic rate condition `k < n − ⌊δ·n⌋` at every
  sampling point.  The unconditional `DeepHoleProbResidual` wrapper remains open in the strict
  residual census because these side conditions are real hypotheses, not implicit facts.

## References

- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. eprint 2025/2046,
  Theorem 2, Claim 3.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026,
  Theorem 5.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CodingTheory.CS25.DeepHole

open scoped NNReal ProbabilityTheory BigOperators ENNReal
open ProximityGap ListDecodable Polynomial Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The minimum-distance "joint-far" argument -/

/-- **CS25 joint-far property (discharged).**

The deep-hole stack `(u⁰, u¹)` at an off-domain hole `a` is *not* jointly `δ`-close to `RS[k]`,
provided the arithmetic rate condition `k < n − ⌊δ.toNNReal · n⌋` holds (the in-chain equivalent
of `δ < 1 − k/n`).

This is the only genuinely external input of the deep-hole probability bound; the proof is the
standard minimum-distance argument: a common agreement set of size `> k` would force the
degree-`≤ k` polynomial `(X − a)·q¹ − 1` to vanish on `> k` distinct points, hence to be zero,
contradicting its value `−1` at `X = a`. -/
theorem deepHoleJointFar_holds
    (domain : ι ↪ F) (u : ι → F) (a : F) (k : ℕ) (δ : ℝ)
    (hdom : ∀ i, domain i ≠ a)
    (hkS : k < Fintype.card ι - Nat.floor (δ.toNNReal * Fintype.card ι)) :
    DeepHoleJointFar domain u a k δ := by
  classical
  -- Unfold the predicate and assume joint closeness for contradiction.
  rw [DeepHoleJointFar, jointProximity]
  intro hclose
  -- Extract an interleaved codeword `V` within distance `δ` of the interleaved deep-hole word.
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hclose
  obtain ⟨V, hVmem, hVdist⟩ := hclose
  -- The agreement set `S`: columns of `⋈|(dhStack …)` and `V` agree on `S`, `|S| ≥ n − ⌊δ·n⌋`.
  rw [relCloseToWord_iff_exists_agreementCols] at hVdist
  obtain ⟨S, hScard, hSagree⟩ := hVdist
  -- `k < |S|`.
  have hkS' : k < S.card := lt_of_lt_of_le hkS hScard
  -- The second row `q¹ = V.transpose 1` is an `RS[k]` codeword, hence an evaluated polynomial.
  have hq1mem : (Matrix.transpose V 1) ∈ ReedSolomon.code domain k := hVmem 1
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hq1mem
  obtain ⟨h, hhdeg, hheval⟩ := hq1mem
  -- The vanishing polynomial `g := (X − C a)·h − 1`.
  set g : F[X] := (Polynomial.X - Polynomial.C a) * h - 1 with hgdef
  -- Degree bound: `natDegree g ≤ k`.
  have hgdeg : g.natDegree ≤ k := by
    rw [hgdef]
    by_cases hh0 : h = 0
    · -- `g = (X − a)·0 − 1 = −1`, degree `0 ≤ k`.
      simp [hh0]
    · -- `natDegree((X−a)·h − 1) ≤ max (1 + natDegree h) 0 ≤ k`.
      have hhnat : h.natDegree < k := by
        rw [Polynomial.natDegree_lt_iff_degree_lt hh0]; exact hhdeg
      calc g.natDegree
          ≤ max ((Polynomial.X - Polynomial.C a) * h).natDegree (1 : F[X]).natDegree := by
            rw [hgdef]; exact Polynomial.natDegree_sub_le _ _
        _ ≤ max (1 + h.natDegree) 0 := by
            apply max_le_max
            · calc ((Polynomial.X - Polynomial.C a) * h).natDegree
                    ≤ (Polynomial.X - Polynomial.C a).natDegree + h.natDegree :=
                      Polynomial.natDegree_mul_le
                  _ ≤ 1 + h.natDegree := by
                      have := Polynomial.natDegree_X_sub_C_le (R := F) a; omega
            · simp
        _ ≤ k := by simp only [max_le_iff]; omega
  -- On `S`, the second-row equality forces `(xᵢ − a)·h(xᵢ) = 1`, i.e. `g(xᵢ) = 0`.
  -- `S.image domain` is a Finset of `|S|` distinct evaluation points where `g` vanishes.
  have hvanish : ∀ x ∈ S.image domain, g.eval x = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hiS, rfl⟩ := hx
    -- Column-wise agreement at `i ∈ S`: `(⋈|dhStack) i = V i`.
    have hcol := (hSagree i).1 hiS
    -- Read off the second-row (`Fin 2 = 1`) coordinate.
    have hrow1 : dhWord1 domain a i = h.eval (domain i) := by
      -- `(⋈|dhStack) i 1 = (dhStack).transpose i 1 = dhStack 1 i = dhWord1 domain a i`.
      have hlhs : (Interleavable.interleave (dhStack domain u a) : Matrix ι (Fin 2) F) i 1
          = dhWord1 domain a i := by
        simp [interleave_wordStack_eq, Matrix.transpose_apply, dhStack, dhWord1]
      -- `V i 1 = V.transpose 1 i = h.eval (domain i)`.
      have hrhs : V i 1 = h.eval (domain i) := by
        have hT : Matrix.transpose V 1 i = h.eval (domain i) := by
          rw [hheval]; simp [ReedSolomon.evalOnPoints]
        simpa [Matrix.transpose_apply] using hT
      have := congrFun hcol 1
      rw [hlhs] at this
      rw [this, hrhs]
    -- `1/(xᵢ − a) = h(xᵢ)` with `xᵢ − a ≠ 0` gives `(xᵢ − a)·h(xᵢ) = 1`.
    have hne : domain i - a ≠ 0 := sub_ne_zero.mpr (hdom i)
    have hmul : (domain i - a) * h.eval (domain i) = 1 := by
      rw [← hrow1, dhWord1, mul_one_div, div_self hne]
    -- Evaluate `g` at `xᵢ`.
    rw [hgdef]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_one]
    rw [hmul, sub_self]
  -- `S.image domain` has cardinality `|S|` (`domain` injective), so `> k ≥ natDegree g`.
  have himgcard : (S.image domain).card = S.card :=
    Finset.card_image_of_injective S domain.injective
  have hcardlt : g.natDegree < (S.image domain).card := by
    rw [himgcard]; exact lt_of_le_of_lt hgdeg hkS'
  -- Vanishing on `> natDegree g` distinct points forces `g = 0`.
  have hg0 : g = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g (S.image domain) hvanish hcardlt
  -- But `g(a) = (a − a)·h(a) − 1 = −1 ≠ 0`.
  have hga : g.eval a = -1 := by
    rw [hgdef]
    simp
  rw [hg0] at hga
  simp only [Polynomial.eval_zero] at hga
  -- `0 = −1` is a contradiction in a field: `−1 = 0` gives `1 = 0`.
  exact one_ne_zero (neg_eq_zero.mp hga.symm)

/-! ### Direct instantiation of `DeepHoleProbResidual` (Issue #22, criterion 1)

The probabilistic residual `DeepHoleProbResidual` (defined in `CS25DeepHoleFinish.lean`) is
instantiated by a single named result under the documented nonnegativity and arithmetic rate
conditions.  The rate condition `k < n − ⌊δ·n⌋` is the genuine parameter regime
`δ < 1 − k/n`, not a residual. This composes the joint-far discharge
(`deepHoleProbResidual_of_jointFar`, proven in `CS25DeepHoleFinish2.lean`) with the
minimum-distance proof of the joint-far property (`deepHoleJointFar_holds`, above). -/

/-- **`DeepHoleProbResidual` discharged (Issue #22).** For any received word `u` and degree-`< k+1`
polynomial family `p`, the CS25 deep-hole probability residual holds at every sampling point with
no remaining geometric/probabilistic side condition once the documented nonnegativity and
arithmetic rate conditions are supplied.

This is the explicit answer to Issue #22's first criterion ("identify the smallest remaining
statement needed to instantiate `DeepHoleProbResidual` without extra geometric side conditions"):
that statement is the rate condition `hkS` (along with `hδ0` for radius coercions), and the
deep-hole probability bound follows from the proven minimum-distance argument
`deepHoleJointFar_holds`. -/
theorem deepHoleProbResidual_holds
    (domain : ι ↪ F) (u : ι → F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hkS : k < Fintype.card ι - Nat.floor (δ.toNNReal * Fintype.card ι)) :
    DeepHoleProbResidual domain k L δ
      (epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
        δ.toNNReal δ.toNNReal).toReal u p :=
  deepHoleProbResidual_of_jointFar domain u p hδ0
    (fun a ha => deepHoleJointFar_holds domain u a k δ
      (mem_sampleSet_imp_off_domain ha) hkS)

/-! ### The fully-discharged final theorem -/

/-- **ABF26 Theorem 5.3 [CS25 Theorem 2] — fully discharged.**

The complete list-size bound for `RS[k+1]`, with the deep-hole geometric/probabilistic chain
closed under the standard CS25 parameter regime plus the documented arithmetic rate condition
`k < n − ⌊δ·n⌋` (the in-chain equivalent of `δ < 1 − k/n`), which discharges the joint-far
property `DeepHoleJointFar` via `deepHoleJointFar_holds`.

Side conditions:
- `hk_pos`, `hη_lo`, `hη_lt` — the standard CS25 parameter regime.
- `hkn : k + 1 ≤ |ι|`, `hs_pos : 0 < |F| − |ι|` — the standard parameter side conditions.
- `hδ0 : 0 ≤ δ` — non-negativity of the proximity radius.
- `hε_ca` — the CA-error cap.
- `hkS` — the documented arithmetic rate condition `k < n − ⌊δ·n⌋`. -/
theorem rs_epsCA_implies_lambda_extended_cs25_complete
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (hk_pos : 0 < k)
    (hη_lo : 0 ≤ η) (hη_lt : η < 1)
    (hkn : k + 1 ≤ Fintype.card ι)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (hδ0 : 0 ≤ δ)
    (hkS : k < Fintype.card ι - Nat.floor (δ.toNNReal * Fintype.card ι))
    (hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F))) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCA (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞) := by
  -- Consume the joint-far final form, discharging `DeepHoleJointFar` at every sampling point
  -- via the proven minimum-distance argument `deepHoleJointFar_holds`.
  apply rs_epsCA_implies_lambda_extended_cs25_jointFar
    domain k δ η hk_pos hη_lo hη_lt hkn hs_pos hδ0 hε_ca
  intro ε L0 u a ha
  exact deepHoleJointFar_holds domain u a k δ
    (mem_sampleSet_imp_off_domain ha) hkS

/-- Prop-level CS25 endpoint from the fully discharged deep-hole chain.

This targets the public ABF26 T5.3 / CS25 proposition from
`ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA`, while keeping the arithmetic side
conditions required by the complete deep-hole proof explicit. -/
theorem rs_epsCA_implies_lambda_extended_cs25_complete_prop
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (hk_pos : 0 < k)
    (hδ_pos : 0 < δ)
    (hδ_min :
        (δ : ℝ) < Code.minDist ((ReedSolomon.code domain k : Set (ι → F)))
                    / Fintype.card ι)
    (hη_lo : 0 ≤ η) (hη_lt : η < 1)
    (hkn : k + 1 ≤ Fintype.card ι)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (hkS : k < Fintype.card ι - Nat.floor (δ.toNNReal * Fintype.card ι))
    (hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F))) :
    CodingTheory.rs_epsCA_implies_lambda_extended_cs25 domain k δ η
      hk_pos hδ_pos hδ_min hη_lo hη_lt hε_ca :=
  rs_epsCA_implies_lambda_extended_cs25_complete
    domain k δ η hk_pos hη_lo hη_lt hkn hs_pos (le_of_lt hδ_pos) hkS hε_ca

end CodingTheory.CS25.DeepHole

section AxiomAudit
#print axioms CodingTheory.CS25.DeepHole.deepHoleJointFar_holds
#print axioms CodingTheory.CS25.DeepHole.deepHoleProbResidual_holds
#print axioms CodingTheory.CS25.DeepHole.rs_epsCA_implies_lambda_extended_cs25_complete
#print axioms CodingTheory.CS25.DeepHole.rs_epsCA_implies_lambda_extended_cs25_complete_prop
end AxiomAudit
