/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.CodeGeometry
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityLeaves
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Proximity-prize foundation leaves (II)

Second batch of verified Layer-2/3 foundation lemmas (build workflow wwsu812kn,
each independently re-verified: compiles, no real sorry, axiom-clean):
the relative-distance ↔ agreement bridge, q-ary entropy rewrites/nonnegativity,
the binomial factorial-quotient (Stirling entry), Reed–Solomon Lagrange
interpolation through a subset, and agreement ⟹ closeness. See
research/formal/arklib-patches/proximity-prize-infrastructure-roadmap.md.
-/

/- ════ relHammingDist_le_iff_agree_ge ════ -/
open CodeGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [DecidableEq α]

omit [DecidableEq ι] in
/-- **Relative-distance ↔ agreement bridge.**

For words `u v : ι → α` over a nonempty index set (`n := Fintype.card ι`), the
relative Hamming distance is at most `δ` iff the agreement count is at least
`(1 - δ)·n`:

`hammingDist u v / n ≤ δ  ↔  (1 - δ)·n ≤ agree u v`.

This lets `CodeGeometry.agree`-based bounds (e.g. the Johnson list-size cap) be
fed relative-distance hypotheses, and vice versa. The proof rests on
`CodeGeometry.agree_add_hammingDist` (`agree u v + hammingDist u v = n`); no
constraint on `δ` is needed because the equivalence holds for all real `δ`. -/
theorem relHammingDist_le_iff_agree_ge (u v : ι → α) (hn : 0 < Fintype.card ι) {δ : ℝ} :
    (hammingDist u v : ℝ) / (Fintype.card ι : ℝ) ≤ δ ↔
      (1 - δ) * (Fintype.card ι : ℝ) ≤ (agree u v : ℝ) := by
  have hn' : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn
  -- the partition identity, cast to ℝ
  have hpart : (agree u v : ℝ) + (hammingDist u v : ℝ) = (Fintype.card ι : ℝ) := by
    have := agree_add_hammingDist u v
    exact_mod_cast this
  rw [div_le_iff₀ hn']
  constructor
  · intro h
    nlinarith [hpart, h]
  · intro h
    nlinarith [hpart, h]

#print axioms relHammingDist_le_iff_agree_ge

/- ════ qEntropy_rpow_eq_exp_qaryEntropy ════ -/
namespace CodingTheory

open Real

-- dedup-audit(#257): `qEntropy_mul_log_eq_qaryEntropy` removed here to resolve the
-- duplicate fully-qualified name (umbrella-build clash). Canonical copy lives in
-- `ProximityPrizeLeaves.lean` and is re-exported via the import added above.

/-- **Entropy rewrite for the C3.8 volume bound.** For `q ≥ 2` and `n : ℕ`, the real
power `q ^ (n · H_q(δ))` (where `H_q = qEntropy q` is ArkLib's base-`q` entropy and `^`
is `Real.rpow`) equals the exponential of `n` times Mathlib's natural-log entropy
`Real.qaryEntropy q δ`:

  `q ^ (n · qEntropy q δ) = Real.exp (n · Real.qaryEntropy q δ)`.

This is the `rpow ↦ exp/qaryEntropy` step feeding `linear_lambda_ge_entropy_volume`:
`Real.rpow_def_of_pos` turns the LHS into `exp (log q · (n · qEntropy q δ))`, and the
base-change bridge `qEntropy q δ · log q = qaryEntropy q δ` rewrites the exponent.

`2 ≤ q` is required: it makes `q > 0` (so `rpow_def_of_pos` applies) and is exactly the
regime in which the base-change identity holds (every consumer has `q = |F| ≥ 2`). -/
theorem qEntropy_rpow_eq_exp_qaryEntropy {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (δ : ℝ) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q δ)
      = Real.exp ((n : ℝ) * Real.qaryEntropy q δ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  -- `rpow` of a positive base: `q ^ y = exp (log q * y)`.
  rw [Real.rpow_def_of_pos hq0]
  -- Reduce both exponents to the same real number.
  congr 1
  -- `log q * (n * qEntropy q δ) = n * qaryEntropy q δ`.
  rw [← qEntropy_mul_log_eq_qaryEntropy hq δ]
  ring

end CodingTheory

/- ════ choose_real_factorial_quotient ════ -/
open Nat

namespace CodingTheory

/-- **Factorial-quotient form of the binomial coefficient over `ℝ`.**

For `k ≤ n`,
  `(n.choose k : ℝ) = n! / (k! * (n - k)!)`,
where `n - k` is truncated natural subtraction (well-defined and equal to the
honest difference because `k ≤ n`).

Derived from `Nat.choose_mul_factorial_mul_factorial` by casting to `ℝ` and
dividing by the nonzero product `k! * (n - k)!`. This is the entry point to the
Stirling lower bound on a single binomial coefficient, hence to the
entropy-volume estimate for the Hamming ball (ABF26 C3.8). -/
theorem choose_real_factorial_quotient {n k : ℕ} (h : k ≤ n) :
    (n.choose k : ℝ) = (n ! : ℝ) / ((k ! : ℝ) * ((n - k)! : ℝ)) := by
  -- The product of factorials in the denominator is nonzero in `ℝ`.
  have hk : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos k).ne'
  have hnk : ((n - k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos (n - k)).ne'
  have hden : (k ! : ℝ) * ((n - k)! : ℝ) ≠ 0 := mul_ne_zero hk hnk
  -- Reduce the goal to the cleared-denominator equation.
  rw [eq_div_iff hden]
  -- Cast the integer identity `choose n k * k! * (n-k)! = n!` into `ℝ`.
  have hnat : n.choose k * k ! * (n - k)! = n ! :=
    Nat.choose_mul_factorial_mul_factorial h
  have hcast : ((n.choose k * k ! * (n - k)! : ℕ) : ℝ) = (n ! : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hnat
  calc (n.choose k : ℝ) * ((k ! : ℝ) * ((n - k)! : ℝ))
      = ((n.choose k * k ! * (n - k)! : ℕ) : ℝ) := by push_cast; ring
    _ = (n ! : ℝ) := hcast

end CodingTheory

-- sorry-free; axiom audit below.
#print axioms CodingTheory.choose_real_factorial_quotient

/- ════ ReedSolomon_interpolate_through_subset ════ -/
open Polynomial

namespace ReedSolomon

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Interpolation through a subset of the Reed–Solomon domain.**
For any subset `S` of the evaluation domain with `#S ≤ k`, and any target values
`target : ι → F`, there is a codeword `f` of the degree-`< k` Reed–Solomon code over
`domain` that matches the targets on `S`, i.e. `f i = target i` for every `i ∈ S`.

The witness codeword is the evaluation vector of the Lagrange interpolant
`Lagrange.interpolate S domain target`, which has degree `< #S ≤ k`. -/
theorem ReedSolomon_interpolate_through_subset
    {k : ℕ} (domain : ι ↪ F) (S : Finset ι) (hS : S.card ≤ k) (target : ι → F) :
    ∃ f ∈ ReedSolomon.code domain k, ∀ i ∈ S, f i = target i := by
  classical
  -- The interpolant of `target` through the nodes `S`.
  set p : F[X] := Lagrange.interpolate S domain target with hp
  -- `domain` is injective on `S`.
  have hInj : Set.InjOn domain S := fun x _ y _ hxy => domain.injective hxy
  -- Degree bound: deg p < #S ≤ k.
  have hdeg : p.degree < (k : WithBot ℕ) := by
    have h1 : p.degree < (S.card : WithBot ℕ) := by
      rw [hp]; exact_mod_cast Lagrange.degree_interpolate_lt _ hInj
    calc p.degree < (S.card : WithBot ℕ) := h1
      _ ≤ (k : WithBot ℕ) := by exact_mod_cast hS
  -- The evaluation vector of `p` is the candidate codeword.
  refine ⟨ReedSolomon.evalOnPoints domain p, ?_, ?_⟩
  · -- Membership in the code: `p` has degree `< k`, evaluated on the domain.
    exact mem_code_of_polynomial_of_degree_lt_of_eval p hdeg (fun i => rfl)
  · -- Agreement on `S`: Lagrange interpolant takes value `target i` at node `domain i`.
    intro i hi
    change p.eval (domain i) = target i
    rw [hp]
    exact Lagrange.eval_interpolate_at_node target hInj hi

end ReedSolomon

#print axioms ReedSolomon.ReedSolomon_interpolate_through_subset

/- ════ ReedSolomon_agreement_implies_close ════ -/
open CodeGeometry ReedSolomon Polynomial

/-- **Agreement ⇒ closeness for Reed–Solomon codewords.**

Let `domain : ι ↪ F` be an evaluation set of size `n = |ι|`, let `p` be a
polynomial of degree `< k`, and let `w : ι → F` be an arbitrary word. Write the
evaluated codeword `p ∘ domain` as `evalOnPoints domain p`. If `p` agrees with
`w` on at least `n - e` positions, i.e.

  `n - e ≤ agree (evalOnPoints domain p) w`,

then

  * the evaluated word is a codeword of the Reed–Solomon code `code domain k`, and
  * its Hamming distance to `w` is at most `e`.

The distance bound is the combinatorial heart: by the partition identity
`agree + hammingDist = n`, an agreement of `≥ n - e` forces a distance of `≤ e`.
The degree hypothesis is what makes the evaluated word an actual RS codeword. -/
theorem ReedSolomon_agreement_implies_close
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    (domain : ι ↪ F) (k e : ℕ) (p : F[X]) (w : ι → F)
    (hdeg : p ∈ Polynomial.degreeLT F k)
    (hagree : Fintype.card ι - e ≤ agree (evalOnPoints domain p) w) :
    (evalOnPoints domain p) ∈ ReedSolomon.code domain k ∧
      hammingDist (evalOnPoints domain p) w ≤ e := by
  refine ⟨?_, ?_⟩
  · -- The evaluated word is a codeword: it is the image of `p ∈ degreeLT F k`.
    exact Submodule.mem_map_of_mem hdeg
  · -- Combinatorial step: `agree + hammingDist = n`, so `agree ≥ n - e ⇒ dist ≤ e`.
    have hpart := agree_add_hammingDist (evalOnPoints domain p) w
    omega

/- ════ qEntropy_nonneg_and_basic ════ -/
namespace CodingTheory

open Real

/-- **Basic `qEntropy` API.**  For an alphabet size `q ≥ 2` and a relative distance
`δ ∈ [0,1]`, the `q`-ary entropy function is non-negative, and it vanishes at `δ = 0`.

This packages the two foundational facts needed by the entropy-volume bounds
(ABF26 Corollary 3.8 / Theorem 3.11):

* `qEntropy q δ ≥ 0`,
* `qEntropy q 0 = 0`.

The non-negativity is the three-term sign decomposition:
`δ · logb q (q-1) ≥ 0`, `-δ · logb q δ ≥ 0`, `-(1-δ) · logb q (1-δ) ≥ 0`. -/
theorem qEntropy_nonneg_and_basic {q : ℕ} (hq : 2 ≤ q) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 ≤ qEntropy q δ ∧ qEntropy q 0 = 0 := by
  refine ⟨?_, qEntropy_zero q⟩
  -- Base `(q : ℝ) > 1`.
  have hb : (1 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  -- `q - 1 ≥ 1` as a real number.
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  -- Term 1: `δ · logb q (q-1) ≥ 0`.
  have t1 : 0 ≤ δ * Real.logb (q : ℝ) ((q : ℝ) - 1) :=
    mul_nonneg hδ0 (Real.logb_nonneg hb hq1)
  -- Term 2: `-(δ · logb q δ) ≥ 0`, i.e. `δ · logb q δ ≤ 0`.
  have t2 : δ * Real.logb (q : ℝ) δ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hδ0 (Real.logb_nonpos hb hδ0 hδ1)
  -- Term 3: `-(1-δ) · logb q (1-δ) ≥ 0`, i.e. `(1-δ) · logb q (1-δ) ≤ 0`.
  have h1δ0 : 0 ≤ 1 - δ := by linarith
  have h1δ1 : 1 - δ ≤ 1 := by linarith
  have t3 : (1 - δ) * Real.logb (q : ℝ) (1 - δ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1δ0 (Real.logb_nonpos hb h1δ0 h1δ1)
  -- Combine.  The cast `((q : ℕ) : ℝ) - 1` matches the definition's `(q - 1)`.
  unfold qEntropy
  -- After unfolding, the base is `((q : ℕ) : ℝ)` (Nat cast), and `q - 1` is `(↑q - 1 : ℝ)`.
  linarith [t1, t2, t3]

end CodingTheory
