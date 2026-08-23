/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve

/-!
# The small-witness regime: marked curve decodability by interpolation
# (issue #334, K5, brick 4)

[Jo26] (ePrint 2026/891) **Lemma 5.2**: an `F_q`-additive code is marked
`(ℓ, δ, a, b)`-curve-decodable for **every** `δ` and every `a ≥ b`, whenever `b ≤ ℓ + 1` —
Lagrange interpolation produces a degree-`(b−1)` codeword-valued curve through any `b` chosen
values of `f`, and additivity puts its coefficients in the code. ([Jo26] Remark 5.3: the
nontrivial applications regime is therefore `b > ℓ + 1`.)

The interpolation core (`curve_through_values`) constructs the curve coefficients explicitly
as `cs j := ∑_{α ∈ T} (Lagrange.basis T id α).coeff j • f α` — module-valued Lagrange
interpolation, reusable wherever a codeword curve must pass through prescribed codeword
values (the `V_T` constructions of Theorems 5.7/5.8 are next).
-/

open Finset Polynomial
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Module-valued Lagrange interpolation**: through any `b` prescribed `A`-valued points
(`b ≤ ℓ + 1`) there is a degree-budget-`ℓ` curve `α ↦ ∑ⱼ αʲ • cs j` agreeing with `g` on all
of `T`, whose coefficients are `F`-combinations of the prescribed values — so any submodule
containing the values contains the coefficients. -/
theorem curve_through_values {ℓ : ℕ} (T : Finset F) (hT : T.card ≤ ℓ + 1)
    (g : F → A) :
    ∃ cs : Fin (ℓ + 1) → A,
      (∀ j, cs j ∈ Submodule.span F (g '' T)) ∧
      ∀ β ∈ T, (∑ j : Fin (ℓ + 1), β ^ (j : ℕ) • cs j) = g β := by
  classical
  -- The coefficients: cs j := ∑_{α ∈ T} (L_α).coeff j • g α, L_α the Lagrange basis at α.
  refine ⟨fun j => ∑ α ∈ T, ((Lagrange.basis T id α).coeff (j : ℕ)) • g α, ?_, ?_⟩
  · intro j
    refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨α, hα, rfl⟩
  · intro β hβ
    have hinj : Set.InjOn (id : F → F) T := Set.injOn_id _
    -- Each basis polynomial has degree b − 1 ≤ ℓ < ℓ + 1.
    have hdeg : ∀ α ∈ T, (Lagrange.basis T id α).natDegree < ℓ + 1 := by
      intro α hα
      rw [Lagrange.natDegree_basis hinj hα]
      omega
    -- Push the smul through the inner coefficient sums, then swap.
    have hswap : (∑ j : Fin (ℓ + 1), β ^ (j : ℕ) •
          (∑ α ∈ T, ((Lagrange.basis T id α).coeff (j : ℕ)) • g α))
        = ∑ α ∈ T, ∑ j : Fin (ℓ + 1),
            β ^ (j : ℕ) • (((Lagrange.basis T id α).coeff (j : ℕ)) • g α) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.smul_sum
    rw [hswap]
    have hpoint : ∀ α ∈ T,
        (∑ j : Fin (ℓ + 1), β ^ (j : ℕ) • (((Lagrange.basis T id α).coeff (j : ℕ)) • g α))
        = ((Lagrange.basis T id α).eval β) • g α := by
      intro α hα
      have hsmul : ∀ j : Fin (ℓ + 1),
          β ^ (j : ℕ) • (((Lagrange.basis T id α).coeff (j : ℕ)) • g α)
          = (((Lagrange.basis T id α).coeff (j : ℕ)) * β ^ (j : ℕ)) • g α := by
        intro j
        rw [smul_smul, mul_comm]
      rw [Finset.sum_congr rfl (fun j _ => hsmul j), ← Finset.sum_smul]
      congr 1
      -- ∑_{j < ℓ+1} coeff j · βʲ = eval β, since natDegree < ℓ + 1.
      rw [Polynomial.eval_eq_sum_range' (hdeg α hα)]
      rw [← Fin.sum_univ_eq_sum_range (fun j => (Lagrange.basis T id α).coeff j * β ^ j)]
    rw [Finset.sum_congr rfl hpoint]
    -- Lagrange: the basis evaluations are the Kronecker delta on T.
    rw [Finset.sum_eq_single β]
    · rw [show (Lagrange.basis T id β).eval β
            = (Lagrange.basis T id β).eval (id β) from rfl,
        Lagrange.eval_basis_self hinj hβ, one_smul]
    · intro α hα hne
      rw [show (Lagrange.basis T id α).eval β
            = (Lagrange.basis T id α).eval (id β) from rfl,
        Lagrange.eval_basis_of_ne hne hβ, zero_smul]
    · intro hβ'
      exact absurd hβ hβ'

/-- **[Jo26] Lemma 5.2 (the small-witness regime).** For `b ≤ ℓ + 1` and any `a ≥ b`, every
`F`-additive code (submodule) is marked `(ℓ, δ, a, b)`-curve-decodable, for **every** `δ`:
choose any `b` points of `A₀` and interpolate. -/
theorem markedCurveDecodable_of_small_witness (C : Submodule F (ι → A)) {ℓ : ℕ}
    (δ : ℝ≥0) {a b : ℕ} (hb : b ≤ ℓ + 1) (hab : b ≤ a) :
    MarkedCurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b := by
  classical
  intro u f hf A₀ hcard _hδ
  -- Choose b points of A₀.
  obtain ⟨T, hsub, hTcard⟩ := Finset.exists_subset_card_eq
    (show b ≤ A₀.card by rw [hcard]; exact hab)
  -- Interpolate coordinatewise — the curve coefficients live in (ι → A), with values f α ∈ C.
  obtain ⟨cs, hcsSpan, hcsAgree⟩ := curve_through_values (A := ι → A) T
    (by rw [hTcard]; exact hb) f
  refine ⟨cs, ?_, ?_⟩
  · -- Span of codeword values is inside the submodule.
    intro j
    have : Submodule.span F (f '' T) ≤ C := by
      rw [Submodule.span_le]
      rintro w ⟨α, _, rfl⟩
      exact hf α
    exact this (hcsSpan j)
  · -- All b chosen points are explained.
    refine le_trans (le_of_eq hTcard.symm) (Finset.card_le_card ?_)
    intro α hα
    rw [Finset.mem_filter]
    refine ⟨hsub hα, ?_⟩
    have h := hcsAgree α hα
    funext i
    have := congrFun h i
    rw [← this]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => rfl

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.curve_through_values
#print axioms ProximityGap.markedCurveDecodable_of_small_witness
