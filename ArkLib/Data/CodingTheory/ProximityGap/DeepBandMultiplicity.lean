/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandCoherence

/-!
# Deep-band multiplicity (#371): the per-scalar fiber, reduced and named

The single open quantity of the deep-band programme — the per-scalar
multiplicity of coherent cores — is here given its exact structural reduction:

* `fiber_subset_explainable` — the coherent cores sharing a value `γ` all
  explain ONE word, the line `Q∘dom + γ·x^k`; the fiber of `γ` is contained in
  the explainable-core family of that single word.
* `ExplainableCoreSupply B` — the named residual: every word admits at most
  `B` explainable `(k+m+1)`-cores.  This is the multiplicity number in its
  final isolated form (the degenerate stratum — words ON the code — shows a
  uniform small `B` cannot be free: `B = C(n,k+m+1)` is attained there, so a
  useful supply must come from second-moment or list-geometry input; that is
  the precise remaining mathematics).
* `deep_band_badSet_card_of_supply` — **the reduction theorem**: given the
  supply, at every band radius,

    **`∃ Q₀ : C(n,k+m+1) ≤ #badSet(Q₀, x^k) · q^m · B`** —

  the witness-mass law converts into a bad-scalar COUNT.  At `B` polynomial
  in `n` this gives production-regime failure at depth `m`; the trivial
  instance `B = C(n,k+m+1)` (`explainableCoreSupply_trivial`) keeps the chain
  nonvacuous unconditionally.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- A word is explainable on a core when some codeword agrees with it there. -/
def ExplainableOn (dom : Fin n ↪ F) (k : ℕ) (w : Fin n → F)
    (T : Finset (Fin n)) : Prop :=
  ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ i ∈ T, c i = w i

open Classical in
/-- **The named residual**: every word admits at most `B` explainable
`(k+m+1)`-cores. -/
def ExplainableCoreSupply (dom : Fin n ↪ F) (k m : ℕ) (B : ℕ) : Prop :=
  ∀ w : Fin n → F,
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
      (fun T => ExplainableOn dom k w T)).card ≤ B

open Classical in
/-- The trivial supply instance: nonvacuity of the chain. -/
theorem explainableCoreSupply_trivial (dom : Fin n ↪ F) (k m : ℕ) :
    ExplainableCoreSupply dom k m (n.choose (k + m + 1)) := by
  intro w
  calc (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k w T)).card
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card :=
        Finset.card_filter_le _ _
    _ = n.choose (k + m + 1) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The fiber structure**: a coherent core explains the line of its pinned
scalar — the value fiber sits inside one word's explainable-core family. -/
theorem coherent_explains_line (dom : Fin n ↪ F) {k m : ℕ}
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) {Q : F[X]}
    (hcoh : IsCoherent dom k m T Q) :
    ExplainableOn dom k
      (fun i => Q.eval (dom i)
        + (-(coreInterp dom T Q).coeff k) * (dom i) ^ k) T := by
  have hvs : Set.InjOn dom T := fun a _ b _ h => dom.injective h
  set γ : F := -(coreInterp dom T Q).coeff k with hγ
  set R : F[X] := coreInterp dom T Q + C γ * X ^ k with hR
  have hIdeg : (coreInterp dom T Q).degree
      < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [coreInterp, ← hT]
    exact Lagrange.degree_interpolate_lt _ hvs
  have hRdeg : R.degree < (k : ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro b hb
    have hbk : k ≤ b := by exact_mod_cast hb
    rw [hR, coeff_add, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge b (k + 1) with h | h
    · have hbk' : b = k := by omega
      subst hbk'
      rw [if_pos rfl, hγ]
      ring
    · rcases Nat.lt_or_ge b (k + m + 1) with h2 | h2
      · have hj : b - (k + 1) < m := by omega
        have hcoeff := hcoh ⟨b - (k + 1), hj⟩
        have hb' : k + 1 + (b - (k + 1)) = b := by omega
        rw [hb'] at hcoeff
        rw [hcoeff, if_neg (by omega)]
        ring
      · have hzero : (coreInterp dom T Q).coeff b = 0 := by
          refine Polynomial.coeff_eq_zero_of_degree_lt ?_
          exact lt_of_lt_of_le hIdeg (by exact_mod_cast h2)
        rw [hzero, if_neg (by omega)]
        ring
  refine ⟨fun i => R.eval (dom i), ⟨R, hRdeg, rfl⟩, fun i hi => ?_⟩
  show R.eval (dom i) = Q.eval (dom i) + γ * (dom i) ^ k
  rw [hR, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  congr 1
  rw [coreInterp]
  exact Lagrange.eval_interpolate_at_node _ hvs hi

open Classical in
/-- **THE MULTIPLICITY REDUCTION**: given the explainable-core supply, the
witness-mass law converts into a bad-scalar count at every band —
`C(n,k+m+1) ≤ #badSet · q^m · B`. -/
theorem deep_band_badSet_card_of_supply (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {B : ℕ} (hB : ExplainableCoreSupply dom k m B) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1)
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
          * (Fintype.card F) ^ m * B := by
  obtain ⟨Q₀, hmass, hcert⟩ := deep_band_witness_mass dom hk hhi (δ := δ)
  refine ⟨Q₀, ?_⟩
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set coh := Pm.filter (fun T => IsCoherent dom k m T Q₀) with hcoh
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ) with hbad
  -- the value map sends coherent cores into the bad set
  set val : Finset (Fin n) → F :=
    fun T => -(coreInterp dom T Q₀).coeff k with hval
  have hmaps : ∀ T ∈ coh, val T ∈ bad := by
    intro T hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcert T hT⟩
  -- each fiber of the value map is bounded by the supply
  have hfiber : ∀ γ, (coh.filter (fun T => val T = γ)).card ≤ B := by
    intro γ
    refine le_trans (Finset.card_le_card ?_) (hB
      (fun i => Q₀.eval (dom i) + γ * (dom i) ^ k))
    intro T hT
    obtain ⟨hTcoh, hTval⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTmem, hTc⟩ := Finset.mem_filter.mp hTcoh
    refine Finset.mem_filter.mpr ⟨hTmem, ?_⟩
    have hTcard : T.card = k + m + 1 :=
      (Finset.mem_powersetCard.mp hTmem).2
    have h := coherent_explains_line dom hTcard hTc
    rw [show -(coreInterp dom T Q₀).coeff k = val T from rfl, hTval] at h
    exact h
  -- fiberwise count
  have hcount : coh.card ≤ bad.card * B := by
    calc coh.card
        = ∑ γ ∈ bad, (coh.filter (fun T => val T = γ)).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ γ ∈ bad, B := Finset.sum_le_sum fun γ _ => hfiber γ
      _ = bad.card * B := by rw [Finset.sum_const, smul_eq_mul]
  -- assemble with the witness mass
  calc n.choose (k + m + 1)
      ≤ coh.card * (Fintype.card F) ^ m := hmass
    _ ≤ (bad.card * B) * (Fintype.card F) ^ m :=
        Nat.mul_le_mul_right _ hcount
    _ = bad.card * (Fintype.card F) ^ m * B := by ring

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.coherent_explains_line
#print axioms ProximityGap.Ownership.deep_band_badSet_card_of_supply
