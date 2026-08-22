/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._W15WidthKGapClosed

/-!
# LANE W15 part 7 (#466, thread ll:low-profile-fiber): THE UNIFORM STRIP EXISTENCE LEMMA —
# the Prouhet–Tarry–Escott pair makes the width-`k` dichotomy parametric over all fields
# of characteristic ≥ 17

## Position in the lane

Part 6 closed the width-`k` strip at `(n, k, a) = (16, 4, 11)` over `F = ZMod 17` and left
one thin sliver: a UNIFORM (all-fields) existence lemma for the symmetric coincidence
(disjoint `(k−1)`-sets `R, W` with `e₁(R) = e₁(W)`, `e₂(R) = e₂(W)`, `e₃` differing).

## The uniform coincidence: a PTE pair, not a counting argument

No fiber counting is needed.  The integer triples

  `R = {0, 5, 7}`,  `W = {1, 3, 8}`

form a degree-2 Prouhet–Tarry–Escott pair: `e₁ = 12` and `e₂ = 35` hold as INTEGER
identities (hence in every commutative ring, every characteristic), while
`e₃(W) − e₃(R) = 24 − 0 = 24`.  Equivalently, the single polynomial identity

  `x(x − 5)(x − 7) − 24 = (x − 1)(x − 3)(x − 8)`     (`pte_vieta`, proved by `ring`)

shows the cubic `e = X(X−5)(X−7)` (roots `R`) takes the CONSTANT value `24` on all of
`W` — in every commutative ring.  The only field-dependent inputs are:

* the sixteen domain points `0, …, 15` are distinct — characteristic `0` or `≥ 17`;
* `c* = 24 ≠ 0` — characteristic `∉ {2, 3}` (implied by the above).

Disjointness of `R` and `W` is automatic (same-`(e₁,e₂)`-fiber cubics differ by the
nonzero constant `24`, so they share no roots — here it is just `0..15` distinctness).

Probe `scripts/probes/probe_466_w15_strip_uniform_pte.py` (deterministic, exit 0)
verifies the assembled line at every prime `17 ≤ p < 200` (exactly — `Λ = 2`, safe,
large-zero — for `p ≤ 31`; certificate-level beyond).

## Headlines

1. `pte_vieta` / `pte_symmetric_coincidence` — the coincidence identities (char-free).
2. `strip_16_4_11_L_one_refuted_uniform` — for EVERY finite field `F` in which
   `(m : F) ≠ 0` for `1 ≤ m ≤ 15` (i.e. characteristic `≥ 17`, any `q = p^e`):
   `¬ LargeZeroSafeLineListBudgeted (uniDom …) 4 11 1` on the standard cast domain.
   The width-`k` strip refutation is now PARAMETRIC with the explicit bound `Q₀ = 17`
   (which is also trivially necessary: a 16-point domain needs `q ≥ 16`).
3. `strip_16_4_11_L_one_refuted_zmod` — the prime-field corollary: every prime `p ≥ 17`.

With parts 3–6 the dichotomy at the `n = 16, k = 4` family is now uniform: for every
finite field of characteristic `≥ 17` and the standard domain, `L_near = 1` holds at
`a ≥ 12` (UD-plus, part 3) and fails at `9 ≤ a ≤ 11` (two-block / secant-pair — the
two-block refuter of part 4 is already field-uniform, and this file makes the strip rung
uniform as well).

## Honesty

* The uniform statement is for the STANDARD cast domain (and any characteristic-`≥ 17`
  finite field); for an ARBITRARY 16-point domain in a large field, a symmetric
  coincidence inside the domain is a codimension-2 condition and can genuinely fail —
  the per-`dom` question is not (and cannot be) closed uniformly in `dom`.  The residual
  `LargeZeroSafeLineListBudgeted` is `dom`-indexed, and the campaign consumes it at
  standard domains.
* `k − 1 = 3` (the campaign-relevant case) is what the PTE pair covers; general `k`
  needs degree-`(k−2)` PTE pairs (they exist over `ℤ` for all sizes — Prouhet's
  construction — but are not formalized here).

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W15StripExistenceUniform

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LineListMCAWeld
open ProximityGap.Frontier.W15SafeBranchLinearCeiling
open ProximityGap.Frontier.W15WidthKGapClosed

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### 1. The PTE coincidence (characteristic-free identities) -/

/-- **The PTE–Vieta identity**: the cubic with roots `{0, 5, 7}` takes the constant
value `24` on `{1, 3, 8}` — in every commutative ring. -/
theorem pte_vieta (x : F) :
    x * (x - 5) * (x - 7) - 24 = (x - 1) * (x - 3) * (x - 8) := by ring

/-- The symmetric-function coincidence of the PTE pair `R = {0,5,7}`, `W = {1,3,8}`:
`e₁` and `e₂` match identically; `e₃` differs by `24`. -/
theorem pte_symmetric_coincidence :
    ((0 : F) + 5 + 7 = 1 + 3 + 8) ∧
      ((0 : F) * 5 + 0 * 7 + 5 * 7 = 1 * 3 + 1 * 8 + 3 * 8) ∧
      ((1 : F) * 3 * 8 - 0 * 5 * 7 = 24) := by norm_num

/-! ### 2. The uniform domain and line data -/

/-- The standard cast domain function `i ↦ (i : F)`. -/
def uniDomFun : Fin 16 → F := fun i => (i.val : F)

/-- Small nonzero naturals stay nonzero: the working characteristic hypothesis. -/
def CharGe17 (F : Type) [Field F] : Prop :=
  ∀ m : ℕ, 0 < m → m ≤ 15 → (m : F) ≠ 0

/-- The standard 16-point cast domain, injective under `CharGe17`. -/
def uniDom (hchar : CharGe17 F) : Fin 16 ↪ F where
  toFun := uniDomFun
  inj' := by
    intro i j h
    by_contra hne
    rcases Nat.lt_or_ge i.val j.val with hlt | hge
    · have hz : ((j.val - i.val : ℕ) : F) = 0 := by
        push_cast [Nat.cast_sub hlt.le]
        simp only [uniDomFun] at h
        rw [h]
        ring
      exact hchar (j.val - i.val) (by omega) (by omega) hz
    · have hlt : j.val < i.val := by
        rcases Nat.lt_or_ge j.val i.val with h' | h'
        · exact h'
        · exact absurd (Fin.ext (le_antisymm h' hge)) hne
      have hz : ((i.val - j.val : ℕ) : F) = 0 := by
        push_cast [Nat.cast_sub hlt.le]
        simp only [uniDomFun] at h
        rw [h]
        ring
      exact hchar (i.val - j.val) (by omega) (by omega) hz

/-- The strip codeword: `e = X(X−5)(X−7)` on the standard domain. -/
def ePTE : Fin 16 → F := fun i => (i.val : F) * ((i.val : F) - 5) * ((i.val : F) - 7)

/-- The zero-block `P = R ∪ D₀ = {0,5,7} ∪ {2,4,6,9}`. -/
def pU : Finset (Fin 16) := {0, 5, 7, 2, 4, 6, 9}

/-- The `e`-block `D₁ = {10, 11, 12, 13}`. -/
def dU : Finset (Fin 16) := {10, 11, 12, 13}

/-- The support design: `u₀ = e(15) − 24 = 1176` at index `15`, `0` at the other support
points (`1, 3, 8, 14`). -/
def wU : Fin 16 → F := fun i => if i = 15 then 1176 else 0

theorem ePTE_mem_rsCode (hchar : CharGe17 F) :
    ePTE ∈ (rsCode (uniDom hchar) 4 : Submodule F (Fin 16 → F)) := by
  refine ⟨X * (X - C 5) * (X - C 7), ?_, ?_⟩
  · have hm : (X * (X - C (5 : F)) * (X - C 7)).Monic :=
      (monic_X.mul (monic_X_sub_C 5)).mul (monic_X_sub_C 7)
    have hdeg : (X * (X - C (5 : F)) * (X - C 7)).natDegree = 3 := by
      rw [(monic_X.mul (monic_X_sub_C 5)).natDegree_mul (monic_X_sub_C 7),
        monic_X.natDegree_mul (monic_X_sub_C 5), natDegree_X, natDegree_X_sub_C,
        natDegree_X_sub_C]
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hdeg]
    exact_mod_cast (by norm_num : (3 : ℕ) < 4)
  · funext i
    simp [ePTE, uniDom, uniDomFun, eval_mul, eval_sub, eval_X, eval_C]

/-- `(24 : F) ≠ 0` under the characteristic hypothesis (`24 = 2·2·2·3`). -/
theorem twentyFour_ne_zero (hchar : CharGe17 F) : (24 : F) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := by exact_mod_cast hchar 2 (by norm_num) (by norm_num)
  have h3 : (3 : F) ≠ 0 := by exact_mod_cast hchar 3 (by norm_num) (by norm_num)
  have h24 : (24 : F) = 2 * 2 * 2 * 3 := by norm_num
  rw [h24]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3

theorem ePTE_ne_zero (hchar : CharGe17 F) : ePTE (F := F) ≠ 0 := by
  intro h
  have h1 := congrFun h ⟨1, by norm_num⟩
  simp only [ePTE, Pi.zero_apply] at h1
  have hval : ((1 : ℕ) : F) * (((1 : ℕ) : F) - 5) * (((1 : ℕ) : F) - 7) = 24 := by
    push_cast
    ring
  rw [hval] at h1
  exact twentyFour_ne_zero hchar h1

/-- `e ≠ 0` on `D₁`: the points `10..13` avoid the roots `{0, 5, 7}`. -/
theorem ePTE_ne_zero_on_dU (hchar : CharGe17 F) : ∀ i ∈ dU, ePTE (F := F) i ≠ 0 := by
  have hfac : ∀ x y : ℕ, y < x → x ≤ 15 → ((x : ℕ) : F) - ((y : ℕ) : F) ≠ 0 := by
    intro x y hlt hx h
    have hz : ((x - y : ℕ) : F) = 0 := by
      push_cast [Nat.cast_sub hlt.le]
      rw [sub_eq_zero] at h
      rw [h]
      ring
    exact hchar (x - y) (by omega) (by omega) hz
  have hpoint : ∀ x : ℕ, 7 < x → x ≤ 15 →
      ((x : ℕ) : F) * (((x : ℕ) : F) - 5) * (((x : ℕ) : F) - 7) ≠ 0 := by
    intro x h7 h15
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact hchar x (by omega) h15
    · have := hfac x 5 (by omega) h15
      exact_mod_cast this
    · have := hfac x 7 (by omega) h15
      exact_mod_cast this
  intro i hi
  fin_cases hi
  · exact hpoint 10 (by norm_num) (by norm_num)
  · exact hpoint 11 (by norm_num) (by norm_num)
  · exact hpoint 12 (by norm_num) (by norm_num)
  · exact hpoint 13 (by norm_num) (by norm_num)

/-! ### 3. The uniform strip refutation -/

/-- The appearance certificate for the codeword `0` at `γ = 0`. -/
def t0U : Finset (Fin 16) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 14}

/-- The appearance certificate for the codeword `e` at `γ = 24`. -/
def t1U : Finset (Fin 16) := {0, 1, 3, 5, 7, 8, 10, 11, 12, 13, 15}

open Classical in
/-- **HEADLINE: the uniform strip refutation.**  For every finite field `F` of
characteristic `≥ 17` (hypothesis `CharGe17`, any `q = p^e`), the standard-domain
near-code list budget `L = 1` is FALSE at the strip shape `(k, a) = (4, 11)`:

  `¬ LargeZeroSafeLineListBudgeted (uniDom hchar) 4 11 1`.

The two appearing codewords are `0` and the PTE cubic `e = X(X−5)(X−7)`, sharing their
support votes on `W = {1, 3, 8}` where `e ≡ 24` (`pte_vieta`).  Explicit bound
`Q₀ = 17`. -/
theorem strip_16_4_11_L_one_refuted_uniform (hchar : CharGe17 F) :
    ¬ LargeZeroSafeLineListBudgeted (uniDom (F := F) hchar) 4 11 1 := by
  refine secantPair_not_largeZeroSafeLineListBudgeted_one (uniDom hchar) (by norm_num)
    ePTE wU (ePTE_mem_rsCode hchar) (ePTE_ne_zero hchar) (P := pU) (D₁ := dU)
    (γ₀ := 0) (γ₁ := 24)
    (by decide) (ePTE_ne_zero_on_dU hchar) (by decide) (by decide) (by decide)
    (by norm_num) ?_ ?_
  · -- codeword 0 at γ = 0 on t0U
    have hpt : ∀ i ∈ t0U,
        (0 : F) = secantOffset pU dU ePTE wU i + (0 : F) • secantDirection pU dU i := by
      intro i hi
      fin_cases hi <;>
        · simp +decide only [secantOffset, secantDirection, wU, pU, dU, smul_eq_mul,
            mul_zero, mul_one, add_zero, zero_add, zero_mul]
          try norm_num
    have hsub : t0U ⊆ agreeSet (0 : Fin 16 → F)
        (fun i => secantOffset pU dU ePTE wU i + (0 : F) • secantDirection pU dU i) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hpt i hi⟩
    calc (11 : ℕ) = t0U.card := by decide
      _ ≤ _ := Finset.card_le_card hsub
  · -- codeword e at γ = 24 on t1U
    have hpt : ∀ i ∈ t1U,
        ePTE (F := F) i
          = secantOffset pU dU ePTE wU i + (24 : F) • secantDirection pU dU i := by
      intro i hi
      fin_cases hi <;>
        · simp +decide only [secantOffset, secantDirection, wU, pU, dU, ePTE,
            smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
          try push_cast
          try ring_nf
          try norm_num
    have hsub : t1U ⊆ agreeSet (ePTE (F := F))
        (fun i => secantOffset pU dU ePTE wU i + (24 : F) • secantDirection pU dU i) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hpt i hi⟩
    calc (11 : ℕ) = t1U.card := by decide
      _ ≤ _ := Finset.card_le_card hsub

/-- `ZMod p` satisfies the characteristic hypothesis for every prime `p ≥ 17`. -/
theorem zmod_charGe17 (p : ℕ) [Fact p.Prime] (hp : 17 ≤ p) : CharGe17 (ZMod p) := by
  intro m h1 h2 hz
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hdvd := (ZMod.natCast_eq_zero_iff m p).mp hz
  exact absurd (Nat.le_of_dvd h1 hdvd) (by omega)

/-- The prime-field corollary: every prime `p ≥ 17`. -/
theorem strip_16_4_11_L_one_refuted_zmod (p : ℕ) [Fact p.Prime] (hp : 17 ≤ p) :
    ¬ LargeZeroSafeLineListBudgeted (uniDom (zmod_charGe17 p hp)) 4 11 1 :=
  strip_16_4_11_L_one_refuted_uniform _

end ProximityGap.Frontier.W15StripExistenceUniform

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W15StripExistenceUniform.pte_vieta
#print axioms ProximityGap.Frontier.W15StripExistenceUniform.pte_symmetric_coincidence
#print axioms ProximityGap.Frontier.W15StripExistenceUniform.ePTE_mem_rsCode
#print axioms ProximityGap.Frontier.W15StripExistenceUniform.twentyFour_ne_zero
#print axioms ProximityGap.Frontier.W15StripExistenceUniform.ePTE_ne_zero
#print axioms ProximityGap.Frontier.W15StripExistenceUniform.ePTE_ne_zero_on_dU
#print axioms
  ProximityGap.Frontier.W15StripExistenceUniform.strip_16_4_11_L_one_refuted_uniform
#print axioms
  ProximityGap.Frontier.W15StripExistenceUniform.strip_16_4_11_L_one_refuted_zmod
