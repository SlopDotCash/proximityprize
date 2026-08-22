/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSmallPoolAssembly

/-!
# `SmallPoolClosure` DISCHARGED: the small-pool branch is an unconditional theorem

Successor of `_P1RateQuarterSmallPoolAssembly`.  That file left exactly one named Prop
open on the small-pool side: `SmallPoolClosure` — the marginal-partition counting-glue
wiring the fiber ledger over the per-`m` `Z`-relative Johnson caps, uniformly in the pool
size `F ≤ F₀ = 75018133`.  **This file proves it** (`smallPoolClosure_holds`), so the
P1 predecessor pin's open content shrinks from `SmallPoolClosure ∧ StallResidual` to
`StallResidual` alone (`predecessor_budget_of_stall`).

**The marginal partition.**  Fix a bad family and a base scalar `γ₀ ∈ G` with pool
`F = |{D ≠ 0}| ≤ F₀`.  Every other bad scalar rides a divided-difference pencil through
the base (`pencilOf`), so `#bad ≤ 1 + Σ_π fib(π)` over the pencil image `P`.  Each fiber
draws `fib(π)·(T − A_π)` disjoint votes from the shared pool (`riders_mul_le_Dsupport`)
and is itself capped by the pool (`riders_card_le_pool`), so `fib(π) ≤ F ≤ F₀` and every
pencil carrying `≥ m` riders is aligned at `A_π ≥ T − ⌊F/m⌋`.  The layer-cake identity
(`sum_layer_cake`) rewrites `Σ_π fib(π) = Σ_{m=1}^{F₀} #{π : fib(π) ≥ m}`, and each level
set is a through-base pencil family Johnson-packed inside `{D = 0}`
(`dirFamily_johnson_on_Dzero`), of cardinality `|Z| = N − F`.

**The uniform per-level caps** (all `F ≤ F₀`, proved as one-variable coefficientwise
polynomial dominations after the additive substitution `x := F₀ − F` resp.
`y := ⌊F₀/m⌋ − ⌊F/m⌋`):

* level `m = 1` (`cap_arith_m1`): `#{π : fib ≥ 1} ≤ 657668325` — the boundary count,
  worst at `F = F₀` where the exact-diagonal division is pinned by
  `657668326·378645484 = 249023141609739784 > 249023141355186198 = 998723691·249341378`;
* level `m = 2` (`cap_arith_m2`): `≤ 7`, via `n ≤ N − 2⌊F/2⌋` monotonisation;
* levels `m ≥ 3` (`cap_arith_m3`): `≤ 5` each, via alignment `≥ T − ⌊F/3⌋`.

Ledger: `#bad ≤ 1 + 657668325 + 7 + 5·(F₀ − 2) = 1032758988 ≤ N = 1073741824` — the
uniform-cap closed bound of `ledger_uniform_caps_le_N`, now a kernel theorem
(`smallPool_budget`).

**Consequences.**

* `smallPoolClosure_holds : ∀ dom, SmallPoolClosure dom` — the named residual of the
  assembly file is DISCHARGED (axiom-clean, no new hypotheses).
* `predecessor_budget_of_stall`: `StallResidual dom → every bad family has ≤ N scalars` —
  the P1 predecessor pin through the counting branch now has the SINGLE open residual
  `StallResidual` (pools `F ≥ F₀ + 1`, the sub-Johnson-on-`Z` stall band): the small-pool
  dichotomy branch is closed unconditionally.

Probe cross-check: `scripts/probes/probe_rate_quarter_p1_dcharge_derecursion.py`
(exact greedy optimum `882722755` at `F₀`; the uniform caps `{m=1: 657668325, m=2: ≤7,
m≥3: ≤5}` swept over all `F ≤ F₀`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolClosureDischarged

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterLayerCakeBudget
open ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolAssembly
open ProximityGap.SharedFreshPencil

local instance localInstance_P1RateQuarterSmallPoolClosureDischarged_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterSmallPoolClosureDischarged_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The layer-cake identity -/

/-- **Layer cake**: a sum of `ℕ`-values bounded by `B` equals the sum of its level-set
counts over `m ∈ [1, B]`. -/
theorem sum_layer_cake {κ : Type*} [DecidableEq κ] (s : Finset κ) (f : κ → ℕ) (B : ℕ)
    (hf : ∀ a ∈ s, f a ≤ B) :
    ∑ a ∈ s, f a =
      ∑ m ∈ Finset.Icc 1 B, (s.filter (fun a => m ≤ f a)).card := by
  classical
  calc ∑ a ∈ s, f a
      = ∑ a ∈ s, ∑ m ∈ Finset.Icc 1 B, (if m ≤ f a then 1 else 0) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [← Finset.card_filter]
        have hfil : (Finset.Icc 1 B).filter (fun m => m ≤ f a) =
            Finset.Icc 1 (f a) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_Icc]
          have := hf a ha
          omega
        rw [hfil, Nat.card_Icc]
        omega
    _ = ∑ m ∈ Finset.Icc 1 B, ∑ a ∈ s, (if m ≤ f a then 1 else 0) := Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc 1 B, (s.filter (fun a => m ≤ f a)).card := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.card_filter]

/-! ## The three uniform per-level cap inequalities (one-variable, coefficientwise) -/

/-- **Level `m = 1` cap arithmetic**, uniform in `F ≤ F₀`: with `n = N − F`,
`a = T − F`, the Johnson ratio stays below `657668326`.  Substituting `x := F₀ − F`
makes everything additive; the constant term is the pinned boundary division, and the
`x`- and `x²`-coefficients are strictly dominated. -/
theorem cap_arith_m1 (Fc : ℕ) (hF : Fc ≤ 75018133) :
    (1073741824 - Fc) * ((592794966 - Fc) - 268435455) <
      657668326 * ((592794966 - Fc) ^ 2 - (1073741824 - Fc) * 268435455) := by
  obtain ⟨x, hx⟩ : ∃ x, Fc + x = 75018133 := ⟨75018133 - Fc, by omega⟩
  have e1 : 1073741824 - Fc = 998723691 + x := by omega
  have e2 : 592794966 - Fc = 517776833 + x := by omega
  rw [e1, e2]
  have e3 : 517776833 + x - 268435455 = 249341378 + x := by omega
  rw [e3]
  have hin : (998723691 + x) * 268435455 ≤ (517776833 + x) ^ 2 := by
    have r1 : (998723691 + x) * 268435455
        = 998723691 * 268435455 + 268435455 * x := by ring
    have r2 : (517776833 + x) ^ 2
        = (517776833 * 517776833 + 1035553666 * x) + x * x := by ring
    rw [r1, r2]
    have c0 : 998723691 * 268435455 ≤ 517776833 * 517776833 := by norm_num
    have c1 : 268435455 * x ≤ 1035553666 * x :=
      Nat.mul_le_mul_right x (by norm_num)
    exact le_trans (Nat.add_le_add c0 c1) (Nat.le_add_right _ _)
  have hadd : (998723691 + x) * (249341378 + x)
      + 657668326 * ((998723691 + x) * 268435455)
      < 657668326 * (517776833 + x) ^ 2 := by
    have r1 : (998723691 + x) * (249341378 + x)
        + 657668326 * ((998723691 + x) * 268435455)
        = (998723691 * 249341378 + 657668326 * (998723691 * 268435455)
            + (249341378 + 998723691 + 657668326 * 268435455) * x) + x * x := by
      ring
    have r2 : 657668326 * (517776833 + x) ^ 2
        = (657668326 * (517776833 * 517776833)
            + (657668326 * 1035553666) * x) + 657668326 * (x * x) := by
      ring
    rw [r1, r2]
    have c0 : 998723691 * 249341378 + 657668326 * (998723691 * 268435455)
        < 657668326 * (517776833 * 517776833) := by norm_num
    have c1 : (249341378 + 998723691 + 657668326 * 268435455) * x
        ≤ (657668326 * 1035553666) * x :=
      Nat.mul_le_mul_right x (by norm_num)
    have c2 : x * x ≤ 657668326 * (x * x) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le c0 c1) c2
  generalize hA : (998723691 + x) * (249341378 + x) = A at hadd ⊢
  generalize hS : (517776833 + x) ^ 2 = S at hin hadd ⊢
  generalize hQ : (998723691 + x) * 268435455 = Q at hin hadd ⊢
  omega

/-- **Level `m = 2` cap arithmetic**, uniform in `q = ⌊F/2⌋ ≤ ⌊F₀/2⌋`: with the
monotonised `n' = N − 2q` and `a = T − q`, the Johnson ratio stays below `8`. -/
theorem cap_arith_m2 (q : ℕ) (hq : q ≤ 37509066) :
    (1073741824 - 2 * q) * ((592794966 - q) - 268435455) <
      8 * ((592794966 - q) ^ 2 - (1073741824 - 2 * q) * 268435455) := by
  obtain ⟨y, hy⟩ : ∃ y, q + y = 37509066 := ⟨37509066 - q, by omega⟩
  have e1 : 1073741824 - 2 * q = 998723692 + 2 * y := by omega
  have e2 : 592794966 - q = 555285900 + y := by omega
  rw [e1, e2]
  have e3 : 555285900 + y - 268435455 = 286850445 + y := by omega
  rw [e3]
  have hin : (998723692 + 2 * y) * 268435455 ≤ (555285900 + y) ^ 2 := by
    have r1 : (998723692 + 2 * y) * 268435455
        = 998723692 * 268435455 + 536870910 * y := by ring
    have r2 : (555285900 + y) ^ 2
        = (555285900 * 555285900 + 1110571800 * y) + y * y := by ring
    rw [r1, r2]
    have c0 : 998723692 * 268435455 ≤ 555285900 * 555285900 := by norm_num
    have c1 : 536870910 * y ≤ 1110571800 * y :=
      Nat.mul_le_mul_right y (by norm_num)
    exact le_trans (Nat.add_le_add c0 c1) (Nat.le_add_right _ _)
  have hadd : (998723692 + 2 * y) * (286850445 + y)
      + 8 * ((998723692 + 2 * y) * 268435455)
      < 8 * (555285900 + y) ^ 2 := by
    have r1 : (998723692 + 2 * y) * (286850445 + y)
        + 8 * ((998723692 + 2 * y) * 268435455)
        = (998723692 * 286850445 + 8 * (998723692 * 268435455)
            + (2 * 286850445 + 998723692 + 16 * 268435455) * y) + 2 * (y * y) := by
      ring
    have r2 : 8 * (555285900 + y) ^ 2
        = (8 * (555285900 * 555285900) + (16 * 555285900) * y) + 8 * (y * y) := by
      ring
    rw [r1, r2]
    have c0 : 998723692 * 286850445 + 8 * (998723692 * 268435455)
        < 8 * (555285900 * 555285900) := by norm_num
    have c1 : (2 * 286850445 + 998723692 + 16 * 268435455) * y
        ≤ (16 * 555285900) * y :=
      Nat.mul_le_mul_right y (by norm_num)
    have c2 : 2 * (y * y) ≤ 8 * (y * y) :=
      Nat.mul_le_mul_right _ (by norm_num)
    exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le c0 c1) c2
  generalize hA : (998723692 + 2 * y) * (286850445 + y) = A at hadd ⊢
  generalize hS : (555285900 + y) ^ 2 = S at hin hadd ⊢
  generalize hQ : (998723692 + 2 * y) * 268435455 = Q at hin hadd ⊢
  omega

/-- **Levels `m ≥ 3` cap arithmetic**, uniform in `q = ⌊F/3⌋ ≤ ⌊F₀/3⌋`: with the
monotonised `n' = N − 3q` and `a = T − q`, the Johnson ratio stays below `6`. -/
theorem cap_arith_m3 (q : ℕ) (hq : q ≤ 25006044) :
    (1073741824 - 3 * q) * ((592794966 - q) - 268435455) <
      6 * ((592794966 - q) ^ 2 - (1073741824 - 3 * q) * 268435455) := by
  obtain ⟨y, hy⟩ : ∃ y, q + y = 25006044 := ⟨25006044 - q, by omega⟩
  have e1 : 1073741824 - 3 * q = 998723692 + 3 * y := by omega
  have e2 : 592794966 - q = 567788922 + y := by omega
  rw [e1, e2]
  have e3 : 567788922 + y - 268435455 = 299353467 + y := by omega
  rw [e3]
  have hin : (998723692 + 3 * y) * 268435455 ≤ (567788922 + y) ^ 2 := by
    have r1 : (998723692 + 3 * y) * 268435455
        = 998723692 * 268435455 + 805306365 * y := by ring
    have r2 : (567788922 + y) ^ 2
        = (567788922 * 567788922 + 1135577844 * y) + y * y := by ring
    rw [r1, r2]
    have c0 : 998723692 * 268435455 ≤ 567788922 * 567788922 := by norm_num
    have c1 : 805306365 * y ≤ 1135577844 * y :=
      Nat.mul_le_mul_right y (by norm_num)
    exact le_trans (Nat.add_le_add c0 c1) (Nat.le_add_right _ _)
  have hadd : (998723692 + 3 * y) * (299353467 + y)
      + 6 * ((998723692 + 3 * y) * 268435455)
      < 6 * (567788922 + y) ^ 2 := by
    have r1 : (998723692 + 3 * y) * (299353467 + y)
        + 6 * ((998723692 + 3 * y) * 268435455)
        = (998723692 * 299353467 + 6 * (998723692 * 268435455)
            + (3 * 299353467 + 998723692 + 18 * 268435455) * y) + 3 * (y * y) := by
      ring
    have r2 : 6 * (567788922 + y) ^ 2
        = (6 * (567788922 * 567788922) + (12 * 567788922) * y) + 6 * (y * y) := by
      ring
    rw [r1, r2]
    have c0 : 998723692 * 299353467 + 6 * (998723692 * 268435455)
        < 6 * (567788922 * 567788922) := by norm_num
    have c1 : (3 * 299353467 + 998723692 + 18 * 268435455) * y
        ≤ (12 * 567788922) * y :=
      Nat.mul_le_mul_right y (by norm_num)
    have c2 : 3 * (y * y) ≤ 6 * (y * y) :=
      Nat.mul_le_mul_right _ (by norm_num)
    exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le c0 c1) c2
  generalize hA : (998723692 + 3 * y) * (299353467 + y) = A at hadd ⊢
  generalize hS : (567788922 + y) ^ 2 = S at hin hadd ⊢
  generalize hQ : (998723692 + 3 * y) * 268435455 = Q at hin hadd ⊢
  omega

/-! ## The generic level-count helper -/

/-- A through-base pencil family aligned at level `a` on `{D = 0}` is capped by `cap`
whenever the (subtraction-free) Johnson division at `(a, |Z|)` stays below `cap + 1`. -/
theorem level_card_le_of_arith (dom : Fin N ↪ F) (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)
    (Fam : Finset ((Fin N → F) × (Fin N → F))) (a cap : ℕ)
    (hmem : ∀ π ∈ Fam, π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom)
    (hbase : ∀ π ∈ Fam, ∀ i, π.1 i + γ₀ * π.2 i = p₀ i)
    (halign : ∀ π ∈ Fam, a ≤ (alignedSet u₀ u₁ π.1 π.2).card)
    (hK : k - 1 ≤ a)
    (hgap : (Dzero u₀ u₁ p₀ γ₀).card * (k - 1) ≤ a ^ 2)
    (harith : (Dzero u₀ u₁ p₀ γ₀).card * (a - (k - 1)) <
      (cap + 1) * (a ^ 2 - (Dzero u₀ u₁ p₀ γ₀).card * (k - 1))) :
    Fam.card ≤ cap := by
  have hcore := dirFamily_johnson_on_Dzero dom u₀ u₁ p₀ γ₀ Fam a hmem hbase halign hK
  have hsub := johnson_core_to_subtracted hK hgap hcore
  have hlt : Fam.card * (a ^ 2 - (Dzero u₀ u₁ p₀ γ₀).card * (k - 1)) <
      (cap + 1) * (a ^ 2 - (Dzero u₀ u₁ p₀ γ₀).card * (k - 1)) :=
    lt_of_le_of_lt hsub harith
  have := lt_of_mul_lt_mul_right hlt (Nat.zero_le _)
  omega

/-! ## The marginal-partition assembly: the small-pool budget theorem -/

/-- **The small-pool branch, unconditionally**: a bad family with SOME base scalar of
pool `F ≤ F₀ = 75018133` respects the budget `G.card ≤ N`.  Proof: fiber partition over
the through-base pencils, layer-cake over the rider counts, per-level `Z`-relative
Johnson caps (`m = 1`: `657668325`; `m = 2`: `7`; `m ≥ 3`: `5` each), and the uniform-cap
ledger `1 + 657668325 + 7 + 5·(F₀ − 2) = 1032758988 ≤ N`. -/
theorem smallPool_budget (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (γ₀ : F) (hγ₀ : γ₀ ∈ G)
    (hpool : (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ 75018133) :
    G.card ≤ N := by
  classical
  set Fc := (Dsupport u₀ u₁ (pf γ₀) γ₀).card with hFcdef
  set Z := (Dzero u₀ u₁ (pf γ₀) γ₀).card with hZdef
  have hFZ : Fc + Z = N := Dsupport_card_add_Dzero_card u₀ u₁ (pf γ₀) γ₀
  have hT := predecessorThreshold_eq
  have hNval : N = 1073741824 := by norm_num [N]
  have hk1 : k - 1 = 268435455 := by norm_num [k]
  have hZval : (Dzero u₀ u₁ (pf γ₀) γ₀).card = 1073741824 - Fc := by omega
  set P := (G.erase γ₀).image (pencilOf pf γ₀) with hPdef
  -- ## Per-pencil facts
  have hmemP : ∀ π ∈ P, π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom := by
    intro π hπ
    obtain ⟨γ₁, hγ₁, hπeq⟩ := Finset.mem_image.mp hπ
    have hγ₁G : γ₁ ∈ G := Finset.mem_of_mem_erase hγ₁
    rw [← hπeq]
    simp only [pencilOf]
    exact ⟨pencilBase_mem _ (hdata γ₀ hγ₀).2.1 (hdata γ₁ hγ₁G).2.1,
      pencilDir_mem _ (hdata γ₀ hγ₀).2.1 (hdata γ₁ hγ₁G).2.1⟩
  have hbaseP : ∀ π ∈ P, ∀ i, π.1 i + γ₀ * π.2 i = pf γ₀ i := by
    intro π hπ i
    obtain ⟨γ₁, hγ₁, hπeq⟩ := Finset.mem_image.mp hπ
    have h := congrFun (pencil_reproduces_first γ₀ γ₁ (pf γ₀) (pf γ₁)) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [← hπeq]
    simp only [pencilOf]
    exact h
  have hrides : ∀ π ∈ P, RidesAll dom u₀ u₁ π.1 π.2
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)) Sf := by
    intro π hπ γ hγ
    have hγe : γ ∈ G.erase γ₀ := (Finset.mem_filter.mp hγ).1
    have hγπ : pencilOf pf γ₀ γ = π := (Finset.mem_filter.mp hγ).2
    have hγne : γ ≠ γ₀ := (Finset.mem_erase.mp hγe).1
    have hγG : γ ∈ G := (Finset.mem_erase.mp hγe).2
    obtain ⟨hcard, hmem, hagree, hno⟩ := hdata γ hγG
    refine ⟨hcard, fun i hi => ?_, hno⟩
    have h2 := congrFun (pencil_reproduces_second (Ne.symm hγne) (pf γ₀) (pf γ)) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [← hγπ]
    simp only [pencilOf]
    rw [h2]
    exact hagree i hi
  have hγ₀fib : ∀ π : (Fin N → F) × (Fin N → F),
      γ₀ ∉ (G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π) := by
    intro π h
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  -- fiber cardinality is pool-capped
  have hcle : ∀ π ∈ P,
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card ≤ Fc := by
    intro π hπ
    exact riders_card_le_pool u₀ u₁ (pf γ₀) γ₀ dom
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)) Sf
      (hmemP π hπ).1 (hmemP π hπ).2 (hbaseP π hπ) (hrides π hπ) (hγ₀fib π)
  -- fiber votes are pool-charged
  have hvote : ∀ π ∈ P,
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card *
        (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) ≤ Fc := by
    intro π hπ
    exact riders_mul_le_Dsupport u₀ u₁ (pf γ₀) γ₀ dom
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)) Sf
      (hbaseP π hπ) (hrides π hπ) (hγ₀fib π)
  -- every pencil in the image has a nonempty fiber
  have hfib1 : ∀ π ∈ P,
      1 ≤ ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card := by
    intro π hπ
    obtain ⟨γ₁, hγ₁, hπeq⟩ := Finset.mem_image.mp hπ
    exact Finset.card_pos.mpr ⟨γ₁, Finset.mem_filter.mpr ⟨hγ₁, hπeq⟩⟩
  -- ## The fiber partition
  have hGsum : G.card = 1 +
      ∑ π ∈ P, ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card := by
    have hsplit : (G.erase γ₀).card + 1 = G.card := Finset.card_erase_add_one hγ₀
    have hfiber : (G.erase γ₀).card =
        ∑ π ∈ P, ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card :=
      Finset.card_eq_sum_card_fiberwise
        (fun γ hγ => Finset.mem_image_of_mem _ hγ)
    omega
  -- ## The layer cake over rider counts
  have hlc : ∑ π ∈ P, ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card =
      ∑ m ∈ Finset.Icc 1 75018133, (P.filter (fun π => m ≤
        ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card :=
    sum_layer_cake P
      (fun π => ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)
      75018133 (fun π hπ => le_trans (hcle π hπ) hpool)
  -- ## The Johnson gap at the boundary, uniform in F ≤ F₀
  have hj := johnson_condition_of_le_boundary (Fp := Fc) hpool
  rw [hT] at hj
  have hZN : N - Fc = Z := by omega
  rw [hZN] at hj
  -- hj : (592794966 - Fc) ^ 2 > Z * (k - 1)
  -- ## Level m = 1: at most 657668325 pencils
  have hlev1 : (P.filter (fun π => 1 ≤
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card
      ≤ 657668325 := by
    refine level_card_le_of_arith dom u₀ u₁ (pf γ₀) γ₀ _ (592794966 - Fc) 657668325
      (fun π hπ => hmemP π (Finset.mem_of_mem_filter π hπ))
      (fun π hπ => hbaseP π (Finset.mem_of_mem_filter π hπ)) ?_ ?_ ?_ ?_
    · intro π hπ
      have hπP := Finset.mem_of_mem_filter π hπ
      have h1 := (Finset.mem_filter.mp hπ).2
      have hv := hvote π hπP
      have hstep : 1 * (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) ≤
          ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card *
            (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) :=
        Nat.mul_le_mul_right _ h1
      omega
    · rw [hk1]
      omega
    · exact le_of_lt hj
    · rw [hk1, hZval]
      exact cap_arith_m1 Fc hpool
  -- ## Level m = 2: at most 7 pencils
  have hlev2 : (P.filter (fun π => 2 ≤
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ 7 := by
    refine level_card_le_of_arith dom u₀ u₁ (pf γ₀) γ₀ _ (592794966 - Fc / 2) 7
      (fun π hπ => hmemP π (Finset.mem_of_mem_filter π hπ))
      (fun π hπ => hbaseP π (Finset.mem_of_mem_filter π hπ)) ?_ ?_ ?_ ?_
    · intro π hπ
      have hπP := Finset.mem_of_mem_filter π hπ
      have h2 := (Finset.mem_filter.mp hπ).2
      have hv := hvote π hπP
      have hstep : 2 * (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) ≤
          ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card *
            (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) :=
        Nat.mul_le_mul_right _ h2
      omega
    · rw [hk1]
      omega
    · refine le_trans (le_of_lt hj) (Nat.pow_le_pow_left ?_ 2)
      omega
    · rw [hk1, hZval]
      have hA2 := cap_arith_m2 (Fc / 2) (by omega)
      have hle : 1073741824 - Fc ≤ 1073741824 - 2 * (Fc / 2) := by omega
      have s1 : (1073741824 - Fc) * ((592794966 - Fc / 2) - 268435455) ≤
          (1073741824 - 2 * (Fc / 2)) * ((592794966 - Fc / 2) - 268435455) :=
        Nat.mul_le_mul_right _ hle
      have s2 : 8 * ((592794966 - Fc / 2) ^ 2 -
            (1073741824 - 2 * (Fc / 2)) * 268435455) ≤
          8 * ((592794966 - Fc / 2) ^ 2 - (1073741824 - Fc) * 268435455) :=
        Nat.mul_le_mul_left 8
          (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hle) _)
      exact lt_of_le_of_lt s1 (lt_of_lt_of_le hA2 s2)
  -- ## Levels m ≥ 3: at most 5 pencils each
  have hlev3 : ∀ m ∈ Finset.Icc 3 75018133, (P.filter (fun π => m ≤
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ 5 := by
    intro m hm
    have hm3 : 3 ≤ m := (Finset.mem_Icc.mp hm).1
    refine level_card_le_of_arith dom u₀ u₁ (pf γ₀) γ₀ _ (592794966 - Fc / 3) 5
      (fun π hπ => hmemP π (Finset.mem_of_mem_filter π hπ))
      (fun π hπ => hbaseP π (Finset.mem_of_mem_filter π hπ)) ?_ ?_ ?_ ?_
    · intro π hπ
      have hπP := Finset.mem_of_mem_filter π hπ
      have hcm := (Finset.mem_filter.mp hπ).2
      have hv := hvote π hπP
      have hstep3 : 3 * (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) ≤
          m * (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) :=
        Nat.mul_le_mul_right _ hm3
      have hstepm : m * (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) ≤
          ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card *
            (predecessorThreshold - (alignedSet u₀ u₁ π.1 π.2).card) :=
        Nat.mul_le_mul_right _ hcm
      omega
    · rw [hk1]
      omega
    · refine le_trans (le_of_lt hj) (Nat.pow_le_pow_left ?_ 2)
      omega
    · rw [hk1, hZval]
      have hA3 := cap_arith_m3 (Fc / 3) (by omega)
      have hle : 1073741824 - Fc ≤ 1073741824 - 3 * (Fc / 3) := by omega
      have s1 : (1073741824 - Fc) * ((592794966 - Fc / 3) - 268435455) ≤
          (1073741824 - 3 * (Fc / 3)) * ((592794966 - Fc / 3) - 268435455) :=
        Nat.mul_le_mul_right _ hle
      have s2 : 6 * ((592794966 - Fc / 3) ^ 2 -
            (1073741824 - 3 * (Fc / 3)) * 268435455) ≤
          6 * ((592794966 - Fc / 3) ^ 2 - (1073741824 - Fc) * 268435455) :=
        Nat.mul_le_mul_left 6
          (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hle) _)
      exact lt_of_le_of_lt s1 (lt_of_lt_of_le hA3 s2)
  -- ## Assemble the ledger (Ico-peel form: `insert`-splits and `sum_const` rewrites on
  -- the width-`F₀` interval blow up the kernel; `sum_eq_sum_Ico_succ_bot` +
  -- `sum_le_card_nsmul` stay symbolic)
  rw [← Finset.Ico_add_one_right_eq_Icc] at hlc
  rw [Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (1:ℕ) < 75018133 + 1)] at hlc
  rw [Finset.sum_eq_sum_Ico_succ_bot (by norm_num : (1+1:ℕ) < 75018133 + 1)] at hlc
  simp only [Nat.reduceAdd] at hlc
  have hb : ∀ m ∈ Finset.Ico 3 75018134, (P.filter (fun π => m ≤
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤ 5 := by
    intro m hm
    have := Finset.mem_Ico.mp hm
    exact hlev3 m (Finset.mem_Icc.mpr (by omega))
  have hcard : (Finset.Ico 3 75018134).card = 75018131 := by rw [Nat.card_Ico]
  have htail : ∑ m ∈ Finset.Ico 3 75018134, (P.filter (fun π => m ≤
      ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card ≤
      75018131 * 5 := by
    calc ∑ m ∈ Finset.Ico 3 75018134, (P.filter (fun π => m ≤
          ((G.erase γ₀).filter (fun γ => pencilOf pf γ₀ γ = π)).card)).card
        ≤ (Finset.Ico 3 75018134).card • 5 := Finset.sum_le_card_nsmul _ _ 5 hb
      _ = 75018131 * 5 := by rw [hcard, smul_eq_mul]
  omega

/-! ## The discharge and the upgraded consumer -/

/-- **`SmallPoolClosure` is DISCHARGED**: the named residual of
`_P1RateQuarterSmallPoolAssembly` holds unconditionally, for every evaluation domain. -/
theorem smallPoolClosure_holds (dom : Fin N ↪ F) : SmallPoolClosure dom := by
  intro u₀ u₁ G Sf pf hdata hex
  obtain ⟨γ₀, hγ₀, hpool⟩ := hex
  exact smallPool_budget dom u₀ u₁ G Sf pf hdata γ₀ hγ₀ hpool

/-- **The single-residual form of the P1 predecessor pin**: the stall residual ALONE now
implies the full predecessor budget — the small-pool dichotomy branch is closed
unconditionally. -/
theorem predecessor_budget_of_stall (dom : Fin N ↪ F) (hstall : StallResidual dom) :
    ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N))
      (pf : F → Fin N → F),
      BadFamilyData dom u₀ u₁ G Sf pf → G.card ≤ N :=
  predecessor_budget_of_smallPool_and_stall dom (smallPoolClosure_holds dom) hstall

/-- The closed histogram at the boundary and the uniform-cap ledger, re-pinned here as the
numeric content of the theorem above: `1 + 657668325 + 7 + 5·(75018133 − 2) = 1032758988 ≤ N`. -/
theorem smallPool_ledger_value :
    1 + 657668325 + 7 + 5 * (75018133 - 2) = 1032758988 ∧ 1032758988 ≤ N := by
  constructor <;> norm_num [N]

end ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolClosureDischarged

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolClosureDischarged

#print axioms sum_layer_cake
#print axioms cap_arith_m1
#print axioms cap_arith_m2
#print axioms cap_arith_m3
#print axioms level_card_le_of_arith
#print axioms smallPool_budget
#print axioms smallPoolClosure_holds
#print axioms predecessor_budget_of_stall
#print axioms smallPool_ledger_value
