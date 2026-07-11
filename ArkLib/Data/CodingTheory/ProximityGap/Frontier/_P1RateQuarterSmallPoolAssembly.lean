/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterDChargeDerecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterLayerCakeBudget

/-!
# Small-pool assembly: the `Z`-relative Johnson machinery and the closure ledger

Final file of the P1 charge arc (session 2026-07-10).  Upgrades the small-pool branch
(`F ≤ F₀ = 75018133`, probe-pinned greedy optimum `882722755 ≤ N`) from probe arithmetic
toward a kernel theorem, in the coordinator's staged form.

**Landed stages:**

* **(a) `Z`-relative Johnson** (`johnson_core_rel`): the in-tree exact-diagonal
  `R15Bracket.johnson_core` transported to families of sets contained in an arbitrary
  ambient `Finset Z` — the count bound scales with `Z.card`, not `N`.  Instantiated for
  through-base pencil families packed by their aligned regions inside `{D = 0}`
  (`dirFamily_johnson_on_Dzero`).
* **(b) the pinned ledger arithmetic:**
  - `boundary_count_pinned`: at the worst pool `F₀ = 75018133`, the direction count at the
    boundary level `T − F₀ = 517776833` on `Z` is at most `657668325` (the `m = 1` ledger
    term; exact-diagonal division pinned by
    `657668326·378645484 = 249023141609739784 > 249023141355186198`);
  - `ledger_histogram_le_N`: the exact greedy value in closed histogram form,
    `1 + 657668325 + 7 + 5 + 27·4 + 3·(75018133 − 30) = 882722755 ≤ N` — the per-`m` caps
    `{m=1: 657668325, m=2: ≤7, m=3: ≤5, 4 ≤ m ≤ 30: ≤4, m ≥ 31: ≤3}` are the probe
    histogram at `F₀`; the probe sweep over `F ≤ F₀` confirms the uniform caps
    (`m=2` term `≤ 7` and `m ≥ 4` terms `≤ 5` for ALL `F ≤ F₀`, with
    `1 + 657668325 + 7 + 5·(F₀ − 2) = 1032758988 ≤ N` as the uniform-cap closed bound,
    `ledger_uniform_caps_le_N`).
* **(c) the dichotomy glue** (`predecessor_budget_of_smallPool_and_stall`): the honest
  named Prop `SmallPoolClosure` (the counting-glue that remains open in Lean: the
  marginal-partition wiring of the fiber ledger over the per-`m` Johnson caps, uniformly in
  `F ≤ F₀`) together with the stall residual implies the full predecessor budget
  `G.card ≤ N` for every bad family — the pin's open content is now EXACTLY
  `SmallPoolClosure ∧ StallResidual`, with all arithmetic discharged.

**Lane retrospective (the charge cone is complete).**  Session arc:
two-cover window REALIZED (`_P1RateQuarterTwoCoverWindow`) → heavy window CLOSED by the
global `D`-charge, realized geometry sterile (`_P1RateQuarterGlobalConsistencyCharge`) →
derecursion boundary `F₀ = 75018133` exact; small pool closed at probe level, stall
taxonomy (`_P1RateQuarterDChargeDerecursion`) → MDS-pool second charge literal but
double-stalls: threshold collapse below `k − 1` is permanent
(`_P1RateQuarterMDSPoolSecondCharge`) → this file: relative-Johnson machinery, pinned
ledger, dichotomy glue.  The three branches: heavy CLOSED (kernel), small-pool CLOSED
(arithmetic kernel-pinned, counting-glue = `SmallPoolClosure`), stall band = beyond-Johnson
MDS agreement families = the prize wall (no lane artifact: the P1 counting cone converges
to the same wall as the B-side).

Probe: `scripts/probes/probe_rate_quarter_p1_dcharge_derecursion.py` and the histogram /
sweep commands recorded in the kb note.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolAssembly

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterGlobalConsistencyCharge
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterLayerCakeBudget

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Stage (a): the `Z`-relative Johnson core -/

/-- Transport of subsets of an ambient `Finset` to its attached subtype preserves cards. -/
theorem card_attach_filter {α : Type*} [DecidableEq α] (Z S : Finset α) (hS : S ⊆ Z) :
    (Z.attach.filter (fun x => x.1 ∈ S)).card = S.card := by
  classical
  refine Eq.symm (Finset.card_bij'
    (fun b hb => (⟨b, hS hb⟩ : {x // x ∈ Z}))
    (fun x _ => x.1) ?_ ?_ ?_ ?_)
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hb⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro b hb
    rfl
  · intro a ha
    rfl

/-- **`Z`-relative exact-diagonal Johnson**: for a family of sets CONTAINED in an ambient
`Finset Z`, the Johnson double count runs over `Z.card` rather than the whole domain. -/
theorem johnson_core_rel {α : Type*} [DecidableEq α] (Z : Finset α)
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (A : κ → Finset α) (a p : ℕ)
    (hsub : ∀ i ∈ s, A i ⊆ Z)
    (ha : ∀ i ∈ s, a ≤ (A i).card)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ((A i ∩ A j)).card ≤ p)
    (hap : p ≤ a) :
    s.card * a ^ 2 + Z.card * p ≤ Z.card * a + s.card * (Z.card * p) := by
  classical
  have hcore := R15Bracket.johnson_core (ι := {x // x ∈ Z}) s
    (fun i => Z.attach.filter (fun x => x.1 ∈ A i)) a p
    (fun i hi => by
      show a ≤ (Z.attach.filter (fun x => x.1 ∈ A i)).card
      rw [card_attach_filter Z (A i) (hsub i hi)]
      exact ha i hi)
    (fun i hi j hj hij => by
      show ((Z.attach.filter (fun x => x.1 ∈ A i)) ∩
          (Z.attach.filter (fun x => x.1 ∈ A j))).card ≤ p
      have hinter : (Z.attach.filter (fun x => x.1 ∈ A i)) ∩
          (Z.attach.filter (fun x => x.1 ∈ A j)) =
          Z.attach.filter (fun x => x.1 ∈ A i ∩ A j) := by
        ext x
        simp [Finset.mem_filter, Finset.mem_inter, and_assoc, and_left_comm]
      rw [hinter, card_attach_filter Z (A i ∩ A j)
        (fun x hx => hsub i hi (Finset.mem_inter.mp hx).1)]
      exact hpair i hi j hj hij)
    hap
  have hcard : Fintype.card {x // x ∈ Z} = Z.card := Fintype.card_coe Z
  rw [hcard] at hcore
  exact hcore

/-- **Through-base pencil families, Johnson-packed inside `{D = 0}`**: pairwise-distinct
pencil pairs through one base, with aligned regions of size `≥ a`, obey the `Z`-relative
Johnson bound with `Z = Dzero` (aligned regions sink into `{D = 0}`; pairwise overlaps are
`≤ k − 1`). -/
theorem dirFamily_johnson_on_Dzero (dom : Fin N ↪ F) (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)
    (Fam : Finset ((Fin N → F) × (Fin N → F))) (a : ℕ)
    (hmem : ∀ π ∈ Fam, π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom)
    (hbase : ∀ π ∈ Fam, ∀ i, π.1 i + γ₀ * π.2 i = p₀ i)
    (halign : ∀ π ∈ Fam, a ≤ (alignedSet u₀ u₁ π.1 π.2).card)
    (hap : k - 1 ≤ a) :
    Fam.card * a ^ 2 + (Dzero u₀ u₁ p₀ γ₀).card * (k - 1) ≤
      (Dzero u₀ u₁ p₀ γ₀).card * a +
        Fam.card * ((Dzero u₀ u₁ p₀ γ₀).card * (k - 1)) := by
  classical
  refine johnson_core_rel (Dzero u₀ u₁ p₀ γ₀) Fam
    (fun π => alignedSet u₀ u₁ π.1 π.2) a (k - 1)
    (fun π hπ => alignedSet_subset_Dzero u₀ u₁ p₀ γ₀ (hbase π hπ))
    halign
    (fun π hπ π' hπ' hne => alignedSet_inter_card_lt_k dom u₀ u₁
      (hmem π hπ).1 (hmem π hπ).2 (hmem π' hπ').1 (hmem π' hπ').2
      (by
        intro h
        exact hne (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))))
    hap

/-! ## Stage (b): the pinned ledger arithmetic -/

/-- **The boundary-level count at the worst pool**: with `|{D=0}| = N − F₀ = 998723691`,
the through-base pencil family aligned at level `T − F₀ = 517776833` has at most
`657668325` members — the `m = 1` term of the ledger, exactly the probe value. -/
theorem boundary_count_pinned (dom : Fin N ↪ F) (u₀ u₁ p₀ : Fin N → F) (γ₀ : F)
    (Fam : Finset ((Fin N → F) × (Fin N → F)))
    (hz : (Dzero u₀ u₁ p₀ γ₀).card = 998723691)
    (hmem : ∀ π ∈ Fam, π.1 ∈ predecessorCode dom ∧ π.2 ∈ predecessorCode dom)
    (hbase : ∀ π ∈ Fam, ∀ i, π.1 i + γ₀ * π.2 i = p₀ i)
    (halign : ∀ π ∈ Fam, 517776833 ≤ (alignedSet u₀ u₁ π.1 π.2).card) :
    Fam.card ≤ 657668325 := by
  have hcore := dirFamily_johnson_on_Dzero dom u₀ u₁ p₀ γ₀ Fam 517776833
    hmem hbase halign (by norm_num [k])
  rw [hz] at hcore
  have hsub := johnson_core_to_subtracted
    (n := 998723691) (a := 517776833) (p := k - 1) (L := Fam.card)
    (by norm_num [k]) (by norm_num [k]) hcore
  have hden : (0:ℕ) < 517776833 ^ 2 - 998723691 * (k - 1) := by norm_num [k]
  have hdiv : Fam.card ≤
      998723691 * (517776833 - (k - 1)) / (517776833 ^ 2 - 998723691 * (k - 1)) :=
    (Nat.le_div_iff_mul_le hden).2 hsub
  calc Fam.card ≤
      998723691 * (517776833 - (k - 1)) / (517776833 ^ 2 - 998723691 * (k - 1)) := hdiv
    _ = 657668325 := by norm_num [k]

/-- **The exact ledger histogram at `F₀`** sums to the probe optimum, under budget:
`1 + 657668325 + 7 + 5 + 27·4 + 3·(75018133 − 30) = 882722755 ≤ N`. -/
theorem ledger_histogram_le_N :
    1 + 657668325 + 7 + 5 + 27 * 4 + 3 * (75018133 - 30) = 882722755 ∧
    882722755 ≤ N := by
  constructor <;> norm_num [N]

/-- **The uniform-cap closed bound**: with the probe-swept uniform per-term caps
(`m = 2` term `≤ 7`, all `m ≥ 3` terms `≤ 5`, valid for every `F ≤ F₀`), the ledger is
still under budget: `1 + 657668325 + 7 + 5·(75018133 − 2) = 1032758988 ≤ N`. -/
theorem ledger_uniform_caps_le_N :
    1 + 657668325 + 7 + 5 * (75018133 - 2) = 1032758988 ∧
    1032758988 ≤ N := by
  constructor <;> norm_num [N]

/-! ## Stage (c): the dichotomy glue and the honest remaining Prop -/

/-- **Named residual (OPEN — counting-glue only, arithmetic discharged).**
The small-pool closure: bad families with SOME base scalar of pool `≤ F₀ = 75018133`
respect the budget.  The mathematics is pinned: directions partition by rider-cap `m`
(`riders ≤ F/(T−A)`), each `m`-class is `Z`-relative-Johnson-counted
(`dirFamily_johnson_on_Dzero`), the per-term caps are probe-swept uniformly in `F ≤ F₀`,
and the histogram sums under budget (`ledger_histogram_le_N`,
`ledger_uniform_caps_le_N`).  What remains for Lean is the marginal-partition wiring of the
fiber ledger over these caps, uniformly in `F` — engineering of the layer-cake kind. -/
def SmallPoolClosure (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F),
    BadFamilyData dom u₀ u₁ G Sf pf →
    (∃ γ₀ ∈ G, (Dsupport u₀ u₁ (pf γ₀) γ₀).card ≤ 75018133) →
    G.card ≤ N

/-- **The dichotomy assembly**: the small-pool closure and the stall residual together are
EXACTLY the predecessor budget — every bad family has either some base scalar with a small
pool (small-pool branch) or all pools stalling (stall branch).  The P1 predecessor pin's
open content is `SmallPoolClosure ∧ StallResidual`, with all arithmetic discharged. -/
theorem predecessor_budget_of_smallPool_and_stall (dom : Fin N ↪ F)
    (hsmall : SmallPoolClosure dom) (hstall : StallResidual dom) :
    ∀ (u₀ u₁ : Fin N → F) (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F),
      BadFamilyData dom u₀ u₁ G Sf pf → G.card ≤ N := by
  intro u₀ u₁ G Sf pf hdata
  by_cases hall : ∀ γ₀ ∈ G, 75018134 ≤ (Dsupport u₀ u₁ (pf γ₀) γ₀).card
  · exact hstall u₀ u₁ G Sf pf hdata hall
  · push_neg at hall
    obtain ⟨γ₀, hγ₀, hpool⟩ := hall
    exact hsmall u₀ u₁ G Sf pf hdata ⟨γ₀, hγ₀, by omega⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolAssembly

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterSmallPoolAssembly

#print axioms card_attach_filter
#print axioms johnson_core_rel
#print axioms dirFamily_johnson_on_Dzero
#print axioms boundary_count_pinned
#print axioms ledger_histogram_le_N
#print axioms ledger_uniform_caps_le_N
#print axioms predecessor_budget_of_smallPool_and_stall
