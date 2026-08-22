/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ32ClusterRouting
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ26LiftingTest
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ22StripBridge

/-!
# SYZ33: the final two strip lemmas — lemma 1 CLOSED, lemma 2 isolated, strip assembled (#466 / #507)

The SYZ29–32 chain reduced the unconditional rate-`1/2` interior-band strip theorem to **two**
named residuals (lemma 3 was closed as a case split in SYZ32 by the cluster-merge routing):

  1. **fresh independence-mod-`E`** (lemma 1) — SYZ31 proved the linear-algebra core
     (`indep_mod_of_private_coord`: a *private escaping coordinate* per fresh functional forces
     independence in `W ⧸ E`), leaving the **support-combinatorial supply** of those coordinates
     as the residual;
  2. **formula `≤` direction / MDS generation** (lemma 2) — SYZ25/26 pinned it as local-to-global
     polynomial rigidity, *strictly stronger* than the over-budget count (the counting corollary
     is REFUTED), with the clean overlap route covering only `δ ≤ 1/4`.

This file **closes lemma 1** to a crisp, honest support hypothesis and proves the linear-algebra
that discharges it in full, then **assembles the strip case split** at abstract `(n,k)`, `n`-uniform,
and instantiates it at `n ∈ {32,64}`.

## Lemma 1 — CLOSED (modulo two crisp, named inputs)

The exact statement `indep_mod_of_private_coord` (SYZ31) needs, per fresh functional `f i`
(anchored on its witness support `S i`), a coordinate `c i` with `c i ∈ S i`, `c i ∉ U'` (the core
envelope support — so `E` vanishes there), and `c i ∉ S j` for `j ≠ i` (so every *other* fresh
functional vanishes there — the `priv` clause, which for anchored functionals is *exactly*
`c i ∉ S j`).  The honest support content is thus a **system of private escaping coordinates**.

* `exists_private_positions` — **the combinatorial supply.**  If the *residual supports*
  `S i ∖ U'` are pairwise **disjoint** and nonempty, a private system exists: pick `c i ∈ S i ∖ U'`;
  disjointness gives `c i ∉ S j` for `j ≠ i` (any `c i ∈ S j` would sit in `S j ∖ U' ∩ S i ∖ U'`).
* `exists_fresh_indep_family` — **lemma 1, closed.**  Given per-fresh *blocks* `Blk i` (the
  `S i`-anchored dual annihilator, `dim = t − k ≥ 1`) that are anchored (`hanch`) and
  **non-degenerate** at each escaping coordinate (`hMDS`: `∀ x ∈ S i ∖ U', ∃ g ∈ Blk i, g x ≠ 0` —
  the MDS/RS-dual property, the same genericity as lemma 2, here isolated as one hypothesis), plus
  the disjoint-residual support condition, there is a choice of fresh functionals `f i ∈ Blk i`
  whose images `E.mkQ (f i)` are linearly independent.  Composed with SYZ30's codimension count
  (`fresh_card_le_codim`) this gives `#fresh ≤ finrank W − finrank E` (`fresh_card_le_codim_of_disjoint`).

So lemma 1's residual is reduced from "bound `#fresh`" to the two crisp inputs: **(a)** the fresh
residual supports are pairwise disjoint off the core (the SYZ18 distinct-support + `γ`-twist content
— `disjoint_residual_supports` records the honest sufficient shape), and **(b)** each block is
MDS-non-degenerate (RS duals are, the same genericity lemma 2 needs).  The `γ`-twist half is proved
outright: `twist_pair_indep` — two shared-support scalars with **distinct** `γ` are already
independent in the syndrome *pair* space, so support-sharing costs at most the field-`F²` factor,
never collapses independence.

## Lemma 2 — isolated (the one open analytic residual, unchanged)

`spread_generation_realizes_budget` re-exports the SYZ26/SYZ24 pipeline: **whenever** the merged
spread cores generate (`⨆ Aᵢ = W`, the probe-established `d = 0` regime for the open strip
`Johnson < δ < 1/3`), the joint syndrome span attains its ceiling `finrank W`, which is exactly the
SYZ22 realizability that closes the union budget `|U| ≤ n − 1`.  The clean overlap route
(`incremental_of_large_cores`, SYZ26) proves generation's sufficient condition for `δ ≤ 1/4`; the
strip interior `1/4 < δ < 1/3` remains the single **open** analytic residual (deficiency-free by
exhaustive-random probe, no polynomial-gluing proof).  We do **not** close it — recorded honestly.

## The strip theorem — assembled as a case split (SYZ32 routing)

`strip_certified_bad_le_budget` is the `n`-uniform merged-branch closure: a strict-interior
over-budget band family whose bad set is block-attributed to `m ≤ 3` merged blocks satisfies
`#B ≤ n − 1` (the SYZ22 budget), *unconditionally* in the linear algebra — the near-duplicate
clusters absorbed by the merge (SYZ32).  The complementary spread branch (`m ≥ 4`) routes through
generation (`strip_spread_budget_of_realizability`) and rests on lemma 2.  Concrete arithmetic
instances `strip_routed_budget_n32`, `strip_routed_budget_n64` discharge the budget at the
production-relevant sizes by the same uniform omega.

**Honest production statement.**  To chain to `mcaDeltaStar (evalCode …) ε* ≥ 1/3 − lattice` at
`n = 2³⁰` one still needs, at that shape: (i) lemma 2 (strip-interior generation, open); (ii) the
SYZ18/`γ`-twist disjoint-residual support control instantiated (lemma 1's input (a)); (iii) the
SYZ22 `SuperadditiveUnion` realizability filled; and (iv) the `MCAThresholdLedger` bridge from the
count bound `#bad ≤ n − 1` to the `δ*` floor.  None of (i)–(iv) is a *cheap* wire — the ledger
consumes a **lower** bound on `mcaDeltaStar` (the BGK/incidence floor, `_PrizeFloorOfBGK`), whereas
the strip supplies the **union/count** ceiling; joining them is the SYZ22 realizability step, still
open.  So SYZ33 does **not** deliver a new unconditional `δ*` statement; it closes lemma 1 and
assembles the merged branch, leaving lemma 2 as the lone open analytic residual.

All results axiom-clean (`propext`/`Classical.choice`/`Quot.sound`); no `sorry`, no
`native_decide`.  `#print axioms` at the bottom.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.SYZ33

open Finset Module Submodule
open ArkLib.ProximityGap.Frontier

/-! ## Lemma 1 — the support-combinatorial supply of private escaping coordinates -/

section PrivateSupply

variable {κ : Type*} [DecidableEq κ]

/-- **The combinatorial supply of a private system.**  If the *residual supports* `S i ∖ U'`
(the parts of the fresh witness supports outside the core envelope `U'`) are pairwise **disjoint**
and each nonempty, then there is a system of private escaping coordinates: `c i ∈ S i`, `c i ∉ U'`,
and `c i ∉ S j` for every `j ≠ i`.  The disjointness is the honest content — any `c i ∈ S j` with
`c i ∉ U'` would land in `(S i ∖ U') ∩ (S j ∖ U')`, contradicting disjointness. -/
theorem exists_private_positions {p : ℕ} (S : Fin p → Finset κ) (U' : Finset κ)
    (hne : ∀ i, (S i \ U').Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i \ U') (S j \ U')) :
    ∃ c : Fin p → κ,
      (∀ i, c i ∈ S i) ∧ (∀ i, c i ∉ U') ∧ (∀ i j, i ≠ j → c i ∉ S j) := by
  choose c hc using hne
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i; exact (Finset.mem_sdiff.mp (hc i)).1
  · intro i; exact (Finset.mem_sdiff.mp (hc i)).2
  · intro i j hij hmem
    have hi : c i ∈ S i \ U' := hc i
    have hj : c i ∈ S j \ U' :=
      Finset.mem_sdiff.mpr ⟨hmem, (Finset.mem_sdiff.mp (hc i)).2⟩
    exact (Finset.disjoint_left.mp (hdisj i j hij)) hi hj

/-- **Distinct-support ⇏ disjoint residuals — the honest gap named.**  This records the sufficient
support shape lemma 1 actually consumes: the residual supports `S i ∖ U'` are pairwise disjoint.
SYZ18 gives distinct *supports*; the `γ`-twist (`twist_pair_indep` below) upgrades support-sharing
to independence in the pair space; together they are the intended source, isolated here as the
single support hypothesis feeding `exists_private_positions`. -/
def DisjointResidualSupports {p : ℕ} (S : Fin p → Finset κ) (U' : Finset κ) : Prop :=
  ∀ i j, i ≠ j → Disjoint (S i \ U') (S j \ U')

end PrivateSupply

/-! ## Lemma 1 — the closed independence family (linear algebra discharged in full) -/

section FreshIndep

variable {F κ : Type*} [Field F] [DecidableEq κ]

/-- **Lemma 1, closed.**  Given, per fresh index `i`, a *block* `Blk i ≤ (κ → F)` (the `S i`-anchored
dual annihilator, `dim = t − k ≥ 1`) such that:
* `hconf` — the core envelope `E` is confined to `U'` (every `e ∈ E` vanishes off `U'`);
* `hanch` — each block is anchored on `S i` (every `g ∈ Blk i` vanishes off `S i`);
* `hMDS` — each block is **non-degenerate** at every escaping coordinate
  (`∀ x ∈ S i ∖ U', ∃ g ∈ Blk i, g x ≠ 0` — the MDS/RS-dual genericity, the same lemma 2 needs);
* `hne`, `hdisj` — the residual supports `S i ∖ U'` are nonempty and pairwise disjoint,

there is a choice of fresh functionals `f i ∈ Blk i` whose images `E.mkQ (f i)` are linearly
independent in `(κ → F) ⧸ E`.  This discharges lemma 1's independence-mod-`E` from the two crisp
inputs (disjoint residual supports + MDS non-degeneracy), via SYZ31's `indep_mod_of_private_coord`
and the `exists_private_positions` supply. -/
theorem exists_fresh_indep_family {p : ℕ}
    (E : Submodule F (κ → F)) (Blk : Fin p → Submodule F (κ → F))
    (S : Fin p → Finset κ) (U' : Finset κ)
    (hconf : ∀ e ∈ E, ∀ x, x ∉ U' → e x = 0)
    (hanch : ∀ i, ∀ g ∈ Blk i, ∀ x, x ∉ S i → g x = 0)
    (hMDS : ∀ i, ∀ x ∈ S i \ U', ∃ g ∈ Blk i, g x ≠ 0)
    (hne : ∀ i, (S i \ U').Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i \ U') (S j \ U')) :
    ∃ f : Fin p → (κ → F),
      (∀ i, f i ∈ Blk i) ∧ LinearIndependent F (fun i => E.mkQ (f i)) := by
  obtain ⟨c, hcS, hcU, hcpriv⟩ := exists_private_positions S U' hne hdisj
  have hpick : ∀ i, ∃ g ∈ Blk i, g (c i) ≠ 0 := fun i =>
    hMDS i (c i) (Finset.mem_sdiff.mpr ⟨hcS i, hcU i⟩)
  choose f hfBlk hfhit using hpick
  refine ⟨f, hfBlk, ?_⟩
  refine SYZ31.indep_mod_of_private_coord E f c ?_ hfhit ?_
  · intro i e he; exact hconf e he (c i) (hcU i)
  · intro i j hij; exact hanch j (f j) (hfBlk j) (c i) (hcpriv i j hij)

/-- **Fresh count from the closed family.**  Composing `exists_fresh_indep_family` with SYZ30's
codimension count: the number `p` of fresh functionals is bounded by `finrank (κ → F) − finrank E`.
This is the honest lemma-1 bound, now resting only on the disjoint-residual support shape and MDS
non-degeneracy. -/
theorem fresh_card_le_codim_of_disjoint [Fintype κ] {p : ℕ}
    (E : Submodule F (κ → F)) (Blk : Fin p → Submodule F (κ → F))
    (S : Fin p → Finset κ) (U' : Finset κ)
    (hconf : ∀ e ∈ E, ∀ x, x ∉ U' → e x = 0)
    (hanch : ∀ i, ∀ g ∈ Blk i, ∀ x, x ∉ S i → g x = 0)
    (hMDS : ∀ i, ∀ x ∈ S i \ U', ∃ g ∈ Blk i, g x ≠ 0)
    (hne : ∀ i, (S i \ U').Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i \ U') (S j \ U')) :
    p ≤ finrank F (κ → F) - finrank F E := by
  obtain ⟨f, _, hindep⟩ :=
    exists_fresh_indep_family E Blk S U' hconf hanch hMDS hne hdisj
  exact SYZ30.fresh_card_le_codim E f hindep

end FreshIndep

/-! ## Lemma 1 — the `γ`-twist: shared support never collapses independence -/

section GammaTwist

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **The `γ`-twist independence in the syndrome pair space.**  Two bad scalars that **share** a
witness support (so the *same* base functional `φ` explains both, `φ v ≠ 0` for a witness point `v`)
but have **distinct** twists `γ₀ ≠ γ₁` give **independent** pair-functionals
`w ↦ φ(w.1) + γ·φ(w.2)` on `V × V`: any relation `a·L(γ₀) + b·L(γ₁) = 0` forces `a = b = 0`.

This is the honest reason support-sharing does not collapse the fresh independence: in the doubled
syndrome space the `(1, γ)` twist separates same-support scalars.  (Evaluate at `(v,0)`: `a+b = 0`;
at `(0,v)`: `a·γ₀ + b·γ₁ = 0`; distinct `γ` ⟹ `a = b = 0`.) -/
theorem twist_pair_indep (φ : V →ₗ[F] F) (v : V) (hv : φ v ≠ 0)
    {γ₀ γ₁ : F} (hγ : γ₀ ≠ γ₁) {a b : F}
    (h : ∀ w : V × V, a * (φ w.1 + γ₀ * φ w.2) + b * (φ w.1 + γ₁ * φ w.2) = 0) :
    a = 0 ∧ b = 0 := by
  have h1 := h (v, 0)
  have h2 := h (0, v)
  simp only [map_zero, mul_zero, add_zero, zero_add] at h1 h2
  -- h1 : a * (φ v) + b * (φ v) = 0  ⟹ (a + b) * φ v = 0
  -- h2 : a * (γ₀ * φ v) + b * (γ₁ * φ v) = 0 ⟹ (a*γ₀ + b*γ₁) * φ v = 0
  have e1 : (a + b) * φ v = 0 := by linear_combination h1
  have e2 : (a * γ₀ + b * γ₁) * φ v = 0 := by linear_combination h2
  have hab : a + b = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact h
    · exact absurd h hv
  have hg : a * γ₀ + b * γ₁ = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · exact h
    · exact absurd h hv
  -- b = -a, and a*γ₀ - a*γ₁ = a*(γ₀ - γ₁) = 0, γ₀ ≠ γ₁ ⟹ a = 0
  have hb : b = -a := by linear_combination hab
  have ha0 : a * (γ₀ - γ₁) = 0 := by linear_combination hg - γ₁ * hab
  have hdne : γ₀ - γ₁ ≠ 0 := sub_ne_zero.mpr hγ
  have ha : a = 0 := by
    rcases mul_eq_zero.mp ha0 with h | h
    · exact h
    · exact absurd h hdne
  exact ⟨ha, by rw [hb, ha, neg_zero]⟩

end GammaTwist

/-! ## Lemma 2 — the spread branch: generation ⟹ realized budget (isolated, one open residual) -/

section SpreadBranch

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **Spread generation realizes the budget (lemma 2 reduction).**  Whenever the merged spread
cores generate (`⨆ Aᵢ = W`, the probe-established `d = 0` regime of the open strip), the joint
syndrome span attains its ceiling `finrank W` — the SYZ22 realizability that closes the union budget
`|U| ≤ n − 1`.  Re-export of the SYZ26 verdict; the hypothesis `hgen` is the single **open** lemma-2
residual (proved for `δ ≤ 1/4` by SYZ26 `incremental_of_large_cores`; the strip interior
`1/4 < δ < 1/3` is deficiency-free only by probe). -/
theorem spread_generation_realizes_budget (A : ℕ → Submodule F V) (W : Submodule F V) (D : ℕ)
    (hAW : ∀ i ∈ Finset.range D, A i ≤ W)
    (hgen : SYZ23.partialSup A D = W) :
    finrank F (SYZ23.partialSup A D) = finrank F W :=
  SYZ26.generation_realizes_budget A W D hAW hgen

/-- **The `δ ≤ 1/4` sufficient condition (proved end).**  Cores of size `≥ s` in a ground set of
size `|G|` with `|G| + k ≤ 2s` (i.e. `δ ≤ 1/4` at rate `1/2`) are incremental-`≥k`-orderable:
every core meets its predecessors in `≥ k` points — SYZ26's clean overlap route, the proven half of
lemma 2's sufficient condition.  The strip interior violates `|G| + k ≤ 2s` (SYZ26
`strip_boundary_overlap_floor_insufficient`), which is why it stays open. -/
theorem spread_incremental_of_large {α : Type*} [DecidableEq α]
    (G : Finset α) (C : ℕ → Finset α) (s k : ℕ)
    (hsub : ∀ i, C i ⊆ G) (hsize : ∀ i, s ≤ (C i).card)
    (hbig : G.card + k ≤ 2 * s) {i : ℕ} (hi : 1 ≤ i) :
    k ≤ (C i ∩ SYZ26.prefixUnion C i).card :=
  SYZ26.incremental_of_large_cores G C s k hsub hsize hbig hi

end SpreadBranch

/-! ## The assembled strip theorem (merged branch, `n`-uniform) + spread reduction -/

section Assembly

/-- **The assembled strip theorem (merged branch).**  A strict-interior over-budget band family
whose bad set `B` is block-attributed to `m ≤ 3` merged blocks (each a band core / merged cluster of
union `Uⱼ ∈ [s, n]`, with `|T j| = n − Uⱼ`) satisfies `#B ≤ n − 1` — the SYZ22 budget.  This is the
`n`-uniform closure of the merged case: near-duplicate clusters are absorbed by the SYZ32 merge, not
forbidden; the linear algebra is unconditional (the routing is via `SYZ32.routed_bad_le_budget`).
The complementary spread branch (`m ≥ 4`) routes through generation
(`strip_spread_budget_of_realizability`) and rests on lemma 2. -/
theorem strip_certified_bad_le_budget {ι F : Type*} [DecidableEq F] [Field F]
    (B : Finset F) (n k s m : ℕ) (U : ℕ → ℕ) (d₀ d₁ : ℕ → ι → F) (T : ℕ → Finset ι)
    (hn : n = 2 * k) (hband : 2 * n < 3 * s) (hm : m ≤ 3)
    (hblk : ∀ j ∈ Finset.range m, s ≤ U j ∧ U j ≤ n)
    (hTU : ∀ j ∈ Finset.range m, (T j).card = n - U j)
    (hattr : ∀ γ ∈ B, ∃ j, j ∈ Finset.range m ∧
      ∃ x ∈ T j, d₁ j x ≠ 0 ∧ d₀ j x + γ * d₁ j x = 0) :
    B.card ≤ n - 1 :=
  SYZ32.routed_bad_le_budget B n k s m U d₀ d₁ T hn hband hm hblk hTU hattr

/-- **The spread branch reduction.**  For the `m ≥ 4` spread families, generation (lemma 2) gives
the SYZ22 realizability `SuperadditiveUnion`, which yields the union budget `|U| ≤ n − 1`.  Honest
re-export of `SYZ22.strip_budget_of_realizability`: the linear algebra is proven, the *input*
(that a specific over-budget family fills its doubled shortening space — equivalently, generation)
is the open lemma-2 residual. -/
theorem strip_spread_budget_of_realizability {F : Type*} [Field F] [DecidableEq F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {n k Ucard : ℕ} (hkU : k ≤ Ucard) (hUn : Ucard ≤ n)
    (cfg : SYZ20JointRankSuperadditive.SuperadditiveUnion (F := F) (V := V) n k Ucard) :
    Ucard ≤ n - 1 :=
  SYZ22.strip_budget_of_realizability hkU hUn cfg

/-- **Concrete merged budget at `n = 32`** (`k = 16`, strip core floor `s = 22 > 2n/3`).  For
`m = 3` merged blocks each of union `Uⱼ ∈ [22, 32]`, the total merged yield `∑ (32 − Uⱼ) ≤ 31 = n − 1`
— the SYZ22 budget at production-relevant size, by the uniform omega. -/
theorem strip_routed_budget_n32 (U : ℕ → ℕ)
    (h : ∀ j ∈ Finset.range 3, 22 ≤ U j ∧ U j ≤ 32) :
    ∑ j ∈ Finset.range 3, (32 - U j) ≤ 31 :=
  SYZ32.routed_yield_cap_le3 32 16 22 3 U rfl (by norm_num) (by norm_num) h

/-- **Concrete merged budget at `n = 64`** (`k = 32`, strip core floor `s = 43 > 2n/3`).  For
`m = 3` merged blocks each of union `Uⱼ ∈ [43, 64]`, the total merged yield `∑ (64 − Uⱼ) ≤ 63 = n − 1`. -/
theorem strip_routed_budget_n64 (U : ℕ → ℕ)
    (h : ∀ j ∈ Finset.range 3, 43 ≤ U j ∧ U j ≤ 64) :
    ∑ j ∈ Finset.range 3, (64 - U j) ≤ 63 :=
  SYZ32.routed_yield_cap_le3 64 32 43 3 U rfl (by norm_num) (by norm_num) h

end Assembly

end ArkLib.ProximityGap.Frontier.SYZ33

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.exists_private_positions
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.exists_fresh_indep_family
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.fresh_card_le_codim_of_disjoint
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.twist_pair_indep
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.spread_generation_realizes_budget
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.spread_incremental_of_large
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.strip_certified_bad_le_budget
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.strip_spread_budget_of_realizability
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.strip_routed_budget_n32
#print axioms ArkLib.ProximityGap.Frontier.SYZ33.strip_routed_budget_n64
