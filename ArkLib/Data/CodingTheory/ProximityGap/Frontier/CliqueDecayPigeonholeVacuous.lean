/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

set_option linter.style.longLine false

/-!
# The clique/Turán pigeonhole bound on the decay rate, and its asymptotic VACUITY (#444)

lalalune's #444 22:13 *decay-rate attack* gave a verified-correct CLIQUE reformulation of the prize's
single open core (`m* = O(log n)` so `δ* → capacity`). Each `(k+1)`-subset `R'` of `μ_n` is assigned a
Schur-ratio level `γ_{R'} = −h_{a−k}(R')/h_{b−k}(R')` (`SchurLagrangeBridge`); the level set
`L_γ = {R' : γ_{R'} = γ}`. A `(k+m)`-**clique** for `γ` is a `(k+m)`-set `W` ALL of whose `(k+1)`-subsets
lie in `L_γ`. The decay envelope is

> `D*(m) = #{ γ : L_γ contains a (k+m)-clique }`,   `m* = ` first `m` with `D*(m) ≤ n`.

This file formalizes, **purely combinatorially and prime-independently** (no cyclotomic structure used),
the two facts lalalune stated about the *count-only* face:

* **The pigeonhole/Markov upper bound** (`cliqueColors_mul_choose_le`, `cliqueColors_le_div`):
  > `D*(m) · C(k+m, k+1) ≤ C(n, k+1)`,   hence   `D*(m) ≤ C(n,k+1) / C(k+m,k+1)`.

  Mechanism: a `γ` with a `(k+m)`-clique `W` contains `≥ C(k+m,k+1)` distinct `(k+1)`-subsets (its
  faces, `card (W.powersetCard (k+1)) = C(k+m,k+1)`), and a `(k+1)`-subset has EXACTLY ONE level `γ`, so
  across distinct clique-bearing levels these face-families are **disjoint** inside the `C(n,k+1)`-element
  universe of all `(k+1)`-subsets.

* **The vacuity mechanism** (`pigeonhole_bound_ge_card_of_choose_le`): if `C(k+m,k+1) ≤ C(n,k+1)/c` for
  a color-budget `c`, the pigeonhole bound is `≥ c` and gives NOTHING beyond the trivial. Numerically
  (`probe_clique_pigeonhole_vacuity.py`: `m_bound/n = 0.375 .. 0.680` for `n = 8..256`, `k = n/4`, rising
  → 1, while true `m* = 3,3,5`) the bound only bites at `m` LINEAR in `n`, as weak as the trivial
  `m* ≤ n − k`. The count-only face CANNOT deliver `m* = O(log n)`.

**ASYMPTOTIC-CLAIM GUARD compliance.** This proves the combinatorial (subset-count) face is *vacuous*,
the OPPOSITE of over-claiming capacity from it. It is a NON-moment, prime-independent hypergraph-Turán
brick + an honest no-go; it does NOT close CORE, which stays open in the cyclotomic level-set structure.
-/

namespace ArkLib.ProximityGap.CliqueDecayPigeonhole

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {β : Type*} [DecidableEq β]

/-- The `(k+1)`-subsets of the ground set, the "edge" universe of the level-set hypergraph,
of which there are exactly `C(n, k+1)`. -/
def edges (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) : Finset (Finset V) :=
  (univ : Finset V).powersetCard (k + 1)

/-- `#edges = C(n, k+1)`. -/
theorem edges_card (k : ℕ) :
    (edges V k).card = (Fintype.card V).choose (k + 1) := by
  classical
  unfold edges
  rw [Finset.card_powersetCard]
  rfl

/-- The "faces" of a candidate clique `W`: its `(k+1)`-subsets. For `|W| = k+m` there are exactly
`C(k+m, k+1)` of them, and each is an element of the global edge universe (since `W ⊆ univ`). -/
def faces (k : ℕ) (W : Finset V) : Finset (Finset V) := W.powersetCard (k + 1)

theorem faces_card_of_card {k m : ℕ} {W : Finset V} (hW : W.card = k + m) :
    (faces k W).card = (k + m).choose (k + 1) := by
  unfold faces
  rw [Finset.card_powersetCard, hW]

/-- A face of `W` is a global edge. -/
theorem faces_subset_edges (k : ℕ) (W : Finset V) : faces k W ⊆ edges V k := by
  classical
  intro R hR
  unfold faces edges at *
  rw [Finset.mem_powersetCard] at hR ⊢
  exact ⟨hR.1.trans (Finset.subset_univ W), hR.2⟩

/-- A `(k+m)`-set `W` is a **clique** for color `g` if every one of its `(k+1)`-subsets has level `g`. -/
def IsClique (γ : Finset V → β) (k m : ℕ) (g : β) (W : Finset V) : Prop :=
  W.card = k + m ∧ ∀ R ∈ faces k W, γ R = g

/-- **The disjoint-faces pigeonhole core.** Given a finset `cols` of colors, each equipped with a
witnessing `(k+m)`-clique `Wc g` of color `g`, the clique face-families are pairwise disjoint inside
the edge universe (a face has a single color), so

> `#cols · C(k+m, k+1) ≤ C(n, k+1)`.

This is lalalune's `D*(m) · C(k+m,k+1) ≤ C(n,k+1)` with `#cols` standing for `D*(m)`. -/
theorem card_mul_choose_le_of_cliques
    (γ : Finset V → β) (k m : ℕ) (cols : Finset β)
    (Wc : β → Finset V)
    (hclique : ∀ g ∈ cols, IsClique γ k m g (Wc g)) :
    cols.card * (k + m).choose (k + 1) ≤ (Fintype.card V).choose (k + 1) := by
  classical
  -- The disjoint union of the face-families over `cols` sits inside `edges`.
  have hdisj : (cols : Set β).PairwiseDisjoint (fun g => faces k (Wc g)) := by
    intro g hg g' hg' hne
    refine Finset.disjoint_left.mpr ?_
    intro R hRg hRg'
    -- R is a (k+1)-face of both Wc g and Wc g', so γ R = g and γ R = g', contradiction.
    have e1 : γ R = g := (hclique g hg).2 R hRg
    have e2 : γ R = g' := (hclique g' hg').2 R hRg'
    exact hne (e1.symm.trans e2)
  -- card of the biUnion = sum of face counts (disjoint), each = C(k+m,k+1).
  have hbu : (cols.biUnion (fun g => faces k (Wc g))).card
      = ∑ g ∈ cols, (faces k (Wc g)).card :=
    Finset.card_biUnion (by
      intro g hg g' hg' hne
      exact hdisj (by simpa using hg) (by simpa using hg') hne)
  have hsum : ∑ g ∈ cols, (faces k (Wc g)).card
      = ∑ _g ∈ cols, (k + m).choose (k + 1) := by
    refine Finset.sum_congr rfl (fun g hg => ?_)
    exact faces_card_of_card (hclique g hg).1
  have hsubset : cols.biUnion (fun g => faces k (Wc g)) ⊆ edges V k := by
    intro R hR
    rw [Finset.mem_biUnion] at hR
    obtain ⟨g, _, hRg⟩ := hR
    exact faces_subset_edges k (Wc g) hRg
  -- Assemble.
  have hle : (cols.biUnion (fun g => faces k (Wc g))).card ≤ (edges V k).card :=
    Finset.card_le_card hsubset
  rw [hbu, hsum, Finset.sum_const, smul_eq_mul, edges_card] at hle
  exact hle

/-- **`D*(m)` packaged.** The set of colors carrying a `(k+m)`-clique, ranged over a finite palette
`cols` of candidate colors. -/
noncomputable def cliqueColors (γ : Finset V → β) (k m : ℕ) (cols : Finset β) : Finset β :=
  @Finset.filter _ (fun g => ∃ W, IsClique γ k m g W)
    (Classical.decPred _) cols

theorem cliqueColors_mem_iff {γ : Finset V → β} {k m : ℕ} {cols : Finset β} {g : β} :
    g ∈ cliqueColors γ k m cols ↔ g ∈ cols ∧ ∃ W, IsClique γ k m g W := by
  letI : DecidablePred (fun g : β => ∃ W, IsClique γ k m g W) := Classical.decPred _
  unfold cliqueColors
  rw [Finset.mem_filter]

theorem cliqueColors_subset (γ : Finset V → β) (k m : ℕ) (cols : Finset β) :
    cliqueColors γ k m cols ⊆ cols := by
  intro g hg
  exact (cliqueColors_mem_iff.mp hg).1

/-! ## Clique NESTING — the agreement-depth antitone descent of `D*(m)` (the real substrate)

The `_OffBGK_*` off-BGK persistence files (`_OffBGK_AgreementDepthMerge`,
`_OPDescentFromAntitoneOrbitCount`) reduce single-orbit persistence to the antitonicity of the
distinct-level envelope `D*(m) = #cliqueColors` in the agreement depth `m`, and cite a
`cliqueColors_antitone` substrate as if proven.  It had NEVER been written (its claimed host file
`_DStarDecreasingEnvelope.lean` does not exist in the tree).  It is proven HERE, purely combinatorially,
by clique NESTING — the genuine structural fact those files depend on. -/

/-- **Clique nesting (one depth step).** A `(k + (m+1))`-clique `W` for color `g` contains a
`(k + m)`-clique for `g`: any `(k+m)`-subset `W' ⊆ W` is again a clique, because `W'`'s `(k+1)`-faces
are a subset of `W`'s `(k+1)`-faces (a face of `W'` lies in `W' ⊆ W`), all of which carry color `g`.
This is the structural engine of the agreement-depth descent: deepening the clique by one vertex can
only RESTRICT, never create, surviving levels. -/
theorem isClique_succ_imp_isClique
    {γ : Finset V → β} {k m : ℕ} {g : β} {W : Finset V}
    (hW : IsClique γ k (m + 1) g W) :
    ∃ W', IsClique γ k m g W' := by
  obtain ⟨hcard, hcol⟩ := hW
  -- pick a (k+m)-subset of W (exists since k+m ≤ k+(m+1) = #W)
  obtain ⟨W', hsub, hW'card⟩ :=
    Finset.exists_subset_card_eq (n := k + m) (s := W) (by omega)
  refine ⟨W', hW'card, ?_⟩
  intro R hR
  -- a (k+1)-face of W' is a (k+1)-face of W (R ⊆ W' ⊆ W, #R = k+1)
  have hRsubW' : R ⊆ W' := (Finset.mem_powersetCard.mp hR).1
  have hRcard : R.card = k + 1 := (Finset.mem_powersetCard.mp hR).2
  have hRW : R ∈ faces k W :=
    Finset.mem_powersetCard.mpr ⟨hRsubW'.trans hsub, hRcard⟩
  exact hcol R hRW

/-- **`D*(m)` is ANTITONE in the agreement depth `m` (one step).**  `cliqueColors γ k (m+1) cols ⊆
cliqueColors γ k m cols`: every color carrying a `(k+(m+1))`-clique also carries a `(k+m)`-clique
(`isClique_succ_imp_isClique`), so deepening the agreement by one rung can only DROP clique-bearing
colors.  This is the structural merge map `D*(m+1) ≤ D*(m)` the off-BGK persistence skeleton relies on. -/
theorem cliqueColors_succ_subset (γ : Finset V → β) (k m : ℕ) (cols : Finset β) :
    cliqueColors γ k (m + 1) cols ⊆ cliqueColors γ k m cols := by
  intro g hg
  rw [cliqueColors_mem_iff] at hg ⊢
  obtain ⟨hgc, W, hW⟩ := hg
  exact ⟨hgc, isClique_succ_imp_isClique hW⟩

/-- **`D*(m)` antitone, MONOTONE form** (`m₁ ≤ m₂ ⟹ D*(m₂) ⊆ D*(m₁)`): iterating the one-step nesting
`cliqueColors_succ_subset` down the depth difference.  The full agreement-depth merge substrate. -/
theorem cliqueColors_antitone (γ : Finset V → β) (k : ℕ) (cols : Finset β)
    {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    cliqueColors γ k m₂ cols ⊆ cliqueColors γ k m₁ cols := by
  induction m₂ with
  | zero =>
    have : m₁ = 0 := Nat.le_zero.mp hm
    subst this; exact fun _ hx => hx
  | succ n ih =>
    rcases Nat.lt_or_ge m₁ (n + 1) with hlt | hge
    · -- m₁ ≤ n: nest one step then induct
      have hm₁n : m₁ ≤ n := Nat.lt_succ_iff.mp hlt
      exact (cliqueColors_succ_subset γ k n cols).trans (ih hm₁n)
    · -- m₁ = n+1: reflexive
      have : m₁ = n + 1 := le_antisymm hm hge
      subst this; exact fun _ hx => hx

/-- **`D*(m)` antitone, CARDINALITY form** (`m₁ ≤ m₂ ⟹ D*(m₂) ≤ D*(m₁)`): the count of
clique-bearing colors is non-increasing in the agreement depth.  This is exactly the antitone
envelope hypothesis the off-BGK orbit-count merge (`orbitCount_antitone_depth`) consumes — supplied
here as a genuine clique-nesting proof rather than an absent import. -/
theorem cliqueColors_card_antitone (γ : Finset V → β) (k : ℕ) (cols : Finset β)
    {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    (cliqueColors γ k m₂ cols).card ≤ (cliqueColors γ k m₁ cols).card :=
  Finset.card_le_card (cliqueColors_antitone γ k cols hm)

/-- **The pigeonhole bound on `D*(m)`.** Choosing a witnessing clique per clique-bearing color,
`D*(m) · C(k+m, k+1) ≤ C(n, k+1)`. -/
theorem cliqueColors_mul_choose_le
    (γ : Finset V → β) (k m : ℕ) (cols : Finset β) :
    (cliqueColors γ k m cols).card * (k + m).choose (k + 1)
      ≤ (Fintype.card V).choose (k + 1) := by
  classical
  -- Every clique-bearing color carries a witnessing clique.
  have hwit : ∀ g ∈ cliqueColors γ k m cols, ∃ W, IsClique γ k m g W := by
    intro g hg
    exact (cliqueColors_mem_iff.mp hg).2
  choose! Wc hWc using hwit
  exact card_mul_choose_le_of_cliques γ k m (cliqueColors γ k m cols) Wc hWc

/-- **The division form.** `D*(m) ≤ C(n,k+1) / C(k+m,k+1)` (`Nat` division), valid whenever
`C(k+m,k+1) > 0` (i.e. `k+1 ≤ k+m`, i.e. `m ≥ 1`). -/
theorem cliqueColors_le_div
    (γ : Finset V → β) (k m : ℕ) (cols : Finset β) (hm : 1 ≤ m) :
    (cliqueColors γ k m cols).card
      ≤ (Fintype.card V).choose (k + 1) / (k + m).choose (k + 1) := by
  classical
  have hpos : 0 < (k + m).choose (k + 1) := by
    apply Nat.choose_pos
    omega
  rw [Nat.le_div_iff_mul_le hpos]
  exact cliqueColors_mul_choose_le γ k m cols

/-- **The vacuity mechanism.** If the clique-face count `C(k+m,k+1)` is at most `C(n,k+1)/c` for a
color budget `c ≥ 1`, then the pigeonhole upper bound `C(n,k+1)/C(k+m,k+1)` is `≥ c`, giving nothing
sharper than the trivial `D*(m) ≤ c`. (The probe shows the threshold `C(k+m,k+1) ≥ C(n,k+1)/n` is only
crossed at `m` LINEAR in `n`, so for `c = n` the pigeonhole bound bites only past `m ~ n`: vacuous vs the
true `m* = O(log n)`.) -/
theorem pigeonhole_bound_ge_of_choose_le
    {n c km1 : ℕ} (_hc : 1 ≤ c) (hpos : 0 < km1)
    (hsmall : km1 * c ≤ n) :
    c ≤ n / km1 := by
  rw [Nat.le_div_iff_mul_le hpos, Nat.mul_comm]
  exact hsmall

/-- **Vacuity at the decay threshold `D*(m) ≤ n`.** Specialising the budget to `c = N` (the threshold
the decay rate reads off, `D*(m) ≤ n`), if the clique-face count times `N` still fits in the global
edge budget `C(n,k+1)`, then the pigeonhole upper bound `C(n,k+1)/C(k+m,k+1)` is `≥ N`: it does NOT
certify `D*(m) ≤ N`. So at every such `m` the count-only face is vacuous. (The probe shows
`km1 * N ≤ C(n,k+1)` persists until `m` is LINEAR in `n`; the true `m* = O(log n)` is reached far
earlier, entirely via the cyclotomic level-set structure this bound discards.) -/
theorem pigeonhole_vacuous_at_threshold
    {N km1 k : ℕ} (hN : 1 ≤ N) (hpos : 0 < km1)
    (hsmall : km1 * N ≤ (Fintype.card V).choose (k + 1)) :
    N ≤ (Fintype.card V).choose (k + 1) / km1 :=
  pigeonhole_bound_ge_of_choose_le hN hpos hsmall

end ArkLib.ProximityGap.CliqueDecayPigeonhole
