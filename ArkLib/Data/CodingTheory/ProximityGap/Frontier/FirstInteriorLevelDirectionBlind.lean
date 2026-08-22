/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# The first window-interior level `a = k+1` is direction-blind (#466, lane R5)

**The round-1 P5 structural discovery, formalized.**  For the degree-`≤ d` smooth evaluation
code (dimension `k = d+1`) the first window-interior agreement level is `a = k+1 = d+2` — one
point above unconditional Lagrange interpolation.  At this level the bad-scalar count is
**direction-blind**: for ANY direction `u₁` — spread, monomial, anything — the scalars `γ`
for which some codeword agrees with `u₀ + γ·u₁` on at least `k+1` points number at most

  `C(n, k+1)`    (`levelBadScalars_card_le_choose` / `mca_firstLevel_badScalars_card_le_choose`),

because each `(k+1)`-subset of coordinates determines **at most one** `γ` by linear
collinearity.  The per-subset uniqueness is a thin corollary of the in-tree
`KKH26CeilingMarch.scalar_eq_of_shared_tuple` (dedup note: that lemma already holds for ANY
tuple, so this file adds only the fiber packaging, the degenerate trichotomy, and the
boundary-level assembly — no argument is re-derived).

## Per-subset trichotomy (the honest degenerate accounting)

For a fixed `(k+1)`-subset `S`, the interpolation-consistency obstruction of `(u₀+γu₁)|_S`
is affine in `γ` (interpolate on any `k` points of `S`; the residual at the last point is
`A + γ·B` with `B` the obstruction of `u₁|_S` and `A` that of `u₀|_S`).  Its vanishing locus
— the fiber `subsetGammaFiber` of scalars explainable on `S` — is accordingly:

* **everything** (`= F`), exactly when `u₁|_S` AND `u₀|_S` both extend to degree-`≤ d`
  polynomials (`B = A = 0`): `subsetGammaFiber_eq_univ`;
* **at most one point**, whenever `u₁|_S` does not extend (`B ≠ 0`):
  `subsetGammaFiber_card_le_one`;
* **empty**, when `u₁|_S` extends but `u₀|_S` does not (`B = 0, A ≠ 0`):
  `subsetGammaFiber_eq_empty`.

(`subsetGammaFiber_trichotomy` packages the three branches.)  The degenerate branch is
therefore handled by an explicit, *necessary* hypothesis: `FirstLevelNondegenerate` demands
that no `(k+1)`-subset jointly explains `u₀` and `u₁`.  Necessity is machine-checked the
other way: if it fails, EVERY scalar is bad (`levelBadScalars_eq_univ_of_degenerate`) — this
is exactly the probe's "direction `a`-close to the code ⟹ worst-`u₀` count `= q` trivially"
exclusion.

## Where this sits relative to the march (why the crux lives at depth `a ≥ k+2`)

`KKH26CeilingMarch.march_badScalars_card_mul_le` requires the agreement threshold to be
*strictly* above `d+2` (its witness carries a non-explainable `(d+3)`-subset), and then the
glueing/ownership argument buys the `(d+2)`-fold sharper `#bad ≤ C(n,d+2)/(d+2)`.  At the
boundary level `a = d+2` exactly, no `(d+3)`-point witness exists and ownership degenerates;
what survives is the per-subset uniqueness alone, giving `#bad ≤ C(n, d+2)` — this file.
Consequences, matching the round-1 P5 probe verdict
(`scripts/probes/probe_466_windowed_extremal.py`, outputs
`scripts/probes/_out_466_windowed_extremal*.txt`):

* the ceiling at `a = k+1` is **uniform over all directions** — no spread direction can be
  separated from a monomial direction by more than the slack below `C(n,k+1)`;
* the probes show **generic saturation** (a numerical observation, NOT proven here): at
  `n = 8, k = 2` the extremal directions attain the ceiling `C(8,3) = 56` EXACTLY (all 4
  eligible monomials and the top-12 spread directions, both primes — the bound of this
  file is tight there); at `n = 16, k = 4` the worst counts are `4251–4293` against
  `C(16,5) = 4368` (97–98%), spread and monomial within 0.5% of each other, across
  primes `65537/65617/65633`;
* hence the **windowed-SumsetExtremal discrimination question has content only at depth
  `a ≥ k+2`** into the window — the first interior level cannot distinguish direction
  classes even in principle;
* and the finished three-prime depth data confirm exactly that (numerical, NOT proven
  here; worst-`u₀` search heuristic, winning witnesses brute-verified over all `γ`): at
  `n = 16, k = 4` the depth-2 level `a = 6` is an EXACT three-prime tie (best monomial
  `= 89 =` best spread, the whole eligible profile `89/73/56/40` is `p`-independent
  across `65537/65617/65633`), while at depth-3 `a = 7` a spread direction strictly
  beats every monomial at ALL three primes (`13` for `sp2_4_14`, `p`-independently, vs
  `9` for every eligible monomial; `14` for `sp2_7_13` at the Fermat prime `65537`
  only) — the first observed direction separation, precisely where the boundary
  theorem above says separation first becomes possible.  Both winning spreads have
  self-agreement `6` (direction `6`-close but not `7`-close to the code): the
  separation lives just above the near-degenerate boundary that
  `FirstLevelNondegenerate` polices.

No `epsMCA`-level corollary is stated: `epsMCA` takes a supremum over stacks, and degenerate
stacks (which genuinely saturate at `q`) exist for every code, so the per-stack
nondegeneracy hypothesis cannot be discharged uniformly.  Honest scope: per-stack bounds
only.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal
open ProximityGap ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.KKH26CeilingMarch

namespace ArkLib.ProximityGap.FirstInteriorLevelDirectionBlind

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## The per-subset scalar fiber -/

open Classical in
/-- The scalars `γ` whose combined word `u₀ + γ·u₁` is explainable (agrees with a
degree-`≤ d` polynomial) on the fixed coordinate subset `S`.  At `|S| = d+2 = k+1` this is
the vanishing locus of an affine-in-`γ` interpolation obstruction. -/
noncomputable def subsetGammaFiber (g : ZMod p) (d : ℕ) (u₀ u₁ : Fin n → ZMod p)
    (S : Finset (Fin n)) : Finset (ZMod p) :=
  Finset.univ.filter (fun γ => ExplainableOn g d (fun i => u₀ i + γ * u₁ i) S)

open Classical in
/-- The level-`a` bad scalars of a stack: those `γ` whose combined word is explainable on
some coordinate set of size at least `a`.  At `a = d+2` this contains (and for the
evaluation code is the honest superset of) every `mcaEvent`-bad scalar at the matching
radius. -/
noncomputable def levelBadScalars (g : ZMod p) (d a : ℕ) (u₀ u₁ : Fin n → ZMod p) :
    Finset (ZMod p) :=
  Finset.univ.filter (fun γ => ∃ S : Finset (Fin n), a ≤ S.card ∧
    ExplainableOn g d (fun i => u₀ i + γ * u₁ i) S)

/-! ## The trichotomy: everything / at most one / empty -/

/-- **Per-subset uniqueness (the nondegenerate branch).**  If the direction `u₁` is not
explainable on `S`, then at most one scalar's combined word is explainable on `S`: the
affine obstruction `A + γ·B` has `B ≠ 0`.  Thin corollary of
`KKH26CeilingMarch.scalar_eq_of_shared_tuple` (which needs no cardinality on `S`). -/
theorem subsetGammaFiber_card_le_one (hg : orderOf g = n) {d : ℕ}
    {u₀ u₁ : Fin n → ZMod p} {S : Finset (Fin n)}
    (hdir : ¬ ExplainableOn g d u₁ S) :
    (subsetGammaFiber g d u₀ u₁ S).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr (fun γ hγ γ' hγ' => ?_)
  rw [subsetGammaFiber, Finset.mem_filter] at hγ hγ'
  exact scalar_eq_of_shared_tuple hg hdir hγ.2 hγ'.2

/-- Explainability transfers off the line: if the combined word and the direction are both
explainable on `S`, so is the offset (`q₀ = q − γ·q₁`). -/
theorem explainableOn_offset_of_combined {d : ℕ} {u₀ u₁ : Fin n → ZMod p}
    {S : Finset (Fin n)} {γ : ZMod p}
    (hcomb : ExplainableOn g d (fun i => u₀ i + γ * u₁ i) S)
    (hdir : ExplainableOn g d u₁ S) :
    ExplainableOn g d u₀ S := by
  obtain ⟨q, hqd, hq⟩ := hcomb
  obtain ⟨q₁, hq₁d, hq₁⟩ := hdir
  refine ⟨q - Polynomial.C γ * q₁, ?_, fun i hi => ?_⟩
  · calc (q - Polynomial.C γ * q₁).natDegree
        ≤ max q.natDegree (Polynomial.C γ * q₁).natDegree :=
          Polynomial.natDegree_sub_le _ _
    _ ≤ d := max_le hqd (le_trans (Polynomial.natDegree_C_mul_le _ _) hq₁d)
  · have h1 : u₀ i + γ * u₁ i = q.eval (g ^ (i : ℕ)) := hq i hi
    have h2 : u₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i hi
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, ← h1, ← h2]
    ring

/-- Explainability assembles onto the line: if the offset and the direction are both
explainable on `S`, so is every combined word (`q₀ + γ·q₁`). -/
theorem explainableOn_combined_of_both {d : ℕ} {u₀ u₁ : Fin n → ZMod p}
    {S : Finset (Fin n)}
    (hoff : ExplainableOn g d u₀ S) (hdir : ExplainableOn g d u₁ S) (γ : ZMod p) :
    ExplainableOn g d (fun i => u₀ i + γ * u₁ i) S := by
  obtain ⟨q₀, hq₀d, hq₀⟩ := hoff
  obtain ⟨q₁, hq₁d, hq₁⟩ := hdir
  refine ⟨q₀ + Polynomial.C γ * q₁, ?_, fun i hi => ?_⟩
  · calc (q₀ + Polynomial.C γ * q₁).natDegree
        ≤ max q₀.natDegree (Polynomial.C γ * q₁).natDegree :=
          Polynomial.natDegree_add_le _ _
    _ ≤ d := max_le hq₀d (le_trans (Polynomial.natDegree_C_mul_le _ _) hq₁d)
  · show u₀ i + γ * u₁ i = (q₀ + Polynomial.C γ * q₁).eval (g ^ (i : ℕ))
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      ← hq₀ i hi, ← hq₁ i hi]

/-- **The degenerate branch is everything**: if `u₁` and `u₀` are both explainable on `S`
(the affine obstruction is constantly zero), then every scalar lies in the fiber. -/
theorem subsetGammaFiber_eq_univ {d : ℕ} {u₀ u₁ : Fin n → ZMod p} {S : Finset (Fin n)}
    (hdir : ExplainableOn g d u₁ S) (hoff : ExplainableOn g d u₀ S) :
    subsetGammaFiber g d u₀ u₁ S = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro γ
  rw [subsetGammaFiber, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, explainableOn_combined_of_both hoff hdir γ⟩

/-- **The mixed branch is empty**: if `u₁` is explainable on `S` but `u₀` is not (the
affine obstruction is a nonzero constant), no scalar lies in the fiber. -/
theorem subsetGammaFiber_eq_empty {d : ℕ} {u₀ u₁ : Fin n → ZMod p} {S : Finset (Fin n)}
    (hdir : ExplainableOn g d u₁ S) (hoff : ¬ ExplainableOn g d u₀ S) :
    subsetGammaFiber g d u₀ u₁ S = ∅ := by
  classical
  rw [subsetGammaFiber, Finset.filter_eq_empty_iff]
  intro γ _
  exact fun hcomb => hoff (explainableOn_offset_of_combined hcomb hdir)

/-- **The per-subset trichotomy**: every coordinate subset's scalar fiber is either the
whole field (degenerate: both rows explainable) or has at most one element.  This is the
affine-obstruction dichotomy `B ≠ 0 ∨ (B = 0 ∧ …)` in fiber form. -/
theorem subsetGammaFiber_trichotomy (hg : orderOf g = n) {d : ℕ}
    (u₀ u₁ : Fin n → ZMod p) (S : Finset (Fin n)) :
    subsetGammaFiber g d u₀ u₁ S = Finset.univ ∨
      (subsetGammaFiber g d u₀ u₁ S).card ≤ 1 := by
  by_cases hdir : ExplainableOn g d u₁ S
  · by_cases hoff : ExplainableOn g d u₀ S
    · exact Or.inl (subsetGammaFiber_eq_univ hdir hoff)
    · refine Or.inr ?_
      rw [subsetGammaFiber_eq_empty hdir hoff]
      simp
  · exact Or.inr (subsetGammaFiber_card_le_one hg hdir)

/-! ## The nondegeneracy hypothesis, and its necessity -/

/-- A stack is **first-level nondegenerate** when no `(d+2)`-subset jointly explains the
direction and the offset.  This is the exact hypothesis under which the direction-blind
ceiling holds; `levelBadScalars_eq_univ_of_degenerate` shows it is necessary. -/
def FirstLevelNondegenerate (g : ZMod p) (d : ℕ) (u₀ u₁ : Fin n → ZMod p) : Prop :=
  ∀ S : Finset (Fin n), S.card = d + 2 →
    ExplainableOn g d u₁ S → ¬ ExplainableOn g d u₀ S

/-- **Necessity of the hypothesis (the degenerate saturation).**  If some `(d+2)`-subset
jointly explains both rows, then EVERY scalar is level-`(d+2)` bad: the count saturates at
`q` and no sub-`q` ceiling can hold.  This is the probe's "direction `a`-close to the code
⟹ `worst = q` trivially" branch, machine-checked. -/
theorem levelBadScalars_eq_univ_of_degenerate {d : ℕ} {u₀ u₁ : Fin n → ZMod p}
    (hdeg : ∃ S : Finset (Fin n), S.card = d + 2 ∧
      ExplainableOn g d u₁ S ∧ ExplainableOn g d u₀ S) :
    levelBadScalars g d (d + 2) u₀ u₁ = Finset.univ := by
  classical
  obtain ⟨S, hScard, hdir, hoff⟩ := hdeg
  apply Finset.eq_univ_iff_forall.mpr
  intro γ
  rw [levelBadScalars, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, S, le_of_eq hScard.symm,
    explainableOn_combined_of_both hoff hdir γ⟩

/-! ## The direction-blind ceiling at the first interior level -/

/-- **The first-interior-level direction-blind ceiling.**  For ANY direction `u₁` (spread
or monomial — the hypothesis never inspects its structure), the scalars whose combined word
is explainable on `≥ d+2 = k+1` points number at most `C(n, k+1)`: the bad set is covered
by the `(k+1)`-subset fibers, and under nondegeneracy each fiber has at most one element.

Contrast with `march_badScalars_card_mul_le`: at thresholds strictly above `d+2` the
glueing/ownership argument sharpens this to `C(n,d+2)/(d+2)`; at the boundary level exactly,
ownership degenerates and the per-subset uniqueness ceiling `C(n,d+2)` is what remains. -/
theorem levelBadScalars_card_le_choose (hg : orderOf g = n) {d : ℕ}
    (u₀ u₁ : Fin n → ZMod p) (hnd : FirstLevelNondegenerate g d u₀ u₁) :
    (levelBadScalars g d (d + 2) u₀ u₁).card ≤ n.choose (d + 2) := by
  classical
  have hcover : levelBadScalars g d (d + 2) u₀ u₁ ⊆
      (Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n))).biUnion
        (fun S => subsetGammaFiber g d u₀ u₁ S) := by
    intro γ hγ
    rw [levelBadScalars, Finset.mem_filter] at hγ
    obtain ⟨-, S, hScard, hexpl⟩ := hγ
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hScard
    refine Finset.mem_biUnion.mpr ⟨T, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩
    · rw [subsetGammaFiber, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, explainableOn_mono hTS hexpl⟩
  calc (levelBadScalars g d (d + 2) u₀ u₁).card
      ≤ ((Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n))).biUnion
          (fun S => subsetGammaFiber g d u₀ u₁ S)).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ S ∈ Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n)),
          (subsetGammaFiber g d u₀ u₁ S).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n)), 1 := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        have hScard : S.card = d + 2 := (Finset.mem_powersetCard.mp hS).2
        by_cases hdir : ExplainableOn g d u₁ S
        · rw [subsetGammaFiber_eq_empty hdir (hnd S hScard hdir)]
          simp
        · exact subsetGammaFiber_card_le_one hg hdir
    _ = n.choose (d + 2) := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The `mcaEvent` consumer at the boundary radius.**  At agreement threshold
`(1−δ)·n ≥ d+2` (non-strict — the level the march theorem's strict hypothesis does NOT
cover), every nondegenerate stack has at most `C(n, d+2) = C(n, k+1)` MCA-bad scalars,
uniformly in the direction. -/
theorem mca_firstLevel_badScalars_card_le_choose (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) (hnd : FirstLevelNondegenerate g d u₀ u₁) :
    (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)).card
      ≤ n.choose (d + 2) := by
  refine le_trans (Finset.card_le_card ?_) (levelBadScalars_card_le_choose hg u₀ u₁ hnd)
  intro γ hγ
  obtain ⟨S, hScard, hwC, -⟩ := (Finset.mem_filter.mp hγ).2
  rw [levelBadScalars, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S, ?_, ?_⟩
  · have h2 : ((d + 2 : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := le_trans hδ hScard
    exact_mod_cast h2
  · obtain ⟨w, ⟨q, hqd, hqw⟩, hagree⟩ := hwC
    refine ⟨q, hqd, fun i hi => ?_⟩
    show u₀ i + γ * u₁ i = q.eval (g ^ (i : ℕ))
    have h1 := hagree i hi
    rw [smul_eq_mul] at h1
    rw [← h1]
    exact hqw i

end ArkLib.ProximityGap.FirstInteriorLevelDirectionBlind

#print axioms ArkLib.ProximityGap.FirstInteriorLevelDirectionBlind.subsetGammaFiber_card_le_one
#print axioms ArkLib.ProximityGap.FirstInteriorLevelDirectionBlind.subsetGammaFiber_trichotomy
#print axioms ArkLib.ProximityGap.FirstInteriorLevelDirectionBlind.levelBadScalars_eq_univ_of_degenerate
#print axioms ArkLib.ProximityGap.FirstInteriorLevelDirectionBlind.levelBadScalars_card_le_choose
#print axioms ArkLib.ProximityGap.FirstInteriorLevelDirectionBlind.mca_firstLevel_badScalars_card_le_choose
