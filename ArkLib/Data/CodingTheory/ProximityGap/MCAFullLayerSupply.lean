/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALYMCeiling

/-!
# Full-layer supply and the exact staircase (#357 round 4)

The window-interior cells pinned so far all follow one pattern: a stack whose bad scalars
biject with the **full layer** of `C(n,t)` witness sets meets the LYM ceiling. This file
names that pattern and proves the conditional exact-staircase law:

* `FullLayerSupply C δ t` — some stack carries `C(n,t)` distinct bad scalars at radius `δ`;
* **`epsMCA_eq_choose_div_of_fullLayerSupply`** — under supply (with floor `t ≥ n/2`
  matching `δ`):  `ε_mca(C, δ) = C(n,t)/q`  **exactly** (LYM above, supply below).

Probe-verified supply instances: `(5,2)` at `δ = 2/5` over `F₁₁`/`F₁₃` (landed exactly in
`MCAWindowInteriorExact.lean`), `(8,3)` at `δ = 1/2` over `p ∈ {1009, 2503, 5003}` —
all strictly inside the window. The issue #357 round-4 comment conjectured a two-regime law:
supply for `q ≫ C(n,t)²` (collision-free regime), and failure of supply below Johnson, making
the layer-attainment boundary exactly the Johnson radius.

**Audit correction (2026-10-28, PG-058): the "must fail below Johnson" half is FALSE as a
blanket statement.**  Polynomial (`poly(n)/q`) Johnson-range bounds do not contradict layer
attainment when the layer size `C(n,t)` is itself polynomial or constant.  Concretely, on the
first staircase layer `t = n`: `fullLayerSupply_top_of_not_mem` shows that for every code
containing `0` and missing some word, `FullLayerSupply C 0 n` holds at radius `δ = 0`; e.g. the
length-4 constant code over `F₅` (Reed–Solomon of dimension 1, Johnson radius
`1 − √(1/4) = 1/2`) has full-layer supply at `δ = 0 < 1/2`
(`fullLayerSupply_constCode_F5`).  Any valid "supply fails below Johnson" statement must be
restricted to an asymptotic interior regime where the layer `C(n,t)` grows super-polynomially,
with its quantifiers stated and proved; nothing of that kind is proved here.  The
collision-free-regime half and the prize-scale question (the collision census of the
interpolation-scalar map) are unaffected.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread ProximityGap.MCALYMCeiling

namespace ProximityGap.MCAFullLayerSupply

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Full-layer supply**: some stack carries a full layer's worth (`C(n,t)`) of distinct
bad scalars at radius `δ`. The probe-measurable per-cell hypothesis of the staircase law. -/
def FullLayerSupply (C : Set (ι → A)) (δ : ℝ≥0) (t : ℕ) : Prop :=
  ∃ u : WordStack A (Fin 2) ι, ∃ G : Finset F,
    G.card = (Fintype.card ι).choose t ∧
    ∀ γ ∈ G, mcaEvent (F := F) C δ (u 0) (u 1) γ

/-- **The exact staircase law (conditional).** With floor `t` matching the radius
(`t ≤ (1−δ)·n`, `n ≤ 2t`) and full-layer supply:

  `ε_mca(C, δ) = C(n, t)/q`  exactly —

the LYM ceiling above, the supplied layer below. Every probe-found full-layer stack
instantly pins its cell. -/
theorem epsMCA_eq_choose_div_of_fullLayerSupply (C : Submodule F (ι → A)) {δ : ℝ≥0}
    {t : ℕ}
    (hfloor : (t : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι : ℝ≥0))
    (hhalf : Fintype.card ι ≤ 2 * t)
    (hsupply : FullLayerSupply (F := F) (C : Set (ι → A)) δ t) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      = (((Fintype.card ι).choose t : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm (epsMCA_le_choose_div C δ hfloor hhalf) ?_
  obtain ⟨u, G, hGcard, hGbad⟩ := hsupply
  have h := epsMCA_ge_card_div_of_mcaEvent_set (F := F) (A := A)
    (C : Set (ι → A)) δ u G hGbad
  rwa [hGcard] at h

/-- Supply is monotone-meaningful: it forces the field to clear the layer
(`C(n,t) ≤ q`) — the pigeonhole floor of the census regime. -/
theorem card_le_of_fullLayerSupply {C : Set (ι → A)} {δ : ℝ≥0} {t : ℕ}
    (hsupply : FullLayerSupply (F := F) C δ t) :
    (Fintype.card ι).choose t ≤ Fintype.card F := by
  obtain ⟨u, G, hGcard, -⟩ := hsupply
  calc (Fintype.card ι).choose t = G.card := hGcard.symm
    _ ≤ Fintype.card F := by
        simpa using Finset.card_le_univ G

/-! ## Full-layer supply below Johnson: the top layer `t = n` at radius `0` -/

/-- **Top-layer supply at radius `0`.** If `0 ∈ C` and some word `v ∉ C`, then the stack
`(0, v)` has the single bad scalar `γ = 0` with witness set `S = univ`: the line is the codeword
`0`, while no codeword agrees with `v` everywhere.  So `FullLayerSupply C 0 n` holds
(`C(n,n) = 1`).  This refutes the blanket claim that full-layer supply must fail below the
Johnson radius (the radius `0` is below Johnson for every code of rate `< 1`). -/
theorem fullLayerSupply_top_of_not_mem {C : Set (ι → A)} (h0 : (0 : ι → A) ∈ C)
    {v : ι → A} (hv : v ∉ C) :
    FullLayerSupply (F := F) C 0 (Fintype.card ι) := by
  classical
  refine ⟨Matrix.of ![0, v], {0}, by simp, ?_⟩
  intro γ hγ
  rw [Finset.mem_singleton] at hγ
  subst hγ
  refine ⟨Finset.univ, by simp, ⟨0, h0, fun i _ => by simp⟩, ?_⟩
  rintro ⟨v₀, -, v₁, hv₁, hagree⟩
  apply hv
  have hv₁v : v₁ = v := funext fun i => by
    simpa using (hagree i (Finset.mem_univ i)).2
  exact hv₁v ▸ hv₁

/-- The constant code of length `4` over `F₅` (= Reed–Solomon of dimension `1`). -/
def constCodeF5 : Set (Fin 4 → ZMod 5) := {f | ∀ i j, f i = f j}

/-- **Concrete witness (PG-058).** The length-4 constant code over `F₅` has full-layer supply
`C(4,4) = 1` at radius `δ = 0`, strictly below its Johnson radius `1 − √(1/4) = 1/2`: the stack
`(0, (0,0,1,1))` has `γ = 0` as a bad scalar on all coordinates. -/
theorem fullLayerSupply_constCode_F5 :
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    FullLayerSupply (F := ZMod 5) constCodeF5 0 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h0 : (0 : Fin 4 → ZMod 5) ∈ constCodeF5 := fun _ _ => rfl
  have hv : (![0, 0, 1, 1] : Fin 4 → ZMod 5) ∉ constCodeF5 := fun h => by
    have := h 0 2
    simp at this
  simpa using fullLayerSupply_top_of_not_mem (F := ZMod 5) h0 hv

/-! ## Source audit -/

#print axioms epsMCA_eq_choose_div_of_fullLayerSupply
#print axioms card_le_of_fullLayerSupply
#print axioms fullLayerSupply_top_of_not_mem
#print axioms fullLayerSupply_constCode_F5

end ProximityGap.MCAFullLayerSupply
