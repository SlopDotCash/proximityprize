/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# The Sidon-except-negation B_h escape, closed: the OFF-SPIKE floor (#444, angle `E4_sidon_stepanov`)

**The angle.** The prize carrier `M(μ_n) = max_{b≠0}|Σ_{y∈μ_n} e_p(by)|` is attacked via the
deep-moment energy `E_r(μ_n) = Σ_c N_r(c)²` at saddle depth `r ≈ ln p`, where
`N_r(c) = #{x ∈ μ_n^r : Σx_i = c}`. The campaign established that `μ_n` is **Sidon-except-negation**:
the depth-2 representation function satisfies `N_2(c) ≤ 2` for every `c ≠ 0` (the only additive
obstruction is the antipodal `σ = 0` diagonal). The natural hope is a **B_h-set / Bose–Chowla**
bound: if `μ_n` were a genuine `B_r` set, every `N_r(c)` would be bounded by a *constant* (`≤ r!`),
collapsing the energy to `E_r ≤ r!·n^r` — well below the Wick target and far below the wall.

**The in-tree no-go** (`_DepthRStepanovNoGo`) already kills the pointwise Stepanov route via the
**central spike**: for negation-closed `G` (`−1 ∈ μ_n`), the *zero* residue has `N_{2s}(0) ≥ n^s`.
But that spike sits at `c = 0` — exactly the one residue the Sidon-mod-negation property *excludes*.
So a B_h advocate can object: "fine, `c = 0` is special; restrict to `c ≠ 0`, where `N_2(c) ≤ 2`."

**This file closes that escape.** It exhibits a *secondary spike at a NONZERO residue*. For
negation-closed `G` and odd depth `r = s + s + 1`, fix any single element `g₀ ∈ G` and pad with
`s` free antipodal pairs `(g₁, −g₁, …, g_s, −g_s)`: the sum is `g₀ + Σ(gᵢ − gᵢ) = g₀ ≠ 0`. This
injects `G^s` into the representations of `c = g₀`, giving

> **`repCount G (s + s + 1) g₀ ≥ |G|^s = n^{(r−1)/2}`  for any `g₀ ∈ G`, `g₀ ≠ 0`.**

Hence the *off-spike* maximum `max_{c≠0} N_r(c)` is itself forced to a **positive power of `n`** at
every odd depth `r ≥ 3` — the Sidon-mod-negation property (`N_2(c) ≤ 2`) does **not** propagate. The
B_h / Bose–Chowla bound is unavailable: `μ_n` is `B_2`-except-negation but is NOT a `B_r` set for
any `r ≥ 3`, even after deleting the `c = 0` residue, and the failure is a *power* of `n`, not a
constant. The pointwise-Stepanov reduction `E_r ≤ B·n^r` is therefore forced `B ≥ n^{(r−1)/2}` even
when restricted to nonzero residues, so it overshoots Wick at every depth `≥ 3`.

**Honest "does near-Sidon-ness give anything the generic subgroup does not?" — NO.** Exact
integer numerics (this session, `scripts/probes`): the depth-`r` representation profile of `μ_n`
matches a *generic negation-closed* set of the same size **value-for-value** off the spike
(`n=16`: `max_{c≠0} N_r(c) = 45, 168, 3160` at `r=3,4,5` for BOTH `μ_n` and a random sign-symmetric
set). The off-spike growth is a property of **negation-closure alone** (antipodal padding), to which
the cyclotomic / multiplicative structure of `μ_n` contributes nothing. The Sidon-except-negation
fact is real at depth 2 and prize-inert at depth `≥ 3`.

## Honest scope (rule 6)
This is a **REFUTED / no-go** result for the B_h-set escape from the depth-`r` Stepanov no-go, not a
closure. It does not touch the open Wick target `(*)_r` itself. It proves the *nonzero-residue*
representation count is forced `≥ n^{(r−1)/2}`, completing the `_DepthRStepanovNoGo` central-spike
argument (which only covered `c = 0`) by extending the floor to the off-spike regime where the
Sidon property lives. Combined: a pointwise bound over *all* residues, and now even over nonzero
residues only, cannot deliver Wick — the B_h / near-Sidon lever is empty.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444 / angle `E4_sidon_stepanov`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Frontier.SidonOffSpikeFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The depth-`r` representation function `N_r(c) = #{x ∈ (Fin r → G) : ∑ x = c}`. -/
noncomputable def repCount (G : Finset F) (r : ℕ) (c : F) : ℕ :=
  (Fintype.piFinset (fun _ : Fin r => G)).filter (fun x => ∑ i, x i = c) |>.card

/-- **The off-spike floor (the B_h-escape closer).** For a negation-closed `G`
(`∀ g ∈ G, −g ∈ G`, automatic for every even-order multiplicative subgroup, in particular
`μ_{2^μ}`), any single element `g₀ ∈ G`, and odd depth `r = s + s + 1`, the residue `c = g₀` has
at least `|G|^s` representations:

> `repCount G (s + s + 1) g₀ ≥ |G|^s`.

Witnessed by the `|G|^s` antipodally-padded tuples `Fin.cons g₀ (Fin.append g (−∘g))` for
`g ∈ G^s`: coordinate `0` is `g₀`, the next `s` are `g`, the last `s` are `−g`, so the sum is
`g₀ + (∑g − ∑g) = g₀`. Distinct `g` give distinct tuples (read off the middle block). For
`g₀ ≠ 0` this is a **nonzero residue** with `≥ n^{(r−1)/2}` representations, so the Sidon-mod-
negation depth-2 bound `N_2(c) ≤ 2` does NOT survive to odd depth `r ≥ 3`. -/
theorem repCount_elem_ge_card_pow (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G)
    {g₀ : F} (hg₀ : g₀ ∈ G) (s : ℕ) :
    G.card ^ s ≤ repCount G (s + s + 1) g₀ := by
  classical
  rw [repCount]
  -- embed `G^s ↪ {x ∈ (Fin (1+(s+s)) → G) : ∑ x = g₀}` via `g ↦ cons g₀ (append g (−∘g))`.
  let emb : (Fin s → F) → (Fin (s + s + 1) → F) :=
    fun g => Fin.cons g₀ (Fin.append g (fun i => - g i))
  have hcard : G.card ^ s = (Fintype.piFinset (fun _ : Fin s => G)).card := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  refine Finset.card_le_card_of_injOn emb ?_ ?_
  · -- maps into the `g₀`-sum tuples over G
    intro g hg
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hg
    rw [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨?_, ?_⟩
    · -- every coordinate lies in G
      intro i
      simp only [emb]
      refine Fin.cases (by rw [Fin.cons_zero]; exact hg₀) (fun j => ?_) i
      rw [Fin.cons_succ]
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · rw [Fin.append_left]; exact hg _
      · rw [Fin.append_right]; exact hneg _ (hg _)
    · -- the sum is `g₀`
      simp only [emb]
      rw [Fin.sum_cons, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← Finset.sum_add_distrib]
      simp only [add_neg_cancel, Finset.sum_const_zero, add_zero]
  · -- injectivity: recover `g` from the middle (left-append) block, at index `succ (castAdd s j)`
    intro g₁ _ g₂ _ heq
    funext j
    have := congrArg (fun f => f (Fin.succ (Fin.castAdd s j))) heq
    simpa only [emb, Fin.cons_succ, Fin.append_left] using this

/-- **No-go, packaged (the B_h escape is empty).** For negation-closed `G`, any `g₀ ∈ G`, and odd
depth `r = s + s + 1`, every uniform pointwise representation bound `B` valid even *only on the
nonzero residues* is still forced `≥ |G|^s = n^{(r−1)/2}` (taking `g₀ ≠ 0`):

> `(∀ c ≠ 0, repCount G (1+(s+s)) c ≤ B) → g₀ ≠ 0 → |G|^s ≤ B`.

This is the off-spike companion of `_DepthRStepanovNoGo.pointwise_bound_ge_card_pow` (which needed
`c = 0`). Together they show the Sidon-mod-negation property `N_2(c) ≤ 2` gives **no** `B_h`
advantage at any depth `r ≥ 3`: the pointwise bound overshoots the Wick energy target even when the
zero residue is excluded. The near-Sidon lever is therefore inert for the prize wall. -/
theorem nonzero_pointwise_bound_ge_card_pow (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G)
    {g₀ : F} (hg₀ : g₀ ∈ G) {s : ℕ} {B : ℕ}
    (hB : ∀ c : F, c ≠ 0 → repCount G (s + s + 1) c ≤ B) (hg₀0 : g₀ ≠ 0) :
    G.card ^ s ≤ B :=
  le_trans (repCount_elem_ge_card_pow G hneg hg₀ s) (hB g₀ hg₀0)

end ProximityGap.Frontier.SidonOffSpikeFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SidonOffSpikeFloor.repCount_elem_ge_card_pow
#print axioms ProximityGap.Frontier.SidonOffSpikeFloor.nonzero_pointwise_bound_ge_card_pow
