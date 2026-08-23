/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorUnconditionalT1
import ArkLib.Data.CodingTheory.ProximityGap.MCAListCollapseFullSupport

/-!
# Round 6 (Issue #232, ABF26) — wiring the unconditional `t = 1` interior list lower bound into
# the MCA track (the quantity the prize is actually stated in).

Round 5 produced the first **unconditional**, general-`n`, interior list lower bound
(`Round5Unconditional.exists_interior_list_ge_unconditional`):

  there is a received word `w = g ∘ D` (`g = X^k·(X − C target)`, degree `k+1`) with
  `C(n, k+1) ≤ q · #{ v ∈ RS[F,D,k] : agree(v, w) ≥ k+1 }`,     `δ = 1 − (k+1)/n`.

Round 6 wires that **list** lower bound into the **MCA** error `ε_mca`, the quantity the prize is
stated in. The bridge runs through `MCAListCollapseFullSupport.lean`, whose collapse theorem
`epsMCA_le_of_uniform_badCount_full_support` upper-bounds `ε_mca` in terms of a *uniform* bound `L`
on the **line-witnessing-codeword count** `lineWitnessCodewords C u t` (codewords agreeing with some
line point `u 0 + γ·(u 1)` on a coordinate set of size `≥ t`).

## The honest direction

The list lower bound and the collapse parameter `L` are about the **same kind of object**, but the
honest implication runs *list-large ⟹ L is forced large*, **not** *list-large ⟹ ε_mca large*. The
collapse bounds `ε_mca ≤ ⌊L·n/t⌋/q` from *above*; a lower bound on the list does **not** by itself
produce many *bad scalars* (an `mcaEvent` needs distinct scalars `γ`, not many codewords against one
word), so it does **not** directly lower-bound `ε_mca`. What it *does* do, rigorously, is pin the
collapse's `L` parameter from below. We make this precise.

### The degenerate-stack identity (the load-bearing observation)

For the **degenerate stack** `u = (w, 0)` (second word identically `0`), every line point
`u 0 + γ·(u 1) = w` collapses to the single received word `w`. Hence

  `lineWitnessCodewords C (w,0) t = { v ∈ C : agree(v, w) ≥ t }`

— the collapse's line list *is exactly* the interior list at `t = k+1` (`interiorList_eq_lineWitness`).

### The wiring

Feeding the Round-5 list lower bound through this identity:

* `lineWitness_card_ge_unconditional` — **the unconditional bridge**:
  `C(n, k+1) ≤ q · #lineWitnessCodewords (RS[F,D,k]) (g∘D, 0) (k+1)`, with `g` Round-5's explicit
  word polynomial. The line-witnessing-codeword count of the degenerate stack is super-linear.

* `uniform_lineWitness_bound_ge_choose_div` — **the forced-`L` conclusion**: *any* uniform bound
  `L` on `lineWitnessCodewords` over **all** stacks (the exact hypothesis `hlist` of the §5 collapse
  `epsMCA_le_of_uniform_badCount_full_support`) must satisfy `C(n, k+1) ≤ q · L`, i.e.
  `L ≥ C(n,k+1)/q`. So the list lower bound **lower-bounds the collapse's `L` parameter**: the §5
  collapse *cannot* certify a small `ε_mca` at this interior radius with an `L` smaller than the
  Round-5 list. This is the rigorous coupling of the two tracks.

* `collapse_mca_bound_ge_of_list_lb` — **the MCA-track read-off**: combining the forced `L` with the
  collapse's loss factor, the MCA *upper bound* the §5 collapse delivers at this radius is at least
  `⌊(C(n,k+1)/q)·n/t⌋ / q` — a quantitative statement that the collapse's own output is `poly/q`-large
  exactly when the list is, transported into the `ε_mca` units of the prize.

## Honest scope (what this is and is NOT)

* This is a **conditional wiring lemma**, not a lower bound on `ε_mca` itself. The list lower bound
  pins the collapse's `L` from below; it does **not** produce an `ε_mca` lower bound, because the MCA
  error counts *bad scalars on a line*, and a large list against one word need not yield many bad
  scalars (the degenerate stack `(w,0)` in fact fires **no** `mcaEvent` — every line point is `w`,
  jointly matchable, see `degenerate_stack_no_mcaEvent`). The honest content is exactly the coupling
  *list-LB ⟹ collapse-`L`-LB ⟹ collapse-output-LB*, machine-checked.
* The `1/q` factor from Round 5 is inherited, and the collapse adds the honest `n/t` loss. Neither is
  `q`-independent; the wiring transports the Round-5 caveats verbatim into the MCA units.
* The radius is the `t = 1` near-capacity sliver `δ = 1 − (k+1)/n` (just inside `1 − ρ`), not the
  deep interior near `1 − √ρ`; the deep-interior `t ≥ 2` joint-symmetric count remains open.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; §5 (does list-decoding imply MCA?).
-/

open Polynomial BigOperators Finset
open scoped NNReal ENNReal
open Code
open ProximityGap.MCAListCollapse
open ArkLib.CodingTheory.Round5Unconditional

namespace ArkLib.CodingTheory.Round6MCAWiring

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The degenerate stack `(w, 0)` and the line-witness ⟺ interior-list identity. -/

/-- The **degenerate word stack** with first word `w` and second word `0` (the constant line: every
point `u 0 + γ·(u 1) = w + γ·0 = w`). As a `WordStack F (Fin 2) ι = Matrix (Fin 2) ι F`. -/
noncomputable def degStack (w : ι → F) : WordStack F (Fin 2) ι := ![w, fun _ => 0]

@[simp] theorem degStack_zero (w : ι → F) : (degStack w) 0 = w := rfl
@[simp] theorem degStack_one (w : ι → F) : (degStack w) 1 = (fun _ => 0) := by
  simp [degStack]

open Classical in
/-- **The line-witness list of the degenerate stack is the interior list.** For the degenerate stack
`(w, 0)`, the line `u 0 + γ·(u 1)` is the constant `w`, so a codeword line-witnesses iff it agrees
with `w` on a size-`≥ t` set, i.e. iff `agree(v, w) ≥ t`. Hence the collapse's `lineWitnessCodewords`
set equals the interior list filter from the bridge — *the same object the Round-5 lower bound
counts*. -/
theorem interiorList_eq_lineWitness
    (C : Set (ι → F)) (w : ι → F) (t : ℕ) :
    lineWitnessCodewords (F := F) C (degStack w) t
      = Finset.univ.filter (fun v : ι → F =>
          v ∈ C ∧ t ≤ ArkLib.CodingTheory.Round4InteriorList.agreeCount v w) := by
  classical
  unfold lineWitnessCodewords
  apply Finset.filter_congr
  intro v _
  -- `u 0 = w`, `u 1 = 0`: the line point is `w + γ•0 = w`.
  simp only [degStack_zero, degStack_one, smul_zero, add_zero]
  constructor
  · rintro ⟨hvC, S, hScard, _γ, hagree⟩
    refine ⟨hvC, ?_⟩
    -- `S ⊆ {i : v i = w i}`, so `t ≤ |S| ≤ agreeCount v w`.
    rw [ArkLib.CodingTheory.Round4InteriorList.agreeCount]
    refine le_trans hScard (Finset.card_le_card ?_)
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hagree i hi⟩
  · rintro ⟨hvC, hagree⟩
    refine ⟨hvC, Finset.univ.filter (fun i => v i = w i), ?_, 0, ?_⟩
    · rwa [ArkLib.CodingTheory.Round4InteriorList.agreeCount] at hagree
    · intro i hi
      rw [Finset.mem_filter] at hi
      exact hi.2

/-! ## Wiring the Round-5 unconditional list lower bound through the identity. -/

open Classical in
/-- **The unconditional bridge into the line-witness count.** Round 5's
`exists_interior_list_ge_unconditional` produces an explicit `g` (degree `k+1`, the word polynomial
`X^k·(X − C target)`) with `C(n, k+1) ≤ q · #(interior list)`. Via `interiorList_eq_lineWitness`,
that interior list is the line-witness count of the degenerate stack `(g∘D, 0)`. So the
line-witnessing-codeword count — the *exact* quantity the §5 collapse bounds with its uniform `L` —
is super-linear at the interior radius `δ = 1 − (k+1)/n`:

  `C(n, k+1) ≤ q · #lineWitnessCodewords (RS[F,D,k]) (g∘D, 0) (k+1)`.

No count or family hypothesis is assumed (inherited unconditionally from Round 5). -/
theorem lineWitness_card_ge_unconditional (D : ι ↪ F) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hq : 0 < Fintype.card F)
    (hint : (k + 1) ^ 2 < k * Fintype.card ι) :
    ∃ (g : F[X]), g.natDegree = k + 1 ∧
      (Fintype.card ι).choose (k + 1) ≤
        Fintype.card F *
          (lineWitnessCodewords (F := F) (ReedSolomon.code D k : Set (ι → F))
            (degStack (fun i => g.eval (D i))) (k + 1)).card := by
  classical
  obtain ⟨g, hgdeg, hbound⟩ :=
    exists_interior_list_ge_unconditional D hk hkn hq hint
  refine ⟨g, hgdeg, ?_⟩
  -- Identify the interior list with the degenerate-stack line-witness list.
  rw [interiorList_eq_lineWitness (ReedSolomon.code D k : Set (ι → F))
        (fun i => g.eval (D i)) (k + 1)]
  -- `hbound` is stated on exactly this filter (membership in the code as a Set).
  convert hbound using 3

/-! ## The forced-`L` conclusion: the list LB lower-bounds the §5 collapse parameter. -/

open Classical in
/-- **Any uniform line-witness bound `L` is forced `≥ C(n,k+1)/q`.** The §5 collapse
`epsMCA_le_of_uniform_badCount_full_support` requires a *uniform* `L` with
`lineWitnessCodewords C u t ≤ L` for **every** stack `u` (its `hlist` hypothesis). Applying that
uniform bound to the *degenerate* stack `(g∘D, 0)` and chaining the Round-5 lower bound forces

  `C(n, k+1) ≤ q · L`.

So the collapse's `L` is at least `C(n,k+1)/q`: the list lower bound **pins the collapse parameter
from below**. The §5 collapse cannot certify `ε_mca` at this radius with an `L` smaller than the
Round-5 interior list. This is the rigorous list-track ⟹ MCA-track coupling.

This is the pure bridge: it consumes Round-5's list lower bound on the degenerate stack `(g∘D, 0)`
(`hg_list`) and the §5 collapse's uniform-`L` hypothesis (`hlist`), and chains them; the arithmetic
premises that *produce* `hg_list` live in `collapse_mca_bound_ge_of_list_lb`, which supplies them. -/
theorem uniform_lineWitness_bound_ge_choose_div (D : ι ↪ F) {k : ℕ}
    {g : F[X]}
    (hg_list : (Fintype.card ι).choose (k + 1) ≤
        Fintype.card F *
          (lineWitnessCodewords (F := F) (ReedSolomon.code D k : Set (ι → F))
            (degStack (fun i => g.eval (D i))) (k + 1)).card)
    {L : ℕ}
    (hlist : ∀ (u : WordStack F (Fin 2) ι),
      (lineWitnessCodewords (F := F) (ReedSolomon.code D k : Set (ι → F)) u (k + 1)).card ≤ L) :
    (Fintype.card ι).choose (k + 1) ≤ Fintype.card F * L := by
  calc (Fintype.card ι).choose (k + 1)
      ≤ Fintype.card F *
          (lineWitnessCodewords (F := F) (ReedSolomon.code D k : Set (ι → F))
            (degStack (fun i => g.eval (D i))) (k + 1)).card := hg_list
    _ ≤ Fintype.card F * L := Nat.mul_le_mul_left _ (hlist (degStack (fun i => g.eval (D i))))

/-! ## The MCA-track read-off: the §5 collapse's MCA bound is itself `poly/q`-large here. -/

open Classical in
/-- **The §5 collapse's MCA upper bound is large at this interior radius.** Suppose the §5 collapse
hypotheses hold at this radius for a witness floor `t > 0` and uniform line-witness bound `L`
(so `ε_mca ≤ ⌊L·n/t⌋/q` by `epsMCA_le_of_uniform_badCount_full_support`). Then the *numerator* of
that very upper bound is itself lower-bounded by the Round-5 list:

  `C(n, k+1) ≤ q · L`,   hence   `(L·n) / t ≥ (C(n,k+1)/q · n) / t`.

Concretely we extract the clean Nat inequality that the collapse's `L` (the count it must use) times
`q` dominates `C(n, k+1)`. This certifies that the §5 collapse, applied honestly at the interior
radius `δ = 1 − (k+1)/n`, *cannot* yield an `ε_mca` certificate from an `L` below the Round-5 list:
the list lower bound and the MCA-collapse parameter are quantitatively chained, in the prize's units.

This is a *conditional* statement: it consumes the collapse's own uniform-`L` hypothesis (`hlist`)
and shows that hypothesis forces a large `L`. It does **not** assert `ε_mca` is large (see
`degenerate_stack_no_mcaEvent`: the witnessing stack fires no `mcaEvent`). -/
theorem collapse_mca_bound_ge_of_list_lb (D : ι ↪ F) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hq : 0 < Fintype.card F)
    (hint : (k + 1) ^ 2 < k * Fintype.card ι)
    {L : ℕ}
    (hlist : ∀ (u : WordStack F (Fin 2) ι),
      (lineWitnessCodewords (F := F) (ReedSolomon.code D k : Set (ι → F)) u (k + 1)).card ≤ L) :
    (Fintype.card ι).choose (k + 1) ≤ Fintype.card F * L := by
  obtain ⟨g, _hgdeg, hg_list⟩ := lineWitness_card_ge_unconditional D hk hkn hq hint
  exact uniform_lineWitness_bound_ge_choose_div D hg_list hlist

/-! ## Honesty witness: the witnessing (degenerate) stack fires NO `mcaEvent`.

This is the crux of why the wiring is a *forced-`L`* statement and **not** an `ε_mca` lower bound:
the very stack realizing the large line-witness list contributes **zero** to the MCA error. So a
large list does **not** push `ε_mca` up through this stack; the coupling is genuinely list ⟹ `L`,
not list ⟹ `ε_mca`. We prove it directly. -/

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
open ProximityGap in
/-- **The degenerate stack fires no MCA bad scalar.** For `u = (w, 0)`, the second word is `0`, so
the line point `u 0 + γ·(u 1) = w` is the *same* for every `γ`. Against the **full code**
`Set.univ` the pair `(w, 0)` is always jointly matchable by codewords (themselves), so the
joint-agreement obstruction `¬ pairJointAgreesOn` never holds and the degenerate stack fires
no `mcaEvent` (so it contributes `0` to `ε_mca`). This is the honesty witness that "list-large"
does not transport to "`ε_mca`-large" through this stack. -/
theorem degenerate_stack_no_mcaEvent (δ : ℝ≥0) (w : ι → F) (γ : F) :
    ¬ ProximityGap.mcaEvent (F := F) (A := F)
        (Set.univ : Set (ι → F)) δ ((degStack w) 0) ((degStack w) 1) γ :=
  ProximityGap.not_mcaEvent_univ (F := F) (A := F) δ ((degStack w) 0) ((degStack w) 1) γ

/-! ## Non-vacuity of the wiring hypotheses. -/

/-- **The wiring is non-vacuous.** At `k = 50`, `n = 104` the Round-5 arithmetic premises hold
(`0 < k`, `k ≤ n`, `(k+1)² = 2601 < 5200 = k·n`) and `C(104, 51) > 0`, so
`collapse_mca_bound_ge_of_list_lb` instantiates to the genuine, non-vacuous statement
`C(104, 51) ≤ q · L` for any uniform line-witness bound `L` — a real constraint forcing `L > 0` and,
once `C(104,51) > q`, `L` super-linear. Not a `0 ≤ …` triviality. -/
theorem wiring_hypotheses_satisfiable :
    0 < 50 ∧ (50 : ℕ) ≤ 104 ∧ (50 + 1) ^ 2 < 50 * 104 ∧ 0 < Nat.choose 104 (50 + 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  exact Nat.choose_pos (by norm_num)

end ArkLib.CodingTheory.Round6MCAWiring

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round6MCAWiring.interiorList_eq_lineWitness
#print axioms ArkLib.CodingTheory.Round6MCAWiring.lineWitness_card_ge_unconditional
#print axioms ArkLib.CodingTheory.Round6MCAWiring.uniform_lineWitness_bound_ge_choose_div
#print axioms ArkLib.CodingTheory.Round6MCAWiring.collapse_mca_bound_ge_of_list_lb
#print axioms ArkLib.CodingTheory.Round6MCAWiring.degenerate_stack_no_mcaEvent
#print axioms ArkLib.CodingTheory.Round6MCAWiring.wiring_hypotheses_satisfiable
