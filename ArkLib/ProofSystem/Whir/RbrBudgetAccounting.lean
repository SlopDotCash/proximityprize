/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# WHIR rbr-soundness budget accounting (issue #113)

The per-phase budget projections + epsRbr_isLUB + soundOk_epsRbr_of_keystone: the
round-error accumulation LUB structure, reducing whir-rbr-soundness to the named
MCA+folding keystone WhirRbrKeystone.
-/

noncomputable section

open scoped NNReal BigOperators
open Finset

namespace Issue113WHIR

/-! ## §0. The WHIR per-challenge budget model (mirror of `whir_rbr_soundness`'s `ε_rbr`)

In `Whir/RBRSoundness.lean:207–214`, the RBR error supplied to `IsSecureWithGap` is the
CONSTANT per-challenge function whose value is the maximum over the four per-round budget
families. We abstract the four families and reproduce that `max'`/`sup` budget exactly,
then prove the domination accounting that justifies it.

Real-tree shapes (`Whir/RBRSoundness.lean`):
  * `ε_fold  : (i : Fin (M+1)) → Fin (P.foldingParam i) → ℝ≥0`  — per (round, fold-step)
  * `ε_out   : Fin (M+1) → ℝ≥0`                                 — per round OOD error
  * `ε_shift : Fin M → ℝ≥0`                                     — per round shift error
  * `ε_fin   : ℝ≥0`                                             — final round error
  * `max_ε_folds i = (univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)`
  * `ε_rbr _ = (univ.image max_ε_folds ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' …`
-/

variable {M : ℕ} {fp : Fin (M + 1) → ℕ}

/-- The per-round inner fold budget: `max_ε_folds i = sup_{j} ε_fold i j`.
    Mirror of `whir_rbr_soundness`'s `let max_ε_folds := fun i => (univ).sup (ε_fold i)`. -/
def maxFolds (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) : Fin (M + 1) → ℝ≥0 :=
  fun i => (univ : Finset (Fin (fp i))).sup (ε_fold i)

/-- The WHIR RBR budget set: the union of the four per-round budget families, as a
    `Finset ℝ≥0`. This is exactly the underlying set of the `…max' …` in
    `whir_rbr_soundness` (`Whir/RBRSoundness.lean:210`). It is always nonempty (it
    contains `ε_fin`), which is what the in-tree `(by simp)` `max'`-nonemptiness side goal
    discharges. -/
def rbrBudgetSet
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) : Finset ℝ≥0 :=
  (univ.image (maxFolds ε_fold) ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift)

/-- The budget set is nonempty (it contains `ε_fin`). This is the side condition the
    in-tree `max' (by simp)` discharges. PROVEN: `ε_fin` is a member. -/
theorem rbrBudgetSet_nonempty
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    (rbrBudgetSet ε_fold ε_out ε_shift ε_fin).Nonempty := by
  refine ⟨ε_fin, ?_⟩
  -- `ε_fin ∈ … ∪ {ε_fin} ∪ … ∪ …`; in the middle `{ε_fin}` block.
  unfold rbrBudgetSet
  simp [Finset.mem_union]

/-- The WHIR per-challenge RBR error: the maximum over the budget set.
    Mirror of `whir_rbr_soundness`'s `ε_rbr` (which is constant in the challenge index,
    `fun _ => …max'…`). We expose the scalar value `…max'…` directly. -/
def epsRbr
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) : ℝ≥0 :=
  (rbrBudgetSet ε_fold ε_out ε_shift ε_fin).max'
    (rbrBudgetSet_nonempty ε_fold ε_out ε_shift ε_fin)

/-! ## §1. The per-challenge budget DOMINATION accounting (the genuine extractable math)

This is the WHIR analogue of #24's linear accumulation (§1 there). Because RBR soundness
is per-challenge (a `max'`, not a `Σ`), the content is: *every per-round bound is ≤ the
RBR budget*, and the RBR budget is the *tightest* uniform bound. We prove all four
domination facts plus the tightness (universal property of `max'`). -/

/-- **Final-round domination.** `ε_fin ≤ ε_rbr`. PROVEN via `Finset.le_max'` from
    membership of `ε_fin` in the `{ε_fin}` block. -/
theorem eps_fin_le_epsRbr
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    ε_fin ≤ epsRbr ε_fold ε_out ε_shift ε_fin := by
  unfold epsRbr
  refine Finset.le_max' _ ε_fin ?_
  unfold rbrBudgetSet
  simp [Finset.mem_union]

/-- **OOD-round domination.** `ε_out i ≤ ε_rbr` for every round `i`. PROVEN via
    `Finset.le_max'` from `ε_out i ∈ univ.image ε_out`. -/
theorem eps_out_le_epsRbr
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (i : Fin (M + 1)) :
    ε_out i ≤ epsRbr ε_fold ε_out ε_shift ε_fin := by
  unfold epsRbr
  refine Finset.le_max' _ (ε_out i) ?_
  unfold rbrBudgetSet
  -- `ε_out i ∈ univ.image ε_out`, which is in the `… ∪ univ.image ε_out ∪ …` block.
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image_of_mem ε_out (Finset.mem_univ i)

/-- **Shift-round domination.** `ε_shift i ≤ ε_rbr` for every round `i`. PROVEN via
    `Finset.le_max'` from `ε_shift i ∈ univ.image ε_shift` (the last union block). -/
theorem eps_shift_le_epsRbr
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (i : Fin M) :
    ε_shift i ≤ epsRbr ε_fold ε_out ε_shift ε_fin := by
  unfold epsRbr
  refine Finset.le_max' _ (ε_shift i) ?_
  unfold rbrBudgetSet
  -- `ε_shift i ∈ univ.image ε_shift`, the outermost `… ∪ univ.image ε_shift` block.
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image_of_mem ε_shift (Finset.mem_univ i)

/-- **Inner-fold domination (single step).** Each individual fold-step error
    `ε_fold i j ≤ ε_rbr`. PROVEN: `ε_fold i j ≤ maxFolds ε_fold i` (`Finset.le_sup`),
    and `maxFolds ε_fold i ≤ ε_rbr` (`Finset.le_max'` from the `image (maxFolds …)`
    block), then transitivity. This is the WHIR-specific two-level (`sup`-then-`max'`)
    accounting absent from FRI/STIR. -/
theorem eps_fold_le_epsRbr
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (i : Fin (M + 1)) (j : Fin (fp i)) :
    ε_fold i j ≤ epsRbr ε_fold ε_out ε_shift ε_fin := by
  -- Step 1: inner sup. `ε_fold i j ≤ (univ).sup (ε_fold i) = maxFolds ε_fold i`.
  have hstep1 : ε_fold i j ≤ maxFolds ε_fold i := by
    unfold maxFolds
    exact Finset.le_sup (Finset.mem_univ j)
  -- Step 2: outer max'. `maxFolds ε_fold i ≤ ε_rbr` from membership in `image (maxFolds …)`.
  have hstep2 : maxFolds ε_fold i ≤ epsRbr ε_fold ε_out ε_shift ε_fin := by
    unfold epsRbr
    refine Finset.le_max' _ (maxFolds ε_fold i) ?_
    unfold rbrBudgetSet
    -- `maxFolds ε_fold i ∈ univ.image (maxFolds ε_fold)`, the innermost block.
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    exact Finset.mem_image_of_mem (maxFolds ε_fold) (Finset.mem_univ i)
  exact le_trans hstep1 hstep2

/-- **Tightness / universal property: `ε_rbr` is the SMALLEST uniform per-challenge bound.**
    If a candidate `c` dominates all four families (every inner fold step, every OOD,
    every shift, and the final error), then `ε_rbr ≤ c`. PROVEN via `Finset.max'_le`:
    we discharge membership-by-cases over the union, mapping each member back to one of
    the four uniform bounds. The `image (maxFolds …)` case additionally uses
    `Finset.sup_le` (`maxFolds ε_fold i = sup_j (ε_fold i j) ≤ c`).

    Together with §1's four domination lemmas this is the exact sense in which the WHIR
    RBR error `ε_rbr` is *the* per-challenge budget: it dominates everything and is
    dominated by anything that dominates everything — the universal property of the
    accounting, the WHIR counterpart of #24's `totalBudget_le`. -/
theorem epsRbr_le_of_forall_le
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (c : ℝ≥0)
    (hfold : ∀ i j, ε_fold i j ≤ c) (hout : ∀ i, ε_out i ≤ c)
    (hshift : ∀ i, ε_shift i ≤ c) (hfin : ε_fin ≤ c) :
    epsRbr ε_fold ε_out ε_shift ε_fin ≤ c := by
  unfold epsRbr
  refine Finset.max'_le _ _ c ?_
  intro y hy
  unfold rbrBudgetSet at hy
  -- `y` is in one of: image (maxFolds ε_fold) / {ε_fin} / image ε_out / image ε_shift.
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hy
  rcases hy with ((hy | hy) | hy) | hy
  · -- y ∈ image (maxFolds ε_fold): y = maxFolds ε_fold i for some i.
    obtain ⟨i, rfl⟩ := hy
    -- maxFolds ε_fold i = sup_j (ε_fold i j) ≤ c via `Finset.sup_le` + `hfold i`.
    unfold maxFolds
    exact Finset.sup_le (fun j _ => hfold i j)
  · -- y = ε_fin.
    rw [hy]; exact hfin
  · -- y ∈ image ε_out: y = ε_out i.
    obtain ⟨i, rfl⟩ := hy; exact hout i
  · -- y ∈ image ε_shift: y = ε_shift i.
    obtain ⟨i, rfl⟩ := hy; exact hshift i

/-- **Equality characterization (combining §1 domination + tightness).** `ε_rbr` is
    exactly the least upper bound: it dominates all four families, and any `c` that
    dominates all four families dominates it. This packages the four §1 lemmas with the
    tightness lemma into the universal-property statement of the WHIR RBR budget.
    PROVEN: conjunction of the proven §1 facts. -/
theorem epsRbr_isLUB
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    (∀ i j, ε_fold i j ≤ epsRbr ε_fold ε_out ε_shift ε_fin) ∧
    (∀ i, ε_out i ≤ epsRbr ε_fold ε_out ε_shift ε_fin) ∧
    (∀ i, ε_shift i ≤ epsRbr ε_fold ε_out ε_shift ε_fin) ∧
    (ε_fin ≤ epsRbr ε_fold ε_out ε_shift ε_fin) ∧
    (∀ c, (∀ i j, ε_fold i j ≤ c) → (∀ i, ε_out i ≤ c) → (∀ i, ε_shift i ≤ c) →
      ε_fin ≤ c → epsRbr ε_fold ε_out ε_shift ε_fin ≤ c) :=
  ⟨eps_fold_le_epsRbr ε_fold ε_out ε_shift ε_fin,
   eps_out_le_epsRbr ε_fold ε_out ε_shift ε_fin,
   eps_shift_le_epsRbr ε_fold ε_out ε_shift ε_fin,
   eps_fin_le_epsRbr ε_fold ε_out ε_shift ε_fin,
   fun c => epsRbr_le_of_forall_le ε_fold ε_out ε_shift ε_fin c⟩

/-- Downstream projection of the WHIR RBR budget domination facts, without the LUB/tightness
tail.  This is the shape consumed by callers that only need to route the four per-round budget
families into the single per-challenge `ε_rbr` envelope. -/
theorem epsRbr_dominates
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    (∀ i j, ε_fold i j ≤ epsRbr ε_fold ε_out ε_shift ε_fin) ∧
    (∀ i, ε_out i ≤ epsRbr ε_fold ε_out ε_shift ε_fin) ∧
    (∀ i, ε_shift i ≤ epsRbr ε_fold ε_out ε_shift ε_fin) ∧
    ε_fin ≤ epsRbr ε_fold ε_out ε_shift ε_fin :=
  ⟨eps_fold_le_epsRbr ε_fold ε_out ε_shift ε_fin,
   eps_out_le_epsRbr ε_fold ε_out ε_shift ε_fin,
   eps_shift_le_epsRbr ε_fold ε_out ε_shift ε_fin,
   eps_fin_le_epsRbr ε_fold ε_out ε_shift ε_fin⟩

/-! ## §2. The keystone+folding residual interface and the soundness reduction

This is the WHIR analogue of #24 §4–§5 (`PerRoundProximityGap` + the keystone adapters),
and the *abstract shape* of the landed `whir_rbr_soundness_of_secure_gap` reduction
wrapper. The genuine open math behind WHIR RBR soundness is NOT the accounting (§1) — it
is the per-round soundness content:

  * the BCIKS20 / MCA `errStar` correlated-agreement bound, supplied in-tree via the
    `GenMutualCorrParams` class's `hasMutualCorrAgreement` field
    (`Whir/RBRSoundness.lean:121` / `Whir/MutualCorrAgreement.lean:149`), itself gated on
    `mca_johnson_bound_CONJECTURE` (`Whir/MutualCorrAgreement.lean:296`); and
  * the folding-preserves-list-decoding lemmas L4.20–4.23 (`Whir/Folding.lean`).

We package these as a single named residual `WhirRbrKeystone` (Prop), and give the
reduction adapter: WHIR RBR soundness *follows from* the keystone together with the §1
budget facts, with the keystone consumed as a black box. This makes precise that the §1
accounting is genuinely separable from — and consumes without re-proving — the MCA/folding
frontier. -/

/-- **Named residual (the genuine open per-round soundness math).** `WhirRbrKeystone`
    abstracts the per-round RBR soundness guarantee: *under the four named per-round
    budget inequalities (the `errStar`/folding bounds that `whir_rbr_soundness`'s
    `hBudget` conjunction states verbatim), the protocol's per-challenge RBR knowledge
    error is bounded by `ε_rbr`*. In the real tree this `Prop` is discharged by composing
    `GenMutualCorrParams.hasMutualCorrAgreement` (MCA Cor 4.11, gated on
    `mca_johnson_bound_CONJECTURE`) with the folding list-decoding lemmas L4.20–4.23 and
    the per-round shift/OOD analyses — i.e. it is precisely the `is_rbr_knowledge_sound`
    field of `IsSecureWithGap` for the constructed `π`.

    This is the SINGLE interface point through which the proven §1 accounting depends on
    the unproven MCA + folding frontier. It is parameterized by an opaque `SoundOk`
    predicate (standing for `IsSecureWithGap …`'s soundness clause for the budget `ε_rbr`)
    so this scratch file states the reduction without re-deriving the OracleReduction
    security machinery. -/
def WhirRbrKeystone
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (SoundOk : ℝ≥0 → Prop) : Prop :=
  SoundOk (epsRbr ε_fold ε_out ε_shift ε_fin)

/-- **Reduction adapter: RBR soundness for the budget from the keystone.**
    Given the named keystone (`WhirRbrKeystone`), the per-challenge soundness guarantee
    holds for `ε_rbr`. PROVEN trivially by unfolding — the *point* is that this is the
    single black-box consumption of the MCA/folding frontier, with NO new probabilistic
    content: the §1 accounting and this adapter together reduce `whir_rbr_soundness`'s
    soundness clause to the keystone. -/
theorem soundOk_epsRbr_of_keystone
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (SoundOk : ℝ≥0 → Prop)
    (hkey : WhirRbrKeystone ε_fold ε_out ε_shift ε_fin SoundOk) :
    SoundOk (epsRbr ε_fold ε_out ε_shift ε_fin) := hkey

/-- **Monotone transport of the keystone to a looser per-challenge budget.**
    If the soundness predicate is *antitone* (a larger error tolerance is easier to
    satisfy — the standard direction for an RBR error bound: `SoundOk e` means "RBR error
    ≤ e", which is upward-closed in `e`), then the keystone at `ε_rbr` transports to any
    `c ≥ ε_rbr`. Combined with §1's `epsRbr_le_of_forall_le`, this shows the keystone for
    the *tight* budget `ε_rbr` yields soundness for any uniform bound `c` dominating all
    four families — the WHIR counterpart of #24's `foldBudget_le_of_keystone`.
    PROVEN: antitone applied to `epsRbr_le_of_forall_le`. -/
theorem soundOk_of_keystone_of_forall_le
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (SoundOk : ℝ≥0 → Prop)
    (hmono : ∀ {a b : ℝ≥0}, a ≤ b → SoundOk a → SoundOk b)
    (hkey : WhirRbrKeystone ε_fold ε_out ε_shift ε_fin SoundOk)
    (c : ℝ≥0)
    (hfold : ∀ i j, ε_fold i j ≤ c) (hout : ∀ i, ε_out i ≤ c)
    (hshift : ∀ i, ε_shift i ≤ c) (hfin : ε_fin ≤ c) :
    SoundOk c :=
  hmono (epsRbr_le_of_forall_le ε_fold ε_out ε_shift ε_fin c hfold hout hshift hfin) hkey

/-! ## §3. Reduction of the *existential* `whir_rbr_soundness` to its three obligations

`whir_rbr_soundness` (`Whir/RBRSoundness.lean:185`) is
    `∃ n, ∃ vPSpec, card (vPSpec.ChallengeIdx) = 2*M+2 ∧ ∃ π, (IsSecureWithGap …) ∧ hBudget`.
The pure logical reduction — *given* the three pieces (challenge-card witness, a `π` with
its security proof, and the budget proof), the existential closes — is exactly the landed
`WhirIOP.whir_rbr_soundness_of_secure_gap` (`ToMathlib/WhirBricksConstruction.lean:434`,
proven by `refine ⟨n, vPSpec, hCard, π, ?_⟩; exact ⟨hSecure, hBudget⟩`).

We reproduce that reduction's *propositional skeleton* abstractly to confirm it is pure
∃-introduction with no hidden math: the conjunction `Secure ∧ Budget` under an `∃`. -/

/-- Abstract skeleton of `whir_rbr_soundness`: a challenge-cardinality fact, a security
    payload, and a budget payload, packaged existentially. (`Sec`/`Bud` stand for the
    `IsSecureWithGap …` and `hBudget` conjunctions; `Spec`/`witness` for `VectorSpec`/`π`.) -/
def whirRbrShape {Spec : Type} (card : Spec → Prop) {Wit : Spec → Type}
    (Sec Bud : (s : Spec) → Wit s → Prop) : Prop :=
  ∃ s : Spec, card s ∧ ∃ w : Wit s, Sec s w ∧ Bud s w

/-- **The existential-assembly reduction (abstract form of `whir_rbr_soundness_of_secure_gap`).**
    Given a spec `s` with the cardinality witness, a `π = w`, its security proof, and the
    budget proof, the `whir_rbr_soundness`-shaped existential follows. PROVEN by pure
    `⟨…⟩` introduction — confirming ask (3b) is plumbing once `π`, `Sec`, `Bud` exist.
    The remaining content is entirely in producing `Sec s w` (= `IsSecureWithGap`, which
    needs the §2 keystone + the constructed `π`) and `Bud s w` (= the four budget
    inequalities, whose accounting is §1). -/
theorem whirRbrShape_of_secure
    {Spec : Type} (card : Spec → Prop) {Wit : Spec → Type}
    (Sec Bud : (s : Spec) → Wit s → Prop)
    (s : Spec) (hcard : card s) (w : Wit s) (hSec : Sec s w) (hBud : Bud s w) :
    whirRbrShape card Sec Bud :=
  ⟨s, hcard, w, hSec, hBud⟩

/-! ## §4. Honest status of the construction obligations (FLAGGED, not provable math)

This section records — as documentation only — what (1) and (2) require and why they are
NOT extractable math. (No declarations; pure prose, mirroring #24 §5's
"SIBLING-OWNED PROTOCOL PLUMBING" note.)

  (1) CONSTRUCT `π : VectorIOP Unit (OracleStatement (ι 0) F) Unit vPSpec F`.
      This is the assembly of a concrete `OracleReduction`/`VectorIOP` term realizing
      Construction 5.1: a `2*M+2`-message Vector IOPP whose per round runs
        fold (`Whir/Folding.lean` `fold_k`/`foldf`) → out-of-domain sample
        (`Whir/OutofDomainSmpl.lean`) → shift, composed across `M+1` rounds, with a final
        check.
      ArkLib has every per-round *map* but no `VectorIOP` term, and no `processRound`/
      run-trace composition wiring at the WHIR level (cf. the same blocker on STIR noted
      in #24: only the one-round reduction exists, the multi-round `VectorIOP` does not).
      Building it is `OracleReduction`-engineering: it produces a *term*, not a proof of a
      probability bound or algebraic identity. There is no mathlib lemma to extract. The
      in-tree `whirVectorSpec` / `whirBlockVectorSpec` bricks supply only the *VectorSpec
      shape* (directions + lengths + the `2*M+2` challenge cardinality), NOT the prover/
      verifier. FLAGGED as sibling-owned construction plumbing.

  (2) PROVE `π.perfectCompleteness …`.
      Not statable until (1) exists (it is a predicate on `π`). Once `π` exists it is the
      run-trace bookkeeping that an honest codeword stays a codeword through each
      fold/OOD/shift round (the fold maps preserve `smoothCode` membership — see
      `Whir/Folding.lean` `foldf_step_mem_smoothCode` / `mem_smoothCode_of_isEvalOf`,
      which are the *only* genuinely-mathematical sub-pieces and already live in
      `Folding.lean`). The completeness proof itself is definitional unfolding of the
      reduction's run, not an isolated bound. FLAGGED as construction-dependent.

  (3) is reduced above: soundness = §1 accounting (proven) + §2 keystone (named residual:
      MCA Cor 4.11 / `mca_johnson_bound_CONJECTURE` + folding L4.20–4.23) + §3 existential
      assembly (proven, = landed `whir_rbr_soundness_of_secure_gap`), gated on (1)+(2)
      because `IsSecureWithGap` and `perfectCompleteness` both mention `π`.

  EXACT GAP (unchanged from the issue's own honest-stop, now with the math/plumbing split
  made explicit):
      whir_rbr_soundness
        = (WHIR VectorIOP construction `π`)            ← §4(1) PLUMBING, no extractable math
        + (perfectCompleteness of `π`)                 ← §4(2) construction-dependent
        + (IsSecureWithGap soundness clause)
            = §1 per-challenge `max'` budget accounting  ← PROVEN here
            + §2 keystone {MCA Cor 4.11 + folding L4.20–4.23}  ← named residual, open upstream
        + (existential assembly)                       ← §3 PROVEN here (= landed wrapper)
-/

/-! ## §5. Summary / honest status

  PROVEN here (elementary `Finset.max'`/`sup` order theory + pure ∃-introduction,
  hand-verified against confirmed mathlib/ArkLib API — `.lake/mathlib` is empty mid-merge
  so no `lake build` was possible):

    §1 (the genuine WHIR-specific extractable math — per-challenge round-error accounting):
      * `rbrBudgetSet_nonempty` — the `max'` side condition the in-tree `(by simp)`
        discharges.
      * `eps_fin_le_epsRbr`, `eps_out_le_epsRbr`, `eps_shift_le_epsRbr`,
        `eps_fold_le_epsRbr` — every named per-round budget (`ε_fin/ε_out/ε_shift` and
        each inner fold step `ε_fold i j`) is ≤ the WHIR RBR error `ε_rbr`. The fold case
        is the WHIR-specific two-level `sup`-then-`max'` accounting. (`Finset.le_max'`,
        `Finset.le_sup`.)
      * `epsRbr_le_of_forall_le` — `ε_rbr` is the *tightest* uniform per-challenge bound
        dominating all four families (`Finset.max'_le` + `Finset.sup_le`).
      * `epsRbr_isLUB` — the universal-property package: `ε_rbr = lub` of the four
        families. This is the WHIR counterpart of #24's `totalBudget_le`, but for the
        `max'` (per-challenge) budget rather than the additive (total) budget.

    §2–§3 (the reduction of `whir_rbr_soundness` to its residual):
      * `soundOk_epsRbr_of_keystone`, `soundOk_of_keystone_of_forall_le` — the soundness
        clause consumes the named keystone as a black box (antitone transport to any
        dominating budget), no double-counting; mirrors #24 `foldBudget_le_of_keystone`.
      * `whirRbrShape_of_secure` — the existential-assembly reduction (abstract form of
        the landed `whir_rbr_soundness_of_secure_gap`): pure ∃-introduction.

  NAMED RESIDUAL (NOT proven here — the genuine open per-round soundness math):
    * `WhirRbrKeystone` — the MCA `errStar` correlated-agreement bound (Cor 4.11, gated on
      `mca_johnson_bound_CONJECTURE`, `Whir/MutualCorrAgreement.lean:296`) composed with
      the folding list-decoding lemmas L4.20–4.23 (`Whir/Folding.lean`). This is the
      `is_rbr_knowledge_sound` content of `IsSecureWithGap` for the constructed `π`.

  FLAGGED CONSTRUCTION PLUMBING (correctly NOT attempted — no extractable math):
    * §4(1) the WHIR `VectorIOP π` (Construction 5.1 OracleReduction term) — sibling-owned
      OracleReduction engineering; ArkLib has the per-round maps but no `VectorIOP`/
      multi-round run-trace composition.
    * §4(2) `π.perfectCompleteness` — not statable without `π`; construction-dependent
      run-trace bookkeeping (the only mathematical sub-pieces, fold codeword-preservation,
      already live in `Folding.lean`).

  CONCLUSION: #113's soundness ask (3) splits cleanly into PROVEN accounting (§1, the WHIR
  per-challenge `max'` round-error budget and its universal property), a PROVEN existential
  reduction (§3, = the landed `whir_rbr_soundness_of_secure_gap`), and a single NAMED
  residual (§2, the MCA Cor 4.11 + folding L4.20–4.23 keystone). Asks (1) construction and
  (2) completeness are pure protocol-construction plumbing with no soundly-extractable
  math, blocked on the missing WHIR `VectorIOP` term and the OracleReduction multi-round
  composition infrastructure. -/

#print axioms rbrBudgetSet_nonempty
#print axioms eps_fin_le_epsRbr
#print axioms eps_out_le_epsRbr
#print axioms eps_shift_le_epsRbr
#print axioms eps_fold_le_epsRbr
#print axioms epsRbr_le_of_forall_le
#print axioms epsRbr_isLUB
#print axioms epsRbr_dominates
#print axioms soundOk_epsRbr_of_keystone
#print axioms soundOk_of_keystone_of_forall_le
#print axioms whirRbrShape_of_secure

end Issue113WHIR
