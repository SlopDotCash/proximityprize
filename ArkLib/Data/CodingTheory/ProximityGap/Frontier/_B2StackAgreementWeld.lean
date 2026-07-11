/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.StackJointAgreement
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._B2StructuredCloseSetBudget

/-!
# B2 — the stack-agreement weld: [GG25] Thm 3.3 into the ledger currency (issue #466, lane W1)

**Where this sits.** The in-tree [GG25] (ePrint 2025/2054) Def 3.1 chain ends, on the consumer
side, at `all_seeds_relClose_of_curveDecodable` (`GG25MCAFromCurveDecodability.lean`): a single
codeword *curve* `comb cs` within `(b/(b−ℓ))·δ` of the tested curve `comb u` at every seed. The
prize ledger, however, trades in **row-wise joint agreement** — `stackJointAgreesOn` /
`Code.jointAgreement` (`StackJointAgreement.lean`, `InterleavedCode.lean`), the consequent shape
of correlated agreement that `mcaEventCurve` (ABF26 Def 4.3) negates. Nothing in-tree crossed
that seam: per-seed closeness of two *curves* is not row-wise agreement of their *stacks*.

**The weld (this file).** The crossing is already latent in [GG25] Lemma 3.2: the spread bound
`disagree_spread_bound` controls `|disagree u cs|`, and `disagree u cs` is *exactly* the
complement of a **common row-wise agreement set** — off it, every row of `u` equals the
corresponding codeword row of `cs` simultaneously. So the Lemma 3.2 output IS a correlated-
agreement witness set; it only needed to be said:

* `rows_eq_of_not_mem_disagree` — off `disagree u cs` all rows agree (pointwise, all `j`);
* `stackJointAgreement_of_curveDecodable` — **the weld, division-free form**: curve
  decodability at `(ℓ, δ, a, b)` with `ℓ < b` plus a close set of size `≥ a` produce a set
  `S ⊆ ι` with `(b−ℓ)·(n − |S|) ≤ b·⌊δn⌋` and `stackJointAgreesOn C S u` — a single codeword
  stack agreeing with **every row of `u` simultaneously on `S`**;
* `jointAgreement_of_curveDecodable` — the ledger form: the same hypotheses give
  `Code.jointAgreement C ((b/(b−ℓ))·δ) u` — the correlated-agreement consequent at the [GG25]
  spread radius `δ·(1 + ℓ/(b−ℓ))`, in the exact `InterleavedCode.jointAgreement` currency;
* `exists_curveCloseSet_witness_of_proximity` — **the entry door**: the chain's hypotheses are
  stated against a chosen codeword-valued `f`; this lemma manufactures `f` from a pure
  proximity hypothesis (seeds where the tested curve is `δ`-close **to the code**), so
  consumers holding only distance-to-code data can enter the chain;
* `jointAgreement_of_gg25ListRecoveryBudget` — the end-to-end conditional: the named [GG25]
  producer input (`GG25ListRecoveryBudget`, `_B2StructuredCloseSetBudget.lean`) now reaches
  `Code.jointAgreement` in one theorem.

**Honest scope.** This weld yields the *correlated*-agreement consequent (one common witness
set, produced by the argument). It does NOT yield the *mutual* strengthening that
`mcaEventCurve` negates — there the adversary picks the witness set `S` and joint agreement is
demanded **on that `S`**; bounding `epsMCACurve` through this chain would additionally need the
produced agreement set to absorb every large adversarial witness set, which is the recognized
open seam (class B4 / the witness-cover residuals of `Connections/ListDecodingAndCA.lean`).
Nothing here advances the plain-RS producer either: for explicit plain RS above Johnson the
input (`GG25ListRecoveryBudget` / `RSCurveListSizeResidual`, BCHKS Conj 1.12, DISPROOF_LOG C43)
remains the open wall. All results here are unconditional plumbing, axiom-clean
`[propext, Classical.choice, Quot.sound]`.

## References
* [GG25] Z. Guo, V. Guruswami, ePrint 2025/2054 (ECCC TR25-166), Def 3.1, Lemma 3.2, Thm 3.3.
* [Jo26] S. Jo, ePrint 2026/891, Def 2.7, §5.
* [ABF26] ePrint 2026/680, Def 4.3 (the MCA event). Issue #466 lane W1 (B2).
-/

set_option linter.unusedSectionVars false

open Finset Code
open scoped NNReal

namespace ProximityGap.B2StackWeld

open ProximityGap ProximityGap.GG25Lemma32 ProximityGap.B2Budget

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Off the disagreement support, all rows agree simultaneously -/

/-- Off the [GG25] Lemma 3.2 disagreement support `disagree u c`, **every** row of the two
stacks agrees: the complement of `disagree u c` is a common row-wise agreement set. -/
theorem rows_eq_of_not_mem_disagree {ℓ : ℕ} {u c : Fin (ℓ + 1) → ι → A} {i : ι}
    (hi : i ∉ disagree u c) (j : Fin (ℓ + 1)) : u j i = c j i := by
  simp only [disagree, mem_filter, mem_univ, true_and, not_exists, not_not] at hi
  exact hi j

/-! ### The weld: curve decodability ⟹ stack joint agreement -/

/-- **The stack-agreement weld ([GG25] Thm 3.3, correlated-agreement form; division-free).**
If `C` is `(ℓ, δ, a, b)`-curve-decodable with `ℓ < b` and the instance `(u, f)` has a close set
of size `≥ a`, then there is a witness set `S` with `(b − ℓ)·(n − |S|) ≤ b·⌊δ·n⌋` on which a
single codeword stack agrees with **every row of `u` simultaneously** — the row-wise
(correlated-agreement) consequent, not merely per-seed closeness of the combined curves.

Mechanism: decodability hands a codeword stack `cs` explaining `≥ b` close seeds; on explained
seeds the two curves are integer-`⌊δn⌋`-close; Lemma 3.2 (`disagree_spread_bound`) then bounds
the *common* disagreement support `T = disagree u cs` by `(b−ℓ)·|T| ≤ b·⌊δn⌋`; and off `T` all
rows agree at once (`rows_eq_of_not_mem_disagree`). -/
theorem stackJointAgreement_of_curveDecodable
    {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ} (hlt : ℓ < b)
    (h : CurveDecodable (F := F) C ℓ δ a b)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ S : Finset ι,
      (b - ℓ) * (Fintype.card ι - S.card) ≤ b * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ ∧
      stackJointAgreesOn C S u := by
  classical
  obtain ⟨cs, hcs, hcount⟩ := h.exists_curve_of_close hf hclose
  set D := ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ with hD
  -- explained close seeds are integer-close seeds of the two curves
  have hsub : ((curveCloseSet δ u f).filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i))
      ⊆ univ.filter (fun α : F => hammingDist (comb u α) (comb cs α) ≤ D) := by
    intro α hα
    rw [mem_filter] at hα
    obtain ⟨hαC, hαeq⟩ := hα
    simp only [curveCloseSet, mem_filter, mem_univ, true_and] at hαC
    simp only [mem_filter, mem_univ, true_and]
    have hcomb_cs : f α = comb cs α := hαeq
    rw [hcomb_cs] at hαC
    exact GG25Lemma32.hammingDist_le_floor_of_relHam_le hαC
  have ht : b ≤ (univ.filter
      (fun α : F => hammingDist (comb u α) (comb cs α) ≤ D)).card :=
    le_trans hcount (Finset.card_le_card hsub)
  -- Lemma 3.2: the common disagreement support is small
  have hmaster := disagree_spread_bound hlt u cs ht
  refine ⟨univ \ disagree u cs, ?_, cs, hcs, fun i hi j => ?_⟩
  · -- size bound: n − |S| = |T| and (b−ℓ)·|T| ≤ b·D
    have hTle : (disagree u cs).card ≤ Fintype.card ι := Finset.card_le_univ _
    have hScard : (univ \ disagree u cs).card
        = Fintype.card ι - (disagree u cs).card := by
      rw [Finset.card_univ_diff]
    rw [hScard, Nat.sub_sub_self hTle]
    have hsm : (b - ℓ) * (disagree u cs).card
        = b * (disagree u cs).card - ℓ * (disagree u cs).card :=
      Nat.sub_mul b ℓ (disagree u cs).card
    omega
  · -- row-wise agreement off the disagreement support
    rw [Finset.mem_sdiff] at hi
    exact (rows_eq_of_not_mem_disagree hi.2 j).symm

/-- **The ledger form of the weld ([GG25] Thm 3.3 ⟹ `Code.jointAgreement`).** Curve
decodability at `(ℓ, δ, a, b)` with `ℓ < b` plus a close set of size `≥ a` give the
correlated-agreement consequent `Code.jointAgreement` at the [GG25] spread radius
`(b/(b−ℓ))·δ = δ·(1 + ℓ/(b−ℓ))` — a witness set of relative size `≥ 1 − (b/(b−ℓ))·δ`
carrying simultaneous row-wise agreement with a codeword stack. -/
theorem jointAgreement_of_curveDecodable
    {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ} (hlt : ℓ < b)
    (h : CurveDecodable (F := F) C ℓ δ a b)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    _root_.Code.jointAgreement (F := A) (κ := Fin (ℓ + 1)) (ι := ι) (C := C)
      (δ := ((b : ℝ≥0) / ((b - ℓ : ℕ) : ℝ≥0)) * δ) (W := u) := by
  rw [jointAgreement_iff_exists_stackJointAgreesOn]
  obtain ⟨S, hbound, hstack⟩ := stackJointAgreement_of_curveDecodable hlt h hf hclose
  refine ⟨S, ?_, hstack⟩
  have htlpos : (0 : ℝ≥0) < ((b - ℓ : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.sub_pos_of_lt hlt
  -- cast the division-free bound and release the floor
  have hcast : ((b - ℓ : ℕ) : ℝ≥0) * (((Fintype.card ι - S.card : ℕ)) : ℝ≥0)
      ≤ (b : ℝ≥0) * (δ * (Fintype.card ι : ℝ≥0)) := by
    have key : ((b - ℓ : ℕ) : ℝ≥0) * (((Fintype.card ι - S.card : ℕ)) : ℝ≥0)
        ≤ (b : ℝ≥0) * ((⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ : ℕ) : ℝ≥0) := by
      exact_mod_cast hbound
    refine key.trans ?_
    gcongr
    exact Nat.floor_le (by positivity)
  -- divide back: the uncovered mass is ≤ (b/(b−ℓ))·δ·n
  have hw : ((Fintype.card ι - S.card : ℕ) : ℝ≥0)
      ≤ ((b : ℝ≥0) / ((b - ℓ : ℕ) : ℝ≥0)) * δ * (Fintype.card ι : ℝ≥0) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ htlpos]
    calc ((Fintype.card ι - S.card : ℕ) : ℝ≥0) * ((b - ℓ : ℕ) : ℝ≥0)
        = ((b - ℓ : ℕ) : ℝ≥0) * ((Fintype.card ι - S.card : ℕ) : ℝ≥0) := by ring
      _ ≤ (b : ℝ≥0) * (δ * (Fintype.card ι : ℝ≥0)) := hcast
      _ = (b : ℝ≥0) * δ * (Fintype.card ι : ℝ≥0) := by ring
  -- assemble: n ≤ |S| + uncovered ≤ |S| + spread·n
  have hsplit : (Fintype.card ι : ℝ≥0)
      ≤ (S.card : ℝ≥0) + ((Fintype.card ι - S.card : ℕ) : ℝ≥0) := by
    have hnat : Fintype.card ι ≤ S.card + (Fintype.card ι - S.card) := by
      have := Finset.card_le_univ S
      omega
    exact_mod_cast hnat
  rw [ge_iff_le, tsub_mul, one_mul, tsub_le_iff_right]
  calc (Fintype.card ι : ℝ≥0)
      ≤ (S.card : ℝ≥0) + ((Fintype.card ι - S.card : ℕ) : ℝ≥0) := hsplit
    _ ≤ (S.card : ℝ≥0)
        + ((b : ℝ≥0) / ((b - ℓ : ℕ) : ℝ≥0)) * δ * (Fintype.card ι : ℝ≥0) := by gcongr

/-! ### The entry door: from distance-to-code seeds to the `f`-based close set -/

open Classical in
/-- **The entry door.** The [GG25] chain is stated against a chosen codeword-valued `f`; this
lemma manufactures one from a pure proximity hypothesis: for any stack `u` there is an `f`
(δ-close codeword per close seed, arbitrary codeword elsewhere) whose `curveCloseSet` contains
every seed at which the tested curve is `δ`-close **to the code**. Consumers holding only
distance-to-code data compose this with the weld theorems above. -/
theorem exists_curveCloseSet_witness_of_proximity {C : Set (ι → A)} (hC : C.Nonempty)
    {ℓ : ℕ} (δ : ℝ≥0) (u : Fin (ℓ + 1) → ι → A) :
    ∃ f : F → ι → A, (∀ γ, f γ ∈ C) ∧
      (univ.filter (fun γ : F =>
        δᵣ((fun i => ∑ j : Fin (ℓ + 1), γ ^ (j : ℕ) • u j i), C) ≤ δ)).card
        ≤ (curveCloseSet δ u f).card := by
  classical
  have hchoice : ∀ γ : F, ∃ w : ι → A, w ∈ C ∧
      (δᵣ((fun i => ∑ j : Fin (ℓ + 1), γ ^ (j : ℕ) • u j i), C) ≤ δ →
        (δᵣ((fun i => ∑ j : Fin (ℓ + 1), γ ^ (j : ℕ) • u j i), w) : ℝ≥0) ≤ δ) := by
    intro γ
    by_cases hγ : δᵣ((fun i => ∑ j : Fin (ℓ + 1), γ ^ (j : ℕ) • u j i), C) ≤ δ
    · obtain ⟨w, hwC, hwd⟩ :=
        (relCloseToCode_iff_relCloseToCodeword_of_minDist _ δ).mp hγ
      exact ⟨w, hwC, fun _ => hwd⟩
    · exact ⟨hC.choose, hC.choose_spec, fun hcontra => absurd hcontra hγ⟩
  choose f hfC hfd using hchoice
  refine ⟨f, hfC, Finset.card_le_card ?_⟩
  intro γ hγ
  rw [mem_filter] at hγ
  simp only [curveCloseSet, mem_filter, mem_univ, true_and]
  exact hfd γ hγ.2

/-! ### The end-to-end conditional: named [GG25] producer input ⟹ ledger joint agreement -/

/-- **The folded-pin end-to-end, in ledger currency.** The named [GG25] list-recovery input
(`GG25ListRecoveryBudget`, an `(m, e)` structured close-set budget) with `m·b + e ≤ a` and
`ℓ < b`: every instance whose close set reaches `a` admits `Code.jointAgreement` at the spread
radius `(b/(b−ℓ))·δ`. The *only* open antecedent is the named budget — for folded/multiplicity/
random RS it is [GG25]'s theorem (paper not on checkout, `/PAPERS_NEEDED.md`); for explicit
plain RS above Johnson it is the open wall (BCHKS Conj 1.12, DISPROOF_LOG C43). -/
theorem jointAgreement_of_gg25ListRecoveryBudget
    {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {m e a b : ℕ}
    (hm : 1 ≤ m) (hab : m * b + e ≤ a) (hlt : ℓ < b)
    (h : GG25ListRecoveryBudget (F := F) C ℓ δ m e)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    _root_.Code.jointAgreement (F := A) (κ := Fin (ℓ + 1)) (ι := ι) (C := C)
      (δ := ((b : ℝ≥0) / ((b - ℓ : ℕ) : ℝ≥0)) * δ) (W := u) :=
  jointAgreement_of_curveDecodable hlt
    (curveDecodable_of_structured_close_set_budget hm hab h) hf hclose

end ProximityGap.B2StackWeld

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.B2StackWeld.rows_eq_of_not_mem_disagree
#print axioms ProximityGap.B2StackWeld.stackJointAgreement_of_curveDecodable
#print axioms ProximityGap.B2StackWeld.jointAgreement_of_curveDecodable
#print axioms ProximityGap.B2StackWeld.exists_curveCloseSet_witness_of_proximity
#print axioms ProximityGap.B2StackWeld.jointAgreement_of_gg25ListRecoveryBudget
