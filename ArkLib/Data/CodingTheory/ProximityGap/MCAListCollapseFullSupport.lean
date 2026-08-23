/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpreadCodeword
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# Uniform general-δ list-decoding ⇒ MCA collapse with explicit loss factor (ABF26 #232 §5)

ABF26's §5 open question is whether a good list-decoding bound for `RS[F, L, k]` at radius `δ`
*implies* a good MCA bound `ε_mca(C, δ) ≤ ε*` — collapsing the two grand challenges into one.
`MCAWitnessSpreadCodeword.lean` proves the two halves of the reduction:

* the clean `δ < 1/2` injective form `badCount_le_witnessCodeword_card` (loss factor `1`), and
* the *per-stack* general-`δ` packing `badCount · (t − z) ≤ |W| · (n − z)`
  (`witnessCodeword_packing_bound`), with `z = #{i : u₁ i = 0}` the stack-dependent zero count.

What was **missing** is the lift of the general-`δ` packing to a single uniform
`ε_mca(C, δ) ≤ f(L, n, t)/|F|` over the *supremum of all stacks* — because both `t` and `z`
vary stack-to-stack, the per-stack packing does not feed `epsMCA_le_of_badCount_le` directly.
This file supplies exactly that lift for the honest full-support regime.

## Main results

* `badCount_le_of_full_support` — **the per-stack engine (the new content).** For a *fixed*
  full-support stack (`u 1` nowhere zero — a satisfiable, load-bearing hypothesis), witness floor
  `t > 0` realized by the `(1-δ)n` size requirement (`hfloor`), and a list bound `L` on the
  line-witnessing-codeword count, the bad-scalar count is `≤ ⌊L · n / t⌋`. This converts the
  per-stack packing `badCount · t ≤ |W| · n` (the `z = 0` case of `witnessCodeword_packing_bound`)
  into an explicit *count* bound with loss factor `n / t`.

* `epsMCA_le_of_uniform_badCount_full_support` — **the uniform general-`δ` collapse.**
  If a fixed integer witness floor `t > 0` is realized by every `(1-δ)n`-size set (`hfloor`),
  *and every stack that has a bad scalar is witnessed by a full-support line second word*
  (`hsupp_of_bad`, a genuinely satisfiable hypothesis — e.g. it holds vacuously for the full code,
  which has no bad scalars), and the line-witnessing-codeword count is uniformly `≤ L` (`hlist`),
  then

  `ε_mca(C, δ) ≤ ⌊L · n / t⌋ / |F|`.

  The loss factor relative to the clean `δ < 1/2` bound (`badCount ≤ L`) is exactly `n / t`,
  i.e. `≈ 1/(1-δ)` when `t = ⌈(1-δ)n⌉`. This is the precise, explicit-constant degradation the §5
  collapse incurs in the gap regime `(1-√ρ, 1-ρ)`: a list bound `L` at radius `δ` yields an MCA
  bound `⌊L·n/t⌋/|F| ≈ (L/(1-δ))/|F|`. So a list bound that is `poly/q` (the open prize core) gives
  an MCA bound that is `poly/q` with only a constant `1/(1-δ)` blowup.

## Honest scope (what is and is NOT proven)

* The full-support hypothesis is genuine and load-bearing (a `u 1` with many zeros lets a single
  codeword witness several bad scalars; see `MCAWitnessSpreadCodeword`). It is stated in the
  uniform theorem as `hsupp_of_bad` — *only the stacks that actually fire a bad scalar* need full
  support — which is satisfiable (vacuously for codes with no bad scalars, and genuinely for RS
  lines on a smooth domain where the second word has full support). Quantifying full support over
  *all* stacks would be contradictory (the zero stack violates it), so the conditional form is the
  honest one.
* The *uniform list bound* `L` itself — beyond the Johnson radius `1-√ρ` for explicit
  smooth-domain RS — is the **open prize core**. This file does not bound `L`; it converts any
  uniform `L` into an MCA bound with the honest `n/t` loss. The endpoints stay open; the §5
  *collapse* (list ⇒ MCA, up to an explicit constant) is what advances here.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; §5 (does list-decoding imply MCA?).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal BigOperators
open ProximityGap Code ProximityGap.MCAWitnessSpreadCodeword

namespace ProximityGap.MCAListCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The line-witnessing-codeword set of a stack `u` at integer witness floor `t`: codewords of
`C` that agree with *some* line point `u 0 + γ·(u 1)` on a coordinate set of size `≥ t`. This is
the "line list" whose size the §5 open question asks to bound. -/
noncomputable def lineWitnessCodewords
    (C : Set (ι → A)) (u : WordStack A (Fin 2) ι) (t : ℕ) : Finset (ι → A) :=
  open Classical in
  Finset.univ.filter (fun w : ι → A => w ∈ C ∧ ∃ S : Finset ι,
    t ≤ S.card ∧ ∃ γ : F, ∀ i ∈ S, w i = u 0 i + γ • u 1 i)

omit [DecidableEq F] in
open Classical in
/-- **Per-stack full-support general-`δ` bad-count bound.** For a full-support stack (`u 1`
nowhere zero) with witness floor `t > 0`, the bad-scalar count is at most `⌊L · n / t⌋` whenever
the line-witnessing-codeword count is `≤ L`. This is `witnessCodeword_packing_bound` with `z = 0`
followed by a Nat division. -/
theorem badCount_le_of_full_support
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (t L : ℕ)
    (hsupp : ∀ i, u 1 i ≠ 0)
    (ht : 0 < t)
    (hfloor : ∀ {S : Finset ι},
      (1 - δ) * Fintype.card ι ≤ (S.card : ℝ≥0) → t ≤ S.card)
    (hlist : (lineWitnessCodewords (F := F) C u t).card ≤ L) :
    (Finset.univ.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ)).card
      ≤ (L * Fintype.card ι) / t := by
  -- Zero-count of a full-support `u 1` is 0.
  have hZ : (Finset.univ.filter (fun i => u 1 i = 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => hsupp i
  -- The raw packing bound from the imported file, with the `lineWitnessCodewords` list as `W`.
  have hpack :=
    badCount_mul_clean_le_witnessCodeword_card_mul (F := F) (A := A) C δ u t hfloor
      (by rw [hZ]; exact ht)
  -- Rewrite the zero-count term to `0` everywhere in the packing bound.
  rw [hZ, Nat.sub_zero, Nat.sub_zero] at hpack
  -- `hpack : badCount * t ≤ (witnessFilter).card * n`. Identify `witnessFilter = lineWitnessCodewords`.
  set badCount := (Finset.univ.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ)).card with hbc
  have hWeq : (Finset.univ.filter (fun w : ι → A => w ∈ C ∧ ∃ S : Finset ι,
      t ≤ S.card ∧ ∃ γ : F, ∀ i ∈ S, w i = u 0 i + γ • u 1 i)).card
      = (lineWitnessCodewords (F := F) C u t).card := by
    rw [lineWitnessCodewords]
  rw [hWeq] at hpack
  -- Now `hpack : badCount * t ≤ (lineWitnessCodewords).card * n ≤ L * n`.
  have hLn : (lineWitnessCodewords (F := F) C u t).card * Fintype.card ι ≤ L * Fintype.card ι :=
    Nat.mul_le_mul_right _ hlist
  have hchain : badCount * t ≤ L * Fintype.card ι := le_trans hpack hLn
  -- Conclude `badCount ≤ (L * n) / t` by Nat division.
  exact (Nat.le_div_iff_mul_le ht).2 hchain

omit [DecidableEq F] in
open Classical in
/-- A stack with *no* bad scalars contributes `0` to the bad-count, hence `≤ B` for any `B`. This
is the honest escape hatch for non-full-support / degenerate stacks: they need no full-support
assumption precisely because they fire no `mcaEvent`. -/
theorem badCount_le_of_no_bad
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (B : ℕ)
    (hnobad : ∀ γ : F, ¬ mcaEvent C δ (u 0) (u 1) γ) :
    (Finset.univ.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ)).card ≤ B := by
  rw [Finset.filter_false_of_mem (fun γ _ => hnobad γ), Finset.card_empty]
  exact Nat.zero_le B

omit [DecidableEq F] in
open Classical in
/-- **The uniform general-`δ` list ⇒ MCA collapse.** Honest conditional form: a fixed integer
witness floor `t > 0` realized by every `(1-δ)n`-size set (`hfloor`); *every stack that fires a
bad scalar* has a full-support line second word (`hsupp_of_bad` — only the firing stacks need it,
so this is satisfiable, vacuously for codes with no bad scalars and genuinely for smooth-domain
RS lines); and a uniform list bound `L` on the line-witnessing-codeword count (`hlist`). Then

`ε_mca(C, δ) ≤ ⌊L · n / t⌋ / |F|`.

The **explicit loss factor** is `n / t` (≈ `1/(1-δ)` for `t = ⌈(1-δ)n⌉`): any uniform list bound
`L` at radius `δ` becomes an MCA bound `⌊L·n/t⌋/|F|`. The clean `δ < 1/2` injective reduction
(`badCount_le_witnessCodeword_card`, loss factor `1`) is the `t > n/2`, `z = 0` corner; here `t`
may be as small as `1` (general `δ`), and the loss is paid exactly through `n/t`.

Stacks that *don't* fire a bad scalar are absorbed for free (`badCount_le_of_no_bad`), so no
universal full-support assumption (which would be contradictory) is needed. -/
theorem epsMCA_le_of_uniform_badCount_full_support
    (C : Set (ι → A)) (δ : ℝ≥0) (t L : ℕ)
    (ht : 0 < t)
    (hfloor : ∀ {S : Finset ι},
      (1 - δ) * Fintype.card ι ≤ (S.card : ℝ≥0) → t ≤ S.card)
    (hsupp_of_bad : ∀ (u : WordStack A (Fin 2) ι),
      (∃ γ : F, mcaEvent C δ (u 0) (u 1) γ) → ∀ i, u 1 i ≠ 0)
    (hlist : ∀ (u : WordStack A (Fin 2) ι),
      (lineWitnessCodewords (F := F) C u t).card ≤ L) :
    epsMCA (F := F) (A := A) C δ
      ≤ ((L * Fintype.card ι / t : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  apply epsMCA_le_of_badCount_le (F := F) (A := A) C δ (L * Fintype.card ι / t)
  intro u
  by_cases hbad : ∃ γ : F, mcaEvent C δ (u 0) (u 1) γ
  · -- The firing stacks are full support, so the packing engine applies.
    exact badCount_le_of_full_support (F := F) (A := A) C δ u t L
      (hsupp_of_bad u hbad) ht hfloor (hlist u)
  · -- Non-firing stacks contribute zero.
    push Not at hbad
    exact badCount_le_of_no_bad (F := F) (A := A) C δ u _ hbad

#print axioms badCount_le_of_full_support
#print axioms badCount_le_of_no_bad
#print axioms epsMCA_le_of_uniform_badCount_full_support

end ProximityGap.MCAListCollapse
