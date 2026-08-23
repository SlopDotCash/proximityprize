/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.BadGammaAffineCount
import ArkLib.Data.CodingTheory.ProximityGap.TheoremQAssembly

/-!
# The UPPER half of the Theorem-Q determination, faced against the lower half in one file

Theorem Q (`TheoremQAssembly.theoremQ_epsMCA_lower`, DISPROOF_LOG O68) pins the **lower** half
of the per-prime Grand MCA determination: in the *list-decoding* window `(1−δ)·n ≤ r·m`
(large `δ`), the deep-quotient line forces `ε_mca(evalCode H k, δ) ≥ B/q` with
`B ≳ ½·min(C(s,r), (q−n)/k)`.

To **pin `δ*`** for this family we need the matching **upper** half: for `δ` *below* a threshold
(the unique-decoding regime), `ε_mca(evalCode H k, δ) ≤ W/q`. Because
`ε_mca = ⨆_(u₀,u₁) badCount(u₀,u₁,δ)/q` (`MCALowerBound.epsMCA_eq_iSup_badCount_div`), an upper
bound is a **uniform-over-stacks** bound on the per-line bad-scalar count.

The right per-line engine is `BadGammaAffineCount.badGamma_affine_card_le`: the scalars `γ` for
which an affine error line `e₀ + γ·e₁` vanishes at a support coordinate of `e₁` number at most
`weight(e₁)`. Its docstring defers exactly one step — *"wiring it to `mcaEvent` via the
minimum-distance codeword extraction"*. This file supplies that wiring as a clean, axiom-clean
**reduction**:

`epsMCA_le_of_affineRoot_extraction` — given, for each stack `u`, an affine error pair
`(e₀ u, e₁ u)` with `weight(e₁ u) ≤ W` and the property that *every* `mcaEvent` bad scalar of `u`
is a root of `e₀ u + γ·e₁ u` at a support coordinate of `e₁ u`, then `ε_mca(C, δ) ≤ W/q`.

The extraction hypothesis (`hroot`) is the **named residual wall**: it is the min-distance
codeword subtraction, provably true in the unique-decoding regime `δ < (d−1)/2n` (the affine
error line is `e₀ = u₀ − c₀`, `e₁ = u₁ − c₁` for the unique nearby codewords `c₀, c₁`), but it
is *not* discharged here — only reduced to and composed against the same `epsMCA` surface
Theorem Q uses, so the two halves finally face each other in one statement
(`theoremQ_epsMCA_two_sided`). The numerical gap they leave is the unpinned window
`δ ∈ (unique-decoding radius, witness radius]`.

**Why the engine targets the affine-root event and NOT line-closeness.** The cruder surrogate
`badCount ≤ lineCloseCount` (`MCALowerBound.badCount_le_lineCloseCount`) is far too lossy here:
a structured stack with `u₀` a codeword and `u₁` a small-weight error is `δ`-close at *every* `γ`
(`lineCloseCount = q`) yet has bad count `0` — the `pairJointAgreesOn` clause fires on the
agreement set. This is verified at `δ = 0.25` (deep in unique decoding) by
`scripts/probes/probe_qline_upper.py` (check C2): `lineCloseCount = q = 97` while the affine-root
count is `1 ≤ weight(u₁) = 3`. The `u₁ = 0` case of this mechanism is proved unconditionally below
(`not_mcaEvent_of_uOne_zero` / `evalCode_not_mcaEvent_uOne_zero`).

**The gap is real (not closable by a global `n/q`).** Since `weight(e₁) ≤ n`, the engine gives at
most `ε_mca ≤ n/q`; but at the witness radius Theorem Q forces `ε_mca ≥ ~C(s,r)/q`, and
`C(s,r) > n` is routine (e.g. `C(6,3) = 20 > 12` at the probe parameters), so a *global* `n/q`
upper bound is FALSE — the upper bound is genuinely unique-decoding-only and the crossover radius
is `δ*`. Probe check C3.

Provenance: builds against the warm oleans (`lake env lean`), axiom-clean
(`[propext, Classical.choice, Quot.sound]`), zero `sorry`, zero warnings. References:
[ABF26] Def 4.3 / Grand Challenge 1; [BCIKS20] proximity gaps; [ACFY25] WHIR; the engine
`BadGammaAffineCount.lean`; the lower half `TheoremQAssembly.lean`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.TheoremQUpper

open _root_.ProximityGap _root_.Code
open scoped NNReal ENNReal BigOperators

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The reduction engine: affine-root extraction ⟹ an `epsMCA` upper bound -/

open Classical in
/-- **The upper-half engine (axiom-clean reduction).** Suppose that for every word stack `u` we
have an affine error pair `(e₀ u, e₁ u)` whose direction `e₁ u` has Hamming weight `≤ W`, and that
*every* `mcaEvent` bad scalar `γ` of `u` is a root of the affine error line `e₀ u + γ·e₁ u` at a
support coordinate of `e₁ u`. Then `ε_mca(C, δ) ≤ W/|F|`.

This is the wiring deferred by `BadGammaAffineCount.badGamma_affine_card_le`'s docstring: it
composes that per-line counting engine (`bad-scalar count ≤ weight(e₁)`) into the `epsMCA`
supremum surface (`MCALowerBound.epsMCA_le_of_badCount_le`). The hypothesis `hroot` is the
min-distance codeword extraction, true in the unique-decoding regime; it is reduced to, not
discharged. -/
theorem epsMCA_le_of_affineRoot_extraction
    (C : Set (ι → F)) (δ : ℝ≥0) (W : ℕ)
    (e₀ e₁ : WordStack F (Fin 2) ι → (ι → F))
    (hweight : ∀ u : WordStack F (Fin 2) ι,
      (Finset.univ.filter (fun i => e₁ u i ≠ 0)).card ≤ W)
    (hroot : ∀ u : WordStack F (Fin 2) ι, ∀ γ : F,
      mcaEvent (F := F) (A := F) C δ (u 0) (u 1) γ →
        ∃ i, e₁ u i ≠ 0 ∧ e₀ u i + γ * e₁ u i = 0) :
    epsMCA (F := F) (A := F) C δ ≤ (W : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  apply epsMCA_le_of_badCount_le C δ W
  intro u
  refine le_trans (Finset.card_le_card ?_)
    (le_trans (CodingTheory.badGamma_affine_card_le (e₀ u) (e₁ u)) (hweight u))
  intro γ hγ
  rw [Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, hroot u γ hγ.2⟩

open Classical in
/-- **Non-vacuity of the engine.** Instantiated at the full code `C = Set.univ`, the extraction
hypotheses are satisfiable (zero error pair, `W = 0`, `hroot` discharged by `not_mcaEvent_univ`),
and the engine fires to `ε_mca(univ, δ) ≤ 0`. This certifies the engine is sound and its
hypotheses are not contradictory (matching `epsMCA_univ_eq_zero`). -/
theorem epsMCA_univ_le_zero (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (Set.univ : Set (ι → F)) δ ≤ 0 := by
  refine le_trans (epsMCA_le_of_affineRoot_extraction (Set.univ : Set (ι → F)) δ 0
    (fun _ => 0) (fun _ => 0) (fun _ => by simp)
    (fun u γ hev => absurd hev (not_mcaEvent_univ (F := F) (A := F) δ (u 0) (u 1) γ))) ?_
  simp

/-! ### The unconditional structural fact behind the affine-root mechanism (`u₁ = 0`) -/

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **A zero direction has no bad scalar (for any code containing `0`).** If `u₁ = 0` and
`0 ∈ C`, then `mcaEvent` never fires: on any candidate witness set `S`, the closeness codeword `w`
and the zero codeword jointly agree with `(u₀, 0)`, so `pairJointAgreesOn` holds, contradicting
the `mcaEvent` non-agreement clause. This is the `u₁ = 0` case of the C2 mechanism (line-closeness
is not bad-ness): the line is constant `u₀` and trivially jointly matchable. -/
theorem not_mcaEvent_of_uOne_zero
    (C : Set (ι → F)) (hC0 : (0 : ι → F) ∈ C) (δ : ℝ≥0) (u₀ : ι → F) (γ : F) :
    ¬ mcaEvent (F := F) (A := F) C δ u₀ (0 : ι → F) γ := by
  rintro ⟨S, _hS, ⟨w, hwC, hweq⟩, hno⟩
  apply hno
  refine ⟨w, hwC, (0 : ι → F), hC0, fun i hi => ⟨?_, rfl⟩⟩
  simpa using hweq i hi

/-! ### Instantiation for the `evalCode` family (the Theorem-Q code) -/

omit [Fintype F] [DecidableEq F] in
/-- The zero word is a codeword of `evalCode H k` whenever `k ≥ 1` (the zero polynomial has
degree `0 < k`). -/
theorem evalCode_zero_mem (H : Finset F) (k : ℕ) (hk : 1 ≤ k) :
    (0 : {x : F // x ∈ H} → F) ∈ TheoremQAssembly.evalCode H k := by
  refine ⟨0, ?_, fun i => by simp⟩
  simpa using hk

omit [Fintype F] [DecidableEq F] in
/-- **`evalCode`: a zero direction has no bad scalar** (`k ≥ 1`). The `u₁ = 0` instance of
`not_mcaEvent_of_uOne_zero` for the Theorem-Q code family. -/
theorem evalCode_not_mcaEvent_uOne_zero
    (H : Finset F) [Nonempty {x : F // x ∈ H}] (k : ℕ) (hk : 1 ≤ k) (δ : ℝ≥0)
    (u₀ : {x : F // x ∈ H} → F) (γ : F) :
    ¬ mcaEvent (F := F) (A := F) (TheoremQAssembly.evalCode H k) δ u₀
        (0 : {x : F // x ∈ H} → F) γ :=
  not_mcaEvent_of_uOne_zero (TheoremQAssembly.evalCode H k) (evalCode_zero_mem H k hk) δ u₀ γ

/-! ### The two halves, facing each other in one statement -/

/-- **The conditional two-sided bracket for the Theorem-Q `evalCode` family.** Under the
Theorem-Q hypotheses (`H` a full `n`-th-root domain, `n = s·m`, `2 ≤ r ≤ s`, `(1−δ)n ≤ rm`,
`q > n + k`) **and** an affine-root extraction (`W`, `e₀`, `e₁`, `hweight`, `hroot` — the
min-distance codeword subtraction, the named residual wall), the per-prime MCA error is bracketed:

`B/q ≤ ε_mca(evalCode H k, δ) ≤ W/q`,  where `k = (r−1)m`,

with the lower `B` (Theorem Q, `B ≳ ½·min(C(s,r), (q−n)/k)`, *unconditional* over stacks) and the
upper `W` (`≤ n`, *conditional* on the extraction). The unpinned window between the halves is
`δ ∈ (unique-decoding radius, witness radius]`; since `C(s,r) > n` is routine, no *global* `n/q`
upper bound exists (probe C3) — the crossover radius is `δ*`. This is the lower-half O68 and this
upper brick composed against the *same* `epsMCA` surface. -/
theorem theoremQ_epsMCA_two_sided
    (H : Finset F) [Nonempty {x : F // x ∈ H}] (n s m r : ℕ)
    (hroots : ∀ x ∈ H, x ^ n = 1) (hcard : H.card = n)
    (hnsm : n = s * m) (hm : 1 ≤ m) (hr : 2 ≤ r) (hrs : r ≤ s)
    (hbig : n + (r - 1) * m < Fintype.card F)
    (δ : ℝ≥0)
    (hδ₁ : (1 - δ) * ((Fintype.card {x : F // x ∈ H} : ℕ) : ℝ≥0) ≤ ((r * m : ℕ) : ℝ≥0))
    (W : ℕ)
    (e₀ e₁ : WordStack F (Fin 2) {x : F // x ∈ H} → ({x : F // x ∈ H} → F))
    (hweight : ∀ u : WordStack F (Fin 2) {x : F // x ∈ H},
      (Finset.univ.filter (fun i => e₁ u i ≠ 0)).card ≤ W)
    (hroot : ∀ u : WordStack F (Fin 2) {x : F // x ∈ H}, ∀ γ : F,
      mcaEvent (F := F) (A := F) (TheoremQAssembly.evalCode H ((r - 1) * m)) δ (u 0) (u 1) γ →
        ∃ i, e₁ u i ≠ 0 ∧ e₀ u i + γ * e₁ u i = 0) :
    ∃ B : ℕ,
      Nat.choose s r * (Fintype.card F - n)
          ≤ B * ((Fintype.card F - n) + Nat.choose s r * ((r - 1) * m)) ∧
      (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
          ≤ epsMCA (F := F) (A := F) (TheoremQAssembly.evalCode H ((r - 1) * m)) δ ∧
      epsMCA (F := F) (A := F) (TheoremQAssembly.evalCode H ((r - 1) * m)) δ
          ≤ (W : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  obtain ⟨B, hB1, hB2⟩ :=
    TheoremQAssembly.theoremQ_epsMCA_lower H n s m r hroots hcard hnsm hm hr hrs hbig δ hδ₁
  exact ⟨B, hB1, hB2,
    epsMCA_le_of_affineRoot_extraction (TheoremQAssembly.evalCode H ((r - 1) * m)) δ W
      e₀ e₁ hweight hroot⟩

end ArkLib.ProximityGap.TheoremQUpper
