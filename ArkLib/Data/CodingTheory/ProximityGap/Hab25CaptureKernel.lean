/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Claim1

/-!
# The BCIKS20 Steps 5–7 capture kernel: statement, decode seam, and the first sub-obligation

`Hab25Claim1.lean` pinned the single remaining deep input of the #302 pair-case chain to the
per-cell hypothesis `hsteps57` of `claim1_dichotomy` — *capture above the threshold*: a large
cell of bad scalars is captured by one degree-`< k` affine pair (`AffineCaptured`). The
in-tree producers of that content (the #304/#138/#139 Hensel stream: `HPzBridge.HenselDatum`,
`MatchingExtractor`, Claims 5.8/5.9) speak a different surface — they pin the per-`z`
**decoded polynomial** `P z` to an affine specialization `v₀ + z·v₁`. Nothing in-tree
converted that output shape into `AffineCaptured`; this file is that seam, plus the
canonical form of the kernel statement itself.

* `McaDecode` — the polynomial-side destructuring of one `mcaEvent` witness: a witness set
  `S` and a degree-`< k` polynomial `P` agreeing with the fold `u₀ + γ·u₁` on `S`, with the
  forbidden-joint-agreement clause carried verbatim. `McaDecode.mcaEvent` /
  `exists_mcaDecode_of_mcaEvent` prove the destructuring **faithful** (an equivalence, via
  `ReedSolomon.mem_code_iff_exists_polynomial`).
* `McaDecode.affineCaptured` — **the capture bridge** (first sub-obligation, proven): a
  decode whose polynomial *is* the affine specialization `a + γ·b` yields
  `AffineCaptured domain k δ u γ (a, b)` verbatim.
* `affineCaptured_iff_exists_mcaDecode` — the canonical form: under the degree bounds,
  affine capture *is* affine decodability — `AffineCaptured γ (a,b)` iff the specialization
  `a + γ·b` is itself an `mcaEvent` decode of `γ`.
* `hsteps57_of_decode_family_pinning` — **the capture-kernel statement, consumer-shaped**:
  a per-`γ` decode family `P : F → F[X]` (the §5 decoded list, GS/matching side) that is
  affine on large cells (`P γ = v₀ + γ·v₁`, the Steps 5–7 Hensel side) yields the literal
  `hsteps57` hypothesis of `claim1_dichotomy`.
* `cell_card_le_of_decode_family_pinning` — composed with the proven dichotomy: the cell
  bound `|Ecell| ≤ T` from the two named per-cell inputs alone.

## The decomposition tree (the kernel's remaining sub-obligations, named)

With this file, `hsteps57` for the GS cells decomposes as K1 ∧ K4 where:

* **K1 (decode family)** — every bad scalar of the cell is decoded by the §5 family:
  `∀ γ ∈ Ecell, ∃ d : McaDecode …, d.P = P γ`. Production lane:
  `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` (proven) + the GS
  interpolation construction (`MultiplicityInterpolation`, in-tree) — the matching factor
  `Y − P_γ ∣ Q|_{Z:=γ}` realizes `P γ` as the decoded polynomial of `γ`'s witness.
* **K4 (affine pinning)** — `T < |Ecell| → ∃ v₀ v₁ (deg < k), ∀ γ ∈ Ecell,
  P γ = v₀ + γ·v₁`. This is the genuinely deep BCIKS20 content: Claim 5.7 (pigeonhole
  branch incidence) + Steps 5–7 (Hensel branch polynomial of degree `< k` by the Λ-weight
  zero count, Claim 5.8, and `Z`-linear, Claim 5.9) + Appendix C (inseparable shell). The
  #138/#139 `HenselNumerator` stream and the #304 `HPzBridge`/`HenselDatum` lanes produce
  per-`z` identities of exactly this shape; their open cores are K4's antecedent-to-witness
  step.

K2 (matching-factor extraction) and K3 (cell assignment by irreducible factor,
`gsFactorIndex`) are already in-tree (`MatchingExtractor.lean`, `Hab25DegreeBudget.lean`);
they feed K1.

Falsify-first probe (`scripts/probes/probe_capture_kernel_bridge.py`, exit 0): the decode
equivalence checked exhaustively over GF(3), n=3 (2,187 stack-scalar pairs) and on 1,000
planted+random GF(5), n=4 stacks (5,000 checks) — 0 mismatches; the `AffineCaptured`
clauses verified verbatim on 1,678 pinned-cell members — 0 failures; all 839 pinned cells
obey the claim-1 bound `|cell| ≤ n`; and in all 839 multi-scalar bad sets the maximal
affine cell was a *strict* subset — the pinning hypothesis is substantive, not auto-true.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory Polynomial

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **A decoded `mcaEvent` witness, polynomial side.** One bad scalar `γ` of the stack `u`,
destructured through `ReedSolomon.mem_code_iff_exists_polynomial`: a witness set `S` of size
`≥ (1−δ)·n`, a degree-`< k` polynomial `P` whose evaluations agree with the fold
`u₀ + γ·u₁` on `S`, and the forbidden-joint-agreement clause, verbatim. This is the surface
the §5 GS/matching machinery natively produces (`P` is the decoded polynomial whose matching
factor `Y − P` divides the specialized interpolant). -/
structure McaDecode (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) ι₀) (γ : F₀) : Type where
  /-- the `mcaEvent` witness set -/
  S : Finset ι₀
  /-- the decoded polynomial -/
  P : F₀[X]
  /-- the decoded polynomial has Reed–Solomon degree -/
  hdeg : P.degree < k
  /-- the witness set is large -/
  hcard : ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀)
  /-- the decoded polynomial agrees with the fold on the witness set -/
  hagree : ∀ i ∈ S, P.eval (domain i) = u 0 i + γ • u 1 i
  /-- no joint pair of codewords agrees with the stack on the witness set -/
  hnjp : ¬ pairJointAgreesOn ((ReedSolomon.code domain k : Set (ι₀ → F₀))) S (u 0) (u 1)

/-- A decode certifies the `mcaEvent`: the destructuring is sound. -/
theorem McaDecode.mcaEvent {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀}
    (d : McaDecode domain k δ u γ) :
    _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀)))
      δ (u 0) (u 1) γ := by
  refine ⟨d.S, d.hcard, ⟨fun i => d.P.eval (domain i), ?_, fun i hi => d.hagree i hi⟩,
    d.hnjp⟩
  exact ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval d.P d.hdeg fun i => rfl

/-- Every `mcaEvent` admits a decode: the destructuring is complete. The codeword of the
witness is realized as the evaluation of a degree-`< k` polynomial via
`ReedSolomon.mem_code_iff_exists_polynomial`. -/
theorem exists_mcaDecode_of_mcaEvent {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀}
    (h : _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀)))
      δ (u 0) (u 1) γ) :
    Nonempty (McaDecode domain k δ u γ) := by
  obtain ⟨S, hcard, ⟨w, hw, hagree⟩, hnjp⟩ := h
  obtain ⟨p, hdeg, hev⟩ := ReedSolomon.mem_code_iff_exists_polynomial.mp hw
  refine ⟨⟨S, p, hdeg, hcard, fun i hi => ?_, hnjp⟩⟩
  have hwi : w i = p.eval (domain i) := by rw [hev]; rfl
  rw [← hwi]
  exact hagree i hi

/-- **The capture bridge (the first sub-obligation of the Steps 5–7 kernel, proven).**
A decode whose polynomial is the affine specialization `a + γ·b` captures `γ` in the exact
`AffineCaptured` sense of the Claim-1 consumer: the witness set, the fold agreement, and the
forbidden-joint-agreement clause transfer verbatim. -/
theorem McaDecode.affineCaptured {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀} {a b : F₀[X]}
    (d : McaDecode domain k δ u γ)
    (haff : d.P = a + Polynomial.C γ * b) :
    AffineCaptured domain k δ u γ (a, b) := by
  refine ⟨d.S, d.hcard, fun i hi => ?_, d.hnjp⟩
  have h := d.hagree i hi
  rw [haff] at h
  exact h

/-- Degree control for affine specializations: if `a` and `b` have `natDegree < k`, the
specialization `a + C γ * b` has `degree < k` (including the `= 0` case). -/
theorem degree_affine_spec_lt {k : ℕ} {a b : F₀[X]} (γ : F₀)
    (ha : a.natDegree < k) (hb : b.natDegree < k) :
    (a + Polynomial.C γ * b).degree < k := by
  by_cases h0 : a + Polynomial.C γ * b = 0
  · rw [h0, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe k
  · rw [← Polynomial.natDegree_lt_iff_degree_lt h0]
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le a (Polynomial.C γ * b)) ?_
    exact max_lt ha (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le γ b) hb)

/-- **The canonical form of the capture kernel.** Under the degree bounds, affine capture is
exactly affine *decodability*: `γ` is captured by `(a, b)` iff the specialization `a + γ·b`
is itself the polynomial of some `mcaEvent` decode of `γ`. This rewrites the `hsteps57`
residual of `claim1_dichotomy` onto the surface the §5 Hensel stream natively produces. -/
theorem affineCaptured_iff_exists_mcaDecode {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀} {a b : F₀[X]}
    (ha : a.natDegree < k) (hb : b.natDegree < k) :
    AffineCaptured domain k δ u γ (a, b) ↔
      ∃ d : McaDecode domain k δ u γ, d.P = a + Polynomial.C γ * b := by
  constructor
  · rintro ⟨S, hcard, hagree, hnjp⟩
    exact ⟨⟨S, a + Polynomial.C γ * b, degree_affine_spec_lt γ ha hb, hcard,
      fun i hi => hagree i hi, hnjp⟩, rfl⟩
  · rintro ⟨d, haff⟩
    exact d.affineCaptured haff

/-- **The capture-kernel statement, consumer-shaped.** Given the two named per-cell inputs —

* **K1 (decode family, GS/matching side):** every scalar of the cell is decoded by the §5
  family `P : F₀ → F₀[X]`;
* **K4 (affine pinning, Steps 5–7 Hensel side):** past the threshold the family is one
  affine pencil, `P γ = v₀ + γ·v₁` with `deg < k` —

the literal `hsteps57` hypothesis of `claim1_dichotomy` follows. This is the exact seam
between the #304/#138/#139 Hensel-stream output shape and the #302 Claim-1 consumer. -/
theorem hsteps57_of_decode_family_pinning {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} (Ecell : Finset F₀) (T : ℕ) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hpin : T < Ecell.card →
      ∃ v₀ v₁ : F₀[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
        ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁) :
    T < Ecell.card →
      ∃ a b : F₀[X], a.natDegree < k ∧ b.natDegree < k ∧
        ∀ γ ∈ Ecell, AffineCaptured domain k δ u γ (a, b) := by
  intro hT
  obtain ⟨v₀, v₁, h₀, h₁, hp⟩ := hpin hT
  refine ⟨v₀, v₁, h₀, h₁, fun γ hγ => ?_⟩
  obtain ⟨d, hd⟩ := hdec γ hγ
  exact d.affineCaptured (hd.trans (hp γ hγ))

/-- **The cell bound from the two kernel inputs.** Composing the seam with the proven
dichotomy `claim1_dichotomy`: a cell whose bad scalars are decoded by a family that is
affine past the threshold has at most `T` members. The deep content left is exactly K4. -/
theorem cell_card_le_of_decode_family_pinning {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} (Ecell : Finset F₀) (T : ℕ) (P : F₀ → F₀[X])
    (hn : Fintype.card ι₀ ≤ T)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hpin : T < Ecell.card →
      ∃ v₀ v₁ : F₀[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
        ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁) :
    Ecell.card ≤ T :=
  claim1_dichotomy domain k δ u Ecell T hn
    (hsteps57_of_decode_family_pinning Ecell T P hdec hpin)

open Classical in
/-- Sanity export: scalars of a decoded cell are genuinely bad (members of
`hab25McaBadScalars`) — the kernel statement quantifies over real `mcaEvent` cells, not an
unsatisfiable surrogate. -/
theorem mem_badScalars_of_decode {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀}
    (d : McaDecode domain k δ u γ) :
    γ ∈ hab25McaBadScalars domain k δ u := by
  rw [hab25McaBadScalars, Finset.mem_filter]
  exact ⟨Finset.mem_univ γ, d.mcaEvent⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.McaDecode.mcaEvent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_mcaDecode_of_mcaEvent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.McaDecode.affineCaptured
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.affineCaptured_iff_exists_mcaDecode
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hsteps57_of_decode_family_pinning
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.cell_card_le_of_decode_family_pinning
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mem_badScalars_of_decode
