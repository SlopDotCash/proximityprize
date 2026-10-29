/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.InterleavedCode

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance
import ProximityPrize.Extensions.Data.CodingTheory.Basic.LinearCode
import ProximityPrize.Extensions.Data.CodingTheory.Basic.RelativeDistance
import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import ProximityPrize.Extensions.Data.Fin.Basic
import ProximityPrize.Extensions.Data.CodingTheory.Prelims
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Qify
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Basic.NNReal.Defs

/-!
## Main definitions

Interleaved codes for generic codes over a semiring, with **unified global APIs**.

### Core Data Types
1. **Single vector data structure**: used for computation
  - **Word**: `(ι → A)` - a word
  - **Codeword**: `(C : Set (ι → A))` - a codeword in base code `C`
2. **Horizontal interleaved data structure**: used for computation, the underlying data structure is
  `Matrix κ ι A`
  - **WordStack**: `Matrix κ ι A` - each row is a word
  - **CodewordStack**: `codewordStackSet (κ := κ) (C := C)` - each row is a codeword in C
3. **Vertical interleaved data structure**: used for security (e.g. Δ₀, δᵣ, ...), the underlying
  data structure is `Matrix ι κ A`
  `(κ → A)`.
  - **InterleavedWord**: `Matrix ι κ A`
  - **InterleavedCodeword**: `interleavedCodeSet (κ := κ) (C := C)`

### Global Unified APIs (Type Classes)
- **`GetRow α RowIdx RowType`** - extract rows uniformly across structures
- **`GetSymbol α SymbolIdx SymbolType`** - extract symbols uniformly
- **`GetCell α RowIdx SymbolIdx CellTy`** - extract individual cells
- **`Interleavable α β`** - interleave structures (notation: `⋈|u`)
- **`Interleavable₂ α β`** - interleave two structures (notation: `u ⋈₂ v`)
- **`CodeInterleavable Code InterleavedCode`** - interleave codes (notation: `C^⋈κ`)
- **`Stackifiable α β`** - inverse of interleaving (notation: `⋈⁻¹|v`)

### Key Set
- **`interleavedCodeSet C`** - set of interleaved codewords for code `C`
- **`codewordStackSet C`** - set of codeword stacks for code `C`
- **`ModuleCode.moduleInterleavedCode`** - interleaved code as
  `ModuleCode ι F (InterleavedSymbol A κ)` (preserves submodule; used with `C^⋈κ`)
- **`ModuleCode.codewordStackSubmodule`** - codeword stack as
  `Submodule F (WordStack A κ ι)` (preserves submodule for horizontal interleaving)

### Joint Proximity & Agreement (Consequent of Proximity Gap)
- **`jointProximity u δ`** - interleaved `u` within relative distance `δ` of `C^⋈κ`
- **`jointProximityNat u e`** - interleaved `u` within concrete distance `e` of `C^⋈κ`
- **`jointProximity₂ u₀ u₁ δ`** - interleaved pair within relative distance `δ` of `C^⋈(Fin 2)`
- **`jointProximityNat₂ u₀ u₁ e`** - interleaved pair within concrete distance `e` of `C^⋈(Fin 2)`
- **`pairJointProximity u v e`** - two interleaved stacks within distance `e` of each other
- **`pairJointProximity₂ u₀ u₁ v₀ v₁ e`** - two interleaved pairs within distance `e` of each other
- **`jointAgreement C δ W`** - words collectively agree on large set with `C`
  (equivalent to `jointProximity`)

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
    * NB we use version 20210703:203025

* [Ames, S., Hazay, C., Ishai, Y., and Venkitasubramaniam, M., *Ligero: Lightweight sublinear
    arguments without a trusted setup*][AHIV22]

* [Diamond, B. E. and Gruen, A., *Proximity Gaps in Interleaved Codes*, In: IACR
  Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.][DG25]
-/

section InterleavedCodeDefinitions
variable (F : Type*) [Semiring F]
variable (A : Type*) [AddCommMonoid A] [Module F A]
variable (κ ι : Type*) [Fintype κ] [Fintype ι]
variable (MC : ModuleCode ι F A)
variable (C : Set (ι → A))

open NNReal
namespace Code

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
-- Column projection shrinks relative Hamming distance for interleaved words.
lemma relHammingDist_transpose_le {F : Type*} [DecidableEq F] [Nonempty ι] {m : ℕ}
    (f V : Matrix ι (Fin m) F) (k : Fin m) :
    δᵣ(V.transpose k, f.transpose k) ≤ δᵣ(V, f) := by
  unfold relHammingDist
  have h : hammingDist (V.transpose k) (f.transpose k) ≤ hammingDist V f := by
    have := hammingDist_comp_le_hammingDist (γ := fun _ : ι => Fin m → F)
      (β := fun _ : ι => F) (fun (_ : ι) (row : Fin m → F) => row k) (x := V) (y := f)
    change hammingDist (fun i => V i k) (fun i => f i k) ≤ hammingDist V f
    exact this
  gcongr

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- A close interleaved codeword projects, column-wise, to a codeword of the base code. -/
lemma closeCodewordsRel_interleaved_transpose_mem_code {F : Type*}
    {m : ℕ} {C : Set (ι → F)} {δ : ℝ}
    {f V : Matrix ι (Fin m) F}
    (hV : V ∈ ListDecodable.closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (k : Fin m) :
    V.transpose k ∈ C :=
  hV.1 k

namespace InterleavedCode

/-!
  ## Interleaved Code Structure
  Implementation of the 7-step blueprint for Interleaved Codes.
-/

variable (RowIdx SymbolIdx : Type*)
variable (RowType SymbolType CellTy : Type*)

/-! ### 1, 2, 3. Accessors -/

export GetRow (getRow)
export GetSymbol (getSymbol)
export GetCell (getCell)

export InterleavedStructure (eq_iff_all_rows_eq eq_iff_all_symbols_eq eq_iff_all_cells_eq)

-- WordStack
example (C : Set (ι → A)) : ((C ^⋈ (Fin 2))) = interleavedCodeSet (κ := Fin 2) C
    := by rfl
example (MC : ModuleCode ι F A) : (MC ^⋈ (Fin 2))
    = ModuleCode.moduleInterleavedCode (F := F) (A := A) (κ := Fin 2) (ι := ι) (MC := MC)
    := by rfl
example (u : CodewordStack A κ ι C) :
  let iuCodewords: InterleavedCodeword A κ ι C := ⋈|u
  let iuWords: InterleavedWord A κ ι := ⋈|u.val
  iuCodewords.val = iuWords := by rfl
example (v₀ v₁ : C) :
  let iv_codeword : InterleavedWord A (Fin 2) ι := v₀.val ⋈₂ v₁.val
  let iv_word : InterleavedCodeword A (Fin 2) ι C := v₀ ⋈₂ v₁
  iv_codeword = iv_word := by rfl

end InterleavedCode

/-! ### Distance Properties for Interleaved Codes
**Naming conventions**:
- by default, when we say "interleaved word", it means the interleaved word of a
  `WordStack` (i.e. using notation `⋈|`).
- if the definition has `₂` at the end of its name, it means the interleaved word is of two
  `Word`s (i.e. using notation `⋈₂`).
- prefix `joint` or `pairjoint` :
  + `joint`: involves distance **from an interleaved word to the interleaved code `C^⋈ κ`**
  + `pairJoint`: involves distance **between two interleaved words**
- suffix `Nat` : the proximity is represented in terms of concrete distance (`Δ₀`),
  without this suffix, relative distance (`δᵣ`) is used instead.
-/
section JointProximityDefinitions

-- variable [DecidableEq A] [DecidableEq ι]

variable {κ ι : Type*} [Fintype ι] [Fintype κ]
  {A : Type*} (C : Set (ι → A)) [DecidableEq A]

/-- If every word in the stack is already a codeword, then the stack has joint agreement with
the code on the full coordinate set.  This is the complete extreme of the
correlated-agreement-to-`jointAgreement` bridge used by FRI/WHIR frontiers. -/
theorem jointAgreement_of_forall_mem {F κ ι : Type*} [Fintype ι] [DecidableEq F]
    {C : Set (ι → F)} {δ : ℝ≥0} {W : κ → ι → F} (hW : ∀ i, W i ∈ C) :
    jointAgreement (F := F) (κ := κ) (ι := ι) (C := C) (δ := δ) (W := W) := by
  classical
  refine ⟨Finset.univ, ?_, W, ?_⟩
  · simpa [mul_comm] using
      mul_le_mul_left (tsub_le_self : 1 - δ ≤ (1 : ℝ≥0)) (Fintype.card ι : ℝ≥0)
  · intro i
    constructor
    · exact hW i
    · intro j hj
      simp

/-- Monotonicity of `jointAgreement` in the proximity radius: increasing `δ` weakens the common
agreement-set size requirement. -/
theorem jointAgreement_mono {F κ ι : Type*} [Fintype ι] [DecidableEq F]
    {C : Set (ι → F)} {δ₁ δ₂ : ℝ≥0} {W : κ → ι → F} (hδ : δ₁ ≤ δ₂)
    (h : jointAgreement (F := F) (κ := κ) (ι := ι) (C := C) (δ := δ₁) (W := W)) :
    jointAgreement (F := F) (κ := κ) (ι := ι) (C := C) (δ := δ₂) (W := W) := by
  classical
  rcases h with ⟨S, hS, v, hv⟩
  refine ⟨S, ?_, v, hv⟩
  have hsub : 1 - δ₂ ≤ 1 - δ₁ := by
    exact tsub_le_tsub_left hδ 1
  have hmul :
      (1 - δ₂) * (Fintype.card ι : ℝ≥0) ≤
        (1 - δ₁) * (Fintype.card ι : ℝ≥0) := by
    simpa [mul_comm] using mul_le_mul_left hsub (Fintype.card ι : ℝ≥0)
  exact hmul.trans hS

/-- Monotonicity of `jointAgreement` in the code: enlarging the code preserves joint agreement,
since each agreeing codeword for the smaller code is also a codeword for the larger one.  Companion
to `jointAgreement_mono` (monotone in the proximity radius). -/
theorem jointAgreement_mono_code {F κ ι : Type*} [Fintype ι] [DecidableEq F]
    {C₁ C₂ : Set (ι → F)} {δ : ℝ≥0} {W : κ → ι → F} (hC : C₁ ⊆ C₂)
    (h : jointAgreement (F := F) (κ := κ) (ι := ι) (C := C₁) (δ := δ) (W := W)) :
    jointAgreement (F := F) (κ := κ) (ι := ι) (C := C₂) (δ := δ) (W := W) := by
  rcases h with ⟨S, hS, v, hv⟩
  exact ⟨S, hS, v, fun i => ⟨hC (hv i).1, (hv i).2⟩⟩

/-- `jointAgreement` in per-word `∀ i, ∃ u` form: the single agreeing-codeword function (the
`∃ v` Skolem form in the definition) is equivalent to per-word existence of an agreeing codeword on
a common large set.  This is the normal form in which the STIR/FRI/WHIR proximity-gap conclusions
are stated (`∃ S, |S| ≥ (1-δ)|ι| ∧ ∀ i, ∃ u ∈ C, agree on S`), so it bridges those bespoke
conclusions to the shared `jointAgreement` API. -/
theorem jointAgreement_iff_forall_exists {F κ ι : Type*} [Fintype ι] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ≥0) (W : κ → ι → F) :
    jointAgreement (F := F) (κ := κ) (ι := ι) (C := C) (δ := δ) (W := W) ↔
      ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι) ∧
        ∀ i, ∃ u, u ∈ C ∧ ∀ x ∈ S, W i x = u x := by
  classical
  constructor
  · rintro ⟨S, hS, v, hv⟩
    refine ⟨S, hS, fun i => ⟨v i, (hv i).1, fun x hx => ?_⟩⟩
    have := (hv i).2 hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.symm
  · rintro ⟨S, hS, h⟩
    choose u hu_mem hu_eq using h
    refine ⟨S, hS, u, fun i => ⟨hu_mem i, ?_⟩⟩
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hu_eq i x hx).symm

#print axioms jointAgreement_of_forall_mem
#print axioms jointAgreement_mono
#print axioms jointAgreement_mono_code
#print axioms jointAgreement_iff_forall_exists

/-- Transport joint agreement across an equivalence of coordinate domains.

The code predicate itself is supplied by `hC`: every codeword for `C₁`, reindexed along
`e.symm`, must be a codeword for `C₂`.  This isolates the finite-coordinate bookkeeping from
domain-specific code transport lemmas such as Reed-Solomon invariance under equivalent
evaluation domains. -/
theorem jointAgreement_equiv_of_codeword_transport
    {F κ ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] [DecidableEq F]
    (e : ι₁ ≃ ι₂)
    (C₁ : Set (ι₁ → F)) (C₂ : Set (ι₂ → F))
    (δ : NNReal) (W₂ : κ → ι₂ → F)
    (hC : ∀ v, v ∈ C₁ → (fun y => v (e.symm y)) ∈ C₂)
    (h :
      jointAgreement
        (C := C₁) (δ := δ) (W := fun k x => W₂ k (e x))) :
      jointAgreement (C := C₂) (δ := δ) (W := W₂) := by
  classical
  rcases h with ⟨S, hS, v, hv⟩
  refine ⟨S.map e.toEmbedding, ?_, fun k y => v k (e.symm y), ?_⟩
  · have hcard : Fintype.card ι₂ = Fintype.card ι₁ := Fintype.card_congr e.symm
    simpa [Finset.card_map, hcard] using hS
  · intro k
    constructor
    · exact hC (v k) (hv k).1
    · intro y hy
      rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hx_filter := (hv k).2 hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx_filter ⊢
      simpa using hx_filter

/-- **Reed-Solomon joint-agreement transport across a domain reindexing.**

Specialises `jointAgreement_equiv_of_codeword_transport` to Reed-Solomon codes: if the two
evaluation embeddings agree up to the coordinate equivalence `e` (`domain₁ x = domain₂ (e x)`),
then joint agreement of the reindexed word stack against the code on `domain₁` lifts to joint
agreement of the original word stack against the code on `domain₂`.  The Reed-Solomon-specific
codeword transport is discharged by `ReedSolomon.code_reindex_mem`.  This is the coding-theoretic
core of the FRI/STIR Claim 8.3 lift between an evaluation subdomain and the full domain. -/
theorem jointAgreement_reedSolomon_equiv
    {F : Type*} [Semiring F] [DecidableEq F]
    {κ ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (e : ι₁ ≃ ι₂) {domain₁ : ι₁ ↪ F} {domain₂ : ι₂ ↪ F} {n : ℕ}
    (hdom : ∀ x, domain₁ x = domain₂ (e x))
    {δ : NNReal} {W₂ : κ → ι₂ → F}
    (h : jointAgreement (C := (↑(ReedSolomon.code domain₁ n) : Set (ι₁ → F)))
          (δ := δ) (W := fun k x => W₂ k (e x))) :
    jointAgreement (C := (↑(ReedSolomon.code domain₂ n) : Set (ι₂ → F)))
      (δ := δ) (W := W₂) := by
  refine jointAgreement_equiv_of_codeword_transport e
    (↑(ReedSolomon.code domain₁ n)) (↑(ReedSolomon.code domain₂ n)) δ W₂ ?_ h
  intro v hv
  exact ReedSolomon.code_reindex_mem e hdom hv

end JointProximityDefinitions

end Code
end InterleavedCodeDefinitions

namespace InterleavedCode

open ListDecodable Code

/-- **Lemma 2.10 of [ABF26]** (= **[GGR11]**) — interleaved-code
list-size bound.

Let `C` be a code with relative minimum distance `δ_C := δ_min(C) / |ι|`,
and let `δ ∈ [0, δ_C)`. Define
  `η := δ_C - δ`,
  `b := ⌈δ / η⌉`,
  `r := ⌈log₂(δ_C / η)⌉`.
Then for every `m ≥ 1`,

  `|Λ(C^{≡m}, δ)| ≤ (b+r choose r) · |Λ(C, δ)|^r`.

The key feature is that the bound's dependence on the interleaving
factor `m` is hidden inside the constant `(b+r choose r)` — once `δ`
is fixed, the list size of `C^{≡m}` grows as a *polynomial in*
`|Λ(C, δ)|` of degree `r`, **independent of `m`**. Used in ABF26 §3
list-decoding analyses and §6.3.

## Disposition: REDUCED to the external GGR11 list-size recursion.

All *in-tree* infrastructure this statement rests on is proven sorry-free in this
file and in `ListDecodability.lean`: the interleaved-code carrier
(`interleavedCodeSet`, with its `Fintype` instance `interleavedCodeSet_fintype`),
the maximised list size `Lambda` (= `ListDecodability.Lambda`) and its monotonicity
(`Lambda_mono`), and the row-projection characterisation `mem_interleavedCode_iff`
(`V ∈ C^{≡m} ↔ ∀ k, V.transpose k ∈ C`).  In particular,
`closeCodewordsRel_interleaved_transpose_mem_code` proves that any interleaved
codeword in a relative Hamming ball projects, row-wise, to a codeword of `C`.

The residual is the **Gopalan–Guruswami–Raghavendra (GGR11)** combinatorial
list-recovery recursion (RANDOM 2011, "List Decoding Tensor Products and Interleaved
Codes"; ABF26 Lemma 2.10).  This `def` only *states* the bound (it is `Prop`-valued,
not proven here); the proof is carried out, modulo a precisely named residual, in
`ArkLib.ToMathlib.GGR11Interleaved`, where the GGR11 §3 argument is split into two
parts:

* **(Leaf counting — now fully in-tree.)**  A rooted tree whose root→leaf paths use
  at most `b` Blue and `r` Red edges, with at most one Blue and `≤ |Λ(C,δ)|` Red
  out-edges per node, has at most `(b+r choose r)·|Λ(C,δ)|^r` leaves (GGR11
  Theorem 3.6).  This is proved sorry-free as
  `InterleavedCode.GGR11.ggr11_tree_count_le` (double induction on the Pascal
  recursion `t(b,r) ≤ t(b-1,r) + L·t(b,r-1)`).

* **(Tree construction — the remaining named residual.)**  The Erase-Decode tree
  (GGR11 Algorithm 1, Lemmas 3.3–3.5) with those Blue/Red budgets exists and
  dominates the per-word close-codeword set.  This is the list-recovery /
  erasure-decoding content that has **no in-tree analogue** (ArkLib has neither a
  list-recovery primitive nor the column-pruning lemmas it needs).  It is named
  `InterleavedCode.GGR11.GGR11TreeStructure`, with the named per-word frontier
  `InterleavedCode.GGR11.GGR11TreeFrontier` exposing the witness data. The chain
  `GGR11TreeFrontier ↔ GGR11TreeStructure → GGR11PerWordBound → (this bound)` is
  fully proven there.

This compatibility statement retains `ListDecodable.Lambda`, which uses `Set.ncard`:
an infinite point list contributes zero. The canonical `Code.Lambda` uses `Set.encard`
instead and assigns infinite lists the value `⊤`; replacing one by the other requires
a finiteness bridge. The finite-alphabet GGR11 interpretation is unchanged. This
`Prop`-valued definition states the external obligation `GGR11TreeStructure`.

Residual external lemma: GGR11 Erase-Decode tree existence
(`InterleavedCode.GGR11.GGR11TreeStructure`). -/
def lambda_le_ggr11 {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (_hm : 1 ≤ m)
    (_hδ_lb : 0 ≤ δ)
    (_hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι) : Prop :=
    let η : ℝ := (Code.minDist C : ℝ) / Fintype.card ι - δ
    let b : ℕ := ⌈δ / η⌉₊
    let r : ℕ := ⌈Real.log ((Code.minDist C : ℝ) / Fintype.card ι / η) /
                  Real.log 2⌉₊
    ListDecodable.Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
      ((b + r).choose r : ℕ∞) * (ListDecodable.Lambda C δ) ^ r

lemma minDist_eq_minDist {F A ι κ : Type*} [Semiring F] [AddCommMonoid A] [Module F A]
    [Fintype ι] [Fintype κ] [Nonempty κ] [DecidableEq A] (C : Set (ι → A)) :
    Code.minDist (C^⋈κ) = Code.minDist C := by
  simpa only [Code.interleavedCode_eq_interleavedCodeSet] using
    (Code.minDist_interleavedCodeSet (κ := κ) C)

end InterleavedCode
