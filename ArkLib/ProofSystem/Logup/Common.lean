/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Basic

/-!
# LogUp Common Definitions

Domain types, protocol statements, and the outer-round algebra shared across all LogUp modules.
-/

namespace Logup

universe u

open scoped BigOperators

/-- The boolean hypercube with `2^n` points.

The paper writes this domain as `H = {±1}^n`; we use bit vectors as row indices and embed
them into a field by `bitToSign`.
-/
@[reducible]
def Hypercube (n : ℕ) : Type :=
  Fin n → Fin 2

/-- Embed a hypercube bit as a `{±1}` field element. -/
def bitToSign (F : Type u) [One F] [Neg F] (b : Fin 2) : F :=
  if b = 0 then -1 else 1

/-- Embed a hypercube row as a point of `{±1}^n ⊂ Fⁿ`. -/
def signPoint (F : Type u) [One F] [Neg F] {n : ℕ} (u : Hypercube n) : Fin n → F :=
  fun j => bitToSign F (u j)

/-- The Lagrange kernel `L_H(x, z) = 2^{-n} * ∏ᵢ (1 + xᵢ zᵢ)` for `H = {±1}^n`. -/
noncomputable def lagrangeKernelAtPoint (F : Type u) [Field F] {n : ℕ}
    (x z : Fin n → F) : F :=
  ((2 : F) ^ n)⁻¹ * ∏ j : Fin n, (1 + x j * z j)

/-- The Lagrange kernel with the first argument restricted to a hypercube row. -/
noncomputable def lagrangeKernel (F : Type u) [Field F] {n : ℕ}
    (u : Hypercube n) (z : Fin n → F) : F :=
  lagrangeKernelAtPoint F (signPoint F u) z

/-- A Lagrange oracle is a function on `H`; queries ask for inner products with `L_H(., z)`. -/
structure LagrangeOracle (F : Type u) (n : ℕ) where
  values : Hypercube n → F

instance {F : Type u} {n : ℕ} : CoeFun (LagrangeOracle F n) (fun _ => Hypercube n → F) where
  coe oracle := oracle.values

/-- A multilinear oracle over the row variables of `H = {±1}^n`, represented in Lagrange form. -/
@[reducible]
def MultilinearOracle (F : Type u) (n : ℕ) : Type u :=
  LagrangeOracle F n

/-- Evaluate a multilinear oracle on a Boolean-hypercube row. -/
def evalOnHypercube {F : Type u} {n : ℕ}
    (p : MultilinearOracle F n) (u : Hypercube n) : F :=
  p u

/-- Lagrange-oracle queries are exactly the paper's inner products with `L_H(., z)`. -/
noncomputable instance instLagrangeOracleInterface {F : Type u} [Field F] {n : ℕ} :
    OracleInterface (LagrangeOracle F n) where
  Query := Fin n → F
  toOC.spec := (Fin n → F) →ₒ F
  toOC.impl z := do
    let oracle ← read
    return ∑ u : Hypercube n, oracle u * lagrangeKernel F u z

/-- The semantic value returned by querying a Lagrange-form multilinear oracle at `z`. -/
noncomputable def lagrangeOracleEval {F : Type u} [Field F] {n : ℕ}
    (oracle : MultilinearOracle F n) (z : Fin n → F) : F :=
  ∑ u : Hypercube n, oracle u * lagrangeKernel F u z

/-- Input oracle labels for Protocol 2: one table oracle and `M` lookup-column oracles. -/
inductive InputOracleIdx (M : ℕ) where
  | table : InputOracleIdx M
  | column : Fin M → InputOracleIdx M
deriving DecidableEq

/-- Term labels `0, ..., M` from the paper, with `0` denoting the table term. -/
@[reducible]
def TermIdx (M : ℕ) : Type :=
  Fin (M + 1)

/-- Interpret term index `0` as the table and term indices `1, ..., M` as lookup columns. -/
def termToInput {M : ℕ} (i : TermIdx M) : InputOracleIdx M :=
  if h : i.val = 0 then
    .table
  else
    .column ⟨i.val - 1, by omega⟩

/-- Interpret input-oracle labels as term indices `0, ..., M`. -/
def inputToTerm {M : ℕ} : InputOracleIdx M → TermIdx M
  | .table => ⟨0, by omega⟩
  | .column i => ⟨i.val + 1, by omega⟩

@[simp] theorem inputToTerm_table {M : ℕ} :
    inputToTerm (.table : InputOracleIdx M) = (0 : TermIdx M) := rfl

@[simp] theorem inputToTerm_column {M : ℕ} (i : Fin M) :
    inputToTerm (.column i) = ⟨i.val + 1, by omega⟩ := rfl

@[simp] theorem termToInput_inputToTerm {M : ℕ} (i : InputOracleIdx M) :
    termToInput (inputToTerm i) = i := by
  cases i with
  | table =>
      simp [termToInput]
  | column i =>
      simp [termToInput]

@[simp] theorem inputToTerm_termToInput {M : ℕ} (i : TermIdx M) :
    inputToTerm (termToInput i) = i := by
  unfold termToInput
  split
  · rename_i h
    apply Fin.ext
    simp [inputToTerm, h]
  · rename_i h
    apply Fin.ext
    simp [inputToTerm]
    have hi_pos : 0 < i.val := Nat.pos_of_ne_zero h
    omega

/-- Protocol parameter `ℓ`, the chosen partial-sum size from Protocol 2. -/
structure ProtocolParams (M : ℕ) where
  /-- The partial-sum size `ℓ`. -/
  sumSize : ℕ
  /-- Protocol 2 requires `1 ≤ ℓ`. -/
  sumSize_pos : 0 < sumSize
  /-- Protocol 2 requires `ℓ ≤ M + 1`. -/
  sumSize_le : sumSize ≤ M + 1

namespace ProtocolParams

/-- The number of partial-sum groups `K = ceil((M + 1) / ℓ)`. -/
def numGroups {M : ℕ} (params : ProtocolParams M) : ℕ :=
  (M + params.sumSize) / params.sumSize

theorem numGroups_pos {M : ℕ} (params : ProtocolParams M) : 0 < params.numGroups := by
  unfold numGroups
  exact Nat.div_pos (by omega) params.sumSize_pos

/-- The consecutive interval `Iₖ = [(k - 1)ℓ, kℓ) ∩ [0, M]`, zero-indexed. -/
def group {M : ℕ} (params : ProtocolParams M) (k : Fin params.numGroups) :
    Finset (TermIdx M) :=
  Finset.univ.filter fun i : TermIdx M =>
    k.val * params.sumSize ≤ i.val ∧ i.val < (k.val + 1) * params.sumSize

@[simp] theorem mem_group_iff {M : ℕ} (params : ProtocolParams M)
    (k : Fin params.numGroups) (i : TermIdx M) :
    i ∈ params.group k ↔
      k.val * params.sumSize ≤ i.val ∧ i.val < (k.val + 1) * params.sumSize := by
  simp [group]

/-- The canonical group index `⌊i / ℓ⌋` is in range for every term `i`. -/
theorem groupIndex_lt_numGroups {M : ℕ} (params : ProtocolParams M) (i : TermIdx M) :
    i.val / params.sumSize < params.numGroups := by
  unfold numGroups
  rw [Nat.div_lt_iff_lt_mul params.sumSize_pos]
  have hmod_lt : (M + params.sumSize) % params.sumSize < params.sumSize :=
    Nat.mod_lt _ params.sumSize_pos
  have hdecomp := Nat.div_add_mod (M + params.sumSize) params.sumSize
  have hdecomp' :
      (M + params.sumSize) / params.sumSize * params.sumSize +
          (M + params.sumSize) % params.sumSize = M + params.sumSize := by
    simpa [Nat.mul_comm] using hdecomp
  have hi : i.val < M + 1 := i.isLt
  omega

/-- Every term belongs to its canonical partial-sum group. -/
@[simp] theorem groupIndex_mem {M : ℕ} (params : ProtocolParams M) (i : TermIdx M) :
    i ∈ params.group ⟨i.val / params.sumSize, params.groupIndex_lt_numGroups i⟩ := by
  rw [mem_group_iff]
  constructor
  · simpa [Nat.mul_comm] using Nat.mul_div_le i.val params.sumSize
  · exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) params.sumSize_pos

/-- The Protocol 2 partial-sum groups cover all term indices. -/
theorem exists_mem_group {M : ℕ} (params : ProtocolParams M) (i : TermIdx M) :
    ∃ k : Fin params.numGroups, i ∈ params.group k :=
  ⟨⟨i.val / params.sumSize, params.groupIndex_lt_numGroups i⟩, params.groupIndex_mem i⟩

/-- Membership in a partial-sum group identifies the quotient `⌊i / ℓ⌋`. -/
theorem groupIndex_eq_of_mem {M : ℕ} (params : ProtocolParams M)
    (k : Fin params.numGroups) (i : TermIdx M) (hmem : i ∈ params.group k) :
    i.val / params.sumSize = k.val := by
  exact Nat.div_eq_of_lt_le ((params.mem_group_iff k i).mp hmem).1
    ((params.mem_group_iff k i).mp hmem).2

/-- A term is in exactly the partial-sum group selected by its quotient `⌊i / ℓ⌋`. -/
theorem mem_group_iff_groupIndex_eq {M : ℕ} (params : ProtocolParams M)
    (k : Fin params.numGroups) (i : TermIdx M) :
    i ∈ params.group k ↔ i.val / params.sumSize = k.val := by
  constructor
  · exact params.groupIndex_eq_of_mem k i
  · intro h
    rw [mem_group_iff]
    constructor
    · have hle := Nat.mul_div_le i.val params.sumSize
      rw [h] at hle
      simpa [Nat.mul_comm] using hle
    · have hlt : i.val / params.sumSize < k.val + 1 := by omega
      exact Nat.lt_mul_of_div_lt hlt params.sumSize_pos

/-- Partial-sum groups are disjoint on term indices. -/
theorem group_eq_of_mem {M : ℕ} (params : ProtocolParams M)
    {k l : Fin params.numGroups} {i : TermIdx M}
    (hk : i ∈ params.group k) (hl : i ∈ params.group l) : k = l := by
  apply Fin.ext
  exact (params.groupIndex_eq_of_mem k i hk).symm.trans
    (params.groupIndex_eq_of_mem l i hl)

end ProtocolParams

/-- Public parameter assumptions for Protocol 2.

The paper fixes a finite field with characteristic larger than `M * 2^n`; we also record that
`-1` and `1` are distinct so that `{±1}^n` is genuinely a Boolean hypercube in the field.
-/
structure StmtIn (F : Type u) [Field F] [Fintype F] (n M : ℕ) : Type u where
  /-- The paper's characteristic condition `char(F) > M * 2^n`. -/
  charLarge : M * 2 ^ n < ringChar F
  /-- The two signs used for the hypercube are distinct. -/
  signsDistinct : (-1 : F) ≠ 1

/-- Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles. -/
@[reducible, simp]
def OStmtIn (F : Type u) (n M : ℕ) : InputOracleIdx M → Type u
  | .table => MultilinearOracle F n
  | .column _ => MultilinearOracle F n

/-- Input LogUp oracles are accessed by evaluating their multilinear polynomial extensions. -/
noncomputable instance instOStmtInOracleInterface {F : Type u} [Field F] {n M : ℕ} :
    ∀ i, OracleInterface (OStmtIn F n M i)
  | .table => inferInstance
  | .column _ => inferInstance

/-- Accessor for the input table oracle `t`. -/
@[reducible, simp]
def tableOracle {F : Type u} {n M : ℕ}
    (oStmt : ∀ i, OStmtIn F n M i) : MultilinearOracle F n :=
  oStmt .table

/-- Accessor for the `i`-th lookup-column oracle `fᵢ`. -/
@[reducible, simp]
def columnOracle {F : Type u} {n M : ℕ}
    (oStmt : ∀ i, OStmtIn F n M i) (i : Fin M) : MultilinearOracle F n :=
  oStmt (.column i)

/-- Semantic input relation for Protocol 2: every lookup-column value occurs in the table range. -/
def inputRelation (F : Type u) [Field F] [Fintype F] (n M : ℕ) :
    Set ((StmtIn F n M × (∀ i, OStmtIn F n M i)) × Unit) :=
  { ⟨⟨_, oStmt⟩, _⟩ |
    ∀ i : Fin M, ∀ x : Hypercube n, ∃ y : Hypercube n,
      evalOnHypercube (columnOracle oStmt i) x = evalOnHypercube (tableOracle oStmt) y }

@[simp] theorem mem_inputRelation_iff
    {F : Type u} [Field F] [Fintype F] {n M : ℕ}
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) (wit : Unit) :
    (((stmt, oStmt), wit) ∈ inputRelation F n M) ↔
      ∀ i : Fin M, ∀ x : Hypercube n, ∃ y : Hypercube n,
        evalOnHypercube (columnOracle oStmt i) x = evalOnHypercube (tableOracle oStmt) y := by
  rfl

/-- The full LogUp protocol returns no additional public data on success. -/
@[reducible, simp]
def StmtOut : Type :=
  Unit

/-- The full LogUp protocol leaves no output oracle statements. -/
@[reducible, simp]
def OutputOracleIdx : Type :=
  Fin 0

/-- Output oracle statements for the full LogUp protocol. -/
@[reducible, simp]
def OStmtOut : OutputOracleIdx → Type :=
  fun i => Fin.elim0 i

/-- The full LogUp protocol has no output oracle interfaces to provide. -/
instance instOStmtOutOracleInterface :
    ∀ i, OracleInterface (OStmtOut i) :=
  fun i => Fin.elim0 i

/-- The full protocol has a trivial final relation: successful verification returns `Unit`. -/
def outputRelation : Set ((StmtOut × (∀ i, OStmtOut i)) × Unit) :=
  Set.univ

@[simp] theorem mem_outputRelation (x : (StmtOut × (∀ i, OStmtOut i)) × Unit) :
    x ∈ outputRelation := by
  simp [outputRelation]

@[simp] theorem outputRelation_language :
    outputRelation.language = (Set.univ : Set (StmtOut × (∀ i, OStmtOut i))) := by
  ext x
  simp [Set.language, outputRelation]

section ProtocolSpec

/-- The prover's first Protocol 2 message: the multiplicity function `m : H → F`. -/
@[reducible, simp]
def MultiplicityMessage (F : Type) (n : ℕ) : Type :=
  MultilinearOracle F n

/-- The prover's second Protocol 2 message: helper functions `h₁, ..., h_K : H → F`. -/
@[reducible, simp]
def HelperMessages (F : Type) (n K : ℕ) : Type :=
  Fin K → MultilinearOracle F n

/-- The verifier's second outer challenge: `z ∈ Fⁿ` and batching scalars `λ₁, ..., λ_K`. -/
@[reducible, simp]
def BatchingChallenge (F : Type) (n K : ℕ) : Type :=
  (Fin n → F) × (Fin K → F)

end ProtocolSpec

section OuterIO

variable (F : Type) [Field F] [Fintype F] (n M : ℕ) (params : ProtocolParams M)

/-- The outer LogUp statement after the verifier has sampled `x`, `z`, and `λ`. -/
structure StmtAfterOuter where
  /-- The logarithmic-derivative challenge `x`. -/
  xChallenge : F
  /-- The Lagrange-kernel point `z ∈ Fⁿ`. -/
  zChallenge : Fin n → F
  /-- The batching scalars `λ₁, ..., λ_K`. -/
  batchingScalars : Fin params.numGroups → F

/-- Oracle labels retained after the outer LogUp phase. -/
inductive OuterOracleIdx (M : ℕ) where
  | input : InputOracleIdx M → OuterOracleIdx M
  | multiplicity : OuterOracleIdx M
  | helpers : OuterOracleIdx M
deriving DecidableEq

/-- Oracle statements retained after the outer LogUp phase. -/
@[reducible, simp]
def OStmtAfterOuter (F : Type) [Field F] (n M : ℕ) (params : ProtocolParams M) :
    OuterOracleIdx M → Type
  | .input i => OStmtIn F n M i
  | .multiplicity => MultiplicityMessage F n
  | .helpers => HelperMessages F n params.numGroups

/-- Oracle interfaces for all oracle statements retained after the outer LogUp phase. -/
noncomputable instance instOStmtAfterOuterOracleInterface
    {F : Type} [Field F] {n M : ℕ} {params : ProtocolParams M} :
    ∀ i, OracleInterface (OStmtAfterOuter F n M params i)
  | .input i => inferInstanceAs (OracleInterface (OStmtIn F n M i))
  | .multiplicity => inferInstanceAs (OracleInterface (MultiplicityMessage F n))
  | .helpers => inferInstanceAs (OracleInterface (HelperMessages F n params.numGroups))

/-- Protocol 2 has no private witness beyond the input oracles at this layer. -/
@[reducible, simp]
def WitIn (F : Type u) [Field F] [Fintype F] (_n M : ℕ) (_params : ProtocolParams M) : Type :=
  Unit

end OuterIO

section ProtocolAlgebra

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}
variable (params : ProtocolParams M)

/-- A decomposition of the term indices `{0, ..., M}` into the partial-sum groups `Iₖ`. -/
@[reducible]
def PartialSumGroups (M K : ℕ) : Type :=
  Fin K → Finset (TermIdx M)

/-- The paper's canonical consecutive groups `Iₖ`, derived from the parameter `ℓ`. -/
def canonicalGroups : PartialSumGroups M params.numGroups :=
  fun k => params.group k

/-- Outer transcript data produced before entering the embedded sumcheck. -/
structure OuterTranscriptData (F : Type) [Field F] [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) where
  /-- The multiplicity function `m : H → F`. -/
  multiplicity : MultiplicityMessage F n
  /-- The verifier challenge `x : F`. -/
  xChallenge : F
  /-- The helper functions `h₁, ..., h_K : H → F`. -/
  helpers : HelperMessages F n params.numGroups
  /-- The Lagrange-kernel point `z ∈ Fⁿ`. -/
  zChallenge : Fin n → F
  /-- The batching scalars `λ₁, ..., λ_K`. -/
  batchingScalars : Fin params.numGroups → F

/-- Number of table rows with value `a`. -/
def tableMultiplicityCount (oStmt : ∀ i, OStmtIn F n M i) (a : F) : ℕ :=
  ((Finset.univ : Finset (Hypercube n)).filter fun u =>
    evalOnHypercube (tableOracle oStmt) u = a).card

/-- Total number of lookup-column entries with value `a`. -/
def lookupMultiplicityCount (oStmt : ∀ i, OStmtIn F n M i) (a : F) : ℕ :=
  ((Finset.univ : Finset (Fin M × Hypercube n)).filter fun ix =>
    evalOnHypercube (columnOracle oStmt ix.1) ix.2 = a).card

omit [Field F] [Fintype F] in
theorem lookupMultiplicityCount_zero_no_columns
    (oStmt : ∀ i, OStmtIn F n 0 i) (a : F) :
    lookupMultiplicityCount oStmt a = 0 := by
  simp [lookupMultiplicityCount]

omit [Field F] [Fintype F] in
theorem lookupMultiplicityCount_eq_sum_column_counts
    (oStmt : ∀ i, OStmtIn F n M i) (a : F) :
    lookupMultiplicityCount oStmt a =
      ∑ i : Fin M,
        ((Finset.univ : Finset (Hypercube n)).filter fun u =>
          evalOnHypercube (columnOracle oStmt i) u = a).card := by
  unfold lookupMultiplicityCount
  rw [Finset.card_eq_sum_ones]
  simp_rw [Finset.card_eq_sum_ones]
  have huniv : (Finset.univ : Finset (Fin M × Hypercube n)) =
      (Finset.univ : Finset (Fin M)).product (Finset.univ : Finset (Hypercube n)) := by
    ext x
    simp
  rw [huniv]
  simp_rw [Finset.sum_filter]
  change (∑ p ∈ (Finset.univ : Finset (Fin M)) ×ˢ
      (Finset.univ : Finset (Hypercube n)),
      if evalOnHypercube (columnOracle oStmt p.1) p.2 = a then (1 : ℕ) else 0) = _
  rw [Finset.sum_product (s := (Finset.univ : Finset (Fin M)))
    (t := (Finset.univ : Finset (Hypercube n)))
    (f := fun p : Fin M × Hypercube n =>
      if evalOnHypercube (columnOracle oStmt p.1) p.2 = a then (1 : ℕ) else 0)]

omit [Field F] [Fintype F] in
theorem tableMultiplicityCount_pos_of_eval
    (oStmt : ∀ i, OStmtIn F n M i) (u : Hypercube n) :
    0 < tableMultiplicityCount oStmt (evalOnHypercube (tableOracle oStmt) u) := by
  unfold tableMultiplicityCount
  apply Finset.card_pos.mpr
  exact ⟨u, by simp⟩

omit [Field F] [Fintype F] in
theorem tableMultiplicityCount_eq_zero_of_not_exists_eval
    (oStmt : ∀ i, OStmtIn F n M i) (a : F)
    (hnot : ¬ ∃ u : Hypercube n,
      evalOnHypercube (tableOracle oStmt) u = a) :
    tableMultiplicityCount oStmt a = 0 := by
  unfold tableMultiplicityCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hnot ⟨u, hmem⟩

theorem lookupMultiplicityCount_eq_zero_of_not_exists_table
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt, oStmt), ()) ∈ inputRelation F n M)) (a : F)
    (hnot : ¬ ∃ u : Hypercube n,
      evalOnHypercube (tableOracle oStmt) u = a) :
    lookupMultiplicityCount oStmt a = 0 := by
  unfold lookupMultiplicityCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ix hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  rcases (mem_inputRelation_iff stmt oStmt ()).mp hInput ix.1 ix.2 with ⟨y, hy⟩
  apply hnot
  refine ⟨y, ?_⟩
  rw [← hy, hmem]

omit [Field F] [Fintype F] in
theorem tableMultiplicityCount_le_card_hypercube
    (oStmt : ∀ i, OStmtIn F n M i) (a : F) :
    tableMultiplicityCount oStmt a ≤ Fintype.card (Hypercube n) := by
  unfold tableMultiplicityCount
  rw [← Finset.card_univ]
  exact Finset.card_filter_le _ _

omit [Fintype F] [DecidableEq F] in
theorem natCast_ne_zero_of_pos_lt_ringChar {m : ℕ}
    (hm_pos : 0 < m) (hm : m < ringChar F) :
    (m : F) ≠ 0 := by
  intro hzero
  have hdvd : ringChar F ∣ m := (ringChar.spec F m).mp hzero
  have hle : ringChar F ≤ m := Nat.le_of_dvd hm_pos hdvd
  omega

@[simp] theorem card_hypercube (n : ℕ) : Fintype.card (Hypercube n) = 2 ^ n := by
  simp [Hypercube]

theorem tableMultiplicityCount_natCast_ne_zero_of_stmt
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) (a : F)
    (hM : 0 < M) (hpos : 0 < tableMultiplicityCount oStmt a) :
    (tableMultiplicityCount oStmt a : F) ≠ 0 := by
  apply natCast_ne_zero_of_pos_lt_ringChar hpos
  have hle_card := tableMultiplicityCount_le_card_hypercube (oStmt := oStmt) a
  have hle_pow : tableMultiplicityCount oStmt a ≤ 2 ^ n := by
    simpa [card_hypercube] using hle_card
  have hpow_le : 2 ^ n ≤ M * 2 ^ n := by
    have hpow_pos : 0 < 2 ^ n := pow_pos (by omega) n
    nlinarith
  exact lt_of_le_of_lt (hle_pow.trans hpow_le) stmt.charLarge

/-- The normalized multiplicity from paper equation (14), evaluated at one table row. -/
noncomputable def normalizedMultiplicityValue (oStmt : ∀ i, OStmtIn F n M i)
    (u : Hypercube n) : F :=
  let a := evalOnHypercube (tableOracle oStmt) u
  (lookupMultiplicityCount oStmt a : F) / (tableMultiplicityCount oStmt a : F)

theorem table_fiber_normalizedMultiplicity_sum_eq_lookup_div
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hM : 0 < M) (a xChallenge : F)
    (hpos : 0 < tableMultiplicityCount oStmt a) :
    (∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter fun u =>
        evalOnHypercube (tableOracle oStmt) u = a,
      normalizedMultiplicityValue oStmt u /
        (xChallenge + evalOnHypercube (tableOracle oStmt) u)) =
      (lookupMultiplicityCount oStmt a : F) / (xChallenge + a) := by
  have hcount_ne :
      (tableMultiplicityCount oStmt a : F) ≠ 0 :=
    tableMultiplicityCount_natCast_ne_zero_of_stmt stmt oStmt a hM hpos
  have hcard :
      ((Finset.univ : Finset (Hypercube n)).filter fun u =>
        evalOnHypercube (tableOracle oStmt) u = a).card =
        tableMultiplicityCount oStmt a := by
    rfl
  calc
    (∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter fun u =>
        evalOnHypercube (tableOracle oStmt) u = a,
      normalizedMultiplicityValue oStmt u /
        (xChallenge + evalOnHypercube (tableOracle oStmt) u))
        = ∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter fun u =>
            evalOnHypercube (tableOracle oStmt) u = a,
          ((lookupMultiplicityCount oStmt a : F) /
              (tableMultiplicityCount oStmt a : F)) / (xChallenge + a) := by
          apply Finset.sum_congr rfl
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          simp [normalizedMultiplicityValue, hu]
    _ = (tableMultiplicityCount oStmt a : F) *
          (((lookupMultiplicityCount oStmt a : F) /
              (tableMultiplicityCount oStmt a : F)) / (xChallenge + a)) := by
          rw [Finset.sum_const]
          simp [hcard, nsmul_eq_mul]
    _ = (lookupMultiplicityCount oStmt a : F) / (xChallenge + a) := by
          field_simp [hcount_ne]

theorem table_sum_normalizedMultiplicity_eq_lookup_sum
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hM : 0 < M) (xChallenge : F) :
    (∑ u : Hypercube n,
      normalizedMultiplicityValue oStmt u /
        (xChallenge + evalOnHypercube (tableOracle oStmt) u)) =
      ∑ a : F, (lookupMultiplicityCount oStmt a : F) / (xChallenge + a) := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Hypercube n)))
    (t := (Finset.univ : Finset F))
    (g := fun u : Hypercube n => evalOnHypercube (tableOracle oStmt) u)
    (f := fun u : Hypercube n =>
      normalizedMultiplicityValue oStmt u /
        (xChallenge + evalOnHypercube (tableOracle oStmt) u))
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hpos : 0 < tableMultiplicityCount oStmt a
  · exact table_fiber_normalizedMultiplicity_sum_eq_lookup_div
      stmt oStmt hM a xChallenge hpos
  · have hnot : ¬ ∃ u : Hypercube n,
        evalOnHypercube (tableOracle oStmt) u = a := by
      intro hex
      rcases hex with ⟨u, hu⟩
      have hcount_pos :=
        tableMultiplicityCount_pos_of_eval (oStmt := oStmt) u
      rw [hu] at hcount_pos
      exact hpos hcount_pos
    have hfilter :
        ((Finset.univ : Finset (Hypercube n)).filter fun u =>
          evalOnHypercube (tableOracle oStmt) u = a) = ∅ := by
      have hcard_zero :=
        tableMultiplicityCount_eq_zero_of_not_exists_eval oStmt a hnot
      simpa [tableMultiplicityCount] using hcard_zero
    have hlookup_zero :=
      lookupMultiplicityCount_eq_zero_of_not_exists_table stmt oStmt hInput a hnot
    simp [hfilter, hlookup_zero]

omit [Fintype F] in
theorem column_fiber_one_div_sum_eq_count_div
    (oStmt : ∀ i, OStmtIn F n M i) (i : Fin M) (a xChallenge : F) :
    (∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter fun u =>
        evalOnHypercube (columnOracle oStmt i) u = a,
      (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u)) =
      (((Finset.univ : Finset (Hypercube n)).filter fun u =>
        evalOnHypercube (columnOracle oStmt i) u = a).card : F) /
        (xChallenge + a) := by
  calc
    (∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter fun u =>
        evalOnHypercube (columnOracle oStmt i) u = a,
      (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u))
        = ∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter fun u =>
            evalOnHypercube (columnOracle oStmt i) u = a,
          (1 : F) / (xChallenge + a) := by
          apply Finset.sum_congr rfl
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          simp [hu]
    _ = (((Finset.univ : Finset (Hypercube n)).filter fun u =>
          evalOnHypercube (columnOracle oStmt i) u = a).card : F) /
          (xChallenge + a) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, div_eq_mul_inv]

theorem lookupMultiplicity_sum_div_eq_column_sum
    (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) :
    (∑ a : F, (lookupMultiplicityCount oStmt a : F) / (xChallenge + a)) =
      ∑ i : Fin M,
        ∑ u : Hypercube n,
          (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
  calc
    (∑ a : F, (lookupMultiplicityCount oStmt a : F) / (xChallenge + a))
        = ∑ a : F,
            (∑ i : Fin M,
              (((Finset.univ : Finset (Hypercube n)).filter fun u =>
                evalOnHypercube (columnOracle oStmt i) u = a).card : F)) /
              (xChallenge + a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [lookupMultiplicityCount_eq_sum_column_counts]
          norm_cast
    _ = ∑ a : F,
          ∑ i : Fin M,
            (((Finset.univ : Finset (Hypercube n)).filter fun u =>
              evalOnHypercube (columnOracle oStmt i) u = a).card : F) /
              (xChallenge + a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_div]
    _ = ∑ i : Fin M,
          ∑ a : F,
            (((Finset.univ : Finset (Hypercube n)).filter fun u =>
              evalOnHypercube (columnOracle oStmt i) u = a).card : F) /
              (xChallenge + a) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin M,
          ∑ u : Hypercube n,
            (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset (Hypercube n)))
            (t := (Finset.univ : Finset F))
            (g := fun u : Hypercube n => evalOnHypercube (columnOracle oStmt i) u)
            (f := fun u : Hypercube n =>
              (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u))
            (fun _ _ => Finset.mem_univ _)]
          apply Finset.sum_congr rfl
          intro a _
          exact (column_fiber_one_div_sum_eq_count_div oStmt i a xChallenge).symm

omit [Fintype F] in
theorem normalizedMultiplicityValue_zero_no_columns
    (oStmt : ∀ i, OStmtIn F n 0 i) (u : Hypercube n) :
    normalizedMultiplicityValue oStmt u = 0 := by
  simp [normalizedMultiplicityValue, lookupMultiplicityCount_zero_no_columns]

/-- The honest multiplicity oracle `m : H → F` from paper equation (14). -/
noncomputable def honestMultiplicity (oStmt : ∀ i, OStmtIn F n M i) :
    MultiplicityMessage F n :=
  ⟨fun u => normalizedMultiplicityValue oStmt u⟩

omit [Fintype F] in
theorem honestMultiplicity_eval_zero_no_columns
    (oStmt : ∀ i, OStmtIn F n 0 i) (u : Hypercube n) :
    evalOnHypercube (honestMultiplicity oStmt) u = 0 := by
  simp [honestMultiplicity, evalOnHypercube, normalizedMultiplicityValue_zero_no_columns]

/-- The denominator term `φᵢ(u)` from Protocol 2. -/
noncomputable def phi (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) :
    InputOracleIdx M → Hypercube n → F
  | .table => fun u => xChallenge + evalOnHypercube (tableOracle oStmt) u
  | .column i => fun u => xChallenge + evalOnHypercube (columnOracle oStmt i) u

/-- The numerator term `mᵢ(u)` from Protocol 2, with `m₀ = m` and `mᵢ = -1` for columns. -/
noncomputable def numerator (multiplicity : MultilinearOracle F n) :
    InputOracleIdx M → Hypercube n → F
  | .table => evalOnHypercube multiplicity
  | .column _ => fun _ => -1

/-- The denominator term, indexed as `0, ..., M` as in the paper. -/
noncomputable def termPhi (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F)
    (i : TermIdx M) (u : Hypercube n) : F :=
  phi oStmt xChallenge (termToInput i) u

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termPhi_zero (oStmt : ∀ i, OStmtIn F n M i)
    (xChallenge : F) (u : Hypercube n) :
    termPhi oStmt xChallenge (0 : TermIdx M) u =
      xChallenge + evalOnHypercube (tableOracle oStmt) u := by
  simp [termPhi, termToInput, phi]

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termPhi_succ (oStmt : ∀ i, OStmtIn F n M i)
    (xChallenge : F) (i : Fin M) (u : Hypercube n) :
    termPhi oStmt xChallenge ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ u =
      xChallenge + evalOnHypercube (columnOracle oStmt i) u := by
  simp [termPhi, termToInput, phi]

omit [DecidableEq F] in
theorem termPhi_ne_zero_of_inputRelation_of_table
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (xChallenge : F)
    (hInput : (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (htable : ∀ u : Hypercube n,
      xChallenge + evalOnHypercube (tableOracle oStmt) u ≠ 0)
    (i : TermIdx M) (u : Hypercube n) :
    termPhi oStmt xChallenge i u ≠ 0 := by
  unfold termPhi
  cases hidx : termToInput i with
  | table =>
      simpa [hidx, phi] using htable u
  | column c =>
      rcases (mem_inputRelation_iff stmt oStmt ()).mp hInput c u with ⟨y, hy⟩
      simpa [hidx, phi, hy] using htable y

/-- The numerator term, indexed as `0, ..., M` as in the paper. -/
noncomputable def termNumerator (multiplicity : MultilinearOracle F n)
    (i : TermIdx M) (u : Hypercube n) : F :=
  numerator multiplicity (termToInput i) u

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termNumerator_zero (multiplicity : MultilinearOracle F n)
    (u : Hypercube n) :
    termNumerator multiplicity (0 : TermIdx M) u = evalOnHypercube multiplicity u := by
  simp [termNumerator, termToInput, numerator]

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termNumerator_succ (multiplicity : MultilinearOracle F n)
    (i : Fin M) (u : Hypercube n) :
    termNumerator multiplicity ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ u = -1 := by
  simp [termNumerator, termToInput, numerator]

/-- Product of the denominator terms in one partial-sum group. -/
noncomputable def denominatorProduct (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) (k : Fin K) (u : Hypercube n) : F :=
  ∏ i ∈ groups k, termPhi oStmt xChallenge i u

omit [Fintype F] [DecidableEq F] in
private theorem sum_div_mul_prod_eq_sum_mul_prod_erase
    {α : Type} [DecidableEq α]
    (s : Finset α) (num den : α → F) (hden : ∀ i ∈ s, den i ≠ 0) :
    (∑ i ∈ s, num i / den i) * (∏ i ∈ s, den i) =
      ∑ i ∈ s, num i * ∏ j ∈ s.erase i, den j := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase s den hi]
  field_simp [hden i hi]

/-- The domain-identity expression for one helper function `hₖ`. -/
noncomputable def domainIdentityTerm (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (xChallenge : F) (k : Fin K) (u : Hypercube n) : F :=
  evalOnHypercube (helpers k) u * denominatorProduct groups oStmt xChallenge k u -
    ∑ i ∈ groups k,
      termNumerator multiplicity i u * ∏ j ∈ (groups k).erase i, termPhi oStmt xChallenge j u

/-- The helper value `hₖ(u) = Σᵢ mᵢ(u)/φᵢ(u)` from paper equation (16). -/
noncomputable def helperValue (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (xChallenge : F) (k : Fin K) (u : Hypercube n) : F :=
  ∑ i ∈ groups k, termNumerator multiplicity i u / termPhi oStmt xChallenge i u

omit [Fintype F] [DecidableEq F] in
theorem helperValue_mul_denominatorProduct
    (groups : PartialSumGroups M K) (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (xChallenge : F) (k : Fin K) (u : Hypercube n)
    (hden : ∀ i ∈ groups k, termPhi oStmt xChallenge i u ≠ 0) :
    helperValue groups oStmt multiplicity xChallenge k u *
        denominatorProduct groups oStmt xChallenge k u =
      ∑ i ∈ groups k,
        termNumerator multiplicity i u *
          ∏ j ∈ (groups k).erase i, termPhi oStmt xChallenge j u := by
  unfold helperValue denominatorProduct
  exact sum_div_mul_prod_eq_sum_mul_prod_erase (groups k)
    (fun i => termNumerator multiplicity i u)
    (fun i => termPhi oStmt xChallenge i u) hden

/-- The honest helper oracle `hₖ : H → F` for one partial-sum group. -/
noncomputable def helperOracle (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (xChallenge : F) (k : Fin K) : MultilinearOracle F n :=
  ⟨fun u => helperValue groups oStmt multiplicity xChallenge k u⟩

omit [Fintype F] [DecidableEq F] in
theorem domainIdentityTerm_honest_helper_eq_zero
    (groups : PartialSumGroups M K) (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (xChallenge : F) (k : Fin K) (u : Hypercube n)
    (hden : ∀ i ∈ groups k, termPhi oStmt xChallenge i u ≠ 0) :
    domainIdentityTerm groups oStmt multiplicity
        (fun k => helperOracle groups oStmt multiplicity xChallenge k) xChallenge k u = 0 := by
  unfold domainIdentityTerm
  simp only [evalOnHypercube, helperOracle]
  rw [helperValue_mul_denominatorProduct groups oStmt multiplicity xChallenge k u hden]
  simp

/-- The honest helper-oracle bundle `h₁, ..., h_K` from paper equation (16). -/
noncomputable def honestHelpers (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) :
    HelperMessages F n params.numGroups :=
  let multiplicity := honestMultiplicity oStmt
  fun k => helperOracle (canonicalGroups params) oStmt multiplicity xChallenge k

/-- The batched polynomial expression `Q` from paper equation (18), evaluated on a row `u ∈ H`. -/
noncomputable def qOnHypercube (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (xChallenge : F) (zChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (u : Hypercube n) : F :=
  ∑ k : Fin K, (
    evalOnHypercube (helpers k) u +
      lagrangeKernel F u zChallenge * batchingScalars k *
        domainIdentityTerm groups oStmt multiplicity helpers xChallenge k u)

omit [Fintype F] [DecidableEq F] in
theorem qOnHypercube_honest_helpers
    (groups : PartialSumGroups M K) (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (xChallenge : F) (zChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (u : Hypercube n)
    (hden : ∀ k : Fin K, ∀ i ∈ groups k, termPhi oStmt xChallenge i u ≠ 0) :
    qOnHypercube groups oStmt multiplicity
        (fun k => helperOracle groups oStmt multiplicity xChallenge k)
        xChallenge zChallenge batchingScalars u =
      ∑ k : Fin K, evalOnHypercube (helperOracle groups oStmt multiplicity xChallenge k) u := by
  unfold qOnHypercube
  apply Finset.sum_congr rfl
  intro k _
  rw [domainIdentityTerm_honest_helper_eq_zero groups oStmt multiplicity xChallenge k u (hden k)]
  simp

/-- Point evaluations queried by the verifier at the final sumcheck point `r`. -/
structure PointEvaluations (F : Type) (M K : ℕ) where
  /-- Claimed value `m(r)`. -/
  multiplicity : F
  /-- Claimed value `t(r)`. -/
  table : F
  /-- Claimed values `fᵢ(r)`. -/
  columns : Fin M → F
  /-- Claimed values `hₖ(r)`. -/
  helpers : Fin K → F

/-- Denominator term at the final sumcheck point, reconstructed from oracle query answers. -/
def phiAtPoint (xChallenge : F) (evals : PointEvaluations F M K) :
    InputOracleIdx M → F
  | .table => xChallenge + evals.table
  | .column i => xChallenge + evals.columns i

/-- Numerator term at the final sumcheck point, reconstructed from oracle query answers. -/
def numeratorAtPoint (evals : PointEvaluations F M K) : InputOracleIdx M → F
  | .table => evals.multiplicity
  | .column _ => -1

/-- Term denominator at the final sumcheck point, indexed by `0, ..., M`. -/
def termPhiAtPoint (xChallenge : F) (evals : PointEvaluations F M K) (i : TermIdx M) : F :=
  phiAtPoint xChallenge evals (termToInput i)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termPhiAtPoint_zero (xChallenge : F) (evals : PointEvaluations F M K) :
    termPhiAtPoint xChallenge evals (0 : TermIdx M) = xChallenge + evals.table := by
  simp [termPhiAtPoint, termToInput, phiAtPoint]

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termPhiAtPoint_succ (xChallenge : F)
    (evals : PointEvaluations F M K) (i : Fin M) :
    termPhiAtPoint xChallenge evals ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
      xChallenge + evals.columns i := by
  simp [termPhiAtPoint, termToInput, phiAtPoint]

/-- Term numerator at the final sumcheck point, indexed by `0, ..., M`. -/
def termNumeratorAtPoint (evals : PointEvaluations F M K) (i : TermIdx M) : F :=
  numeratorAtPoint evals (termToInput i)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termNumeratorAtPoint_zero (evals : PointEvaluations F M K) :
    termNumeratorAtPoint evals (0 : TermIdx M) = evals.multiplicity := by
  simp [termNumeratorAtPoint, termToInput, numeratorAtPoint]

omit [Fintype F] [DecidableEq F] in
@[simp] theorem termNumeratorAtPoint_succ
    (evals : PointEvaluations F M K) (i : Fin M) :
    termNumeratorAtPoint evals ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = -1 := by
  simp [termNumeratorAtPoint, termToInput, numeratorAtPoint]

/-- The domain-identity expression at the final sumcheck point `r`. -/
noncomputable def domainIdentityAtPoint (groups : PartialSumGroups M K)
    (xChallenge : F) (evals : PointEvaluations F M K) (k : Fin K) : F :=
  evals.helpers k * (∏ i ∈ groups k, termPhiAtPoint xChallenge evals i) -
    ∑ i ∈ groups k,
      termNumeratorAtPoint evals i *
        ∏ j ∈ (groups k).erase i, termPhiAtPoint xChallenge evals j

omit [Fintype F] [DecidableEq F] in
noncomputable def helperValueAtPoint (groups : PartialSumGroups M K)
    (xChallenge : F) (evals : PointEvaluations F M K) (k : Fin K) : F :=
  ∑ i ∈ groups k, termNumeratorAtPoint evals i / termPhiAtPoint xChallenge evals i

omit [Fintype F] [DecidableEq F] in
theorem helperValueAtPoint_mul_denominatorProduct
    (groups : PartialSumGroups M K) (xChallenge : F) (evals : PointEvaluations F M K)
    (k : Fin K) (hden : ∀ i ∈ groups k, termPhiAtPoint xChallenge evals i ≠ 0) :
    helperValueAtPoint groups xChallenge evals k *
        (∏ i ∈ groups k, termPhiAtPoint xChallenge evals i) =
      ∑ i ∈ groups k,
        termNumeratorAtPoint evals i *
          ∏ j ∈ (groups k).erase i, termPhiAtPoint xChallenge evals j := by
  unfold helperValueAtPoint
  exact sum_div_mul_prod_eq_sum_mul_prod_erase (groups k)
    (fun i => termNumeratorAtPoint evals i)
    (fun i => termPhiAtPoint xChallenge evals i) hden

omit [Fintype F] [DecidableEq F] in
theorem domainIdentityAtPoint_eq_zero
    (groups : PartialSumGroups M K) (xChallenge : F) (evals : PointEvaluations F M K)
    (k : Fin K)
    (hhelper : evals.helpers k = helperValueAtPoint groups xChallenge evals k)
    (hden : ∀ i ∈ groups k, termPhiAtPoint xChallenge evals i ≠ 0) :
    domainIdentityAtPoint groups xChallenge evals k = 0 := by
  unfold domainIdentityAtPoint
  rw [hhelper, helperValueAtPoint_mul_denominatorProduct groups xChallenge evals k hden]
  simp

/-- The verifier's final check value `Q(L_H(r,z), m(r), φᵢ(r), hₖ(r))` from paper (19). -/
noncomputable def qAtPoint (groups : PartialSumGroups M K) (xChallenge : F)
    (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (evals : PointEvaluations F M K) : F :=
  ∑ k : Fin K, (
    evals.helpers k +
      lagrangeKernelAtPoint F rChallenge zChallenge * batchingScalars k *
        domainIdentityAtPoint groups xChallenge evals k)

omit [Fintype F] [DecidableEq F] in
theorem qAtPoint_eq_sum_helpers
    (groups : PartialSumGroups M K) (xChallenge : F) (zChallenge rChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (evals : PointEvaluations F M K)
    (hhelper : ∀ k : Fin K, evals.helpers k = helperValueAtPoint groups xChallenge evals k)
    (hden : ∀ k : Fin K, ∀ i ∈ groups k, termPhiAtPoint xChallenge evals i ≠ 0) :
    qAtPoint groups xChallenge zChallenge rChallenge batchingScalars evals =
      ∑ k : Fin K, evals.helpers k := by
  unfold qAtPoint
  apply Finset.sum_congr rfl
  intro k _
  rw [domainIdentityAtPoint_eq_zero groups xChallenge evals k (hhelper k) (hden k)]
  simp

/-- Predicate for paper step 4: final oracle-query answers match the sumcheck's expected value. -/
noncomputable def finalQueryCheck (groups : PartialSumGroups M K) (xChallenge : F)
    (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (evals : PointEvaluations F M K) (expectedValue : F) : Prop :=
  qAtPoint groups xChallenge zChallenge rChallenge batchingScalars evals = expectedValue

omit [Fintype F] [DecidableEq F] in
theorem finalQueryCheck_of_expected_sum_helpers
    (groups : PartialSumGroups M K) (xChallenge : F) (zChallenge rChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (evals : PointEvaluations F M K)
    (hhelper : ∀ k : Fin K, evals.helpers k = helperValueAtPoint groups xChallenge evals k)
    (hden : ∀ k : Fin K, ∀ i ∈ groups k, termPhiAtPoint xChallenge evals i ≠ 0) :
    finalQueryCheck groups xChallenge zChallenge rChallenge batchingScalars evals
      (∑ k : Fin K, evals.helpers k) := by
  unfold finalQueryCheck
  exact qAtPoint_eq_sum_helpers groups xChallenge zChallenge rChallenge batchingScalars evals
    hhelper hden

end ProtocolAlgebra

end Logup
