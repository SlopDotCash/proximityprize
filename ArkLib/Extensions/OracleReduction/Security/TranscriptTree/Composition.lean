/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Security.TranscriptTree.Composition

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.TranscriptTree.Basic

/-!
  # Trees of transcripts — sequential composition

  This file relates trees of transcripts across sequential composition. If the first reduction
  speaks protocol `pSpec₁` and the second `pSpec₂`, the composed reduction speaks the appended
  protocol `pSpec₁ ++ₚ pSpec₂`. The central operation `appendSplit` cuts a tree over the appended
  protocol into a *first-stage* tree over `pSpec₁` and, below each first-stage leaf, a
  *second-stage* tree over `pSpec₂` — mirroring how the two reductions run in sequence. Everything
  is proved for an *arbitrary* `ChallengeTreeShape`, so each notion's composition theorem reduces to
  checking that its shape composes like the generic one, instead of repeating the work here.

  ## Main definitions

  - `ChallengeTree.appendArity` / `ChallengeTreeShape.append` — the canonical appended arity and
    shape for `pSpec₁ ++ₚ pSpec₂`, built by routing each appended challenge index back to its left
    or right component via `ChallengeIdx.sumEquiv`.
  - `ChallengeTree.AppendSplit` / `ChallengeTree.appendSplit` — the split of a tree over
    `pSpec₁ ++ₚ pSpec₂` into a first-stage tree (`fst`) and a path-indexed family of suffix trees
    (`sndAt`).

  ## Main theorems

  - `appendSplit_fst_isStructured` — the first-stage tree of a structured appended tree is itself
    structured (for `S₁`).
  - `appendSplit_sndAt_isStructured` — so is every second-stage tree hanging below a first-stage
    leaf (for `S₂`).
  - `appendSplit_fullTranscripts_append_of_mem` — recombination: gluing a first-stage leaf
    transcript onto any leaf transcript of the second-stage tree it selects gives back a leaf
    transcript of the original appended tree. This is the bridge from "extract on each stage" to
    "extract on the whole protocol".

  ## Implementation

  The mathematical split is simple: read the appended tree until the `pSpec₁` part ends, then view
  each remaining subtree as a `pSpec₂` tree. The Lean implementation is longer because
  `ChallengeTree` is indexed by its current round `Fin (n + 1)`. A round of the appended protocol is
  propositionally, but usually not definitionally, the same as the corresponding round of
  `pSpec₁` or `pSpec₂`, so directly doing `cases` on a tree or `LeafPath` can leave Lean with an
  unresolvable dependent index equation.

  To make the split visible to Lean, the file uses small certificate types. `RightProj` certifies
  that an appended subtree is already in the right-hand protocol, and `SplitData` certifies the
  left-hand prefix together with a `RightProj` at every boundary leaf. Each certificate has a `src`
  function reconstructing the original appended tree, so the auxiliary builders always return both
  the certificate and the proof that this reconstruction is faithful.

  Most of the technical code is then just dependent bookkeeping. The builders and `LeafPath`
  peelers (`peelMsg`, `chalPeel`) recurse with the round and tree still general, only specializing
  after matching the actual constructor; this is the usual convoy pattern. Bundling the
  reconstruction equation into the same recursion ensures that the proof obligations mention
  concrete constructors rather than an opaque recursive call. The reducible helpers `rightRound`
  and `leftRound` make the appended round indices line up by computation, leaving only the expected
  casts for directions, message/challenge types, and arities.

  ## Limitation

  Composition is binary and sequential (a single append `pSpec₁ ++ₚ pSpec₂`); `n`-ary composition
  is obtained by iterating.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

namespace ChallengeTree

section AppendShape

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

end AppendShape

end ChallengeTree

namespace ChallengeTreeShape

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

end ChallengeTreeShape

namespace ChallengeTree

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section AppendSplit

variable {arity₁ : pSpec₁.ChallengeIdx → ℕ} {arity₂ : pSpec₂.ChallengeIdx → ℕ}

/-- An appended subtree that is already in the right protocol, as an internal certificate indexed
by the right-protocol round. -/
inductive RightProj
    (arity₁ : pSpec₁.ChallengeIdx → ℕ) (arity₂ : pSpec₂.ChallengeIdx → ℕ) :
    Fin (n + 1) → Type where
  | leaf : RightProj arity₁ arity₂ (Fin.last n)
  | msg (i : Fin n) (h : pSpec₂.dir i = .P_to_V) (msg : pSpec₂.Message ⟨i, h⟩)
      (child : RightProj arity₁ arity₂ i.succ) : RightProj arity₁ arity₂ i.castSucc
  | chal (i : Fin n) (h : pSpec₂.dir i = .V_to_P)
      (challenges : Fin (arity₂ ⟨i, h⟩) → pSpec₂.Challenge ⟨i, h⟩)
      (children : Fin (arity₂ ⟨i, h⟩) → RightProj arity₁ arity₂ i.succ) :
      RightProj arity₁ arity₂ i.castSucc

/-- The right-protocol tree represented by a `RightProj` certificate. -/
def RightProj.tree : {r : Fin (n + 1)} → RightProj arity₁ arity₂ r →
    ChallengeTree pSpec₂ arity₂ r
  | _, .leaf => .leaf
  | _, .msg _ h m₂ child => .msgNode _ h m₂ child.tree
  | _, .chal _ h challenges children => .chalNode _ h challenges fun j => (children j).tree

/-- The appended source tree represented by a `RightProj` certificate. Thanks to `rightRound`
being reducible, every constructor index lands on the nose; only the `dir`/`Type`/arity transports
require casts. -/
def RightProj.src : {r : Fin (n + 1)} → RightProj arity₁ arity₂ r →
    ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)
  | _, .leaf => .leaf
  | _, .msg i h m₂ child =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .P_to_V := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h
      .msgNode (Fin.natAdd m i) hApp
        (cast (by simp [ProtocolSpec.Message, Fin.vappend_eq_append,
          Fin.append_right]) m₂) child.src
  | _, .chal i h challenges children =>
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h
      have hIdx : (⟨Fin.natAdd m i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inr ⟨i, h⟩ := by ext; rfl
      have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m i, hApp⟩ = arity₂ ⟨i, h⟩ := by
        rw [hIdx]; simpa [appendArity] using
          congrArg (Sum.elim arity₁ arity₂)
            (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨i, h⟩)
      .chalNode (Fin.natAdd m i) hApp
        (fun j => cast (by simp [ProtocolSpec.Challenge, Fin.vappend_eq_append,
          Fin.append_right]) (challenges (Fin.cast hAr j)))
        (fun j => (children (Fin.cast hAr j)).src)

/-- The legacy right certificate reconstructs the canonical right-tree embedding. -/
theorem RightProj.src_eq_embedRight :
    {r : Fin (n + 1)} → (R : RightProj arity₁ arity₂ r) → R.src = embedRight R.tree
  | _, .leaf => rfl
  | _, .msg i h message child => by
      simp only [RightProj.src, RightProj.tree, embedRight]
      rw [child.src_eq_embedRight]
  | _, .chal i h challenges children => by
      simp only [RightProj.src, RightProj.tree, embedRight]
      congr 1
      funext j
      exact (children _).src_eq_embedRight

/-- Build a `RightProj` certificate from an appended tree, **bundled with the proof** that its
`src` recovers the original tree. Bundling is essential: the round-trip equation is discharged in
the same convoy recursion that builds the certificate, so every obligation is about a literal
constructor (the recursor-defined function never needs to be reduced under a variable index). -/
def rightProjOfTreeAux : {a : Fin (m + n + 1)} →
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a) →
    (r : Fin (n + 1)) → (heq : a = rightRound r) →
    { R : RightProj arity₁ arity₂ r // HEq R.src t } := fun {a} t =>
  ChallengeTree.rec
    (motive := fun a t => (r : Fin (n + 1)) → (heq : a = rightRound r) →
      { R : RightProj arity₁ arity₂ r // HEq R.src t })
    (fun r heq => by
      have hr : r = Fin.last n := by
        apply Fin.ext
        have hv := congrArg Fin.val heq
        unfold rightRound at hv
        simp only [Fin.val_last, Fin.val_natAdd] at hv ⊢
        omega
      subst hr
      exact ⟨.leaf, HEq.rfl⟩)
    (fun m' h' m₂ child ih r heq =>
      r.lastCases
        (motive := fun r => (heq : m'.castSucc = rightRound r) →
          { R : RightProj arity₁ arity₂ r // HEq R.src (ChallengeTree.msgNode m' h' m₂ child) })
        (fun heq => by
          exfalso
          have hv := congrArg Fin.val heq
          unfold rightRound at hv
          simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hv
          have := m'.isLt; omega)
        (fun r₀ heq => by
          have hm' : m' = Fin.natAdd m r₀ := by
            apply Fin.ext
            have hv := congrArg Fin.val heq
            unfold rightRound at hv
            simp only [Fin.val_castSucc, Fin.val_natAdd] at hv ⊢
            omega
          subst hm'
          have hdir : pSpec₂.dir r₀ = .P_to_V := by
            simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h'
          refine ⟨.msg r₀ hdir
            (cast (by simp [ProtocolSpec.Message, Fin.vappend_eq_append,
              Fin.append_right]) m₂)
            (ih r₀.succ rfl).1, ?_⟩
          have hchild : ((ih r₀.succ rfl).1).src = child := eq_of_heq (ih r₀.succ rfl).2
          apply heq_of_eq
          simp only [RightProj.src]
          rw [hchild]
          congr 1
          simp [cast_cast])
        heq)
    (fun m' h' chals children ih r heq =>
      r.lastCases
        (motive := fun r => (heq : m'.castSucc = rightRound r) →
          { R : RightProj arity₁ arity₂ r //
            HEq R.src (ChallengeTree.chalNode m' h' chals children) })
        (fun heq => by
          exfalso
          have hv := congrArg Fin.val heq
          unfold rightRound at hv
          simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hv
          have := m'.isLt; omega)
        (fun r₀ heq => by
          have hm' : m' = Fin.natAdd m r₀ := by
            apply Fin.ext
            have hv := congrArg Fin.val heq
            unfold rightRound at hv
            simp only [Fin.val_castSucc, Fin.val_natAdd] at hv ⊢
            omega
          subst hm'
          have hdir : pSpec₂.dir r₀ = .V_to_P := by
            simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h'
          have hIdx : (⟨Fin.natAdd m r₀, h'⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
              = ChallengeIdx.inr ⟨r₀, hdir⟩ := by ext; rfl
          have hAr : appendArity arity₁ arity₂ ⟨Fin.natAdd m r₀, h'⟩ = arity₂ ⟨r₀, hdir⟩ := by
            rw [hIdx]; simpa [appendArity] using
              congrArg (Sum.elim arity₁ arity₂)
                (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨r₀, hdir⟩)
          refine ⟨.chal r₀ hdir
            (fun j => cast (by simp [ProtocolSpec.Challenge, Fin.vappend_eq_append,
              Fin.append_right]) (chals (Fin.cast hAr.symm j)))
            (fun j => (ih (Fin.cast hAr.symm j) r₀.succ rfl).1), ?_⟩
          apply heq_of_eq
          simp only [RightProj.src]
          congr 1
          · funext j
            simp [cast_cast]
          · funext j
            exact eq_of_heq (ih _ r₀.succ rfl).2)
        heq)
    t

/-- Build a `RightProj` certificate from an appended tree already in the right protocol. -/
def rightProjOfTree {r : Fin (n + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)) :
    RightProj arity₁ arity₂ r := (rightProjOfTreeAux T r rfl).1

/-- The `RightProj` certificate built from an appended tree faithfully represents it. -/
theorem rightProjOfTree_src {r : Fin (n + 1)}
    (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) (rightRound r)) :
    (rightProjOfTree (arity₁ := arity₁) (arity₂ := arity₂) T).src = T :=
  eq_of_heq (rightProjOfTreeAux T r rfl).2

/-- Build a `SplitData` certificate from an appended tree, bundled with the round-trip proof. The
boundary case delegates to `rightProjOfTreeAux`; `leftRound (Fin.last m)` is defeq `rightRound 0`
so the same `heq` is reused. -/
def splitDataOfTreeAux : {a : Fin (m + n + 1)} →
    (t : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) a) →
    (r : Fin (m + 1)) → (heq : a = leftRound r) →
    { S : SplitData arity₁ arity₂ r // HEq S.src t }  := fun {a} t r heq => by
  cases heq
  exact ⟨splitDataOfTree t, heq_of_eq (splitDataOfTree_src t)⟩

section Structure

variable {S₁ : ChallengeTreeShape pSpec₁} {S₂ : ChallengeTreeShape pSpec₂}

/-- If the appended source tree of a `RightProj` is structured then so is its right-protocol
tree. -/
theorem RightProj.tree_isStructured :
    {r : Fin (n + 1)} → (R : RightProj S₁.arity S₂.arity r) →
    R.src.IsStructured (S₁.append S₂) → R.tree.IsStructured S₂
  | _, .leaf, _ => trivial
  | _, .msg i h m₂ child, hR =>
      RightProj.tree_isStructured child
        (by simpa [RightProj.src, ChallengeTree.IsStructured] using hR)
  | _, .chal i h chals children, hR => by
      have hApp : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P := by
        simpa [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right] using h
      have hIdx : (⟨Fin.natAdd m i, hApp⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
          = ChallengeIdx.inr ⟨i, h⟩ := by ext; rfl
      have hAr : appendArity S₁.arity S₂.arity ⟨Fin.natAdd m i, hApp⟩ = S₂.arity ⟨i, h⟩ := by
        rw [hIdx]; simpa [appendArity] using
          congrArg (Sum.elim S₁.arity S₂.arity)
            (ChallengeIdx.sumEquiv_symm_inr (pSpec₁ := pSpec₁) ⟨i, h⟩)
      have hR' := hR
      simp only [RightProj.src, ChallengeTree.IsStructured] at hR'
      refine ⟨?_, fun j => RightProj.tree_isStructured (children j) (hR'.2 (Fin.cast hAr.symm j))⟩
      -- `hsymm` is quantified over the dir proof so `simp` rewrites the `match` scrutinee
      -- regardless
      -- of which (proof-irrelevant) proof term `RightProj.src` inlined.
      have hsymm : ∀ (P : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i) = .V_to_P),
          ChallengeIdx.sumEquiv.symm (⟨Fin.natAdd m i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx)
            = Sum.inr ⟨i, h⟩ := fun P => by
        rw [show (⟨Fin.natAdd m i, P⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) = ChallengeIdx.inr ⟨i, h⟩
          from by ext; rfl, ChallengeIdx.sumEquiv_symm_inr]
      have hR1 := hR'.1
      simp only [ChallengeTreeShape.append] at hR1
      split at hR1
      · rename_i i₁ heqs; exact absurd (heqs.symm.trans (hsymm _)) (by simp)
      · rename_i i₂ heqs
        obtain rfl : i₂ = ⟨i, h⟩ := Sum.inr.inj (heqs.symm.trans (hsymm _))
        convert hR1 using 2
        simp [cast_cast]

end Structure

variable {S₁ : ChallengeTreeShape pSpec₁} {S₂ : ChallengeTreeShape pSpec₂}

section Membership

/-- A right-suffix transcript, prefixed by a full left transcript, is a transcript of the appended
source tree (membership form: induction on the certificate, no `LeafPath` peeling). -/
theorem RightProj.mem_transcripts_append :
    {r : Fin (n + 1)} → (R : RightProj arity₁ arity₂ r) → (tr₁ : FullTranscript pSpec₁) →
    (pre₂ : Transcript r pSpec₂) → {tr₂ : FullTranscript pSpec₂} →
    tr₂ ∈ R.tree.transcripts pre₂ → tr₁ ++ₜ tr₂ ∈ R.src.transcripts (rightPrefix tr₁ pre₂)
  | _, R, tr₁, pre₂, tr₂, htr₂ => by
      rw [R.src_eq_embedRight]
      exact embedRight_mem_transcripts_append R.tree tr₁ pre₂ htr₂

end Membership

end AppendSplit

end ChallengeTree

end ProtocolSpec
