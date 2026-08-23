/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
  # Sequential Composition of Many Oracle Reductions

  This file defines the sequential composition of an arbitrary `m + 1` number of oracle reductions.
  This is defined by iterating the composition of two reductions, as defined in `Append.lean`.

  The security properties of the general sequential composition of reductions are then inherited
  from the case of composing two reductions.
-/

open ProtocolSpec OracleComp

universe u v

variable {ι : Type} {oSpec : OracleSpec ι}

section Composition

namespace Prover

/-- Sequential composition of provers, defined via iteration of the composition (append) of two
  provers. Specifically, we have the following definitional equalities:
- `seqCompose (m := 0) P = Prover.id`
- `seqCompose (m := m + 1) P = append (P 0) (seqCompose (m := m) P)`

Note: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
      Prover oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) :=
  match m with
  | 0 => Prover.id
  | _ + 1 => append (P 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P (Fin.succ i)))

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type) (Wit : Fin 1 → Type) {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin 0) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit P = Prover.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin (m + 1)) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit P =
      append (P 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P (Fin.succ i))) := rfl

end Prover

namespace Verifier

/-- Sequential composition of verifiers, defined via iteration of the composition (append) of
two verifiers. Specifically, we have the following definitional equalities:
- `seqCompose (m := 0) V = Verifier.id`
- `seqCompose (m := m + 1) V = append (V 0) (seqCompose (m := m) V)`

Note: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    Verifier oSpec (Stmt 0) (Stmt (Fin.last m)) (seqCompose pSpec) := match m with
  | 0 => Verifier.id
  | _ + 1 => append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i)))

@[simp]
lemma seqCompose_zero (Stmt : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin 0) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    seqCompose Stmt V = Verifier.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ} (Stmt : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin (m + 1)) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    seqCompose Stmt V = append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i))) := rfl

end Verifier

namespace Reduction

/-- Sequential composition of reductions, defined via sequential composition of provers and
  verifiers (or equivalently, folding over the append of reductions).

Note: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    Reduction oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := Prover.seqCompose Stmt Wit (fun i => (R i).prover)
  verifier := Verifier.seqCompose Stmt (fun i => (R i).verifier)

@[simp]
lemma seqCompose_zero (Stmt : Fin 1 → Type) (Wit : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin 0) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit R = Reduction.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin (m + 1)) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit R =
      append (R 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))) := rfl

end Reduction

namespace OracleProver

/-- Sequential composition of provers in oracle reductions, defined via sequential composition of
  provers in non-oracle reductions. -/
@[inline]
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      OracleProver oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    OracleProver oSpec (Stmt 0) (OStmt 0) (Wit 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (Wit (Fin.last m)) (seqCompose pSpec) :=
  Prover.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit P

@[simp]
lemma seqCompose_def {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      OracleProver oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt OStmt Wit P = Prover.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit P :=
  rfl

end OracleProver

namespace OracleVerifier

/-- Sequential composition of verifiers in oracle reductions.

This is the auxiliary version that has instance parameters as implicit parameters, so that matching
on `m` can properly specialize those parameters.

Note: have to fix instance diamonds to make this work -/
def seqCompose' {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)) :
    OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (seqCompose pSpec) := match m with
  | 0 => @OracleVerifier.id ι oSpec (Stmt 0) (ιₛ 0) (OStmt 0) (Oₛ := Oₛ 0)
  | _ + 1 =>
    letI : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0) (V 0) :=
      coh 0
    append (V 0) (seqCompose' (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
      (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i))
      (fun i => coh i.succ))

/-- Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the
  composition (append) of two oracle verifiers. -/
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)] :
    OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (seqCompose pSpec) :=
  seqCompose' Stmt OStmt Oₛ Oₘ V coh

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type)
    {ιₛ : Fin 1 → Type} (OStmt : (i : Fin 1) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin 0) → OracleVerifier oSpec
      (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)] :
    seqCompose Stmt OStmt V = OracleVerifier.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type)
    {ιₛ : Fin (m + 2) → Type} (OStmt : (i : Fin (m + 2)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin (m + 1)) → OracleVerifier oSpec
      (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)] :
    seqCompose Stmt OStmt V =
      letI : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0) (V 0) :=
        coh 0
      append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
          (fun i => V (Fin.succ i))
          (coh := fun i => coh i.succ)) := rfl

@[simp]
lemma seqCompose_toVerifier {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)]
    (hSeqComposeToVerifier :
      (seqCompose Stmt OStmt V).toVerifier =
        Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier)) :
    (seqCompose Stmt OStmt V).toVerifier =
      Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier) :=
  hSeqComposeToVerifier

/-- **Sequential-composition coherence.** A `seqCompose'` of oracle verifiers whose every leaf is
`AppendCoherent` is itself `AppendCoherent` (as the outer verifier over the `seqCompose`d message
oracles).  Proved by induction: `seqCompose'` unfolds (via `seqCompose_succ`) to a binary `append`
of `V 0` with the tail's `seqCompose'`, whose coherence is supplied by `AppendCoherent.append`
together with the inductive hypothesis; the base case is the trivial `OracleVerifier.id`.  The
appended-spec message interface `instOracleInterfaceMessageAppend (pSpec 0) (seqCompose tail)` is
definitionally the `seqCompose`-message interface, so no message-interface coercion is needed. -/
theorem seqCompose'_appendCoherent {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)) :
    OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ (Fin.last m))
      (OracleVerifier.seqCompose' Stmt OStmt Oₛ Oₘ V coh) := by
  induction m with
  | zero =>
    refine { hCohInl := fun a k h => ?_, hCohInr := fun a k h => k.1.elim0 }
    simp only [OracleVerifier.seqCompose', OracleVerifier.id, Function.Embedding.inl_apply] at h ⊢
    obtain rfl := Sum.inl.inj h; rfl
  | succ m ih =>
    letI : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0) (V 0) :=
      coh 0
    letI tailcoh := ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (fun i => Oₛ (Fin.succ i))
      (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i)) (fun i => coh i.succ)
    exact OracleVerifier.Append.AppendCoherent.append (c₁ := coh 0) (c₂ := tailcoh) (V 0) _

/-- Instance form of `seqCompose'_appendCoherent` for the public `OracleVerifier.seqCompose`: chains
of `seqCompose` synthesize their outer `AppendCoherent` automatically from the per-round leaf
instances. -/
instance seqCompose_appendCoherent {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)] :
    OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ (Fin.last m))
      (OracleVerifier.seqCompose Stmt OStmt V) :=
  seqCompose'_appendCoherent Stmt OStmt Oₛ Oₘ V coh

end OracleVerifier

namespace OracleReduction

/-- Sequential composition of oracle reductions, defined via sequential composition of oracle
  provers and oracle verifiers. -/
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier] :
    OracleReduction oSpec (Stmt 0) (OStmt 0) (Wit 0)
      (Stmt (Fin.last m)) (OStmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := OracleProver.seqCompose Stmt OStmt Wit (fun i => (R i).prover)
  verifier := OracleVerifier.seqCompose Stmt OStmt (fun i => (R i).verifier)

/-- The verifier of a `seqCompose`d oracle reduction is again `AppendCoherent` (its `verifier` field
is definitionally `OracleVerifier.seqCompose … (fun i => (R i).verifier)`), so a `seqCompose`
composite can itself be `.append`ed onto another phase with coherence synthesized automatically. -/
instance seqCompose_verifier_appendCoherent {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier] :
    OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ (Fin.last m))
      (seqCompose Stmt OStmt Wit R).verifier :=
  OracleVerifier.seqCompose_appendCoherent Stmt OStmt (fun i => (R i).verifier)

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type)
    {ιₛ : Fin 1 → Type} (OStmt : (i : Fin 1) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin 0) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier] :
    seqCompose Stmt OStmt Wit R =
      @OracleReduction.id ι oSpec (Stmt 0) (ιₛ 0) (OStmt 0) (Wit 0) (Oₛ 0) := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type)
    {ιₛ : Fin (m + 2) → Type} (OStmt : (i : Fin (m + 2)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin (m + 1)) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier] :
    seqCompose Stmt OStmt Wit R =
      letI : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0)
          (R 0).verifier := coh 0
      append (R 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
          (fun i => R (Fin.succ i))
          (coh := fun i => coh i.succ)) := rfl

end OracleReduction

end Composition

variable {m : ℕ}
    {Stmt : Fin (m + 1) → Type}
    {ιₛ : Fin (m + 1) → Type} {OStmt : (i : Fin (m + 1)) → ιₛ i → Type}
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {Wit : Fin (m + 1) → Type}
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- section Execution

-- end Execution

section Security

open scoped NNReal

namespace Reduction

omit Oₘ in
theorem seqCompose_completeness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i))
    (completenessError : Fin m → ℝ≥0)
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i))
    (hSeqComposeCompleteness :
      (Reduction.seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
        (∑ i, completenessError i)) :
      (Reduction.seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
        (∑ i, completenessError i) :=
  hSeqComposeCompleteness

omit Oₘ in
theorem seqCompose_perfectCompleteness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ))
    (hSeqComposePerfectCompleteness :
      (Reduction.seqCompose Stmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m))) :
      (Reduction.seqCompose Stmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m)) :=
  hSeqComposePerfectCompleteness

set_option maxHeartbeats 1000000 in
-- The induction proof creates large dependent Fin goals in the successor case.
/-- **Brick (issue #25): n-ary `seqCompose` perfect completeness reduces to the binary `append`
keystone.** By induction on `m`: base case `Reduction.id_perfectCompleteness`; step unfolds via
`seqCompose_succ` and discharges the binary `append` with `hAppend` + the IH. Feeding the eventual
unconditional binary `reduction_append_perfectCompleteness` as `hAppend` closes the n-ary statement.
Modeled on the proven `seqCompose'_appendCoherent` induction. -/
theorem seqCompose_perfectCompleteness_of_append {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)},
        R₁.perfectCompleteness init impl r₁ r₂ → R₂.perfectCompleteness init impl r₂ r₃ →
        (R₁.append R₂).perfectCompleteness init impl r₁ r₃)
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  induction m with
  | zero =>
    rw [seqCompose_zero]
    simpa using
      (Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0))
  | succ m ih =>
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.perfectCompleteness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
    exact hAppend (R 0) _ (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => h (Fin.succ i)))

set_option maxHeartbeats 1000000 in
-- The induction proof creates large dependent Fin goals in the successor case.
/-- **Brick (issue #25): n-ary `seqCompose` completeness reduces to the binary `append` keystone.**
Error-bearing analogue of `seqCompose_perfectCompleteness_of_append`: base case
`Reduction.id_perfectCompleteness` (= completeness with error `0`) and `∑ (i : Fin 0) = 0`;
step splits the error with `Fin.sum_univ_succ` into `completenessError 0 + ∑ tail` and applies
`hAppend`. -/
theorem seqCompose_completeness_of_append {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (completenessError : Fin m → ℝ≥0)
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)} {e₁ e₂ : ℝ≥0},
        R₁.completeness init impl r₁ r₂ e₁ → R₂.completeness init impl r₂ r₃ e₂ →
        (R₁.append R₂).completeness init impl r₁ r₃ (e₁ + e₂))
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i)) :
    (seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
      (∑ i, completenessError i) := by
  induction m with
  | zero =>
    rw [seqCompose_zero, Fin.sum_univ_zero]
    simpa [Reduction.perfectCompleteness] using
      (Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0))
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.completeness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
        (completenessError 0 + ∑ i, completenessError (Fin.succ i))
    exact hAppend (R 0) _ (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => completenessError (Fin.succ i))
        (fun i => h (Fin.succ i)))

end Reduction

namespace Verifier

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
    sequential composition also satisfies soundness.
    The soundness error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).soundness init impl (lang i.castSucc) (lang i.succ) (soundnessError i))
    (hSeqComposeSoundness :
      (Verifier.seqCompose Stmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i)) :
      (Verifier.seqCompose Stmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) :=
  hSeqComposeSoundness

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (knowledgeError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).knowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (knowledgeError i))
    (hSeqComposeKnowledgeSoundness :
      (Verifier.seqCompose Stmt V).knowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (∑ i, knowledgeError i)) :
      (Verifier.seqCompose Stmt V).knowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (∑ i, knowledgeError i) :=
  hSeqComposeKnowledgeSoundness

/-- Reduction of `seqComposeChallengeIdxToSigma` along the `inl` embedding of a challenge index of
    the head protocol `pSpec 0`: it lands in the first component (`Fin 0`) with the original
    index. -/
private theorem seqComposeIdx_inl {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (s : (pSpec 0).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0) (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
      = ⟨0, s⟩ := by
  have hsplit : (Fin.splitSum (n := n)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1) = ⟨0, s.1⟩ := by
    rw [Fin.splitSum_succ]; erw [Fin.dappend_left]
  have hfst : (seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).fst = (0 : Fin (m + 1)) :=
    congrArg Sigma.fst hsplit
  refine Sigma.ext hfst ?_
  rw [Subtype.heq_iff_coe_heq (by rw [hfst]) (by rw [hfst])]
  have hval : ((seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).snd.1)
      = (Fin.splitSum (n := n)
          (ChallengeIdx.inl (pSpec₁ := pSpec 0)
            (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1).snd := rfl
  rw [hval]
  exact (Sigma.ext_iff.mp hsplit).2

/-- Reduction of `seqComposeChallengeIdxToSigma` along the `inr` embedding of a challenge index of
    the tail protocol: the first component is shifted by `Fin.succ` and the tail index is recovered
    by `seqComposeChallengeIdxToSigma` on the tail. -/
private theorem seqComposeIdx_inr {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (s : (ProtocolSpec.seqCompose (fun i => pSpec i.succ)).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0) (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
      = ⟨(seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).fst.succ,
          (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).snd⟩ := by
  have hsplit : (Fin.splitSum (n := n)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1)
      = ⟨(Fin.splitSum (n := fun i => n i.succ) s.1).fst.succ,
          (Fin.splitSum (n := fun i => n i.succ) s.1).snd⟩ := by
    rw [Fin.splitSum_succ]; erw [Fin.dappend_right]
  have hfst : (seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).fst =
        (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).fst.succ :=
    congrArg Sigma.fst hsplit
  refine Sigma.ext hfst ?_
  rw [Subtype.heq_iff_coe_heq (by rw [hfst]) (by rw [hfst])]
  have hval : ((seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).snd.1)
      = (Fin.splitSum (n := n)
          (ChallengeIdx.inr (pSpec₁ := pSpec 0)
            (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1).snd := rfl
  rw [hval]
  exact (Sigma.ext_iff.mp hsplit).2

/-- The RBR error of a sequential composition, expressed via `seqComposeChallengeIdxToSigma` over
    the *global* challenge index, equals the appended-form error built from the head error and the
    tail's `seqCompose` error transported by `ChallengeIdx.sumEquiv.symm`. This is the combinatorial
    bridge identifying the two indexings of the composed protocol's challenges, used to discharge
    the challenge-index transport goals left by `convert append_rbr…`. -/
private theorem seqComposeError_eq_append {m : ℕ} {n : Fin (m + 1) → ℕ}
    {pSpec : ∀ i, ProtocolSpec (n i)} (f : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (a : (pSpec 0 ++ₚ ProtocolSpec.seqCompose (fun i => pSpec i.succ)).ChallengeIdx) :
    f (seqComposeChallengeIdxToSigma (pSpec := pSpec) a).fst
        (seqComposeChallengeIdxToSigma (pSpec := pSpec) a).snd =
      (Sum.elim (f 0)
          (fun k => f (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) k).fst.succ
            (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) k).snd) ∘
        ⇑ChallengeIdx.sumEquiv.symm) a := by
  set g : ((i : Fin (m + 1)) × (pSpec i).ChallengeIdx) → ℝ≥0 := fun x => f x.fst x.snd with hg
  rw [Function.comp_apply]
  rw [show a = ChallengeIdx.sumEquiv (ChallengeIdx.sumEquiv.symm a) from
    (Equiv.apply_symm_apply _ _).symm]
  rw [Equiv.symm_apply_apply]
  rcases ChallengeIdx.sumEquiv.symm a with s | s
  · simp only [Sum.elim_inl, ChallengeIdx.sumEquiv, Equiv.coe_fn_mk]
    exact congrArg g (seqComposeIdx_inl s)
  · simp only [Sum.elim_inr, ChallengeIdx.sumEquiv, Equiv.coe_fn_mk]
    exact congrArg g (seqComposeIdx_inr s)

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem seqCompose_rbrSoundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness init impl (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hSeqComposeRbrSoundness :
      (Verifier.seqCompose Stmt V).rbrSoundness init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2)) :
      (Verifier.seqCompose Stmt V).rbrSoundness init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) :=
  hSeqComposeRbrSoundness

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem seqCompose_rbrKnowledgeSoundness
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i))
    (hSeqComposeRbrKnowledgeSoundness :
      (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrKnowledgeError ij.1 ij.2)) :
      (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrKnowledgeError ij.1 ij.2) :=
  hSeqComposeRbrKnowledgeSoundness

end Verifier

namespace OracleReduction

theorem seqCompose_completeness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier]
    (completenessError : Fin m → ℝ≥0)
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i))
    (hSeqComposeCompleteness :
      (OracleReduction.seqCompose Stmt OStmt Wit R).completeness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, completenessError i)) :
      (OracleReduction.seqCompose Stmt OStmt Wit R).completeness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, completenessError i) :=
  hSeqComposeCompleteness

theorem seqCompose_perfectCompleteness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (R i).verifier]
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ))
    (hSeqComposePerfectCompleteness :
      (OracleReduction.seqCompose Stmt OStmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m))) :
      (OracleReduction.seqCompose Stmt OStmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m)) :=
  hSeqComposePerfectCompleteness

end OracleReduction

namespace OracleVerifier

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
  sequential composition also satisfies soundness.
  The soundness error of the sequentially composed oracle verifier is the sum of the individual
  errors. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i × ∀ j, OStmt i j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)]
    (soundnessError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).soundness init impl (lang i.castSucc) (lang i.succ) (soundnessError i))
    (hSeqComposeSoundness :
      (OracleVerifier.seqCompose Stmt OStmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) :=
  hSeqComposeSoundness

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the sequentially composed oracle verifier is the sum of the individual
    errors. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)]
    (knowledgeError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).knowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (knowledgeError i))
    (hSeqComposeKnowledgeSoundness :
      (OracleVerifier.seqCompose Stmt OStmt V).knowledgeSoundness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, knowledgeError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).knowledgeSoundness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, knowledgeError i) :=
  hSeqComposeKnowledgeSoundness

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem seqCompose_rbrSoundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i × ∀ j, OStmt i j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)]
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness init impl (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hSeqComposeRbrSoundness :
      (OracleVerifier.seqCompose Stmt OStmt V).rbrSoundness
        init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2)) :
      (OracleVerifier.seqCompose Stmt OStmt V).rbrSoundness
        init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) :=
  hSeqComposeRbrSoundness

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem seqCompose_rbrKnowledgeSoundness
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) → OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)]
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i))
    (hSeqComposeRbrKnowledgeSoundness :
      (OracleVerifier.seqCompose Stmt OStmt V).rbrKnowledgeSoundness
        init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrKnowledgeError ij.1 ij.2)) :
    (OracleVerifier.seqCompose Stmt OStmt V).rbrKnowledgeSoundness
        init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrKnowledgeError ij.1 ij.2) :=
  hSeqComposeRbrKnowledgeSoundness

end OracleVerifier

/-! ## Source audit for current n-ary sequential-composition residual fronts -/

#print axioms Reduction.seqCompose_completeness
#print axioms Reduction.seqCompose_perfectCompleteness
#print axioms Verifier.seqCompose_soundness
#print axioms Verifier.seqCompose_knowledgeSoundness
#print axioms Verifier.seqComposeError_eq_append
#print axioms Verifier.seqCompose_rbrSoundness
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleReduction.seqCompose_completeness
#print axioms OracleReduction.seqCompose_perfectCompleteness
#print axioms OracleVerifier.seqCompose_soundness
#print axioms OracleVerifier.seqCompose_knowledgeSoundness
#print axioms OracleVerifier.seqCompose_rbrSoundness
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness

end Security
