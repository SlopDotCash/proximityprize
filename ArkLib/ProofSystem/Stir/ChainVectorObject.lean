/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.VSpecBridge
import ArkLib.OracleReduction.Cast

/-!
# The hOₘ object cast: `stirChainVectorObject` (#301)

The **object-side identity** completing the `VectorIOP` packaging of the full vectorised STIR
chain: `stirFullVectorReduction` (which lives over the compound append spec) is transported via
`OracleReduction.cast` onto `(stirChainVSpec ι F M).toProtocolSpec F` — the protocol spec of a
single literal `VectorSpec` — using the spec equality `stirChainVSpec_toProtocolSpec`.

The `hOₘ` side condition of `OracleReduction.cast` demands that the two message-interface
families agree (up to `dcast` along the message-type equality): on the compound side the family
is the nested `instOracleInterfaceMessageAppend` / `instOracleInterfaceMessageSeqCompose` tower,
on the `toProtocolSpec` side it is the literal `fun _ => OracleInterface.instVector`. The proof
goes through a generic predicate `IsVectorFamily` ("every slot's interface is heterogeneously
`instVector` at a given length profile"):

* leaves (`VectorSpec.toProtocolSpec`) are vector families at their length profile
  (`isVectorFamily_toProtocolSpec`, definitional);
* `++ₚ` of vector families is a vector family at the `Fin.vappend` of the profiles
  (`isVectorFamily_append`, via `instAppend_inl_heq`/`instAppend_inr_heq`);
* `seqCompose` of vector families is a vector family at the `Fin.vflatten` of the profiles
  (`isVectorFamily_seqCompose`, by induction using the definitional equality
  `seqCompose (m+1) ≡ head ++ₚ seqCompose tail` of both the specs and the instances);
* two vector families at the *same* profile on propositionally equal specs satisfy the `hOₘ`
  condition (`hOm_of_isVectorFamily`).

Main results: `stirChainVectorObject` (the cast object) and `stirChainVectorIOR` (the same
object packaged in the literal `VectorIOR` type that `stir_main`/`stir_rbr_soundness`-style
statements quantify over).
-/

namespace ProtocolSpec

open OracleInterface

/-- A message-interface family on `pSpec` is a **vector family** at length profile
`ℓ : Fin n → ℕ` (over alphabet `A`) if at every message slot it agrees, heterogeneously, with
the canonical `Vector`-oracle interface `OracleInterface.instVector` at that slot's length.

This is the invariant preserved by `++ₚ` and `seqCompose` that lets the compound-spec
interface tower be compared with the single-`VectorSpec` interface family. -/
@[reducible]
def IsVectorFamily {n : ℕ} {pSpec : ProtocolSpec n} (A : Type) (ℓ : Fin n → ℕ)
    (O : ∀ i, OracleInterface (pSpec.Message i)) : Prop :=
  ∀ i, HEq (O i) (OracleInterface.instVector (α := A) (n := ℓ i.1))

/-- `instVector` is heterogeneously congruent in its length index. -/
theorem instVector_heq_of_eq {A : Type} {k₁ k₂ : ℕ} (h : k₁ = k₂) :
    HEq (OracleInterface.instVector (α := A) (n := k₁))
      (OracleInterface.instVector (α := A) (n := k₂)) := by
  subst h; rfl

/-- **Leaf case**: the canonical message-interface family of `vPSpec.toProtocolSpec A` is a
vector family at `vPSpec.length` (definitionally). -/
theorem isVectorFamily_toProtocolSpec {n : ℕ} (A : Type) (v : VectorSpec n) :
    IsVectorFamily A v.length
      (VectorSpec.instOracleInterfaceMessageToProtocolSpec (A := A) (vPSpec := v)) :=
  fun _ => HEq.rfl

/-- **Append case**: appending two vector families yields a vector family at the `Fin.vappend`
of the length profiles. -/
theorem isVectorFamily_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {A : Type} {ℓ₁ : Fin m → ℕ} {ℓ₂ : Fin n → ℕ}
    [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    (h₁ : IsVectorFamily A ℓ₁ O₁) (h₂ : IsVectorFamily A ℓ₂ O₂) :
    IsVectorFamily A (Fin.vappend ℓ₁ ℓ₂)
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)) := by
  rintro ⟨⟨i, hi⟩, hdir⟩
  rcases Nat.lt_or_ge i m with hlt | hge
  · -- the slot lies in the left block: the index is `MessageIdx.inl` of a `pSpec₁` index
    have hd1 : pSpec₁.dir ⟨i, hlt⟩ = .P_to_V := by
      have hv := Fin.vappend_left pSpec₁.dir pSpec₂.dir ⟨i, hlt⟩
      rw [← hv]; exact hdir
    have hlen : ℓ₁ ⟨i, hlt⟩ = Fin.vappend ℓ₁ ℓ₂ ⟨i, hi⟩ :=
      (Fin.vappend_left ℓ₁ ℓ₂ ⟨i, hlt⟩).symm
    have hfin : HEq (OracleInterface.instVector (α := A) (n := ℓ₁ ⟨i, hlt⟩))
        (OracleInterface.instVector (α := A) (n := Fin.vappend ℓ₁ ℓ₂ ⟨i, hi⟩)) :=
      instVector_heq_of_eq hlen
    -- `MessageIdx.inl ⟨⟨i, hlt⟩, hd1⟩` is definitionally the ambient index
    exact (OracleVerifier.Append.instAppend_inl_heq (pSpec₂ := pSpec₂)
      ⟨⟨i, hlt⟩, hd1⟩).trans ((h₁ ⟨⟨i, hlt⟩, hd1⟩).trans hfin)
  · -- the slot lies in the right block: the index is `MessageIdx.inr` of a `pSpec₂` index
    have hj : i - m < n := by omega
    have hnat : (Fin.natAdd m ⟨i - m, hj⟩ : Fin (m + n)) = ⟨i, hi⟩ := by
      apply Fin.ext
      show m + (i - m) = i
      omega
    have hd2 : pSpec₂.dir ⟨i - m, hj⟩ = .P_to_V := by
      have hv := Fin.vappend_right pSpec₁.dir pSpec₂.dir ⟨i - m, hj⟩
      rw [← hv, hnat]; exact hdir
    have hidx : (⟨⟨i, hi⟩, hdir⟩ : (pSpec₁ ++ₚ pSpec₂).MessageIdx)
        = MessageIdx.inr (pSpec₁ := pSpec₁) ⟨⟨i - m, hj⟩, hd2⟩ :=
      Subtype.ext hnat.symm
    have h0 : HEq
        (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
          ⟨⟨i, hi⟩, hdir⟩)
        (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
          (MessageIdx.inr ⟨⟨i - m, hj⟩, hd2⟩)) := by
      rw [hidx]
    have hlen : ℓ₂ ⟨i - m, hj⟩ = Fin.vappend ℓ₁ ℓ₂ ⟨i, hi⟩ := by
      rw [← hnat]
      exact (Fin.vappend_right ℓ₁ ℓ₂ ⟨i - m, hj⟩).symm
    have hfin : HEq (OracleInterface.instVector (α := A) (n := ℓ₂ ⟨i - m, hj⟩))
        (OracleInterface.instVector (α := A) (n := Fin.vappend ℓ₁ ℓ₂ ⟨i, hi⟩)) :=
      instVector_heq_of_eq hlen
    exact h0.trans ((OracleVerifier.Append.instAppend_inr_heq (pSpec₁ := pSpec₁)
      ⟨⟨i - m, hj⟩, hd2⟩).trans ((h₂ ⟨⟨i - m, hj⟩, hd2⟩).trans hfin))

/-- **Sequential-composition case**: the `seqCompose` of a family of vector families is a
vector family at the `Fin.vflatten` of the length profiles. Induction on the number of blocks,
exploiting that at `m + 1` both `seqCompose` and its message-interface instance are
*definitionally* the append of the head with the `seqCompose` of the tail. -/
theorem isVectorFamily_seqCompose {m : ℕ} :
    ∀ {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} {A : Type}
      (ℓ : ∀ i, Fin (n i) → ℕ)
      [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)],
      (∀ i, IsVectorFamily A (ℓ i) (Oₘ i)) →
      IsVectorFamily A (Fin.vflatten ℓ)
        (instOracleInterfaceMessageSeqCompose (pSpec := pSpec)) := by
  induction m with
  | zero =>
    intro n pSpec A ℓ Oₘ h i
    exact absurd i.1.isLt (by simp)
  | succ m ih =>
    intro n pSpec A ℓ Oₘ h
    exact isVectorFamily_append (h 0) (ih (fun i => ℓ i.succ) (fun i => h i.succ))

/-- **The glue**: two vector families at the *same* length profile on propositionally equal
protocol specs satisfy the `hOₘ` side condition of `OracleReduction.cast` (at `hn = rfl`). -/
theorem hOm_of_isVectorFamily {n : ℕ} {pSpec₁ pSpec₂ : ProtocolSpec n}
    (hSpec : pSpec₁.cast rfl = pSpec₂) {A : Type} {ℓ : Fin n → ℕ}
    [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    (h₁ : IsVectorFamily A ℓ O₁) (h₂ : IsVectorFamily A ℓ O₂) :
    ∀ i, O₁ i = dcast (Message.cast_idx hSpec) (O₂ (i.cast rfl hSpec)) := by
  intro i
  rw [dcast_eq_root_cast, eq_cast_iff_heq]
  exact (h₁ i).trans (h₂ (i.cast rfl hSpec)).symm

end ProtocolSpec

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec ProtocolSpec.VectorSpec STIR NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq ι] in
/-- The compound-spec message-interface tower of the full vectorised STIR chain is a vector
family at the literal chain `VectorSpec`'s length profile. (The length profiles agree
definitionally because `vsAppend`/`vsSeqCompose` build `length` by exactly the
`Fin.vappend`/`Fin.vflatten` that `++ₚ`/`seqCompose` use on the `Type` fields.) -/
theorem isVectorFamily_stirChainCompound (M : ℕ) :
    IsVectorFamily F (stirChainVSpec ι F M).length
      (instStirVecFullMsgInterface (F := F) (ι := ι) M) :=
  isVectorFamily_append (isVectorFamily_toProtocolSpec F stirInitVSpec)
    (isVectorFamily_append (isVectorFamily_toProtocolSpec F (stirRound3VSpec ι F))
      (isVectorFamily_append
        (isVectorFamily_seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).length)
          (fun _ => isVectorFamily_toProtocolSpec F (stirRound3VSpec ι F)))
        (isVectorFamily_toProtocolSpec F (stirFinalVSpec ι F))))

/-- **The `hOₘ` side condition** for casting the full vectorised chain onto
`(stirChainVSpec ι F M).toProtocolSpec F`: the compound-spec interface tower agrees (up to
`dcast` along the message-type equality induced by `stirChainVSpec_toProtocolSpec`) with the
single-`VectorSpec` interface family. -/
theorem stirChain_hOm (M : ℕ) :
    ∀ i, instStirVecFullMsgInterface (F := F) (ι := ι) M i
      = dcast (Message.cast_idx ((stirChainVSpec_toProtocolSpec (ι := ι) (F := F) M).symm))
          (VectorSpec.instOracleInterfaceMessageToProtocolSpec
            (i.cast rfl ((stirChainVSpec_toProtocolSpec M).symm))) :=
  hOm_of_isVectorFamily ((stirChainVSpec_toProtocolSpec M).symm)
    (isVectorFamily_stirChainCompound M)
    (isVectorFamily_toProtocolSpec F (stirChainVSpec ι F M))

/-- **The hOₘ object cast (#301)**: the full vectorised STIR chain, transported via
`OracleReduction.cast` onto the protocol spec of the *single literal* `VectorSpec`
`stirChainVSpec ι F M`. This is `stirFullVectorReduction` viewed over the genuine
`VectorSpec`-generated wire format. -/
noncomputable def stirChainVectorObject (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ Unit (OStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((stirChainVSpec ι F M).toProtocolSpec F) :=
  OracleReduction.cast rfl ((stirChainVSpec_toProtocolSpec M).symm) (stirChain_hOm M)
    (stirFullVectorReduction φ deg M)

/-- The chain object packaged in the literal `VectorIOR` type: the full vectorised STIR chain
IS a vector interactive oracle reduction over the single `VectorSpec` `stirChainVSpec ι F M`. -/
noncomputable def stirChainVectorIOR (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    VectorIOR Unit (OStmt ι F) Unit (F × F) (VOStmt ι F) Unit (stirChainVSpec ι F M) F :=
  stirChainVectorObject φ deg M

end Round3

end StirIOP

#print axioms ProtocolSpec.isVectorFamily_toProtocolSpec
#print axioms ProtocolSpec.isVectorFamily_append
#print axioms ProtocolSpec.isVectorFamily_seqCompose
#print axioms ProtocolSpec.hOm_of_isVectorFamily
#print axioms StirIOP.Round3.isVectorFamily_stirChainCompound
#print axioms StirIOP.Round3.stirChain_hOm
#print axioms StirIOP.Round3.stirChainVectorObject
#print axioms StirIOP.Round3.stirChainVectorIOR
