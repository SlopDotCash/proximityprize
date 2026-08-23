/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform

/-!
# Foundation bricks for Claim 5.23 (`Hyb23StepResidual`, Δ(Hyb₂, Hyb₃) = 0)

This module proves the foundation layer (bricks H23-1 through H23-4) of the CO25 Claim 5.23
campaign: structural facts about the `φ⁻¹` parser stack
(`lookupEncodedMessageAlphaHat?` / `decodeMessagePhiInv?` / `decodeMessagesPrefixPhiInv?` /
`hybEncodedMessagesBefore?` in `TraceTransform.lean`) and the codec-image guard
(`d2sInCodecImagePredicate` in `ProverTransform.lean`).

Main results:
- `lookupEncodedMessageAlphaHat?_toList` (**H23-1**): looking up message index `j` in the
  flattened `EncodedMessagesBefore.toList` is exactly the structured projection `em ⟨j, hj⟩`.
- `d2sInCodecImagePredicate_eq_true_iff` (Bool glue): the simulator's image guard holds iff
  every encoded block before the round has a serialize-preimage.
- `hybEncodedMessagesBefore?_isSome_of_inImage` /
  `hybEncodedMessagesBefore?_isSome_of_d2sInCodecImagePredicate` (**H23-2**): the `φ⁻¹`
  parser succeeds on every codec-image input; hence `Hyb₃`'s parse-abort branch
  (`d2sCodecBridgeImpl` step 1) is dead code behind the guarded `gᵢ` emitter
  (`d2sHandleBacktrackSome`).
- `hybEncodedMessagesBefore?_serialize_eq` (**H23-3**, section property): on success, the
  decoded prefix re-serializes to the input blocks, `Serialize.serialize (mb.at j) = α̂_j`.
- `hybEncodedMessagesBefore?_injOn` (**H23-4**): `φ⁻¹` is injective on its success domain —
  two encoded prefixes decoding to the same message prefix are equal.
- `betaKey_injOn` (**H23-4'**): injectivity of the `Hyb₂ → Hyb₃` memo-key re-keying
  `β : (i, 𝕩, τ̂, α̂) ↦ (i, ((𝕩, bin(τ̂)), φ⁻¹(α̂)))` on decode-success keys, via
  `SaltCodec.encode_injective` and H23-4. This is what makes distinct `Hyb₂` memo misses
  read distinct (hence i.i.d.) cells of the coupled `f`-table in the Claim 5.23 coupling.

These bricks deliberately contain no probabilistic content; the table coupling and the
relational `simulateQ` lift (bricks H23-6..H23-10) consume them downstream. The generic
uniform-family comap brick (H23-5) lives in `ArkLib.ToVCVio.UniformFamilyComap`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.Hyb23Bricks

open Backtrack TraceTransform ProverTransform

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)]
  {δ : Nat}

noncomputable section

/-! ## List helpers -/

/-- `findSome?` over a `filterMap` is `findSome?` of the Kleisli composite. -/
private lemma findSome?_filterMap {α β γ : Type _} (l : List α)
    (g : α → Option β) (f : β → Option γ) :
    (l.filterMap g).findSome? f = l.findSome? (fun x => (g x).bind f) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hgx : g x with
    | none => simp [List.filterMap_cons, hgx, ih]
    | some b =>
      cases hfb : f b with
      | none => simp [List.filterMap_cons, List.findSome?_cons, hgx, hfb, ih]
      | some c => simp [List.filterMap_cons, List.findSome?_cons, hgx, hfb]

/-- `findSome?` of a function that is `some` at a unique member of the list. -/
private lemma findSome?_eq_some_of_unique {α β : Type _} {l : List α} {f : α → Option β}
    {a : α} {b : β} (hmem : a ∈ l) (hfa : f a = some b)
    (huniq : ∀ x ∈ l, x ≠ a → f x = none) :
    l.findSome? f = some b := by
  classical
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    rcases eq_or_ne x a with hxa | hxa
    · subst hxa
      simp [List.findSome?_cons, hfa]
    · have hxnone : f x = none := huniq x (List.mem_cons_self ..) hxa
      have hmem' : a ∈ xs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hxa
        · exact h
      simp only [List.findSome?_cons, hxnone]
      exact ih hmem' (fun y hy hya => huniq y (List.mem_cons_of_mem _ hy) hya)

/-! ## H23-1 — flat lookup is the structured projection -/

/-- **H23-1.** Looking up the encoded block for message index `j` in the flattened
`EncodedMessagesBefore.toList em` returns exactly the structured entry `em ⟨j, hj⟩`,
for every `j` with round before `k`. -/
lemma lookupEncodedMessageAlphaHat?_toList
    {k : Fin (n + 1)} (em : pSpec.EncodedMessagesBefore U k)
    (j : pSpec.MessageIdx) (hj : j.1.1 < k.1) :
    lookupEncodedMessageAlphaHat? (pSpec := pSpec) (U := U)
      (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) j
      = some (em ⟨j, hj⟩) := by
  classical
  unfold lookupEncodedMessageAlphaHat? EncodedMessagesBefore.toList
  rw [findSome?_filterMap]
  refine findSome?_eq_some_of_unique
    (Finset.mem_toList.mpr (Finset.mem_univ j)) ?_ ?_
  · simp only [dif_pos hj, Option.bind_some, dif_pos trivial]
  · intro x _ hxj
    by_cases hxlt : x.1.1 < k.1
    · simp only [dif_pos hxlt, Option.bind_some, dif_neg hxj]
    · simp only [dif_neg hxlt, Option.bind_none]

/-! ## `decodeMessagePhiInv?` success characterization -/

/-- `φ_j⁻¹` (brute-force preimage search) succeeds iff a serialize-preimage exists. -/
lemma decodeMessagePhiInv?_isSome_of_exists
    {msgIdx : pSpec.MessageIdx} {encoded : Vector U (messageSize msgIdx)}
    (h : ∃ m : pSpec.Message msgIdx, Serialize.serialize m = encoded) :
    (decodeMessagePhiInv? (pSpec := pSpec) (U := U) msgIdx encoded).isSome := by
  obtain ⟨m, hm⟩ := h
  unfold decodeMessagePhiInv?
  rw [List.find?_isSome]
  exact ⟨m, Finset.mem_toList.mpr (Finset.mem_univ m), by simp [hm]⟩

/-- A `φ_j⁻¹` witness re-serializes to the input block (the `List.find?` success property). -/
lemma decodeMessagePhiInv?_serialize
    {msgIdx : pSpec.MessageIdx} {encoded : Vector U (messageSize msgIdx)}
    {m : pSpec.Message msgIdx}
    (h : decodeMessagePhiInv? (pSpec := pSpec) (U := U) msgIdx encoded = some m) :
    Serialize.serialize m = encoded := by
  unfold decodeMessagePhiInv? at h
  have := List.find?_some h
  simpa using this

/-! ## Prefix-walk infrastructure

`decodeMessagesPrefixPhiInv?` is a `Fin.induction` walk; we expose it as `decodePrefixBuild`
with definitional step equations, plus a positional accessor `messagesUpToAt` for
`MessagesUpTo` prefixes with `concat`/`extend` computation rules.
-/

/-- Access the message at index `j` (with round `< k`) of a `MessagesUpTo k` prefix. -/
def messagesUpToAt {k : Fin (n + 1)} (mb : pSpec.MessagesUpTo k)
    (j : pSpec.MessageIdx) (hj : j.1.1 < k.1) : pSpec.Message j :=
  mb ⟨⟨j.1.1, hj⟩, j.2⟩

/-- `concat` does not disturb earlier message entries. -/
lemma messagesUpToAt_concat_of_lt {k : Fin n} (mb : pSpec.MessagesUpTo k.castSucc)
    (hdir : pSpec.dir k = .P_to_V) (msg : pSpec.Message ⟨k, hdir⟩)
    (j : pSpec.MessageIdx) (hj : j.1.1 < k.succ.1) (hlt : j.1.1 < k.1) :
    messagesUpToAt (MessagesUpTo.concat mb hdir msg) j hj = messagesUpToAt mb j hlt := by
  show Fin.dconcat
      (motive := fun i : Fin (k.1 + 1) =>
        pSpec.dir (i.castLE (by omega)) = .P_to_V → pSpec.«Type» (i.castLE (by omega)))
      (fun i hi => mb ⟨i, hi⟩) _ (Fin.castSucc ⟨j.1.1, hlt⟩) j.2 = _
  rw [Fin.dconcat_castSucc]
  rfl

/-- `concat` writes the new message at the last position. -/
lemma messagesUpToAt_concat_self {k : Fin n} (mb : pSpec.MessagesUpTo k.castSucc)
    (hdir : pSpec.dir k = .P_to_V) (msg : pSpec.Message ⟨k, hdir⟩)
    (hk : (⟨k, hdir⟩ : pSpec.MessageIdx).1.1 < k.succ.1) :
    messagesUpToAt (MessagesUpTo.concat mb hdir msg) ⟨k, hdir⟩ hk = msg := by
  show Fin.dconcat
      (motive := fun i : Fin (k.1 + 1) =>
        pSpec.dir (i.castLE (by omega)) = .P_to_V → pSpec.«Type» (i.castLE (by omega)))
      (fun i hi => mb ⟨i, hi⟩) _ (Fin.last k.1) hdir = _
  rw [Fin.dconcat_last]

/-- `extend` (challenge round) does not disturb message entries. -/
lemma messagesUpToAt_extend {k : Fin n} (mb : pSpec.MessagesUpTo k.castSucc)
    (hdir : pSpec.dir k = .V_to_P)
    (j : pSpec.MessageIdx) (hj : j.1.1 < k.succ.1) (hlt : j.1.1 < k.1) :
    messagesUpToAt (MessagesUpTo.extend mb hdir) j hj = messagesUpToAt mb j hlt := by
  show Fin.dconcat
      (motive := fun i : Fin (k.1 + 1) =>
        pSpec.dir (i.castLE (by omega)) = .P_to_V → pSpec.«Type» (i.castLE (by omega)))
      (fun i hi => mb ⟨i, hi⟩) _ (Fin.castSucc ⟨j.1.1, hlt⟩) j.2 = _
  rw [Fin.dconcat_castSucc]
  rfl

/-- A message index strictly before `k.succ` whose round is not the challenge round `k`
is strictly before `k`. -/
lemma messageIdx_lt_of_lt_succ_of_dir {k : Fin n} (j : pSpec.MessageIdx)
    (hj : j.1.1 < k.1 + 1) (hdir : pSpec.dir k = .V_to_P) : j.1.1 < k.1 := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
  · exact h
  · exfalso
    have hjk : j.1 = k := Fin.ext h
    have h2 := j.2
    rw [hjk, hdir] at h2
    simp at h2

/-- The `Fin.induction` walk underlying `decodeMessagesPrefixPhiInv?`, exposed with the
flattened encoded list as an explicit parameter. -/
def decodePrefixBuild
    (encodedList : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)))
    (k : Fin (n + 1)) : Option (pSpec.MessagesUpTo k) :=
  Fin.induction (some default)
    (fun j ih =>
      match ih with
      | none => none
      | some messages =>
          decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) encodedList j messages)
    k

@[simp]
lemma decodePrefixBuild_zero
    (encodedList : List (Sigma fun msgIdx : pSpec.MessageIdx =>
      Vector U (messageSize msgIdx))) :
    decodePrefixBuild (pSpec := pSpec) (U := U) encodedList 0 = some default := rfl

lemma decodePrefixBuild_succ
    (encodedList : List (Sigma fun msgIdx : pSpec.MessageIdx =>
      Vector U (messageSize msgIdx))) (j : Fin n) :
    decodePrefixBuild (pSpec := pSpec) (U := U) encodedList j.succ
      = match decodePrefixBuild (pSpec := pSpec) (U := U) encodedList j.castSucc with
        | none => none
        | some messages =>
            decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) encodedList j messages :=
  rfl

/-- `hybEncodedMessagesBefore?` is the walk applied to the flattened prefix. -/
lemma hybEncodedMessagesBefore?_eq_decodePrefixBuild
    (i : pSpec.ChallengeIdx) (em : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em
      = decodePrefixBuild (pSpec := pSpec) (U := U)
          (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) i.1.castSucc := rfl

/-- Step equation at a challenge round: extend the prefix, always succeeds. -/
lemma decodeMessagesPrefixStepPhiInv_vToP
    (encodedList : List (Sigma fun msgIdx : pSpec.MessageIdx =>
      Vector U (messageSize msgIdx)))
    (j : Fin n) (hdir : pSpec.dir j = .V_to_P) (mb : pSpec.MessagesUpTo j.castSucc) :
    decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) encodedList j mb
      = some (MessagesUpTo.extend mb hdir) := by
  unfold decodeMessagesPrefixStepPhiInv
  rw [dif_neg (by simp [hdir])]

/-- Step equation at a message round: look up the encoded block and apply `φ_j⁻¹`. -/
lemma decodeMessagesPrefixStepPhiInv_pToV
    (encodedList : List (Sigma fun msgIdx : pSpec.MessageIdx =>
      Vector U (messageSize msgIdx)))
    (j : Fin n) (hdir : pSpec.dir j = .P_to_V) (mb : pSpec.MessagesUpTo j.castSucc) :
    decodeMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) encodedList j mb
      = (lookupEncodedMessageAlphaHat? (pSpec := pSpec) (U := U)
            encodedList ⟨j, hdir⟩).bind fun encodedMsg =>
          (decodeMessagePhiInv? (pSpec := pSpec) (U := U) ⟨j, hdir⟩ encodedMsg).map
            fun msg => MessagesUpTo.concat mb hdir msg := by
  unfold decodeMessagesPrefixStepPhiInv
  rw [dif_pos hdir]
  cases lookupEncodedMessageAlphaHat? (pSpec := pSpec) (U := U) encodedList ⟨j, hdir⟩ with
  | none => simp
  | some encodedMsg =>
      simp only [Option.bind_some]
      cases decodeMessagePhiInv? (pSpec := pSpec) (U := U) ⟨j, hdir⟩ encodedMsg with
      | none => simp
      | some msg => simp

/-! ## H23-2 — the parser succeeds on codec-image inputs -/

/-- Walk-level success: if every encoded block before round `i` has a serialize-preimage,
the prefix walk succeeds up to every `k ≤ i`. -/
lemma decodePrefixBuild_isSome_of_inImage
    (i : pSpec.ChallengeIdx) (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (h : ∀ (j : pSpec.MessageIdx) (hj : j.1.1 < i.1.castSucc.1),
      ∃ m : pSpec.Message j, Serialize.serialize m = em ⟨j, hj⟩)
    (k : Fin (n + 1)) :
    k.1 ≤ i.1.castSucc.1 →
    (decodePrefixBuild (pSpec := pSpec) (U := U)
      (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) k).isSome := by
  induction k using Fin.induction with
  | zero => intro _; simp
  | succ j ih =>
    intro hk
    have hjle : (j.castSucc).1 ≤ i.1.castSucc.1 := by
      simp only [Fin.coe_castSucc, Fin.val_succ] at hk ⊢
      omega
    obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.mp (ih hjle)
    rw [decodePrefixBuild_succ, hmb]
    dsimp only
    cases hdir : pSpec.dir j with
    | V_to_P =>
        rw [decodeMessagesPrefixStepPhiInv_vToP (hdir := hdir)]
        rfl
    | P_to_V =>
        have hjlt : (⟨j, hdir⟩ : pSpec.MessageIdx).1.1 < i.1.castSucc.1 := by
          show j.1 < (i.1.castSucc).1
          simp only [Fin.val_succ] at hk
          omega
        rw [decodeMessagesPrefixStepPhiInv_pToV (hdir := hdir),
          lookupEncodedMessageAlphaHat?_toList em ⟨j, hdir⟩ hjlt]
        dsimp only
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
          (decodeMessagePhiInv?_isSome_of_exists (h ⟨j, hdir⟩ hjlt))
        simp only [Option.bind_some]
        rw [hm]
        simp

/-- **H23-2.** `hybEncodedMessagesBefore?` succeeds whenever every encoded block before the
round lies in the serialize-image. -/
lemma hybEncodedMessagesBefore?_isSome_of_inImage
    (i : pSpec.ChallengeIdx) (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (h : ∀ (j : pSpec.MessageIdx) (hj : j.1.1 < i.1.castSucc.1),
      ∃ m : pSpec.Message j, Serialize.serialize m = em ⟨j, hj⟩) :
    (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em).isSome := by
  rw [hybEncodedMessagesBefore?_eq_decodePrefixBuild]
  exact decodePrefixBuild_isSome_of_inImage i em h i.1.castSucc le_rfl

/-! ## Bool glue — the simulator's image guard -/

/-- The codec-image guard of the single `gᵢ` emitter (`d2sHandleBacktrackSome`) holds iff
every encoded block strictly before the round has a serialize-preimage. -/
lemma d2sInCodecImagePredicate_eq_true_iff
    [∀ i, DecidableEq (pSpec.Message i)]
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true ↔
      ∀ (j : pSpec.MessageIdx) (hj : j.1.1 < out.roundIdx.1.castSucc.1),
        ∃ m : pSpec.Message j, Serialize.serialize m = out.encodedMessages ⟨j, hj⟩ := by
  unfold d2sInCodecImagePredicate backtrackOutputMessagesInImage messageInSerializeImage
  rw [List.all_eq_true]
  constructor
  · intro hall j hj
    have hmem : j ∈ messageIdxListBefore (pSpec := pSpec) out.roundIdx := by
      unfold messageIdxListBefore
      rw [Finset.mem_toList, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hj⟩
    have := hall ⟨j, hmem⟩ (List.mem_attach _ _)
    rw [decide_eq_true_iff] at this
    exact this
  · intro h x _
    obtain ⟨j, hmem⟩ := x
    have hj : j.1.1 < out.roundIdx.1.castSucc.1 := by
      unfold messageIdxListBefore at hmem
      rw [Finset.mem_toList, Finset.mem_filter] at hmem
      exact hmem.2
    rw [decide_eq_true_iff]
    exact h j hj

/-- **H23-2 glue.** On any backtrack output passing the simulator's image guard, the `Hyb₃`
codec bridge's `φ⁻¹` parse (step 1 of `d2sCodecBridgeImpl`) succeeds — the bridge's abort
branch is dead code behind the guard. -/
lemma hybEncodedMessagesBefore?_isSome_of_d2sInCodecImagePredicate
    [∀ i, DecidableEq (pSpec.Message i)]
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hguard : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      out = true) :
    (hybEncodedMessagesBefore? (pSpec := pSpec) (U := U)
      out.roundIdx out.encodedMessages).isSome :=
  hybEncodedMessagesBefore?_isSome_of_inImage out.roundIdx out.encodedMessages
    ((d2sInCodecImagePredicate_eq_true_iff out).mp hguard)

/-! ## H23-3 — section property: decoded prefixes re-serialize to the input -/

/-- Walk-level section property: a successful prefix walk yields messages that re-serialize
to the corresponding encoded input blocks. -/
lemma decodePrefixBuild_serialize_eq
    (i : pSpec.ChallengeIdx) (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (k : Fin (n + 1)) :
    k.1 ≤ i.1.castSucc.1 →
    ∀ {mb : pSpec.MessagesUpTo k},
      decodePrefixBuild (pSpec := pSpec) (U := U)
        (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) k = some mb →
      ∀ (j : pSpec.MessageIdx) (hjk : j.1.1 < k.1) (hj : j.1.1 < i.1.castSucc.1),
        Serialize.serialize (messagesUpToAt mb j hjk) = em ⟨j, hj⟩ := by
  induction k using Fin.induction with
  | zero =>
    intro _ mb _ j hjk _
    exact absurd hjk (Nat.not_lt_zero _)
  | succ j₀ ih =>
    intro hk mb hbuild j hjk hj
    have hj₀le : (j₀.castSucc).1 ≤ i.1.castSucc.1 := by
      simp only [Fin.coe_castSucc, Fin.val_succ] at hk ⊢
      omega
    rw [decodePrefixBuild_succ] at hbuild
    cases hprev : decodePrefixBuild (pSpec := pSpec) (U := U)
        (EncodedMessagesBefore.toList (pSpec := pSpec) (U := U) em) j₀.castSucc with
    | none => rw [hprev] at hbuild; simp at hbuild
    | some mb₀ =>
      rw [hprev] at hbuild
      dsimp only at hbuild
      cases hdir : pSpec.dir j₀ with
      | V_to_P =>
        rw [decodeMessagesPrefixStepPhiInv_vToP (hdir := hdir)] at hbuild
        have hmb : mb = MessagesUpTo.extend mb₀ hdir := (Option.some.inj hbuild).symm
        subst hmb
        have hlt : j.1.1 < j₀.1 :=
          messageIdx_lt_of_lt_succ_of_dir j hjk hdir
        rw [messagesUpToAt_extend mb₀ hdir j hjk hlt]
        exact ih hj₀le hprev j hlt hj
      | P_to_V =>
        rw [decodeMessagesPrefixStepPhiInv_pToV (hdir := hdir)] at hbuild
        have hj₀lt : (⟨j₀, hdir⟩ : pSpec.MessageIdx).1.1 < i.1.castSucc.1 := by
          show j₀.1 < (i.1.castSucc).1
          simp only [Fin.val_succ] at hk
          omega
        rw [lookupEncodedMessageAlphaHat?_toList em ⟨j₀, hdir⟩ hj₀lt] at hbuild
        simp only [Option.bind_some] at hbuild
        cases hdec : decodeMessagePhiInv? (pSpec := pSpec) (U := U) ⟨j₀, hdir⟩
            (em ⟨⟨j₀, hdir⟩, hj₀lt⟩) with
        | none => rw [hdec] at hbuild; simp at hbuild
        | some msg =>
          rw [hdec] at hbuild
          simp only [Option.map_some] at hbuild
          have hmb : mb = MessagesUpTo.concat mb₀ hdir msg := (Option.some.inj hbuild).symm
          subst hmb
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hlt | heq
          · rw [messagesUpToAt_concat_of_lt mb₀ hdir msg j hjk hlt]
            exact ih hj₀le hprev j hlt hj
          · have hjeq : j = ⟨j₀, hdir⟩ := Subtype.ext (Fin.ext heq)
            subst hjeq
            rw [messagesUpToAt_concat_self mb₀ hdir msg hjk]
            exact decodeMessagePhiInv?_serialize hdec

/-- **H23-3.** On success of `hybEncodedMessagesBefore?`, every decoded message
re-serializes to the corresponding encoded input block:
`Serialize.serialize (mb.at j) = α̂_j`. -/
lemma hybEncodedMessagesBefore?_serialize_eq
    (i : pSpec.ChallengeIdx) {em : pSpec.EncodedMessagesBefore U i.1.castSucc}
    {mb : pSpec.MessagesUpTo i.1.castSucc}
    (h : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em = some mb)
    (j : pSpec.MessageIdx) (hj : j.1.1 < i.1.castSucc.1) :
    Serialize.serialize (messagesUpToAt mb j hj) = em ⟨j, hj⟩ := by
  rw [hybEncodedMessagesBefore?_eq_decodePrefixBuild] at h
  exact decodePrefixBuild_serialize_eq i em i.1.castSucc le_rfl h j hj hj

/-! ## H23-4 — `φ⁻¹` is injective on its success domain -/

/-- **H23-4.** Two encoded prefixes decoding (via `hybEncodedMessagesBefore?`) to the same
message prefix are equal. No `Codec` message-roundtrip law is needed: `φ⁻¹` is preimage
search, so both inputs equal the re-serialization of the common output. -/
lemma hybEncodedMessagesBefore?_injOn
    (i : pSpec.ChallengeIdx) {em em' : pSpec.EncodedMessagesBefore U i.1.castSucc}
    {mb : pSpec.MessagesUpTo i.1.castSucc}
    (h : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em = some mb)
    (h' : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em' = some mb) :
    em = em' := by
  funext jh
  obtain ⟨j, hj⟩ := jh
  rw [← hybEncodedMessagesBefore?_serialize_eq i h j hj,
    ← hybEncodedMessagesBefore?_serialize_eq i h' j hj]

/-! ## H23-4' — β-injectivity of the memo-key re-keying -/

section BetaKey

variable {Salt : Type} [SaltCodec U δ Salt]

/-- The `Hyb₂ → Hyb₃` key re-keying `β`: a `gSpec`/`eSpec`-style raw key
`(i, 𝕩, τ̂, α̂_{<i})` together with its decoded prefix `mb = φ⁻¹(α̂_{<i})` maps to the
salted FS-standard key `(i, ((𝕩, bin(τ̂)), α_{<i}))`. -/
def betaKey
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (mb : pSpec.MessagesUpTo q.1.1.castSucc) :
    (fsChallengeOracle (StmtIn × Salt) pSpec).Domain :=
  ⟨q.1, ((q.2.1, SaltCodec.encode (Salt := Salt) q.2.2.1), mb)⟩

/-- **H23-4'.** `β` is injective on decode-success keys: distinct `Hyb₂` memo keys map to
distinct `f`-table keys in the Claim 5.23 coupling. Uses `SaltCodec.encode_injective`
(class law, CO25 line 1729) for the salt component and H23-4 for the message component. -/
lemma betaKey_injOn
    {q q' : (gSpec (U := U) StmtIn pSpec δ).Domain}
    {mb : pSpec.MessagesUpTo q.1.1.castSucc} {mb' : pSpec.MessagesUpTo q'.1.1.castSucc}
    (hq : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) q.1 q.2.2.2 = some mb)
    (hq' : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) q'.1 q'.2.2.2 = some mb')
    (heq : betaKey (Salt := Salt) (StmtIn := StmtIn) q mb
      = betaKey (Salt := Salt) (StmtIn := StmtIn) q' mb') :
    q = q' := by
  obtain ⟨i, stmt, salt, em⟩ := q
  obtain ⟨i', stmt', salt', em'⟩ := q'
  obtain ⟨hi, h2⟩ := Sigma.mk.inj_iff.mp heq
  subst hi
  have h2' := eq_of_heq h2
  have h3 : (stmt, SaltCodec.encode (Salt := Salt) salt)
      = (stmt', SaltCodec.encode (Salt := Salt) salt') := congrArg Prod.fst h2'
  have h4 : mb = mb' := congrArg Prod.snd h2'
  have hstmt : stmt = stmt' := congrArg Prod.fst h3
  have hsalt : SaltCodec.encode (Salt := Salt) salt
      = SaltCodec.encode (Salt := Salt) salt' := congrArg Prod.snd h3
  subst hstmt
  have hsalt' : salt = salt' := SaltCodec.encode_injective hsalt
  subst hsalt'
  subst h4
  have hem : em = em' := hybEncodedMessagesBefore?_injOn i hq hq'
  subst hem
  rfl

end BetaKey

end

end DuplexSpongeFS.Hyb23Bricks

#print axioms DuplexSpongeFS.Hyb23Bricks.lookupEncodedMessageAlphaHat?_toList
#print axioms DuplexSpongeFS.Hyb23Bricks.decodeMessagePhiInv?_isSome_of_exists
#print axioms DuplexSpongeFS.Hyb23Bricks.decodeMessagePhiInv?_serialize
#print axioms DuplexSpongeFS.Hyb23Bricks.decodePrefixBuild_isSome_of_inImage
#print axioms DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore?_isSome_of_inImage
#print axioms DuplexSpongeFS.Hyb23Bricks.d2sInCodecImagePredicate_eq_true_iff
#print axioms
  DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore?_isSome_of_d2sInCodecImagePredicate
#print axioms DuplexSpongeFS.Hyb23Bricks.decodePrefixBuild_serialize_eq
#print axioms DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore?_serialize_eq
#print axioms DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore?_injOn
#print axioms DuplexSpongeFS.Hyb23Bricks.betaKey_injOn
