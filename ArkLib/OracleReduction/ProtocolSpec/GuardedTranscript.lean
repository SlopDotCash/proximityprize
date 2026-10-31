/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.OracleReduction.ProtocolSpec.TranscriptRecompose

/-!
# Explicit-round projections of composed partial transcripts

Adapted from ArkLib reviewed head `9b0b5c962d97a9a0a9388c0bcc7e70d503e9ddd9`.
These projections and heterogeneous equality lemmas support guarded composition
without replacing the native extractor or its transcript representation.
-/

set_option autoImplicit false
open ProtocolSpec

namespace ProtocolSpec
variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The appended round type agrees with the left protocol before the seam. -/
theorem append_Type_castAdd (k : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n k) = pSpec₁.«Type» k := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.castAdd n k) = pSpec₁.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_left]
end ProtocolSpec

namespace ProtocolSpec.Transcript
variable {n : ℕ} {pSpec : ProtocolSpec n}
/-- Below the last round, `Transcript.concat` agrees with the transcript it extends.
`ℕ`-indexed, `HEq`-valued form of `concat_castSucc`. -/
lemma concat_apply_lt {m : Fin n} (T : Transcript m.castSucc pSpec) (msg : pSpec.«Type» m)
    (i : ℕ) (hi : i < m.val) (hi' : i < (m.succ : Fin (n + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) (T ⟨i, hi⟩) := by
  unfold concat Fin.snoc
  rw [dite_eq_left hi]
  exact cast_heq _ _

/-- At the last round, `Transcript.concat` returns the newly appended message.
`ℕ`-indexed, `HEq`-valued form of `concat_last`. -/
lemma concat_apply_last {m : Fin n} (T : Transcript m.castSucc pSpec) (msg : pSpec.«Type» m)
    (i : ℕ) (him : i = m.val) (hi' : i < (m.succ : Fin (n + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) msg := by
  subst him
  unfold concat Fin.snoc
  rw [dite_eq_right (Nat.lt_irrefl m.val)]
  exact cast_heq _ _

/-- **Extensionality for partial transcripts at propositionally equal rounds.** Two partial
transcripts whose rounds have equal values are heterogeneously equal when they agree entrywise at
every raw `ℕ` index. Companion of `concat_apply_lt` / `concat_apply_last`: composition proofs
compare transcripts at rounds such as `min k m` or `k - m` that are only propositionally equal. -/
theorem heq_ext {k k' : Fin (n + 1)} {T : Transcript k pSpec} {T' : Transcript k' pSpec}
    (hk : k.val = k'.val)
    (h : ∀ (i : ℕ) (hi : i < k.val) (hi' : i < k'.val), HEq (T ⟨i, hi⟩) (T' ⟨i, hi'⟩)) :
    HEq T T' := by
  obtain rfl : k = k' := Fin.ext hk
  exact heq_of_eq (funext fun i => eq_of_heq (h i.val i.isLt i.isLt))


end ProtocolSpec.Transcript

namespace ProtocolSpec.Transcript

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} {k : Fin (m + n + 1)}

/-- The first `j` rounds of a partial transcript of an appended protocol, as a partial transcript
of the first protocol, for any `j` not exceeding the rounds already played. Unlike
`Transcript.fst`, which stops at the round `min k m` fixed by `k`, the target round is explicit, so
statements can name it directly (`fst_eq_fstUpTo`). -/
def fstUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (j : Fin (m + 1)) (hj : j.val ≤ k.val) :
    pSpec₁.Transcript j :=
  fun i => _root_.cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨i.val, by have := i.isLt; omega⟩) (T ⟨i.val, by have := i.isLt; omega⟩)

/-- The first `j` rounds of the second protocol's part of a partial transcript of an appended
protocol, for any `j` such that those rounds have already been played. Unlike `Transcript.snd`,
which stops at the round `k - m`, the target round is explicit (`snd_eq_sndUpTo`). -/
def sndUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (j : Fin (n + 1)) (hj : m + j.val ≤ k.val) :
    pSpec₂.Transcript j :=
  fun i => _root_.cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨i.val, by have := i.isLt; omega⟩) (T ⟨m + i.val, by have := i.isLt; omega⟩)

/-- `Transcript.fst`, which stops at round `min k m`, is `fstUpTo` at that round. -/
theorem fst_eq_fstUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) :
    T.fst = T.fstUpTo ⟨min k.val m, by omega⟩ (min_le_left _ _) := rfl

/-- At or after the seam, `Transcript.snd`, which stops at round `k - m`, is `sndUpTo` at that
round. Before the seam `snd` is empty, while `sndUpTo` is not defined. -/
theorem snd_eq_sndUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (hk : m ≤ k.val) :
    T.snd = T.sndUpTo ⟨k.val - m, by omega⟩ (by simp; omega) := by
  funext i
  have hlt : m < k.val := by have := i.isLt; simp only [Fin.val_mk] at this; omega
  simp only [snd, dite_eq_right (Nat.not_le.mpr hlt), sndUpTo]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- Appending a message does not change rounds that were already played. -/
theorem fstUpTo_concat_of_le {j : Fin (m + n)} (T : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» j) (J : Fin (m + 1)) (hJ : J.val ≤ j.val) :
    (T.concat msg).fstUpTo J (by simp; omega) = T.fstUpTo J hJ := by
  funext i
  have := i.isLt
  exact eq_of_heq ((cast_heq _ _).trans ((Transcript.concat_apply_lt T msg i.val
    (by omega) _).trans (cast_heq _ _).symm))

/-- Appending a message in the first protocol extends the first protocol's transcript by it. -/
theorem fstUpTo_concat_castAdd (j : Fin m)
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castAdd n j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n j)) :
    (T.concat msg).fstUpTo j.succ (by simp) =
      (T.fstUpTo j.castSucc (by simp)).concat (_root_.cast (append_Type_castAdd j) msg) := by
  funext i
  have hi : i.val < j.val + 1 := i.isLt
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  rcases Nat.lt_or_ge i.val j.val with hij | hij
  · exact (Transcript.concat_apply_lt T msg i.val (by simpa using hij) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_lt (T.fstUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_castAdd j) msg) i.val hij i.isLt).symm)
  · exact (Transcript.concat_apply_last T msg i.val (by simp; omega) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_last (T.fstUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_castAdd j) msg) i.val (by omega) i.isLt).symm)

/-- Appending a message does not change the second protocol's rounds that were already played. -/
theorem sndUpTo_concat_of_le {j : Fin (m + n)} (T : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» j) (J : Fin (n + 1)) (hJ : m + J.val ≤ j.val) :
    (T.concat msg).sndUpTo J (by simp; omega) = T.sndUpTo J hJ := by
  funext i
  have := i.isLt
  exact eq_of_heq ((cast_heq _ _).trans ((Transcript.concat_apply_lt T msg (m + i.val)
    (by omega) _).trans (cast_heq _ _).symm))

/-- Appending a message in the second protocol extends the second protocol's transcript by it. -/
theorem sndUpTo_concat_natAdd (j : Fin n)
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m j)) :
    (T.concat msg).sndUpTo j.succ (by simp; omega) =
      (T.sndUpTo j.castSucc (by simp)).concat (_root_.cast (append_Type_natAdd j) msg) := by
  funext i
  have hi : i.val < j.val + 1 := i.isLt
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  rcases Nat.lt_or_ge i.val j.val with hij | hij
  · exact (Transcript.concat_apply_lt T msg (m + i.val) (by simp; omega) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_lt (T.sndUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_natAdd j) msg) i.val hij i.isLt).symm)
  · exact (Transcript.concat_apply_last T msg (m + i.val) (by simp; omega) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_last (T.sndUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_natAdd j) msg) i.val (by omega) i.isLt).symm)

/-- On a full transcript, the whole first-protocol part is `FullTranscript.fst`. -/
theorem fstUpTo_last (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    Transcript.fstUpTo (k := Fin.last (m + n)) T (Fin.last m) (by simp) = T.fst := by
  funext i
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  unfold FullTranscript.fst
  exact (cast_heq _ _).symm

/-- On a full transcript, the whole second-protocol part is `FullTranscript.snd`. -/
theorem sndUpTo_last (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    Transcript.sndUpTo (k := Fin.last (m + n)) T (Fin.last n) (by simp) = T.snd := by
  funext i
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  unfold FullTranscript.snd
  exact (cast_heq _ _).symm

end ProtocolSpec.Transcript
