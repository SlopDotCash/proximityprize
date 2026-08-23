/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma512Honest

/-!
# #316 — Duplex-Sponge Fiat-Shamir: the hash half of the M2c honest timing residual
(CO25 Lemma 5.16, `E_{time,h}` side: `¬E(tr) → ¬E_time_h_honest(tr, s, S)`).

`Lemma512Honest.lean` already produces, off `E`, a **raw-trace** witness of the
out-of-order-hash event: a hash anchor that is the *first occurrence* of its hash entry,
preceded by a forward permutation entry sharing the hash capacity
(`e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E`). This file closes
the remaining dedup-collision step:

1. `HasFirstHashFwdCapNat` — an index-arithmetic-friendly (ℕ-indexed, `getElem?`-based)
   restatement of `HasFirstHashForwardCapacityBeforeHash`.
2. `hasFirstHashFwdCapNat_eraseIdx` — **one-step preservation**: erasing one redundant
   entry preserves the shape. The hash anchor is never the erased slot (a first-occurrence
   hash slot is not redundant, `not_redundantEntryDS_hash_of_no_prior`); if the forward
   witness is erased, its redundancy certificate (`redundant_forward_capacity_prior`) is an
   *earlier* forward entry still touching the capacity; otherwise both survive with
   order-preserving index shifts.
3. `hasFirstHashFwdCapNat_removeRedundant` — fixpoint preservation through
   `removeRedundantEntryDS` (strong induction on trace length).
4. `lemma5_16_honest_hash_half` — assembly: off `E`, the honest out-of-order-hash event
   `E_time_h_honest` is absent (its dedup'd collision shape would fire
   `capacitySegmentDupHash`, i.e. `E`, via `E_of_base_hasForwardCapacityBeforeHash`).

**Scope note (honesty)**: this is the `E_{time,h}` *half* of the in-tree
`Lemma5_16HonestFalseAsStated` only. The `E_{time,p}` half (out-of-order *permutation*
queries) is NOT proven here, and appears to be **false as currently stated**: the in-tree
`redundantEntryDS` treats a forward entry `(p, x, y)` as redundant given an earlier
*same-direction swapped* entry `(p, y, x)` (CO25 Def. 5.5 instead uses the
*opposite-direction* entry `(p⁻¹, y, x)`), which lets a backtrack chain alternate across a
single surviving permutation entry and realize an out-of-order permutation pair while the
dedup'd trace carries only query-side capacity touches — firing none of the
`capacitySegmentDup*` anchors. Statement repair of `redundantEntryDS` (one token:
`.inl ↦ .inr` in the swapped certificate) is the prerequisite for the full Lemma 5.16.
-/

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

namespace DuplexSpongeFS.Sponge316

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- ℕ-indexed, `getElem?`-based restatement of `HasFirstHashForwardCapacityBeforeHash`:
a first-occurrence hash anchor at `jh`, preceded (`jp < jh`) by a forward permutation entry
touching the hash capacity on either state side. -/
def HasFirstHashFwdCapNat (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) : Prop :=
  ∃ jh jp : ℕ, jp < jh ∧
    tr[jh]? = some (⟨Sum.inl stmt, capSeg⟩ :
      OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
    (∀ k, k < jh → tr[k]? ≠ some (⟨Sum.inl stmt, capSeg⟩ :
      OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) ∧
    ∃ sIn sOut : CanonicalSpongeState U,
      tr[jp]? = some (⟨Sum.inr (Sum.inl sIn), sOut⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      (sOut.capacitySegment = capSeg ∨ sIn.capacitySegment = capSeg)

/-- The `Fin`-indexed first-occurrence shape implies the ℕ-indexed one. -/
lemma hasFirstHashFwdCapNat_of_first
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashForwardCapacityBeforeHash tr stmt capSeg) :
    HasFirstHashFwdCapNat tr stmt capSeg := by
  obtain ⟨jHash, hhash, hfirst, jPerm, hlt, sIn, sOut, hperm, hcap⟩ := h
  refine ⟨jHash.val, jPerm.val, hlt, ?_, ?_, sIn, sOut, ?_, hcap⟩
  · rw [List.getElem?_eq_getElem jHash.isLt]
    exact congrArg some hhash
  · intro k hk hbad
    have hklt : k < tr.length := lt_trans hk jHash.isLt
    rw [List.getElem?_eq_getElem hklt] at hbad
    exact hfirst ⟨k, hklt⟩ hk (Option.some.inj hbad)
  · rw [List.getElem?_eq_getElem jPerm.isLt]
    exact congrArg some hperm

/-- The ℕ-indexed shape implies the plain (`Fin`-indexed, no firstness) collision shape. -/
lemma hasForwardCapacityBeforeHash_of_nat
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashFwdCapNat tr stmt capSeg) :
    HasForwardCapacityBeforeHash tr stmt capSeg := by
  obtain ⟨jh, jp, hlt, hhash, _hfirst, sIn, sOut, hperm, hcap⟩ := h
  obtain ⟨hjh_lt, hjh⟩ := List.getElem?_eq_some_iff.mp hhash
  obtain ⟨hjp_lt, hjp⟩ := List.getElem?_eq_some_iff.mp hperm
  exact ⟨⟨jh, hjh_lt⟩, hjh, ⟨jp, hjp_lt⟩, hlt, sIn, sOut, hjp, hcap⟩

/-- **One-step preservation**: erasing one redundant entry preserves
`HasFirstHashFwdCapNat`. -/
lemma hasFirstHashFwdCapNat_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDS idx)
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashFwdCapNat tr stmt capSeg) :
    HasFirstHashFwdCapNat (tr.eraseIdx idx.val) stmt capSeg := by
  classical
  obtain ⟨jh, jp, hlt, hhash, hfirst, sIn, sOut, hperm, hcap⟩ := h
  obtain ⟨hjh_lt, hjh⟩ := List.getElem?_eq_some_iff.mp hhash
  -- the erased slot is never the (first-occurrence) hash anchor
  have hjh_ne : idx.val ≠ jh := by
    intro hcontr
    refine not_redundantEntryDS_hash_of_no_prior tr idx (stmt := stmt) (capSeg := capSeg)
      ?_ ?_ hred
    · simpa [hcontr] using hjh
    · intro j hj hbad
      have : tr[j.val]? = some (⟨Sum.inl stmt, capSeg⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
        rw [List.getElem?_eq_getElem j.isLt]
        exact congrArg some hbad
      exact hfirst j.val (by omega) this
  -- the new firstness proof is shared across all cases (for the shifted hash index)
  have hfirst' : ∀ jh' : ℕ, (idx.val < jh → jh' = jh - 1) → (jh < idx.val → jh' = jh) →
      ∀ k, k < jh' → (tr.eraseIdx idx.val)[k]? ≠ some (⟨Sum.inl stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    intro jh' hgt hlt' k hk hbad
    rcases Nat.lt_or_ge k idx.val with hki | hki
    · rw [List.getElem?_eraseIdx_of_lt hki] at hbad
      refine hfirst k ?_ hbad
      rcases Nat.lt_or_ge idx.val jh with h1 | h1
      · have := hgt h1; omega
      · have h2 : jh < idx.val := lt_of_le_of_ne h1 (Ne.symm hjh_ne)
        have := hlt' h2; omega
    · rw [List.getElem?_eraseIdx_of_ge hki] at hbad
      refine hfirst (k + 1) ?_ hbad
      rcases Nat.lt_or_ge idx.val jh with h1 | h1
      · have := hgt h1; omega
      · have h2 : jh < idx.val := lt_of_le_of_ne h1 (Ne.symm hjh_ne)
        have := hlt' h2; omega
  by_cases hjp : jp = idx.val
  · -- erased the forward witness: its redundancy certificate is an earlier forward
    -- entry still touching the capacity
    have hidx_lt_jh : idx.val < jh := by omega
    have hidxval : tr[idx] =
        (⟨Sum.inr (Sum.inl sIn), sOut⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
      have : tr[idx.val]? = some (⟨Sum.inr (Sum.inl sIn), sOut⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
        rw [← hjp]; exact hperm
      rw [List.getElem?_eq_getElem idx.isLt] at this
      exact Option.some.inj this
    obtain ⟨j', hj'lt, sIn', sOut', hj'e, hcap'⟩ :=
      redundant_forward_capacity_prior tr idx (capSeg := capSeg) hidxval hred hcap
    have hj'idx : j'.val < idx.val := hj'lt
    refine ⟨jh - 1, j'.val, by omega, ?_,
      hfirst' (jh - 1) (fun _ => rfl) (fun hc => absurd hc (by omega)),
      sIn', sOut', ?_, hcap'⟩
    · rw [List.getElem?_eraseIdx_of_ge (by omega : idx.val ≤ jh - 1),
        show jh - 1 + 1 = jh by omega]
      exact hhash
    · rw [List.getElem?_eraseIdx_of_lt hj'idx, List.getElem?_eq_getElem j'.isLt]
      exact congrArg some hj'e
  · -- both witnesses survive, with order-preserving index shifts
    by_cases hjhi : jh < idx.val
    · -- everything strictly below the erased slot: indices unchanged
      refine ⟨jh, jp, hlt, ?_, hfirst' jh (fun hc => absurd hc (by omega)) (fun _ => rfl),
        sIn, sOut, ?_, hcap⟩
      · rw [List.getElem?_eraseIdx_of_lt hjhi]; exact hhash
      · rw [List.getElem?_eraseIdx_of_lt (by omega : jp < idx.val)]; exact hperm
    · have hidx_lt_jh : idx.val < jh := by
        rcases Nat.lt_or_ge idx.val jh with h1 | h1
        · exact h1
        · exact absurd (lt_of_le_of_ne h1 (Ne.symm hjh_ne)) hjhi
      by_cases hjpi : jp < idx.val
      · -- perm below, hash above the erased slot
        refine ⟨jh - 1, jp, by omega, ?_,
          hfirst' (jh - 1) (fun _ => rfl) (fun hc => absurd hc (by omega)),
          sIn, sOut, ?_, hcap⟩
        · rw [List.getElem?_eraseIdx_of_ge (by omega : idx.val ≤ jh - 1),
            show jh - 1 + 1 = jh by omega]
          exact hhash
        · rw [List.getElem?_eraseIdx_of_lt hjpi]; exact hperm
      · -- both above the erased slot
        have hidx_lt_jp : idx.val < jp :=
          lt_of_le_of_ne (Nat.le_of_not_lt hjpi) (fun hcontr => hjp hcontr.symm)
        refine ⟨jh - 1, jp - 1, by omega, ?_,
          hfirst' (jh - 1) (fun _ => rfl) (fun hc => absurd hc (by omega)),
          sIn, sOut, ?_, hcap⟩
        · rw [List.getElem?_eraseIdx_of_ge (by omega : idx.val ≤ jh - 1),
            show jh - 1 + 1 = jh by omega]
          exact hhash
        · rw [List.getElem?_eraseIdx_of_ge (by omega : idx.val ≤ jp - 1),
            show jp - 1 + 1 = jp by omega]
          exact hperm

/-- **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves
`HasFirstHashFwdCapNat` (strong induction on the trace length). -/
lemma hasFirstHashFwdCapNat_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      ∀ {stmt : StmtIn} {capSeg : Vector U SpongeSize.C},
        HasFirstHashFwdCapNat tr stmt capSeg →
        HasFirstHashFwdCapNat (removeRedundantEntryDS tr).1 stmt capSeg := by
  intro N
  induction N with
  | zero =>
      intro tr hlen stmt capSeg hP
      obtain ⟨jh, jp, _, hhash, _⟩ := hP
      obtain ⟨hjh_lt, _⟩ := List.getElem?_eq_some_iff.mp hhash
      omega
  | succ N ih =>
      intro tr hlen stmt capSeg hP
      rw [removeRedundantEntryDS]
      split
      · rename_i hex
        refine ih _ ?_ (hasFirstHashFwdCapNat_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hP

/-- Raw first-occurrence collision shape fires the combined bad event `E`: transport the
shape through dedup, forget firstness, and apply the `capacitySegmentDupHash` constructor. -/
theorem E_of_hasFirstHashForwardCapacityBeforeHash
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashForwardCapacityBeforeHash tr stmt capSeg) :
    BadEventDS.E tr :=
  E_of_base_hasForwardCapacityBeforeHash tr
    (hasForwardCapacityBeforeHash_of_nat _
      (hasFirstHashFwdCapNat_removeRedundant tr.length tr le_rfl
        (hasFirstHashFwdCapNat_of_first tr h)))

/-- **M2c, hash half** — CO25 Lemma 5.16, `E_{time,h}` side: off the combined bad event
`E`, no backtrack payload's anchoring hash query appears after its first chain permutation
query. (The `E_{time,p}` side of `Lemma5_16HonestFalseAsStated` is *not* covered; see the
module docstring.) -/
theorem lemma5_16_honest_hash_half
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hE : ¬ BadEventDS.E tr) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S := by
  intro hTime
  obtain ⟨stmt, capSeg, hshape⟩ :=
    e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E
      (tr := tr) hE (state := state) (S := S) hTime
  exact hE (E_of_hasFirstHashForwardCapacityBeforeHash tr hshape)

end DuplexSpongeFS.Sponge316

#print axioms DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_eraseIdx
#print axioms DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_removeRedundant
#print axioms DuplexSpongeFS.Sponge316.E_of_hasFirstHashForwardCapacityBeforeHash
#print axioms DuplexSpongeFS.Sponge316.lemma5_16_honest_hash_half
