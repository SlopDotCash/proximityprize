/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BetaSetYoungDiagram
import ArkLib.Data.CodingTheory.ProximityGap.BorderStrip
import ArkLib.Data.CodingTheory.ProximityGap.OrderStatResort

/-!
# Rim-hook removal yields a border strip (#389)

The capstone of the geometric James–Kerber bridge: a single abacus bead-move (rim-`n`-hook
removal) `B → B'` produces a skew shape `YD(B) / YD(B')` that is a **border strip** — contained,
`2×2`-free, and connected. We prove the row-length handle on `youngDiagramOfBeta` and then the
border-strip properties.
-/

open YoungDiagram Finset
open ArkLib.ProximityGap.BetaSetYoungDiagram ArkLib.ProximityGap.RimHookArea
open ArkLib.ProximityGap.BorderStrip ArkLib.ProximityGap.OrderStatResort

namespace ArkLib.ProximityGap.RimHookBorderStrip

variable {B : Finset ℕ} {n : ℕ}

/-- The `i`-th row length of `youngDiagramOfBeta` is the `i`-th part from the top:
`β_{n-1-i} - (n-1-i)` (with `β` the increasing enumeration of `B`). -/
theorem rowLen_youngDiagramOfBeta (h : B.card = n) (i : ℕ) (hi : i < n) :
    (youngDiagramOfBeta h).rowLen i
      = B.orderEmbOfFin h (Fin.rev ⟨i, hi⟩) - (n - 1 - i) := by
  have hlen : (List.ofFn (fun j : Fin n =>
      B.orderEmbOfFin h (Fin.rev j) - ((Fin.rev j : Fin n) : ℕ))).length = n :=
    List.length_ofFn
  have key := rowLen_ofRowLens
    (w := List.ofFn (fun j : Fin n =>
      B.orderEmbOfFin h (Fin.rev j) - ((Fin.rev j : Fin n) : ℕ)))
    (hw := by
      rw [List.sortedGE_ofFn_iff]
      exact (parts_monotone h).comp_antitone Fin.rev_anti)
    ⟨i, by rw [hlen]; exact hi⟩
  rw [youngDiagramOfBeta, key]
  simp only [List.getElem_ofFn, Fin.val_rev, Fin.getElem_fin]
  congr 1
  omega

/-- `μ ≤ ν` for Young diagrams iff every row of `μ` is no longer than the corresponding row of
`ν`. (One direction is `BorderStrip.rowLen_le_of_le`; the converse is membership-by-row.) -/
theorem le_iff_rowLen (μ ν : YoungDiagram) : μ ≤ ν ↔ ∀ i, μ.rowLen i ≤ ν.rowLen i := by
  constructor
  · intro h i; exact rowLen_le_of_le h i
  · intro h
    intro c hc
    obtain ⟨i, j⟩ := c
    rw [mem_iff_lt_rowLen] at hc ⊢
    exact lt_of_lt_of_le hc (h i)

open ArkLib.ProximityGap.BetaSetYoungDiagram (orderEmbOfFin_le)

/-- Rows beyond the number of beads are empty. -/
theorem rowLen_youngDiagramOfBeta_zero (h : B.card = n) (i : ℕ) (hi : n ≤ i) :
    (youngDiagramOfBeta h).rowLen i = 0 := by
  by_contra hne
  have hpos : 0 < (youngDiagramOfBeta h).rowLen i := Nat.pos_of_ne_zero hne
  rw [← mem_iff_lt_rowLen, youngDiagramOfBeta, mem_ofRowLens] at hpos
  obtain ⟨hlt, _⟩ := hpos
  rw [List.length_ofFn] at hlt
  omega

/-- **Rim-hook removal yields a `2×2`-free skew shape (a ribbon).** A single abacus bead-move
`B → B'` produces `YD(B') ≤ YD(B)` with no `2×2` box. Together with
`youngDiagram_card_removeRimHook` (exactly `hsz` cells removed) this is the border-strip property
up to connectivity. -/
theorem youngDiagram_removeRimHook_le_no2x2 {B B' : Finset ℕ} {n hsz : ℕ}
    (hB : B.card = n) (hstep : RemovesRimHook B B' hsz) :
    youngDiagramOfBeta (show B'.card = n from (card_removeRimHook hstep).trans hB)
        ≤ youngDiagramOfBeta hB ∧
    ¬ Has2x2 (youngDiagramOfBeta (show B'.card = n from (card_removeRimHook hstep).trans hB))
        (youngDiagramOfBeta hB) := by
  have hB' : B'.card = n := (card_removeRimHook hstep).trans hB
  -- containment
  have hle : youngDiagramOfBeta hB' ≤ youngDiagramOfBeta hB := by
    rw [le_iff_rowLen]
    intro i
    rcases lt_or_ge i n with hi | hi
    · rw [rowLen_youngDiagramOfBeta hB' i hi, rowLen_youngDiagramOfBeta hB i hi]
      have hmono := orderEmbOfFin_le_of_removeRimHook hstep hB hB' (Fin.rev ⟨i, hi⟩)
      omega
    · rw [rowLen_youngDiagramOfBeta_zero hB' i hi]; exact Nat.zero_le _
  refine ⟨hle, ?_⟩
  rw [no2x2_iff_rowLen hle]
  intro i
  rcases lt_or_ge (i + 1) n with hi1 | hi1
  · have hi : i < n := by omega
    rw [rowLen_youngDiagramOfBeta hB (i + 1) hi1, rowLen_youngDiagramOfBeta hB' i hi]
    -- key interleaving β_{n-2-i} ≤ β'_{n-1-i}, transported to the Fin.rev indices
    have hpred := orderEmbOfFin_pred_le hstep hB hB' (n - 1 - (i + 1)) (by omega)
    have hcongrB : B.orderEmbOfFin hB ⟨n - 1 - (i + 1), by omega⟩
        = B.orderEmbOfFin hB (Fin.rev ⟨i + 1, hi1⟩) :=
      congrArg (B.orderEmbOfFin hB) (by apply Fin.ext; simp only [Fin.val_rev]; omega)
    have hcongrB' : B'.orderEmbOfFin hB' ⟨(n - 1 - (i + 1)) + 1, by omega⟩
        = B'.orderEmbOfFin hB' (Fin.rev ⟨i, hi⟩) :=
      congrArg (B'.orderEmbOfFin hB') (by apply Fin.ext; simp only [Fin.val_rev]; omega)
    rw [hcongrB, hcongrB'] at hpred
    have hlowB : (n - 1 - (i + 1)) ≤ B.orderEmbOfFin hB (Fin.rev ⟨i + 1, hi1⟩) := by
      have hx := orderEmbOfFin_le hB (n - 1 - (i + 1)) (by omega)
      rw [hcongrB] at hx; exact hx
    have hlowB' : (n - 1 - i) ≤ B'.orderEmbOfFin hB' (Fin.rev ⟨i, hi⟩) := by
      have hx := orderEmbOfFin_le hB' (n - 1 - i) (by omega)
      have he : B'.orderEmbOfFin hB' ⟨n - 1 - i, by omega⟩
          = B'.orderEmbOfFin hB' (Fin.rev ⟨i, hi⟩) :=
        congrArg (B'.orderEmbOfFin hB') (by apply Fin.ext; simp only [Fin.val_rev]; omega)
      rw [he] at hx; exact hx
    omega
  · rw [rowLen_youngDiagramOfBeta_zero hB (i + 1) hi1]; exact Nat.zero_le _

/-- A skew shape `ν/μ` is a **border strip** (rim hook): contained, nonempty, `2×2`-free, and
connected (consecutive occupied rows overlap in exactly one column — the ladder). -/
def IsBorderStrip (μ ν : YoungDiagram) : Prop :=
  μ ≤ ν ∧ μ ≠ ν ∧ (¬ Has2x2 μ ν) ∧
    ∀ i, μ.rowLen i < ν.rowLen i → μ.rowLen (i + 1) < ν.rowLen (i + 1) →
      ν.rowLen (i + 1) = μ.rowLen i + 1

/-- **The full geometric James–Kerber theorem.** A single abacus rim-hook removal `B → B'` produces
a genuine border strip `YD(B') / YD(B)`: contained, nonempty, `2×2`-free, and connected. -/
theorem youngDiagram_removeRimHook_isBorderStrip {B B' : Finset ℕ} {n hsz : ℕ}
    (hB : B.card = n) (hstep : RemovesRimHook B B' hsz)
    (hne : youngDiagramOfBeta (show B'.card = n from (card_removeRimHook hstep).trans hB)
        ≠ youngDiagramOfBeta hB) :
    IsBorderStrip (youngDiagramOfBeta (show B'.card = n from (card_removeRimHook hstep).trans hB))
        (youngDiagramOfBeta hB) := by
  have hB' : B'.card = n := (card_removeRimHook hstep).trans hB
  obtain ⟨hle, hno2⟩ := youngDiagram_removeRimHook_le_no2x2 hB hstep
  refine ⟨hle, hne, hno2, ?_⟩
  intro i hocci hocci1
  have hi1 : i + 1 < n := by
    by_contra hcon; push Not at hcon
    rw [rowLen_youngDiagramOfBeta_zero hB' (i + 1) (by omega),
      rowLen_youngDiagramOfBeta_zero hB (i + 1) (by omega)] at hocci1
    omega
  have hi : i < n := by omega
  -- value-equality: order stat at Fin.rev = order stat at explicit reversed index
  have cv : ∀ (s : Finset ℕ) (hs : s.card = n) (a b : ℕ) (ha : a < n) (hb : b < n),
      (Fin.rev ⟨a, ha⟩ : Fin n).val = b →
      s.orderEmbOfFin hs (Fin.rev ⟨a, ha⟩) = s.orderEmbOfFin hs ⟨b, hb⟩ :=
    fun s hs a b ha hb hval => congrArg _ (Fin.ext hval)
  -- rewrite goal + hyps to explicit indices n-1-i and n-1-(i+1)
  rw [rowLen_youngDiagramOfBeta hB (i + 1) hi1, rowLen_youngDiagramOfBeta hB' i hi,
    cv B hB (i + 1) (n - 1 - (i + 1)) hi1 (by omega) (by simp only [Fin.val_rev]; omega),
    cv B' hB' i (n - 1 - i) hi (by omega) (by simp only [Fin.val_rev]; omega)]
  rw [rowLen_youngDiagramOfBeta hB' i hi, rowLen_youngDiagramOfBeta hB i hi,
    cv B' hB' i (n - 1 - i) hi (by omega) (by simp only [Fin.val_rev]; omega),
    cv B hB i (n - 1 - i) hi (by omega) (by simp only [Fin.val_rev]; omega)] at hocci
  rw [rowLen_youngDiagramOfBeta hB' (i + 1) hi1, rowLen_youngDiagramOfBeta hB (i + 1) hi1,
    cv B' hB' (i + 1) (n - 1 - (i + 1)) hi1 (by omega) (by simp only [Fin.val_rev]; omega),
    cv B hB (i + 1) (n - 1 - (i + 1)) hi1 (by omega) (by simp only [Fin.val_rev]; omega)] at hocci1
  -- lower bounds
  have lb1 : n - 1 - i ≤ B'.orderEmbOfFin hB' ⟨n - 1 - i, by omega⟩ := orderEmbOfFin_le hB' _ (by omega)
  have lb2 : n - 1 - i ≤ B.orderEmbOfFin hB ⟨n - 1 - i, by omega⟩ := orderEmbOfFin_le hB _ (by omega)
  have lb3 : n - 1 - (i+1) ≤ B'.orderEmbOfFin hB' ⟨n - 1 - (i+1), by omega⟩ := orderEmbOfFin_le hB' _ (by omega)
  have lb4 : n - 1 - (i+1) ≤ B.orderEmbOfFin hB ⟨n - 1 - (i+1), by omega⟩ := orderEmbOfFin_le hB _ (by omega)
  -- apply the ladder at k = ⟨n-1-i⟩
  have hk1 : 1 ≤ (⟨n - 1 - i, by omega⟩ : Fin n).val := by simp only [Fin.val_mk]; omega
  have hock : B'.orderEmbOfFin hB' ⟨n - 1 - i, by omega⟩ < B.orderEmbOfFin hB ⟨n - 1 - i, by omega⟩ := by
    omega
  have hveB' : B'.orderEmbOfFin hB' ⟨(⟨n - 1 - i, by omega⟩ : Fin n).val - 1, by omega⟩
      = B'.orderEmbOfFin hB' ⟨n - 1 - (i + 1), by omega⟩ :=
    congrArg _ (Fin.ext (by simp only [Fin.val_mk]; omega))
  have hveB : B.orderEmbOfFin hB ⟨(⟨n - 1 - i, by omega⟩ : Fin n).val - 1, by omega⟩
      = B.orderEmbOfFin hB ⟨n - 1 - (i + 1), by omega⟩ :=
    congrArg _ (Fin.ext (by simp only [Fin.val_mk]; omega))
  have hock1 : B'.orderEmbOfFin hB' ⟨(⟨n - 1 - i, by omega⟩ : Fin n).val - 1, by omega⟩
      < B.orderEmbOfFin hB ⟨(⟨n - 1 - i, by omega⟩ : Fin n).val - 1, by omega⟩ := by
    rw [hveB', hveB]; omega
  have hlad := orderEmbOfFin_ladder hstep hB hB'
    ⟨n - 1 - i, by omega⟩ hk1 hock hock1
  rw [hveB] at hlad
  omega

end ArkLib.ProximityGap.RimHookBorderStrip
