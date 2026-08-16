/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

/-!
# Issue #232 — the folding-transfer NO-GO (§6 route 4, blocked in the naive direction)

The issue's §6 lists "subspace-design / folded-RS transfer" as a viable research route: folded RS
achieves list-decoding capacity (CZ25/Guruswami–Rudra, with alphabet blow-up), and the smooth
`2^m`-domain folds naturally along its subgroup ⟨ω⟩ (orbits `{x, ωx, …}`).  Could a capacity bound
for the FOLDED code transfer to the plain smooth-domain RS list?

**This file machine-checks why the naive transfer is blocked.**  Model the folded structure
abstractly: coordinates `Fin N × Fin (d+1)` (`N` orbits of size `d+1`), folding by the first
coordinate.

* `foldedAgree_mul_le_plainAgree` — the only direction that holds: each fully-agreeing orbit
  contributes `d+1` plain agreements, so `(d+1) · foldedAgree ≤ plainAgree`.  (A plain-list bound
  therefore transfers UP to the folded code — the useless direction.)
* `folding_transfer_no_go` (the NO-GO) — the converse fails **maximally**: over any type with
  `0 ≠ 1` there is a word `w` with `plainAgree w 0 = N·d` — a `d/(d+1)` fraction of ALL coordinates,
  far above any list-decoding radius — while `foldedAgree w 0 = 0`: **not a single orbit agrees**.
  Witness: `w(o, p) = 1` if `p = 0` else `0` (one corrupted position per orbit).

Consequence: a folded-code list bound at ANY radius (even capacity) says nothing about the plain
list even at relative radius `1/(d+1)` — the agreement structure simply does not transfer downward.
The folded-RS capacity results bound lists of words close IN THE FOLDED METRIC, a strictly smaller
set than plain-close words.  Closing this gap (a transfer that survives per-orbit corruption) is
precisely the open part of §6 route 4 — now isolated as such, with the naive route a
theorem-certified dead end.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset

namespace ArkLib.CodingTheory.FoldingTransferNoGo

variable {F : Type*} [DecidableEq F] {N d : ℕ}

/-- Plain (unfolded) agreement count between two words on the orbit-structured domain. -/
def plainAgree (w v : Fin N × Fin (d + 1) → F) : ℕ :=
  (Finset.univ.filter fun x : Fin N × Fin (d + 1) => w x = v x).card

/-- Folded agreement count: the number of orbits on which the words agree at EVERY position. -/
def foldedAgree (w v : Fin N × Fin (d + 1) → F) : ℕ :=
  (Finset.univ.filter fun o : Fin N => ∀ p : Fin (d + 1), w (o, p) = v (o, p)).card

/-- **The trivial (upward) transfer:** `(d+1) · foldedAgree ≤ plainAgree`.  Each fully-agreeing
orbit contributes its `d+1` positions to the plain count. -/
theorem foldedAgree_mul_le_plainAgree (w v : Fin N × Fin (d + 1) → F) :
    (d + 1) * foldedAgree w v ≤ plainAgree w v := by
  classical
  rw [foldedAgree, plainAgree]
  have hsub : ((Finset.univ.filter fun o : Fin N => ∀ p : Fin (d + 1), w (o, p) = v (o, p)) ×ˢ
      (Finset.univ : Finset (Fin (d + 1)))) ⊆
      (Finset.univ.filter fun x : Fin N × Fin (d + 1) => w x = v x) := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨ho, _⟩ := hx
    rw [Finset.mem_filter] at ho ⊢
    exact ⟨Finset.mem_univ _, ho.2 x.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Nat.mul_comm]
  exact hcard

/-- The adversarial word: corrupted at exactly the first position of every orbit. -/
def oneCorruptionPerOrbit (N d : ℕ) (F : Type*) [Zero F] [One F] :
    Fin N × Fin (d + 1) → F :=
  fun x => if x.2 = (0 : Fin (d + 1)) then 1 else 0

/-- A proposed downward transfer from plain agreement to folded agreement at thresholds `A,T`
over one alphabet.
This is the exact extra theorem a folded-code capacity bound would need before it could control
plain-close words: every pair with at least `A` unfolded agreeing coordinates would have to agree
on at least `T` whole folded orbits. -/
def PlainToFoldAgreementTransfer (G : Type*) [Zero G] [One G] [DecidableEq G]
    (N d A T : ℕ) : Prop :=
  ∀ w v : Fin N × Fin (d + 1) → G, A ≤ plainAgree w v → T ≤ foldedAgree w v

/-- Alphabet-uniform form of `PlainToFoldAgreementTransfer`.  Refuting this is enough to show that
there is no bare agreement-threshold theorem that can transfer folded capacity bounds down to the
plain word metric. -/
def UniversalPlainToFoldAgreementTransfer (N d A T : ℕ) : Prop :=
  ∀ (G : Type) [Zero G] [One G] [DecidableEq G], (0 : G) ≠ 1 →
    PlainToFoldAgreementTransfer G N d A T

/-- **THE FOLDING-TRANSFER NO-GO.**  Over any type with `0 ≠ 1`, the word corrupted at one position
per orbit has:

* plain agreement with the zero word `= N·d` — a `d/(d+1)` fraction of all coordinates
  (far above every list-decoding radius), yet
* folded agreement `= 0` — **no orbit survives**.

So folded-code list bounds (at any radius, including the capacity results for folded RS) give NO
information about plain-close words: the naive §6-route-4 transfer is a certified dead end. -/
theorem folding_transfer_no_go (N d : ℕ) (F : Type*) [Zero F] [One F]
    [DecidableEq F] (h01 : (0 : F) ≠ 1) :
    plainAgree (oneCorruptionPerOrbit N d F) (0 : Fin N × Fin (d + 1) → F) = N * d ∧
    foldedAgree (oneCorruptionPerOrbit N d F) (0 : Fin N × Fin (d + 1) → F) = 0 := by
  classical
  constructor
  · -- plain agreement: exactly the positions with p ≠ 0, i.e. N·d of them
    rw [plainAgree]
    have hset : (Finset.univ.filter fun x : Fin N × Fin (d + 1) =>
        oneCorruptionPerOrbit N d F x = (0 : Fin N × Fin (d + 1) → F) x)
        = Finset.univ.filter fun x : Fin N × Fin (d + 1) => x.2 ≠ (0 : Fin (d + 1)) := by
      apply Finset.filter_congr
      intro x _
      simp only [oneCorruptionPerOrbit, Pi.zero_apply]
      by_cases h : x.2 = (0 : Fin (d + 1))
      · rw [if_pos h]
        constructor
        · intro h1; exact absurd h1.symm h01
        · intro hne; exact absurd h hne
      · rw [if_neg h]
        exact ⟨fun _ => h, fun _ => rfl⟩
    rw [hset]
    have hprod : (Finset.univ.filter fun x : Fin N × Fin (d + 1) => x.2 ≠ (0 : Fin (d + 1)))
        = (Finset.univ : Finset (Fin N)) ×ˢ
          (Finset.univ.filter fun p : Fin (d + 1) => p ≠ 0) := by
      ext x
      simp [Finset.mem_product, Finset.mem_filter]
    rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  · -- folded agreement: every orbit fails at position 0 (where the word is 1 ≠ 0)
    rw [foldedAgree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro o _ hall
    have h := hall (0 : Fin (d + 1))
    simp only [oneCorruptionPerOrbit, Pi.zero_apply] at h
    exact h01 h.symm

/-- Non-vacuity at concrete scale: `N = 8` orbits of size `4` (`d = 3`) over `ZMod 5` — plain
agreement `24` of `32` coordinates (relative `3/4`), folded agreement `0`. -/
theorem no_go_concrete :
    plainAgree (oneCorruptionPerOrbit 8 3 (ZMod 5)) 0 = 24 ∧
    foldedAgree (oneCorruptionPerOrbit 8 3 (ZMod 5)) 0 = 0 := by
  have h := folding_transfer_no_go 8 3 (ZMod 5) (by decide)
  simpa using h

/-- **Threshold form of the no-go.**  No nonzero folded-agreement conclusion follows from any
plain-agreement threshold at or below the one-corruption-per-orbit witness `N*d`.  Thus a folded
capacity/list bound can affect the plain smooth-domain prize only after a stronger theorem than a
bare plain-to-fold agreement transfer is supplied. -/
theorem not_plainToFoldAgreementTransfer_of_A_le_N_mul_d_of_T_pos
    {A T : ℕ} (hA : A ≤ N * d) (hT : 0 < T) :
    ¬ UniversalPlainToFoldAgreementTransfer N d A T := by
  intro htransfer
  have hno := folding_transfer_no_go N d (ZMod 5) (by decide)
  have hplain : A ≤
      plainAgree (oneCorruptionPerOrbit N d (ZMod 5)) (0 : Fin N × Fin (d + 1) → ZMod 5) := by
    simpa [hno.1] using hA
  have hfold : T ≤
      foldedAgree (oneCorruptionPerOrbit N d (ZMod 5)) (0 : Fin N × Fin (d + 1) → ZMod 5) :=
    htransfer (ZMod 5) (by decide)
      (oneCorruptionPerOrbit N d (ZMod 5)) (0 : Fin N × Fin (d + 1) → ZMod 5) hplain
  omega

end ArkLib.CodingTheory.FoldingTransferNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.FoldingTransferNoGo.foldedAgree_mul_le_plainAgree
#print axioms ArkLib.CodingTheory.FoldingTransferNoGo.folding_transfer_no_go
#print axioms ArkLib.CodingTheory.FoldingTransferNoGo.no_go_concrete
open ArkLib.CodingTheory.FoldingTransferNoGo in
#print axioms not_plainToFoldAgreementTransfer_of_A_le_N_mul_d_of_T_pos
