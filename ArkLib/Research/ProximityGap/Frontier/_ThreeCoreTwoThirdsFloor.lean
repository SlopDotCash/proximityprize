/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# Three affine cores at two thirds of the block length

For `n = 3r+1`, store the line `(j² X,j)` on a disjoint core of size `r`,
for each `j = 0,1,2`, and store `(8,3)` at the evaluation point one. Every
ordinary coordinate supplies two scalar challenges and the remaining coordinate
supplies three. Separation of three cosets and the three exceptional scalars
makes the resulting family have size `2n+1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial Code
open _root_.ProximityGap
open scoped NNReal ENNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.ThreeCoreTwoThirdsFloor

/-- Multipliers for the three ordinary cosets. -/
def ordScale (p : ℕ) (c : Fin 3) : ZMod p := -((c.val + 1 : ℕ) : ZMod p)

/-- The challenge for source line `i` at the exceptional point. -/
noncomputable def exceptional (p : ℕ) [Fact p.Prime] (i : Fin 3) : ZMod p :=
  ((i.val : ZMod p) ^ 2 - 8) / (3 - (i.val : ZMod p))

private def owner : Fin 6 → Fin 3 := ![0, 1, 0, 2, 1, 2]
private def source : Fin 6 → Fin 3 := ![1, 0, 2, 0, 2, 1]
private def coset : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

private theorem source_ne_owner (s : Fin 6) : source s ≠ owner s := by
  revert s
  decide

private theorem val_sum (s : Fin 6) :
    (coset s).val + 1 = (source s).val + (owner s).val := by
  revert s
  decide

private theorem code_unique : ∀ s s' : Fin 6,
    coset s = coset s' → owner s = owner s' → s = s' := by decide

variable {n r k p : ℕ} [NeZero n] [Fact p.Prime]

private def slot (hn : n = 3 * r + 1) (j : Fin 3) (q : Fin r) : Fin n :=
  ⟨3 * q.val + j.val + 1, by omega⟩

private theorem slot_unique {hn : n = 3 * r + 1} {j j' : Fin 3} {q q' : Fin r}
    (h : slot hn j q = slot hn j' q') : j = j' ∧ q = q' := by
  have h' := congrArg Fin.val h
  change 3 * q.val + j.val + 1 = 3 * q'.val + j'.val + 1 at h'
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private def core (hn : n = 3 * r + 1) (j : Fin 3) : Finset (Fin n) :=
  Finset.univ.map ⟨slot hn j, fun _ _ h => (slot_unique h).2⟩

private lemma mem_core {hn : n = 3 * r + 1} {j : Fin 3} {x : Fin n} :
    x ∈ core hn j ↔ ∃ q : Fin r, slot hn j q = x := by
  simp [core]
  rfl

private lemma card_core (hn : n = 3 * r + 1) (j : Fin 3) : (core hn j).card = r := by
  simp [core]

private def lineAt (z : Fin n) : Fin 3 := ⟨(z.val - 1) % 3, Nat.mod_lt _ (by decide)⟩

private lemma lineAt_slot (hn : n = 3 * r + 1) (j : Fin 3) (q : Fin r) :
    lineAt (slot hn j q) = j := by
  apply Fin.ext
  change (3 * q.val + j.val + 1 - 1) % 3 = j.val
  omega

private lemma slot_ne_zero (hn : n = 3 * r + 1) (j : Fin 3) (q : Fin r) :
    slot hn j q ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  change 3 * q.val + j.val + 1 = 0 at h'
  omega

private noncomputable def stack (dom : Fin n ↪ ZMod p) : WordStack (ZMod p) (Fin 2) (Fin n) :=
  ![fun z => if z = 0 then 8 else ((lineAt z).val : ZMod p) ^ 2 * dom z,
    fun z => if z = 0 then 3 else ((lineAt z).val : ZMod p)]

private lemma stack_slot (dom : Fin n ↪ ZMod p) (hn : n = 3 * r + 1) (j : Fin 3) (q : Fin r) :
    stack dom 0 (slot hn j q) = (j.val : ZMod p) ^ 2 * dom (slot hn j q) ∧
    stack dom 1 (slot hn j q) = (j.val : ZMod p) := by
  simp [stack, slot_ne_zero hn j q, lineAt_slot hn j q]

private lemma cast_eq {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using congrArg ZMod.val h

private def ordinary (hn : n = 3 * r + 1) (dom : Fin n ↪ ZMod p)
    (s : Fin 6) (q : Fin r) : ZMod p := ordScale p (coset s) * dom (slot hn (owner s) q)

private lemma ordinary_pow (hn : n = 3 * r + 1) (dom : Fin n ↪ ZMod p)
    (hroot : ∀ z, dom z ^ n = 1) (s : Fin 6) (q : Fin r) :
    ordinary hn dom s q ^ n = ordScale p (coset s) ^ n := by
  simp [ordinary, mul_pow, hroot]

private lemma event (hn : n = 3 * r + 1) (dom : Fin n ↪ ZMod p)
    (hk : 2 ≤ k) (hkr : k ≤ r) (i : Fin 3) (z : Fin n) (γ : ZMod p)
    (hz : z ∉ core hn i)
    (hfold : (i.val : ZMod p)^2 * dom z + γ * i.val = stack dom 0 z + γ * stack dom 1 z)
    (hdir : (i.val : ZMod p) ≠ stack dom 1 z) :
    mcaEvent (F := ZMod p) (ReedSolomon.code dom k : Set (Fin n → ZMod p))
      (((2*r : ℕ) : ℝ≥0) / n) (stack dom 0) (stack dom 1) γ := by
  have h1 : (1 : WithBot ℕ) < (k : ℕ) := by exact_mod_cast (by omega : 1 < k)
  have hconst : ∀ a : ZMod p, (C a).degree < (k : ℕ) := fun a =>
    degree_C_le.trans_lt (lt_trans (by decide : (0 : WithBot ℕ) < 1) h1)
  have ha := (degree_C_mul_X_le ((i.val : ZMod p)^2)).trans_lt h1
  apply HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh dom k _ (stack dom)
    γ (core hn i) z (C ((i.val : ZMod p)^2) * X) (C (i.val : ZMod p)) hz ha (hconst _)
  · rw [← C_mul]
    exact (degree_add_le _ _).trans_lt (max_lt ha (hconst _))
  · simpa only [card_core] using hkr
  · have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Fintype.card_fin, card_core, tsub_mul, one_mul, div_mul_cancel₀ _ hn0]
    rw [← Nat.cast_tsub]
    exact_mod_cast (by omega : n - 2*r ≤ r+1)
  · intro x hx
    obtain ⟨q, rfl⟩ := mem_core.mp hx
    simpa only [eval_mul, eval_C, eval_X] using
      ⟨(stack_slot dom hn i q).1.symm, (stack_slot dom hn i q).2.symm⟩
  · simpa only [eval_add, eval_mul, eval_C, eval_X] using hfold
  · intro heq
    apply hdir
    simpa only [eval_C] using congrArg Prod.snd heq

private lemma ordinary_event (hn : n = 3 * r + 1) (dom : Fin n ↪ ZMod p)
    (hp : 3 < p) (hk : 2 ≤ k) (hkr : k ≤ r) (s : Fin 6) (q : Fin r) :
    mcaEvent (F := ZMod p) (ReedSolomon.code dom k : Set (Fin n → ZMod p))
      (((2*r : ℕ) : ℝ≥0) / n) (stack dom 0) (stack dom 1) (ordinary hn dom s q) := by
  let z := slot hn (owner s) q
  have hs := stack_slot dom hn (owner s) q
  apply event hn dom hk hkr (source s) z
  · intro h
    obtain ⟨q', hq'⟩ := mem_core.mp h
    exact source_ne_owner s (slot_unique hq').1
  · dsimp only [z]
    rw [hs.1, hs.2]
    have hadd : (((coset s).val + 1 : ℕ) : ZMod p) =
        ((source s).val : ZMod p) + ((owner s).val : ZMod p) := by
      rw [val_sum, Nat.cast_add]
    unfold ordinary ordScale
    rw [hadd]
    ring
  · dsimp only [z]
    rw [hs.2]
    exact fun h => source_ne_owner s (Fin.ext (cast_eq (by omega) (by omega) h))

private lemma exceptional_event (hn : n = 3 * r + 1) (dom : Fin n ↪ ZMod p)
    (hp : 3 < p) (hk : 2 ≤ k) (hkr : k ≤ r) (hzero : dom 0 = 1) (i : Fin 3) :
    mcaEvent (F := ZMod p) (ReedSolomon.code dom k : Set (Fin n → ZMod p))
      (((2*r : ℕ) : ℝ≥0) / n) (stack dom 0) (stack dom 1) (exceptional p i) := by
  have hne : (i.val : ZMod p) ≠ 3 := by
    intro h
    have h' := cast_eq (a := i.val) (b := 3) (by omega) hp (by simpa using h)
    omega
  apply event hn dom hk hkr i 0
  · intro h
    obtain ⟨q, hq⟩ := mem_core.mp h
    exact slot_ne_zero hn i q hq
  · simp [stack, exceptional, hzero]
    field_simp [sub_ne_zero.mpr hne.symm]
    ring
  · simpa [stack] using hne

private noncomputable def label (hn : n = 3 * r + 1) (dom : Fin n ↪ ZMod p) :
    (Fin 6 × Fin r) ⊕ Fin 3 → ZMod p :=
  Sum.elim (fun x => ordinary hn dom x.1 x.2) (exceptional p)

private lemma label_injective (hn : n = 3 * r + 1) (dom : Fin n ↪ ZMod p)
    (hp : 3 < p) (hroot : ∀ z, dom z ^ n = 1)
    (hOrd : Function.Injective (fun c : Fin 3 => ordScale p c ^ n))
    (hExc : Function.Injective (exceptional p))
    (hSep : ∀ c i : Fin 3, ordScale p c ^ n ≠ exceptional p i ^ n) :
    Function.Injective (label hn dom) := by
  intro x y h
  rcases x with ⟨s, q⟩ | i <;> rcases y with ⟨s', q'⟩ | i'
  · change ordinary hn dom s q = ordinary hn dom s' q' at h
    have hpows := congrArg (fun a : ZMod p => a ^ n) h
    simp only [ordinary_pow hn dom hroot] at hpows
    have hcos := hOrd hpows
    have hscale : ordScale p (coset s') ≠ 0 := by
      unfold ordScale
      intro heq
      have hcast : (((coset s').val + 1 : ℕ) : ZMod p) = 0 := neg_eq_zero.mp heq
      have := cast_eq (p := p) (a := (coset s').val + 1) (b := 0) (by omega) (by omega)
        (by simpa using hcast)
      omega
    unfold ordinary at h
    rw [hcos] at h
    have hslot := dom.injective ((mul_right_inj' hscale).mp h)
    obtain ⟨howner, hq⟩ := slot_unique hslot
    rw [code_unique s s' hcos howner, hq]
  · change ordinary hn dom s q = exceptional p i' at h
    have hpows := congrArg (fun a : ZMod p => a ^ n) h
    exact False.elim (hSep (coset s) i' (by simpa only [ordinary_pow hn dom hroot] using hpows))
  · change exceptional p i = ordinary hn dom s' q' at h
    have hpows := congrArg (fun a : ZMod p => a ^ n) h.symm
    exact False.elim (hSep (coset s') i (by simpa only [ordinary_pow hn dom hroot] using hpows))
  · exact congrArg Sum.inr (hExc h)

/-- The normalized bad-scalar count at radius `2r/n` for every dimension between
two and `r`. All three numerical hypotheses describe elements of the field. -/
theorem epsMCA_lower_bound (dom : Fin n ↪ ZMod p) (hn : n = 3 * r + 1)
    (hp : 3 < p) (hk : 2 ≤ k) (hkr : k ≤ r) (hzero : dom 0 = 1)
    (hroot : ∀ z, dom z ^ n = 1)
    (hOrd : Function.Injective (fun c : Fin 3 => ordScale p c ^ n))
    (hExc : Function.Injective (exceptional p))
    (hSep : ∀ c i : Fin 3, ordScale p c ^ n ≠ exceptional p i ^ n) :
    ((6*r+3 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      epsMCA (F := ZMod p) (A := ZMod p) (ReedSolomon.code dom k : Set (Fin n → ZMod p))
        (((2*r : ℕ) : ℝ≥0) / n) := by
  classical
  let e : (Fin 6 × Fin r) ⊕ Fin 3 ↪ ZMod p :=
    ⟨label hn dom, label_injective hn dom hp hroot hOrd hExc hSep⟩
  have h := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code dom k : Set (Fin n → ZMod p)) (((2*r : ℕ) : ℝ≥0) / n)
    (stack dom) (Finset.univ.map e) ?_
  · simpa only [Finset.card_map, Finset.card_univ, Fintype.card_sum,
      Fintype.card_prod, Fintype.card_fin, ZMod.card] using h
  · intro γ hγ
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hγ
    rcases a with ⟨s,q⟩ | i
    · exact ordinary_event hn dom hp hk hkr s q
    · exact exceptional_event hn dom hp hk hkr hzero i

end ArkLib.ProximityGap.Frontier.ThreeCoreTwoThirdsFloor

#print axioms ArkLib.ProximityGap.Frontier.ThreeCoreTwoThirdsFloor.epsMCA_lower_bound
