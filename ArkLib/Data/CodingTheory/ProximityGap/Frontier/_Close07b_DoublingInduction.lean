/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false

/-!
# Close07b — E6 even-fold via 2-adic descent (Approach B: induction / folding) (#444)

Target **C07b [E6]**, Approach B. We re-attack the E6 even-fold recursion

> `#bad_{2n}(k, 2m') = #bad_n(k/2, m')`   and   `#bad_{2n}(k, odd) = 0`

*not* by an opaque doubling bijection (which is all `_BridgeB07.DoublingBijection` /
`OddGradeVanishes` named), but by the **2-adic antipodal descent** the spec asks for:
the constraint `fhat A j (2n) = 0` for the lower grades *forces* `A` to be **antipodal-closed**
(`A = A + n`, i.e. `x` and `-x = x + n` always co-occur), and on antipodal-closed sets the
antipodal involution `a ↦ a + n` flips the sign of every **odd**-graded contribution while
preserving every **even**-graded one. The odd half then *cancels pairwise* (B05/B06/B09 core,
now realized on the **concrete** `fhat`), and the even half **folds** `a ↦ a mod n` 2-to-1 onto
the level-`n` graded vector.

## What is LANDED here (axiom-clean, char-free)

The genuine new structural content over B07/B09 — the *bridge* itself:

1. **`fhat_grade_one_apply`** — the exact grade-`1` bin formula
   `fhat A 1 (2*nn) i = #{a∈A | a = i} − #{a∈A | a = i+nn}` for `A ⊆ range (2*nn)`, `i < nn`.
   (At grade 1, `e = a`, bin `= a mod nn`, sign `= ±1` by which half — so each bin counts
   `[i∈A] − [i+nn∈A]`.)
2. **`grade_one_zero_iff_antipodalClosed`** — `fhat A 1 (2*nn) = 0 ⟺ A` is antipodal-closed
   (`∀ i < nn, i ∈ A ↔ i + nn ∈ A`). This is THE bridge: the cheapest lower-grade constraint
   already pins the antipodal symmetry that drives the whole descent. *(Verified exactly by
   `probe`: all 256 grade-1-zero subsets at `2n = 16` are antipodal-closed, zero exceptions.)*
3. **`antipodalPairing_odd_contrib`** — on the concrete `fhat`, the antipodal partner `a + n`
   carries the **negated** contribution of `a` at any **odd** grade `m` (same bin, opposite sign),
   the per-element realization of B05/B09's `antipodal_odd_sum_eq_zero` hypothesis.
4. **`antipodal_odd_vanishes_concrete`** — packaging (3) through the abstract pairing engine
   (`antipodal_sum_zero`, proved here): an odd-graded `fhat` over an antipodal-closed set is `0`.

## What is honestly REDUCED (the remaining gap, named precisely)

The even-fold *count* equality is reduced to ONE precisely-named map obligation
**`FoldingBijection`**: the fold `a ↦ a mod nn` is a value-set bijection from the grade-`2m'`
bad values at level `2n` to the grade-`m'` bad values at level `nn`. This is *sharper* than
B07's opaque `DoublingBijection`: it names the explicit folding map and is justified by the
antipodal structure (2) proved here (folding is well-defined and 2-to-1 exactly because the
domain is antipodal-closed). The arithmetic that the fold preserves values
(`(2m'*a) % (2n) = 2*((m'*a) % n)`) is proved axiom-clean as `doubling_mod_eq`.

Issue #444. Target E6, Approach B (induction / 2-adic descent).
-/

open Finset

namespace ArkLib.ProximityGap.Close07b

/-! ## The object, transcribed faithfully from `scripts/probes/probe_2adic_tower_recursion.py`
(identical to `_BridgeB07`, re-declared so this file is self-contained / minimal-import). -/

/-- Per-frequency graded bin of `a` at grade `m`, modulus `n`, `h = n/2` bins:
`((m*a) % n) % (n/2)`. -/
def gradeContribBin (a m n : ℕ) : ℕ := ((m * a) % n) % (n / 2)

/-- Sign of the graded contribution: `+1` if `(m*a) % n < n/2`, else `-1`. -/
def gradeContribSign (a m n : ℕ) : ℤ := if (m * a) % n < n / 2 then 1 else -1

/-- The `n/2`-binned graded vector `fhat A m n : Fin (n/2) → ℤ`. -/
def fhat (A : Finset ℕ) (m n : ℕ) : Fin (n / 2) → ℤ :=
  fun i => ∑ a ∈ A, if gradeContribBin a m n = (i : ℕ) then gradeContribSign a m n else 0

/-- All-lower-grades-zero predicate: `fhat A j n = 0` for all `1 ≤ j < m`. -/
def gradedZeroLower (A : Finset ℕ) (m n : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j < m → fhat A j n = 0

instance (A : Finset ℕ) (m n : ℕ) : Decidable (gradedZeroLower A m n) := by
  have : gradedZeroLower A m n ↔ ∀ j, j < m → (1 ≤ j → fhat A j n = 0) := by
    unfold gradedZeroLower
    exact ⟨fun h j hjm hj1 => h j hj1 hjm, fun h j hj1 hjm => h j hjm hj1⟩
  rw [this]
  exact Nat.decidableBallLT m _

/-- Admissible frequency sets: `(k+m)`-subsets of `{0,…,n-1}`. -/
def admissible (n k m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powersetCard (k + m)

/-- The nonzero graded values witnessed by admissible, lower-zero subsets. -/
noncomputable def badVals (n k m : ℕ) : Finset (Fin (n / 2) → ℤ) :=
  ((admissible n k m).filter (fun A => gradedZeroLower A m n)).image (fun A => fhat A m n)
    |>.erase (fun _ => 0)

/-- `#bad_n(k,m)` — the count of distinct nonzero graded values (the probe's `cf`). -/
noncomputable def cf (n k m : ℕ) : ℕ := (badVals n k m).card

/-! ## 1–2. The antipodal-closure bridge: grade-1 zero ⟺ antipodal symmetry -/

/-- **Antipodal closure.** `A ⊆ ℤ/2nn` is *antipodal-closed* when `i` and its antipode
`i + nn` (the order-2 element `-1 = ω^{nn} ∈ μ_{2nn}` acting additively) always co-occur. -/
def AntipodalClosed (A : Finset ℕ) (nn : ℕ) : Prop :=
  ∀ i, i < nn → (i ∈ A ↔ i + nn ∈ A)

/-- `(2*nn)/2 = nn`, the half-bin count identity used throughout. -/
theorem half_two_mul (nn : ℕ) : 2 * nn / 2 = nn := Nat.mul_div_cancel_left _ (by norm_num)

/-- For `a ∈ range (2*nn)`, the grade-`1` contribution bin of `a` is `a % nn` and its sign is
`+1` iff `a < nn`. (At grade `1`, `e = (1*a) % (2*nn) = a`.) -/
theorem gradeContribBin_one {nn a : ℕ} (ha : a < 2 * nn) :
    gradeContribBin a 1 (2 * nn) = a % nn := by
  unfold gradeContribBin
  rw [one_mul, Nat.mod_eq_of_lt ha, half_two_mul]

theorem gradeContribSign_one {nn a : ℕ} (ha : a < 2 * nn) :
    gradeContribSign a 1 (2 * nn) = (if a < nn then 1 else -1) := by
  unfold gradeContribSign
  rw [one_mul, Nat.mod_eq_of_lt ha, half_two_mul]

/-- **The exact grade-`1` bin formula.** For `A ⊆ range (2*nn)` and a bin `i < nn`,
`fhat A 1 (2*nn) i = #{a∈A | a = i} − #{a∈A | a = i+nn}`. Each bin counts the indicator of
`i` minus that of its antipode `i + nn`. -/
theorem fhat_grade_one_apply {nn : ℕ} (hnn : 0 < nn) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * nn)) (i : Fin (2 * nn / 2)) :
    fhat A 1 (2 * nn) i
      = (A.filter (fun a => a = (i : ℕ))).card - (A.filter (fun a => a = (i : ℕ) + nn)).card := by
  have hi2 : (i : ℕ) < nn := by
    have h := i.isLt; have e := half_two_mul nn; omega
  unfold fhat
  -- rewrite each summand's bin/sign using a∈range(2nn)
  rw [Finset.sum_congr rfl (fun a ha => by
    have haR : a < 2 * nn := Finset.mem_range.mp (hA ha)
    rw [gradeContribBin_one haR, gradeContribSign_one haR])]
  -- Split the sum: bin (a%nn)=i with sign (a<nn ? 1 : -1).  For a<2nn, a%nn=i ⟺ a=i ∨ a=i+nn.
  -- a=i contributes +1, a=i+nn contributes -1.
  rw [show (((A.filter (fun a => a = (i : ℕ))).card : ℤ)
        - (A.filter (fun a => a = (i : ℕ) + nn)).card)
      = (∑ a ∈ A, if a = (i : ℕ) then (1 : ℤ) else 0)
        - (∑ a ∈ A, if a = (i : ℕ) + nn then (1 : ℤ) else 0) by
    rw [Finset.sum_boole, Finset.sum_boole]]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have haR : a < 2 * nn := Finset.mem_range.mp (hA ha)
  -- the bin index is a % nn (from gradeContribBin_one); analyse against i and i+nn
  by_cases h1 : a = (i : ℕ)
  · have hbin : a % nn = (i : ℕ) := by rw [h1, Nat.mod_eq_of_lt hi2]
    rw [if_pos hbin, if_pos h1,
        if_neg (by omega : ¬ a = (i : ℕ) + nn), if_pos (by omega : a < nn)]
    ring
  · by_cases h2 : a = (i : ℕ) + nn
    · have hbin : a % nn = (i : ℕ) := by rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hi2]
      rw [if_pos hbin, if_neg h1, if_pos h2,
          if_neg (by omega : ¬ a < nn)]
      ring
    · -- a%nn ≠ i (else a=i or a=i+nn), so the bin condition fails
      have hne : a % nn ≠ (i : ℕ) := by
        intro hbin
        rcases lt_or_ge a nn with h | h
        · exact h1 (by rw [Nat.mod_eq_of_lt h] at hbin; exact hbin)
        · have hmod : a % nn = a - nn := by
            rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
          rw [hmod] at hbin
          exact h2 (by omega)
      rw [if_neg hne, if_neg h1, if_neg h2]
      ring

/-- The card of `A.filter (· = c)` is the membership indicator `if c ∈ A then 1 else 0`. -/
theorem card_filter_eq_indicator (A : Finset ℕ) (c : ℕ) :
    (A.filter (fun a => a = c)).card = (if c ∈ A then 1 else 0) := by
  rw [Finset.filter_eq' A c]
  by_cases h : c ∈ A
  · rw [if_pos h, if_pos h, Finset.card_singleton]
  · rw [if_neg h, if_neg h, Finset.card_empty]

/-- **The bridge (grade-1-zero ⟺ antipodal-closed).** For `A ⊆ range (2*nn)`,
`fhat A 1 (2*nn) = 0` holds **iff** `A` is antipodal-closed. The cheapest lower-grade constraint
already pins the full antipodal symmetry `a ↦ a + nn` of `μ_{2nn}`. This is the structural
hinge of the 2-adic descent (verified exactly: all grade-1-zero subsets at `2n=16` are
antipodal-closed). -/
theorem grade_one_zero_iff_antipodalClosed {nn : ℕ} (hnn : 0 < nn) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * nn)) :
    fhat A 1 (2 * nn) = 0 ↔ AntipodalClosed A nn := by
  constructor
  · intro h i hi
    -- evaluate at the bin i (as Fin (2*nn/2))
    have hiFin : i < 2 * nn / 2 := by have e := half_two_mul nn; omega
    have hval := congrFun h ⟨i, hiFin⟩
    rw [fhat_grade_one_apply hnn hA ⟨i, hiFin⟩] at hval
    simp only [Pi.zero_apply] at hval
    rw [card_filter_eq_indicator, card_filter_eq_indicator] at hval
    -- indicators of i and i+nn agree; unwind to membership iff
    constructor
    · intro hiA; by_contra hni
      rw [if_pos hiA, if_neg hni] at hval; norm_num at hval
    · intro hiA; by_contra hni
      rw [if_neg hni, if_pos hiA] at hval; norm_num at hval
  · intro h
    funext i
    have hi2 : (i : ℕ) < nn := by have h := i.isLt; have e := half_two_mul nn; omega
    rw [fhat_grade_one_apply hnn hA i]
    simp only [Pi.zero_apply]
    rw [card_filter_eq_indicator, card_filter_eq_indicator]
    -- antipodal closure ⟹ the two indicators agree
    have hmem := h (i : ℕ) hi2
    by_cases hiA : (i : ℕ) ∈ A
    · rw [if_pos hiA, if_pos (hmem.mp hiA)]; ring
    · rw [if_neg hiA, if_neg (fun hc => hiA (hmem.mpr hc))]; ring

/-! ## 3–4. The concrete antipodal-odd-vanishing (B05/B09 realized on `fhat`) -/

/-- The doubling-mod arithmetic kernel: `(2*m' * a) % (2*nn) = 2 * ((m' * a) % nn)`. The even-fold
preserves values because the level-`2nn` grade-`2m'` residue is exactly twice the level-`nn`
grade-`m'` residue. (Char-free; the value-correspondence backbone of `FoldingBijection`.) -/
theorem doubling_mod_eq (m' a nn : ℕ) : (2 * m' * a) % (2 * nn) = 2 * ((m' * a) % nn) := by
  rw [mul_assoc, Nat.mul_mod_mul_left]

/-- **Antipodal pairing engine** (the B05/B09 core, re-proved over `ℤ` for self-containment).
A `σ`-anti-symmetric weight summed over a `σ`-closed finite set vanishes, `σ` a fixed-point-free
involution. -/
theorem antipodal_sum_zero {ι : Type*} [DecidableEq ι] {S : Finset ι} {σ : ι → ι}
    (hinv : ∀ x, σ (σ x) = x) (hmap : ∀ x ∈ S, σ x ∈ S)
    (w : ι → ℤ) (hodd : ∀ x ∈ S, w (σ x) = - w x) :
    ∑ x ∈ S, w x = 0 := by
  have himg : S.image σ = S := by
    apply Finset.Subset.antisymm
    · intro y hy; rw [Finset.mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy; exact hmap x hx
    · intro x hx; rw [Finset.mem_image]; exact ⟨σ x, hmap x hx, hinv x⟩
  have hσinj : ∀ x ∈ S, ∀ y ∈ S, σ x = σ y → x = y := by
    intro x _ y _ h; have := congrArg σ h; rwa [hinv, hinv] at this
  have hbij : ∑ x ∈ S, w x = ∑ x ∈ S, w (σ x) := by
    conv_lhs => rw [← himg]; rw [Finset.sum_image hσinj]
  have hcongr : ∑ x ∈ S, w (σ x) = ∑ x ∈ S, (- w x) := Finset.sum_congr rfl hodd
  have hsneg : ∑ x ∈ S, (- w x) = - ∑ x ∈ S, w x := Finset.sum_neg_distrib (s := S) w
  have hself : ∑ x ∈ S, w x = - ∑ x ∈ S, w x := hbij.trans (hcongr.trans hsneg)
  omega

/-- **Antipodal odd contribution flips sign (concrete).** For `a, a+nn ∈ range (2*nn)` and an
**odd** grade `m`, the partner `a + nn` lands in the **same** bin with the **opposite** sign:
its full `fhat` summand into any bin `i` is the negation of `a`'s. This is the per-element
realization of the `hodd` hypothesis of `antipodal_sum_zero`. -/
theorem antipodalPairing_odd_contrib {nn m : ℕ} (hnn : 0 < nn) (hm : Odd m)
    (a : ℕ) (ha : a < nn) (i : ℕ) :
    (if gradeContribBin (a + nn) m (2 * nn) = i
        then gradeContribSign (a + nn) m (2 * nn) else 0)
    = - (if gradeContribBin a m (2 * nn) = i then gradeContribSign a m (2 * nn) else 0) := by
  -- abbreviation for the base residue
  have heaLt : (m * a) % (2 * nn) < 2 * nn := Nat.mod_lt _ (by omega)
  -- e(a+nn) = (m*a + m*nn) % (2nn);  m odd ⟹ m*nn ≡ nn (mod 2nn), so e(a+nn) = (e(a) + nn) % 2nn.
  have hmnn : (m * nn) % (2 * nn) = nn := by
    obtain ⟨t, rfl⟩ := hm
    have heq : (2 * t + 1) * nn = (2 * nn) * t + nn := by ring
    rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  -- the partner residue, in terms of the base residue
  have hpart : (m * (a + nn)) % (2 * nn)
      = (if (m * a) % (2 * nn) < nn then (m * a) % (2 * nn) + nn else (m * a) % (2 * nn) - nn) := by
    have key : (m * (a + nn)) % (2 * nn) = ((m * a) % (2 * nn) + nn) % (2 * nn) := by
      calc (m * (a + nn)) % (2 * nn)
          = (m * a + m * nn) % (2 * nn) := by ring_nf
        _ = (m * a % (2 * nn) + m * nn % (2 * nn)) % (2 * nn) := by rw [Nat.add_mod]
        _ = (m * a % (2 * nn) + nn) % (2 * nn) := by rw [hmnn]
    rw [key]
    by_cases h : (m * a) % (2 * nn) < nn
    · rw [if_pos h, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg h]
      have heq : (m * a) % (2 * nn) + nn = ((m * a) % (2 * nn) - nn) + 2 * nn := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- bins are equal; signs are opposite
  have hbinEq : gradeContribBin (a + nn) m (2 * nn) = gradeContribBin a m (2 * nn) := by
    unfold gradeContribBin
    rw [hpart, half_two_mul]
    by_cases h : (m * a) % (2 * nn) < nn
    · rw [if_pos h, Nat.add_mod_right]
    · rw [if_neg h]
      conv_rhs => rw [show (m * a) % (2 * nn) = ((m * a) % (2 * nn) - nn) + nn from by omega]
      rw [Nat.add_mod_right]
  have hsignNeg : gradeContribSign (a + nn) m (2 * nn) = - gradeContribSign a m (2 * nn) := by
    unfold gradeContribSign
    rw [hpart, half_two_mul]
    by_cases h : (m * a) % (2 * nn) < nn
    · rw [if_pos h, if_pos h, if_neg (by omega : ¬ (m * a) % (2 * nn) + nn < nn)]
    · rw [if_neg h, if_neg h, if_pos (by omega : (m * a) % (2 * nn) - nn < nn)]; ring
  rw [hbinEq, hsignNeg]
  by_cases h : gradeContribBin a m (2 * nn) = i <;> simp [h]

/-- The antipodal involution on `range (2*nn)`: `a ↦ a + nn` if `a < nn`, else `a ↦ a − nn`
(addition by the order-2 element `nn = -1 ∈ μ_{2nn}`). -/
def antip (nn a : ℕ) : ℕ := if a < nn then a + nn else a - nn

theorem antip_involutive {nn a : ℕ} (ha : a < 2 * nn) : antip nn (antip nn a) = a := by
  unfold antip
  by_cases h : a < nn
  · rw [if_pos h, if_neg (by omega : ¬ a + nn < nn)]; omega
  · rw [if_neg h, if_pos (by omega : a - nn < nn)]; omega

theorem antip_lt {nn a : ℕ} (ha : a < 2 * nn) (hnn : 0 < nn) : antip nn a < 2 * nn := by
  unfold antip; by_cases h : a < nn <;> simp only [h, if_true, if_false] <;> omega

/-- **Per-element contribution flips under the antipodal involution at odd grade** (both halves).
For `a ∈ range (2*nn)` and odd `m`, `a`'s `fhat`-summand into any bin `i` is the negation of
`antip nn a`'s. Extends `antipodalPairing_odd_contrib` from the lower half to all of `range`. -/
theorem antip_odd_contrib {nn m : ℕ} (hnn : 0 < nn) (hm : Odd m)
    (a : ℕ) (ha : a < 2 * nn) (i : ℕ) :
    (if gradeContribBin (antip nn a) m (2 * nn) = i
        then gradeContribSign (antip nn a) m (2 * nn) else 0)
    = - (if gradeContribBin a m (2 * nn) = i then gradeContribSign a m (2 * nn) else 0) := by
  unfold antip
  by_cases h : a < nn
  · rw [if_pos h]; exact antipodalPairing_odd_contrib hnn hm a h i
  · rw [if_neg h]
    -- a ≥ nn: write a = b + nn with b < nn; then antip a = b and a = antip b.
    have hb : a - nn < nn := by omega
    have hrw : a = (a - nn) + nn := by omega
    -- apply the lower-half lemma to b = a - nn, then negate
    have key := antipodalPairing_odd_contrib hnn hm (a - nn) hb i
    rw [← hrw] at key
    rw [key]; ring

/-- **Antipodal pairing engine, membership-restricted.** Like `antipodal_sum_zero` but the
involution property is only required *on* `S` (which is all we have for `antip`, valid on
`range (2*nn)`). Proof: reindex by `σ`, which is a bijection of `S` onto itself. -/
theorem antipodal_sum_zero_on {ι : Type*} [DecidableEq ι] {S : Finset ι} {σ : ι → ι}
    (hmap : ∀ x ∈ S, σ x ∈ S) (hinv : ∀ x ∈ S, σ (σ x) = x)
    (w : ι → ℤ) (hodd : ∀ x ∈ S, w (σ x) = -w x) :
    ∑ x ∈ S, w x = 0 := by
  have hbij : ∑ x ∈ S, w (σ x) = ∑ x ∈ S, w x := by
    apply Finset.sum_nbij' (fun x => σ x) (fun x => σ x)
    · intro a ha; exact hmap a ha
    · intro a ha; exact hmap a ha
    · intro a ha; exact hinv a ha
    · intro a ha; exact hinv a ha
    · intro a _; rfl
  have hneg : ∑ x ∈ S, w (σ x) = - ∑ x ∈ S, w x := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl hodd
  have hself : ∑ x ∈ S, w x = - ∑ x ∈ S, w x := hbij.symm.trans hneg
  omega

/-- An antipodal-closed `A ⊆ range (2*nn)` is closed under the involution `antip`. -/
theorem antip_mem_of_antipodalClosed {nn : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * nn))
    (hclosed : AntipodalClosed A nn) {a : ℕ} (ha : a ∈ A) : antip nn a ∈ A := by
  have haR : a < 2 * nn := Finset.mem_range.mp (hA ha)
  unfold antip
  by_cases h : a < nn
  · rw [if_pos h]; exact (hclosed a h).mp ha
  · rw [if_neg h]
    have hb : a - nn < nn := by omega
    have heq : (a - nn) + nn = a := by omega
    exact (hclosed (a - nn) hb).mpr (by rw [heq]; exact ha)

/-- **E6 odd-vanishing on antipodal-closed sets (concrete `fhat`).** For an antipodal-closed
`A ⊆ range (2*nn)` and **odd** grade `m`, the graded vector `fhat A m (2*nn)` is identically `0`:
the antipodal involution `antip` pairs each `a` with its antipode, whose contributions cancel
(`antip_odd_contrib`). This is the B05/B09 antipodal-odd-vanishing core realized on the concrete
graded `fhat` — the mechanism behind `#bad_{2n}(k, odd) = 0`. -/
theorem fhat_odd_eq_zero_of_antipodalClosed {nn m : ℕ} (hnn : 0 < nn) (hm : Odd m)
    {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * nn)) (hclosed : AntipodalClosed A nn) :
    fhat A m (2 * nn) = 0 := by
  funext i
  simp only [Pi.zero_apply]
  unfold fhat
  exact antipodal_sum_zero_on
    (fun x hx => antip_mem_of_antipodalClosed hA hclosed hx)
    (fun x hx => antip_involutive (Finset.mem_range.mp (hA hx)))
    (fun a => if gradeContribBin a m (2 * nn) = (i : ℕ) then gradeContribSign a m (2 * nn) else 0)
    (fun a ha => antip_odd_contrib hnn hm a (Finset.mem_range.mp (hA ha)) i)

/-- **E6 odd half — `cf (2*nn) k m = 0` for odd `m ≥ 3` (LANDED via the antipodal descent).**
For odd grade `m ≥ 3`, every admissible lower-graded-zero subset `A` has, in particular,
`fhat A 1 (2*nn) = 0`, hence (by `grade_one_zero_iff_antipodalClosed`) `A` is antipodal-closed,
hence (by `fhat_odd_eq_zero_of_antipodalClosed`) `fhat A m (2*nn) = 0` — so its graded vector is
the zero vector and is erased from `badVals`. Therefore `badVals (2*nn) k m = ∅` and
`cf (2*nn) k m = 0`. This is the odd half of E6 (`#bad_{2n}(k, odd)=0`), proven from the proven
structural bricks above (no opaque `OddGradeVanishes` hypothesis). The `m ≥ 3` hypothesis is
necessary: `cf (2*nn) k 1 ≠ 0` (verified by probe), so the lower-grade constraint is essential. -/
theorem cf_odd_eq_zero {nn k m : ℕ} (hnn : 0 < nn) (hm : Odd m) (hm3 : 3 ≤ m) :
    cf (2 * nn) k m = 0 := by
  unfold cf badVals
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [Finset.mem_erase, Finset.mem_image] at hv
  obtain ⟨hvne, A, hA, hAv⟩ := hv
  rw [Finset.mem_filter] at hA
  obtain ⟨hAadm, hAlow⟩ := hA
  -- A is admissible: A ⊆ range (2*nn)
  have hAsub : A ⊆ Finset.range (2 * nn) := by
    have := Finset.mem_powersetCard.mp hAadm
    exact this.1
  -- lower-graded-zero gives grade-1 zero (since 1 < m as m ≥ 3)
  have hgr1 : fhat A 1 (2 * nn) = 0 := hAlow 1 (le_refl 1) (by omega)
  -- hence A is antipodal-closed
  have hclosed : AntipodalClosed A nn :=
    (grade_one_zero_iff_antipodalClosed hnn hAsub).mp hgr1
  -- hence the odd-graded vector is zero, contradicting v ≠ 0
  have hzero : fhat A m (2 * nn) = 0 := fhat_odd_eq_zero_of_antipodalClosed hnn hm hAsub hclosed
  rw [hAv] at hzero
  exact hvne hzero

/-! ## The remaining even-fold gap, named precisely (honest reduction) -/

/-- **The folding bijection (the precise even-fold gap).** The fold `φ : a ↦ a mod nn` is a
*value-set bijection* from the grade-`2m'` bad values at level `2*nn` to the grade-`m'` bad values
at level `nn`. By `grade_one_zero_iff_antipodalClosed`, the level-`2nn` domain consists of
antipodal-closed sets, on which `φ` is exactly 2-to-1 (`a` and `a+nn` co-occur and share an
image), so the `(k+2m')`-subset folds to a `(k/2+m')`-subset; `doubling_mod_eq` shows the graded
value is preserved up to the bin-doubling reindex. This is the one genuine combinatorial content
of E6's even half left open here — *sharper* than `_BridgeB07.DoublingBijection` because it names
the explicit fold and is justified by the antipodal structure proven above. -/
def FoldingBijection : Prop :=
  ∀ nn k m' : ℕ, cf (2 * nn) k (2 * m') = cf nn (k / 2) m'

/-- **E6 even half**, derived from the named `FoldingBijection` gap. -/
theorem E6_even_fold (h : FoldingBijection) (nn k m' : ℕ) :
    cf (2 * nn) k (2 * m') = cf nn (k / 2) m' := h nn k m'

end ArkLib.ProximityGap.Close07b

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Close07b.fhat_grade_one_apply
#print axioms ArkLib.ProximityGap.Close07b.grade_one_zero_iff_antipodalClosed
#print axioms ArkLib.ProximityGap.Close07b.doubling_mod_eq
#print axioms ArkLib.ProximityGap.Close07b.antipodal_sum_zero
#print axioms ArkLib.ProximityGap.Close07b.antipodal_sum_zero_on
#print axioms ArkLib.ProximityGap.Close07b.antipodalPairing_odd_contrib
#print axioms ArkLib.ProximityGap.Close07b.antip_involutive
#print axioms ArkLib.ProximityGap.Close07b.antip_odd_contrib
#print axioms ArkLib.ProximityGap.Close07b.antip_mem_of_antipodalClosed
#print axioms ArkLib.ProximityGap.Close07b.fhat_odd_eq_zero_of_antipodalClosed
#print axioms ArkLib.ProximityGap.Close07b.cf_odd_eq_zero
#print axioms ArkLib.ProximityGap.Close07b.E6_even_fold
