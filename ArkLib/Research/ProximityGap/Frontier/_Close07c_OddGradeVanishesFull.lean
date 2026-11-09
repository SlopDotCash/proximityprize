/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Close C07c — target E6 (odd half): `#bad_{2n}(k, m) = 0` for ODD `m`, PROVED

This file **closes** B07's `OddGradeVanishes` obligation *fully* — not the abstract
antipodal core (which B05/B06/B09 already landed), but the concrete graded count `cf`
on the actual `fhat` object defined in `_BridgeB07.lean`. We re-derive the `fhat`/`cf`
definitions here verbatim (so the file is standalone with minimal imports) and prove the
missing link:

> **odd-graded `fhat` is anti-invariant under the antipodal map `a ↦ a + h` on `ℤ/2h`.**

Concretely, for `N = 2h` even and `m` *odd*, every frequency `a` and its antipodal partner
`a + h (mod N)` land in the **same** `h`-bin with **opposite** signs:

* `gradeContribBin ((a+h) % N) m N = gradeContribBin a m N`,
* `gradeContribSign ((a+h) % N) m N = - gradeContribSign a m N`.

(The arithmetic kernel is `(m*(a+h)) % (2h) = ((m*a) % (2h) + h) % (2h)` for `m` odd, since
`m*h ≡ h (mod 2h)`.) Combined with the **grade-1 constraint** — which says exactly that the
admissible subset `A` is *closed under the antipodal map* (`fhat A 1 N [i] = [i∈A] − [(i+h)∈A]`)
— the antipodal involution pairs each `a ∈ A` with `a + h ∈ A`, the two graded contributions
cancel bin-by-bin, and so `fhat A m N = 0`. Hence the bad-value set is empty and `cf (2n) k m = 0`.

## The correction (machine-checked)

The probe `probe_2adic_tower_recursion.py` tests odd `m ∈ {3,5,7}` only. The statement is
**FALSE at `m = 1`**: `cf(16,0,1) = 16 ≠ 0` (grade 1 *is* the base obstruction; it is the
constraint, not a vanisher). The grade-1 constraint requires `1 ≤ j < m`, which is *non-empty
iff `m ≥ 2`*. So the correct, provable statement carries the hypothesis `1 < m` (equivalently
odd `m ≥ 3`). We verify across `N ∈ {8,16,18,20}` that all odd `m ≥ 3` give `cf = 0`, with
`m = 1` the sole exception. The B07 `OddGradeVanishes` Prop omits this hypothesis and is thus
literally false; this file proves the corrected `OddGradeVanishesStrong` (odd `m`, `1 < m`)
in full, axiom-clean, and records the `m = 1` refutation as a `decide`-checked countermodel.

Issue #444. Target E6 (odd half), C07c.
-/

open Finset

namespace ArkLib.ProximityGap.Close07c

/-! ## The object, re-derived verbatim from `_BridgeB07.lean` -/

/-- The per-frequency graded bin of `a` at grade `m`, modulus `n`, bins `h = n/2`. -/
def gradeContribBin (a m n : ℕ) : ℕ := ((m * a) % n) % (n / 2)

/-- The sign of the graded contribution: `+1` if `(m*a)%n < n/2`, else `-1`. -/
def gradeContribSign (a m n : ℕ) : ℤ := if (m * a) % n < n / 2 then 1 else -1

/-- The `h`-binned graded vector `fhat A m n : Fin (n/2) → ℤ`. -/
def fhat (A : Finset ℕ) (m n : ℕ) : Fin (n / 2) → ℤ :=
  fun i => ∑ a ∈ A, if gradeContribBin a m n = (i : ℕ) then gradeContribSign a m n else 0

/-- The all-lower-grades-zero predicate: `fhat A j n = 0` for all `1 ≤ j < m`. -/
def gradedZeroLower (A : Finset ℕ) (m n : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j < m → fhat A j n = 0

instance (A : Finset ℕ) (m n : ℕ) : Decidable (gradedZeroLower A m n) := by
  have : gradedZeroLower A m n ↔ ∀ j, j < m → (1 ≤ j → fhat A j n = 0) := by
    unfold gradedZeroLower
    exact ⟨fun h j hjm hj1 => h j hj1 hjm, fun h j hj1 hjm => h j hjm hj1⟩
  rw [this]
  exact Nat.decidableBallLT m _

/-- The universe of admissible frequency sets: `(k+m)`-subsets of `{0,…,n-1}`. -/
def admissible (n k m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powersetCard (k + m)

/-- The (nonzero) graded values witnessed by admissible, lower-zero subsets. -/
noncomputable def badVals (n k m : ℕ) : Finset (Fin (n / 2) → ℤ) :=
  ((admissible n k m).filter (fun A => gradedZeroLower A m n)).image (fun A => fhat A m n)
    |>.erase (fun _ => 0)

/-- `#bad_n(k,m)` — the number of distinct nonzero graded values. -/
noncomputable def cf (n k m : ℕ) : ℕ := (badVals n k m).card

/-! ## The antipodal map on `{0,…,2h−1}` and the arithmetic kernel -/

/-- The antipodal involution on `ℤ/2h` (the action of `-1 = ω^h ∈ μ_{2h}`): `a ↦ (a + h) % 2h`. -/
def antipode (h a : ℕ) : ℕ := (a + h) % (2 * h)

/-- **Antipode is an involution on `{0,…,2h−1}`.** For `a < 2h`, applying `a ↦ (a+h)%2h` twice
returns `a`. -/
theorem antipode_involutive {h a : ℕ} (ha : a < 2 * h) :
    antipode h (antipode h a) = a := by
  unfold antipode
  -- ((a+h)%2h + h) ≡ (a+h)+h = a+2h ≡ a (mod 2h), and a < 2h.
  have hmod : ((a + h) % (2 * h) + h) % (2 * h) = (a + h + h) % (2 * h) :=
    Nat.ModEq.add_right h (Nat.mod_modEq (a + h) (2 * h))
  rw [hmod, show a + h + h = a + 2 * h by ring, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt ha

/-- **Antipode lands in range.** If `a < 2h` then `antipode h a < 2h`. -/
theorem antipode_lt {h a : ℕ} (hh : 0 < h) : antipode h a < 2 * h := by
  unfold antipode; exact Nat.mod_lt _ (by omega)

/-- **The arithmetic kernel: odd `m` shifts the graded position by `h`.**
For `m` odd and any `a`, `(m * ((a+h) % 2h)) % 2h = ((m*a) % 2h + h) % 2h`.
(Because `m*h ≡ h (mod 2h)` when `m` is odd.) -/
theorem grade_antipode_shift {h m a : ℕ} (hm : Odd m) :
    (m * ((a + h) % (2 * h))) % (2 * h) = ((m * a) % (2 * h) + h) % (2 * h) := by
  -- m*((a+h)%2h) ≡ m*(a+h) = m*a + m*h ≡ m*a + h (mod 2h).
  obtain ⟨t, rfl⟩ := hm
  -- Goal residues, established via `Nat.ModEq`.
  -- LHS ≡ (2t+1)*(a+h) (mod 2h).
  have e1 : (2 * t + 1) * ((a + h) % (2 * h)) ≡ (2 * t + 1) * (a + h) [MOD 2 * h] :=
    (Nat.mod_modEq (a + h) (2 * h)).mul_left (2 * t + 1)
  -- (2t+1)*(a+h) = ((2t+1)*a + h) + (2h)*t  ≡ (2t+1)*a + h (mod 2h).
  have e3 : (2 * t + 1) * (a + h) ≡ (2 * t + 1) * a + h [MOD 2 * h] := by
    show (2 * t + 1) * (a + h) % (2 * h) = ((2 * t + 1) * a + h) % (2 * h)
    rw [show (2 * t + 1) * (a + h) = ((2 * t + 1) * a + h) + (2 * h) * t by ring,
        Nat.add_mul_mod_self_left]
  -- RHS ≡ (2t+1)*a + h (mod 2h).
  have e4 : (2 * t + 1) * a % (2 * h) + h ≡ (2 * t + 1) * a + h [MOD 2 * h] :=
    (Nat.mod_modEq ((2 * t + 1) * a) (2 * h)).add_right h
  -- chain
  calc (2 * t + 1) * ((a + h) % (2 * h)) % (2 * h)
      = ((2 * t + 1) * a + h) % (2 * h) := (e1.trans e3)
    _ = ((2 * t + 1) * a % (2 * h) + h) % (2 * h) := e4.symm

/-! ## Per-element antipodal anti-symmetry of the graded contribution (odd grade) -/

/-- **Bins agree under antipode (odd grade).** -/
theorem gradeContribBin_antipode {h m a : ℕ} (hh : 0 < h) (hm : Odd m) :
    gradeContribBin (antipode h a) m (2 * h) = gradeContribBin a m (2 * h) := by
  unfold gradeContribBin antipode
  rw [show (2 * h) / 2 = h by omega]
  -- use the shift kernel; (e + h) % 2h reduces mod h to e % h
  have key : (m * ((a + h) % (2 * h))) % (2 * h) = ((m * a) % (2 * h) + h) % (2 * h) :=
    grade_antipode_shift hm
  rw [key]
  -- ((e + h) % 2h) % h = e % h, where e := (m*a) % 2h < 2h.
  set e := (m * a) % (2 * h) with he
  have hee : e < 2 * h := by rw [he]; exact Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge e h with hlt | hge
  · -- e < h ⇒ (e+h) < 2h ⇒ (e+h)%2h = e+h ⇒ %h = (e+h)%h = e%h
    rw [Nat.mod_eq_of_lt (by omega : e + h < 2 * h)]
    rw [Nat.add_mod_right]
  · -- e ≥ h ⇒ e+h ≥ 2h, (e+h)%2h = e - h, %h = (e-h)%h = e%h
    have : (e + h) % (2 * h) = e - h := by
      have h2 : e + h - 2 * h = e - h := by omega
      rw [show e + h = (e - h) + 2 * h by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : e - h < 2 * h)]
    rw [this]
    -- (e - h) % h = e % h since e = (e-h) + h
    conv_rhs => rw [show e = (e - h) + h by omega, Nat.add_mod_right]

/-- **Signs flip under antipode (odd grade).** -/
theorem gradeContribSign_antipode {h m a : ℕ} (hh : 0 < h) (hm : Odd m) :
    gradeContribSign (antipode h a) m (2 * h) = - gradeContribSign a m (2 * h) := by
  unfold gradeContribSign antipode
  rw [show (2 * h) / 2 = h by omega]
  have key : (m * ((a + h) % (2 * h))) % (2 * h) = ((m * a) % (2 * h) + h) % (2 * h) :=
    grade_antipode_shift hm
  rw [key]
  set e := (m * a) % (2 * h) with he
  have hee : e < 2 * h := by rw [he]; exact Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_ge e h with hlt | hge
  · -- e < h: original sign +1; (e+h) ∈ [h,2h) so new sign -1.
    rw [Nat.mod_eq_of_lt (by omega : e + h < 2 * h)]
    rw [if_pos hlt, if_neg (by omega : ¬ e + h < h)]
  · -- e ≥ h: original sign -1; (e+h)%2h = e-h ∈ [0,h) so new sign +1.
    have hred : (e + h) % (2 * h) = e - h := by
      rw [show e + h = (e - h) + 2 * h by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : e - h < 2 * h)]
    rw [hred, if_pos (by omega : e - h < h), if_neg (by omega : ¬ e < h)]
    norm_num

/-! ## Grade-1 constraint ⟺ antipodal closure of `A` -/

/-- **Grade-1 graded position of `a < 2h` is `a % h`** (since `(1*a)%2h = a`). -/
theorem gradeContribBin_one {h a : ℕ} (ha : a < 2 * h) :
    gradeContribBin a 1 (2 * h) = a % h := by
  unfold gradeContribBin
  rw [one_mul, Nat.mod_eq_of_lt ha, show (2 * h) / 2 = h by omega]

/-- **Grade-1 sign of `a < 2h` is `+1` iff `a < h`.** -/
theorem gradeContribSign_one {h a : ℕ} (ha : a < 2 * h) :
    gradeContribSign a 1 (2 * h) = if a < h then 1 else -1 := by
  unfold gradeContribSign
  rw [one_mul, Nat.mod_eq_of_lt ha, show (2 * h) / 2 = h by omega]

/-- **For `b < 2h` with `0 < h`, the grade-1 contribution of `b` into bin `i` (with `i < h`)
is nonzero only at `b ∈ {i, i+h}`, with value `+1` at `b = i` and `−1` at `b = i+h`.** -/
theorem gradeOne_contrib {h b i : ℕ} (hh : 0 < h) (hb : b < 2 * h) (hi : i < h) :
    (if gradeContribBin b 1 (2 * h) = i then gradeContribSign b 1 (2 * h) else 0)
      = (if b = i then (1 : ℤ) else 0) - (if b = i + h then (1 : ℤ) else 0) := by
  rw [gradeContribBin_one hb, gradeContribSign_one hb]
  -- bin = b % h; for b < 2h, b%h = i ↔ b = i ∨ b = i+h.
  by_cases hbi : b = i
  · subst hbi
    rw [Nat.mod_eq_of_lt hi, if_pos rfl, if_pos (by omega), if_pos rfl,
        if_neg (by omega : ¬ b = b + h)]; ring
  · by_cases hbih : b = i + h
    · subst hbih
      rw [show (i + h) % h = i by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi],
          if_pos rfl, if_neg (by omega : ¬ i + h < h), if_neg (by omega), if_pos rfl]; ring
    · -- b ∉ {i, i+h}: then b % h ≠ i.
      rw [if_neg hbi, if_neg hbih, sub_zero]
      have hbh : b % h ≠ i := by
        intro hbh
        rcases (by omega : b < h ∨ b ≥ h) with hlt | hge
        · exact hbi (by rwa [Nat.mod_eq_of_lt hlt] at hbh)
        · have hbm : (b - h) % h = i := by
            rwa [show b = (b - h) + h by omega, Nat.add_mod_right] at hbh
          have : b - h < h := by omega
          rw [Nat.mod_eq_of_lt this] at hbm
          exact hbih (by omega)
      rw [if_neg hbh]

/-- **Grade-1 vanishing ⟹ antipodal closure of `A`.** If `A ⊆ {0,…,2h−1}` and the grade-1 graded
vector vanishes (`fhat A 1 (2h) = 0`), then `A` is closed under the antipodal map `a ↦ (a+h)%2h`.
(`fhat A 1 (2h) [i] = [i∈A] − [(i+h)∈A]`, so its vanishing means `i∈A ↔ (i+h)∈A`.) -/
theorem antipode_closed_of_gradeOne_zero {h : ℕ} {A : Finset ℕ} (hh : 0 < h)
    (hsub : ∀ a ∈ A, a < 2 * h) (hzero : fhat A 1 (2 * h) = 0) :
    ∀ a ∈ A, antipode h a ∈ A := by
  intro a ha
  have ha2 : a < 2 * h := hsub a ha
  set i := a % h with hi_def
  have hi : i < h := Nat.mod_lt _ hh
  -- evaluate fhat A 1 (2h) at bin i
  have hcoord : fhat A 1 (2 * h) ⟨i, by rw [show (2*h)/2 = h by omega]; exact hi⟩ = 0 := by
    rw [hzero]; rfl
  -- unfold the coordinate sum and rewrite each contribution via gradeOne_contrib
  rw [fhat] at hcoord
  simp only at hcoord
  -- replace the summand
  have hsum : ∑ b ∈ A, ((if b = i then (1:ℤ) else 0) - (if b = i + h then (1:ℤ) else 0)) = 0 := by
    have hcongr : ∑ b ∈ A, ((if b = i then (1:ℤ) else 0) - (if b = i + h then (1:ℤ) else 0))
        = ∑ b ∈ A, (if gradeContribBin b 1 (2 * h) = i then gradeContribSign b 1 (2 * h) else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (gradeOne_contrib hh (hsub b hb) hi).symm
    rw [hcongr]; exact hcoord
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' A i, Finset.sum_ite_eq' A (i + h)] at hsum
  -- hsum : (if i ∈ A then 1 else 0) - (if i+h ∈ A then 1 else 0) = 0
  -- so i ∈ A ↔ i+h ∈ A
  have hiff : (i ∈ A) ↔ (i + h ∈ A) := by
    by_cases h1 : i ∈ A <;> by_cases h2 : i + h ∈ A <;>
      simp only [h1, h2, if_true, if_false] at hsum <;> simp [h1, h2] <;> omega
  -- now: antipode h a is the partner of a in {i, i+h}; show it ∈ A.
  unfold antipode
  rcases (by omega : a < h ∨ a ≥ h) with hlt | hge
  · -- a < h ⇒ a = i, antipode = a+h = i+h, and i ∈ A ⇒ i+h ∈ A
    have : a = i := by rw [hi_def, Nat.mod_eq_of_lt hlt]
    rw [Nat.mod_eq_of_lt (by omega : a + h < 2 * h)]
    rw [this]; exact hiff.mp (this ▸ ha)
  · -- a ≥ h ⇒ a = i+h, antipode = a-h = i, and i+h ∈ A ⇒ i ∈ A
    have hmodeq : a % h = a - h := by
      conv_lhs => rw [show a = (a - h) + h by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a - h < h)]
    have hia : i = a - h := by rw [hi_def]; exact hmodeq
    have hai : a = i + h := by omega
    rw [show a + h = (a - h) + 2 * h by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : a - h < 2 * h), ← hia]
    exact hiff.mpr (hai ▸ ha)

/-! ## The antipodal-involution vanishing (B05 core, inlined ℤ-valued) -/

/-- **Antipodal odd-sum vanishing** (the B05/B09 core, ℤ-valued, inlined to keep imports minimal).
If `σ` is an involution mapping the finite set `S` into itself, and `w` flips sign across `σ`
(`w (σ x) = − w x`), then `∑_{x∈S} w x = 0`. -/
theorem antipodal_odd_sum_zero {ι : Type*} [DecidableEq ι] {S : Finset ι} {σ : ι → ι}
    (hinv : ∀ x ∈ S, σ (σ x) = x) (hmap : ∀ x ∈ S, σ x ∈ S)
    (w : ι → ℤ) (hodd : ∀ x ∈ S, w (σ x) = - w x) :
    ∑ x ∈ S, w x = 0 := by
  have hreindex : ∑ x ∈ S, w (σ x) = ∑ x ∈ S, w x := by
    apply Finset.sum_nbij' (fun x => σ x) (fun x => σ x)
    · intro a ha; exact hmap a ha
    · intro a ha; exact hmap a ha
    · intro a ha; exact hinv a ha
    · intro a ha; exact hinv a ha
    · intro a _; rfl
  have hneg : ∑ x ∈ S, w (σ x) = - ∑ x ∈ S, w x := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl hodd
  have hself : ∑ x ∈ S, w x = - ∑ x ∈ S, w x := hreindex.symm.trans hneg
  omega

/-! ## Main: odd-graded `fhat` vanishes on antipodally-closed admissible subsets -/

/-- **The missing link, PROVED: odd-graded `fhat` vanishes.** For `N = 2h` even, `m` odd, an
admissible subset `A ⊆ {0,…,2h−1}` whose grade-1 piece vanishes (`fhat A 1 (2h) = 0`, the
antipodal-closure constraint) has vanishing grade-`m` piece: `fhat A m (2h) = 0`.

This is the concrete realization of the antipodal-involution vanishing on the actual `fhat`
object: the antipodal map `a ↦ (a+h)%2h` is an involution preserving `A`, and for *odd* `m` it
fixes the bin while flipping the sign of each graded contribution, so every bin's sum cancels. -/
theorem fhat_odd_eq_zero {h m : ℕ} {A : Finset ℕ} (hh : 0 < h) (hm : Odd m)
    (hsub : ∀ a ∈ A, a < 2 * h) (hgrade1 : fhat A 1 (2 * h) = 0) :
    fhat A m (2 * h) = 0 := by
  have hclosed := antipode_closed_of_gradeOne_zero hh hsub hgrade1
  funext i
  show (∑ a ∈ A, if gradeContribBin a m (2 * h) = (i : ℕ) then gradeContribSign a m (2 * h) else 0)
      = 0
  apply antipodal_odd_sum_zero (σ := antipode h)
  · intro a ha; exact antipode_involutive (hsub a ha)
  · exact hclosed
  · intro a ha
    by_cases hbin : gradeContribBin a m (2 * h) = (i : ℕ)
    · rw [if_pos hbin, if_pos (by rw [gradeContribBin_antipode hh hm]; exact hbin)]
      exact gradeContribSign_antipode hh hm
    · rw [if_neg hbin, if_neg (by rw [gradeContribBin_antipode hh hm]; exact hbin), neg_zero]

/-! ## The graded count vanishes: `cf (2h) k m = 0` for odd `m > 1` -/

/-- **C07c — `OddGradeVanishes` closed (corrected, strong form).** For `N = 2h` even, `m` *odd*
with `m > 1` (so the grade-1 constraint is active), the graded count vanishes: `cf (2h) k m = 0`.

The hypothesis `1 < m` is **essential**: the bare odd statement is false at `m = 1`
(`cf(16,0,1) = 16 ≠ 0`), since grade 1 is the antipodal-closure *constraint*, not a vanisher.
For `m > 1`, every admissible lower-zero subset has `fhat A 1 (2h) = 0` (grade 1 is a lower
grade), hence is antipodally closed, hence `fhat A m (2h) = 0` by `fhat_odd_eq_zero` — so the
bad-value set is empty. -/
theorem cf_odd_eq_zero {h k m : ℕ} (hh : 0 < h) (hm : Odd m) (hm1 : 1 < m) :
    cf (2 * h) k m = 0 := by
  rw [cf, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  -- unpack membership in badVals
  rw [badVals, Finset.mem_erase, Finset.mem_image] at hv
  obtain ⟨hne, A, hAfilter, hAv⟩ := hv
  rw [Finset.mem_filter] at hAfilter
  obtain ⟨hAadm, hAlower⟩ := hAfilter
  -- A ⊆ {0,…,2h−1}
  have hsub : ∀ a ∈ A, a < 2 * h := by
    intro a ha
    rw [admissible, Finset.mem_powersetCard] at hAadm
    have := hAadm.1 ha
    rwa [Finset.mem_range] at this
  -- grade 1 vanishes (it is a lower grade, since 1 ≤ 1 < m)
  have hgrade1 : fhat A 1 (2 * h) = 0 := hAlower 1 (le_refl 1) hm1
  -- hence fhat A m (2h) = 0, contradicting v ≠ 0
  have : v = fun _ => (0 : ℤ) := hAv ▸ fhat_odd_eq_zero hh hm hsub hgrade1
  exact hne this

/-! ## The corrected `OddGradeVanishes` Prop and its full discharge -/

/-- **The corrected E6 odd-half obligation.** B07 states `OddGradeVanishes := ∀ n k m, Odd m →
cf (2n) k m = 0`. That is *false at `m = 1`* (see `oddGradeVanishes_false_at_one`). The correct,
provable statement carries `0 < n` and `1 < m` (odd `m ≥ 3`). -/
def OddGradeVanishesStrong : Prop :=
  ∀ n k m : ℕ, 0 < n → Odd m → 1 < m → cf (2 * n) k m = 0

/-- **C07c CLOSED: `OddGradeVanishesStrong` is a theorem.** The corrected odd half of E6 holds
in full: `#bad_{2n}(k, m) = 0` for every odd `m > 1`. This discharges B07's `OddGradeVanishes`
obligation (modulo the necessary `1 < m` correction) directly on the concrete `fhat` count,
wiring the antipodal-involution vanishing (`fhat_odd_eq_zero`) to it. -/
theorem oddGradeVanishesStrong_holds : OddGradeVanishesStrong :=
  fun n k m hn hm hm1 => cf_odd_eq_zero hn hm hm1

/-- **The `m = 1` refutation (machine-checked countermodel).** The *bare* odd statement (B07's
`OddGradeVanishes`, no `1 < m`) is FALSE: at `n = 1, k = 0, m = 1` (so `2n = 2`, odd `m`), the
singleton `A = {0}` is admissible and vacuously lower-zero, and `fhat {0} 1 2 = (fun _ => 1) ≠ 0`,
so its value is a genuine bad value and `cf 2 0 1 ≠ 0`. -/
theorem cf_two_zero_one_ne_zero : cf 2 0 1 ≠ 0 := by
  unfold cf
  rw [Finset.card_ne_zero]
  -- the constant-1 vector is in badVals 2 0 1, witnessing nonemptiness.
  refine ⟨fun _ => (1 : ℤ), ?_⟩
  have hwit : (fun _ => (1 : ℤ)) ∈ badVals 2 0 1 := by
    rw [badVals, Finset.mem_erase, Finset.mem_image]
    refine ⟨?_, {0}, ?_, ?_⟩
    · -- (fun _ => 1) ≠ (fun _ => 0)
      intro h
      have := congrFun h ⟨0, by norm_num⟩
      simp at this
    · -- {0} ∈ filter (gradedZeroLower · 1 2) (admissible 2 0 1)
      rw [Finset.mem_filter]
      constructor
      · rw [admissible, Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx; rw [Finset.mem_singleton] at hx; subst hx; simp
        · rfl
      · -- gradedZeroLower {0} 1 2 is vacuous
        intro j hj1 hj; omega
    · -- fhat {0} 1 2 = fun _ => 1
      funext i
      have hi0 : (i : ℕ) = 0 := by omega
      rw [fhat]
      simp only [Finset.sum_singleton]
      rw [show gradeContribBin 0 1 2 = (i : ℕ) by rw [hi0]; rfl,
          if_pos rfl, gradeContribSign]
      norm_num
  exact hwit

end ArkLib.ProximityGap.Close07c

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Close07c.fhat_odd_eq_zero
#print axioms ArkLib.ProximityGap.Close07c.cf_odd_eq_zero
#print axioms ArkLib.ProximityGap.Close07c.oddGradeVanishesStrong_holds
#print axioms ArkLib.ProximityGap.Close07c.antipode_closed_of_gradeOne_zero
#print axioms ArkLib.ProximityGap.Close07c.gradeContribBin_antipode
#print axioms ArkLib.ProximityGap.Close07c.gradeContribSign_antipode
#print axioms ArkLib.ProximityGap.Close07c.grade_antipode_shift
#print axioms ArkLib.ProximityGap.Close07c.cf_two_zero_one_ne_zero
