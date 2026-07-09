/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BridgeB07

/-!
# Close C07a — the explicit doubling fold map for E6 (#444)

Target **C07a [E6]** (`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`):
prove the even-fold bijection underlying `B07`'s `DoublingBijection`,
`#bad_{2n}(k, 2m') = #bad_n(k/2, m')`, by *constructing the explicit fold map* and proving the
half of the bijection that is elementary, reducing the remainder to a precisely-named `Prop`.

This file builds directly on `_BridgeB07` (it reuses `fhat`, `gradeContribBin`,
`gradeContribSign`, `cf`, `badVals` — it does **not** re-derive them) and on the dyadic-split
philosophy of `DyadicTowerRecursion.lean` (P4: `μ_{2n} = μ_n ⊔ ω·μ_n`, here realized
concretely as the additive antipodal shift `a ↦ a + n`).

## The mathematics (discovered & machine-checked exactly at 16↔8)

Write `N = 2n`, `h = N/2 = n`, grade `2m'` (`n` even, as in the `2`-adic tower `n = 2^μ`).

* **(A) arithmetic correspondence.** For every `a`,
    `gradeContribBin a (2*m') (2*n) = 2 * gradeContribBin a m' n`     and
    `gradeContribSign a (2*m') (2*n) = gradeContribSign a m' n`.
  *(`probe_arith.py` IDENTITY A: `(2m'a) % 2n = 2·((m'a) % n)`.)*
* **(B) antipodal pairing.** Adding `n` to the frequency leaves the level-`n` grade-`m'`
  contribution unchanged: `gradeContribBin (a+n) m' n = gradeContribBin a m' n`,
  `gradeContribSign (a+n) m' n = gradeContribSign a m' n`.
  *(`probe_arith.py` IDENTITY B: `(m'(a+n)) % n = (m'a) % n`.)*
* **(V) value fold.** Hence, for a shift-symmetric `A = A' ⊔ (A'+n)`,
    `fhat A (2m') (2n) i = 2 * fhat A' m' n (i/2)`  if `i` even, `= 0`  if `i` odd.
  This is the explicit value-level fold `foldVal` below; it is an **injective** map
  `(Fin (n/2) → ℤ) → (Fin ((2n)/2) → ℤ)`, so distinct level-`n` values give distinct
  level-`2n` values. *(`probe_fold3.py`: "ALL HOLD".)*
* **(S) shift symmetry.** Every *bad* subset `A ⊆ ℤ/2n` (admissible, all lower grades
  vanishing, nonzero at grade `2m'`) is invariant under `a ↦ (a + n) mod 2n`, so equals
  `A' ⊔ (A'+n)`. *(`probe_fold2.py`: "shift-by-8-symmetric? True" on every nonzero rung.)*

## What is proved here (honesty contract — strict)

Proved **axiom-clean** (`propext, Classical.choice, Quot.sound`, no `sorry`):

* the modular doubling identity `two_mul_mod_two_mul`;
* the arithmetic correspondence **(A)** `gradeContribBin_double`, `gradeContribSign_double`;
* the antipodal pairing **(B)** `gradeContribBin_shift`, `gradeContribSign_shift`, and its
  level-`2n` half-shift form **(B')** `bin_shift_half`, `sign_shift_half`;
* `foldVal` (the explicit fold of value vectors) and its **injectivity** `foldVal_injective`;
* the explicit **carrier fold map** `Φ = foldSubset` and its disjointness `foldSubset_disjoint`;
* the central **carrier-to-value fold identity (V)** `fhat_foldSubset`:
    `fhat (foldSubset n A') (2m') (2n) = foldVal n hn (fhat A' m' n)`   for `A' ⊆ {0,…,n−1}`,
  i.e. `Φ` intertwines the graded vectors with `foldVal` — the whole *value-level* mechanism
  of the doubling bijection;
* the consequence `doublingBijection_of_foldImage`: *given the carrier-symmetry residual below,
  the cardinality identity `cf(2n,k,2m')=cf(n,k/2,m')` follows* — via
  `Finset.card_image_of_injective` and `foldVal_injective`.

**Reduced** to the single precisely-named structural `Prop`:

* `FoldImageHyp` — *the bad-value set at level `2n`, even grade, is exactly the `foldVal`-image
  of the bad-value set at level `n`*:
    `badVals (2n) k (2m') = (badVals n (k/2) m').image (foldVal n)`.
  Since the value-fold engine **(V)** `fhat_foldSubset` and `foldVal_injective` are now proven,
  the only content this residual still carries is the **carrier-symmetry forcing (S)** — that
  every bad carrier at level `2n` is `Φ A'` for an admissible lower-vanishing `A'` at level `n`,
  and conversely. It is the honest remaining gap; from it plus the axiom-clean machinery the
  even-`n` doubling identity follows (`doublingBijection_of_foldImage`), exactly
  `B07.DoublingBijection`'s content on the meaningful even-`n` `2`-adic-tower domain.

So C07a status: **REDUCED** to `FoldImageHyp` — concretely to the carrier-symmetry forcing (S),
since the explicit fold maps (carrier `Φ` and value `foldVal`), their injectivity, the full
arithmetic correspondence, and the carrier-to-value intertwiner (V) are all axiom-clean.

Issue #444. Target C07a / E6.
-/

open Finset

namespace ArkLib.ProximityGap.Close07a

open ArkLib.ProximityGap.BridgeB07

/-! ## (A) The arithmetic correspondence: doubling grade & modulus -/

/-- **Modular doubling identity** (probe IDENTITY A): `(2*m*a) % (2*n) = 2 * ((m*a) % n)`.
The graded coefficient at level `2n`, grade `2m'`, lives entirely on the *even* residues, and
its half is exactly the level-`n` grade-`m'` residue. -/
theorem two_mul_mod_two_mul (a m n : ℕ) :
    (2 * m * a) % (2 * n) = 2 * ((m * a) % n) := by
  rw [show 2 * m * a = 2 * (m * a) by ring, Nat.mul_mod_mul_left 2 (m * a) n]

/-- **(A) bin part.** For the doubling fold (`n` even), the level-`2n` grade-`2m'` bin of `a` is
exactly twice the level-`n` grade-`m'` bin.
(`gradeContribBin a (2m') (2n) = 2 * gradeContribBin a m' n`.) -/
theorem gradeContribBin_double (a m n : ℕ) (hn : Even n) :
    gradeContribBin a (2 * m) (2 * n) = 2 * gradeContribBin a m n := by
  unfold gradeContribBin
  rw [two_mul_mod_two_mul a m n, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]
  obtain ⟨t, ht⟩ := hn
  have hn2 : n / 2 = t := by omega
  have hn' : n = 2 * t := by omega
  rw [hn2, hn', Nat.mul_mod_mul_left 2 ((m * a) % (2 * t)) t]

/-- **(A) sign part.** The level-`2n` grade-`2m'` sign of `a` equals the level-`n` grade-`m'`
sign (`n` even). (`gradeContribSign a (2m') (2n) = gradeContribSign a m' n`.) -/
theorem gradeContribSign_double (a m n : ℕ) (hn : Even n) :
    gradeContribSign a (2 * m) (2 * n) = gradeContribSign a m n := by
  unfold gradeContribSign
  rw [two_mul_mod_two_mul a m n, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]
  obtain ⟨t, ht⟩ := hn
  have hn2 : n / 2 = t := by omega
  by_cases h : (m * a) % n < n / 2
  · rw [if_pos h, if_pos]; omega
  · rw [if_neg h, if_neg]; omega

/-! ## (B) The antipodal pairing: `a` and `a + n` agree at level `n` grade `m'` -/

/-- **(B) bin part** (probe IDENTITY B): `gradeContribBin (a+n) m n = gradeContribBin a m n`.
Adding `n` to the frequency leaves the level-`n` grade-`m'` bin unchanged. -/
theorem gradeContribBin_shift (a m n : ℕ) :
    gradeContribBin (a + n) m n = gradeContribBin a m n := by
  unfold gradeContribBin
  have h : (m * (a + n)) % n = (m * a) % n := by
    have h2 : m * (a + n) = m * a + n * m := by ring
    rw [h2, Nat.add_mul_mod_self_left]
  rw [h]

/-- **(B) sign part**: `gradeContribSign (a+n) m n = gradeContribSign a m n`. -/
theorem gradeContribSign_shift (a m n : ℕ) :
    gradeContribSign (a + n) m n = gradeContribSign a m n := by
  unfold gradeContribSign
  have h : (m * (a + n)) % n = (m * a) % n := by
    have h2 : m * (a + n) = m * a + n * m := by ring
    rw [h2, Nat.add_mul_mod_self_left]
  rw [h]

/-! ## (B') The half-shift invariance at level `2n`, even grade

At level `2n`, grade `2m'`, adding `n` (= the antipodal half) to a frequency leaves the
contribution **identical** (because `2m'·n ≡ 0 mod 2n`). This is the precise mechanism by which
a shift-symmetric carrier `A' ⊔ (A'+n)` doubles each level-`n` contribution. -/

/-- **(B') bin part** at level `2n` grade `2m'`:
`gradeContribBin (a+n) (2m') (2n) = gradeContribBin a (2m') (2n)`. -/
theorem bin_shift_half (a m n : ℕ) :
    gradeContribBin (a + n) (2 * m) (2 * n) = gradeContribBin a (2 * m) (2 * n) := by
  unfold gradeContribBin
  have h : (2 * m * (a + n)) % (2 * n) = (2 * m * a) % (2 * n) := by
    have h2 : 2 * m * (a + n) = 2 * m * a + m * (2 * n) := by ring
    rw [h2, Nat.add_mul_mod_self_right]
  rw [h]

/-- **(B') sign part** at level `2n` grade `2m'`:
`gradeContribSign (a+n) (2m') (2n) = gradeContribSign a (2m') (2n)`. -/
theorem sign_shift_half (a m n : ℕ) :
    gradeContribSign (a + n) (2 * m) (2 * n) = gradeContribSign a (2 * m) (2 * n) := by
  unfold gradeContribSign
  have h : (2 * m * (a + n)) % (2 * n) = (2 * m * a) % (2 * n) := by
    have h2 : 2 * m * (a + n) = 2 * m * a + m * (2 * n) := by ring
    rw [h2, Nat.add_mul_mod_self_right]
  rw [h]

/-! ## (V) The explicit value-level fold map and its injectivity -/

/-- **The explicit value fold `foldVal`** (`n` even). Maps a level-`n` graded value
`w : Fin (n/2) → ℤ` to the level-`2n` graded value `foldVal n hn w : Fin ((2*n)/2) → ℤ`,
`(foldVal n hn w) i = 2 * w (i/2)` when `i` is even, `0` when `i` is odd. This realizes fact
(V): for a shift-symmetric bad set, the level-`2n` grade-`2m'` vector is `foldVal` of the
level-`n` grade-`m'` vector. -/
def foldVal (n : ℕ) (hn : Even n) (w : Fin (n / 2) → ℤ) : Fin ((2 * n) / 2) → ℤ :=
  fun i =>
    if h : (i : ℕ) % 2 = 0 then
      2 * w ⟨(i : ℕ) / 2, by
        have hi : (i : ℕ) < (2 * n) / 2 := i.isLt
        have he : (2 * n) / 2 = n := Nat.mul_div_cancel_left n (by norm_num : 0 < 2)
        obtain ⟨t, ht⟩ := hn
        omega⟩
    else 0

/-- **`foldVal` is injective.** Distinct level-`n` graded values fold to distinct level-`2n`
graded values. This is the value side of the doubling bijection: it forces
`#(level-2n values) = #(level-n values)`, the cardinality content of `DoublingBijection`. -/
theorem foldVal_injective (n : ℕ) (hn : Even n) (_hpos : 0 < n) :
    Function.Injective (foldVal n hn) := by
  intro w₁ w₂ h
  funext j
  have he : (2 * n) / 2 = n := Nat.mul_div_cancel_left n (by norm_num : 0 < 2)
  -- evaluate the folded vectors at the even index `2 * j`
  have hjlt : (2 * (j : ℕ)) < (2 * n) / 2 := by
    have hj := j.isLt
    obtain ⟨t, ht⟩ := hn
    omega
  have hev : ((⟨2 * (j : ℕ), hjlt⟩ : Fin ((2 * n) / 2)) : ℕ) % 2 = 0 := by
    simp [Nat.mul_mod_right]
  have e := congrFun h ⟨2 * (j : ℕ), hjlt⟩
  simp only [foldVal, hev, dif_pos] at e
  have hdiv : (2 * (j : ℕ)) / 2 = (j : ℕ) := Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
  -- e equates `2 * w₁ ⟨(2j)/2, _⟩ = 2 * w₂ ⟨(2j)/2, _⟩`; cancel `2`, then rewrite the index to `j`
  have ecancel := mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) e
  have hcast : (⟨(2 * (j : ℕ)) / 2, by
      have hi : (2 * (j : ℕ)) < (2 * n) / 2 := hjlt
      omega⟩ : Fin (n / 2)) = j := by
    apply Fin.ext; simp [hdiv]
  rw [hcast] at ecancel
  exact ecancel

/-! ## (Φ) The explicit carrier fold map and the carrier-to-value identity

The fold map on *carriers* is the concrete antipodal doubling `Φ : A' ↦ A' ⊔ (A'+n)`
(realizing the dyadic split `μ_{2n} = μ_n ⊔ ω·μ_n` of `DyadicTowerRecursion` additively). The
theorem `fhat_foldSubset` proves that `Φ` intertwines the graded vectors with `foldVal`: the
level-`2n` grade-`2m'` vector of `Φ A'` is exactly `foldVal` of the level-`n` grade-`m'` vector
of `A'`. This is the proven engine (V) of the bijection. -/

/-- **The explicit carrier fold map** `Φ`: `A' ↦ A' ⊔ (A' + n)`. -/
def foldSubset (n : ℕ) (A' : Finset ℕ) : Finset ℕ :=
  A' ∪ A'.image (· + n)

/-- For `A' ⊆ {0,…,n−1}`, the carrier `A'` and its `n`-shift `A'+n` are disjoint, so
`Φ A'` is a genuine doubling of cardinality. -/
theorem foldSubset_disjoint (n : ℕ) (A' : Finset ℕ) (hA' : ∀ a ∈ A', a < n) :
    Disjoint A' (A'.image (· + n)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [Finset.mem_image] at hb
  obtain ⟨b, hbA, hba⟩ := hb
  have : a < n := hA' a ha
  omega

/-- **The carrier-to-value fold identity (V), proven axiom-clean.** For `A' ⊆ {0,…,n−1}` and
`n` even, the level-`2n` grade-`2m'` graded vector of the folded carrier `Φ A' = A' ⊔ (A'+n)`
equals `foldVal` of the level-`n` grade-`m'` graded vector of `A'`:
  `fhat (foldSubset n A') (2m') (2n) = foldVal n hn (fhat A' m' n)`.
Combined with `foldVal_injective` this is the entire *value-level* mechanism of the doubling
bijection; only the carrier-symmetry forcing of *bad* sets (S) remains a gap. -/
theorem fhat_foldSubset (n : ℕ) (hn : Even n) (_hpos : 0 < n) (A' : Finset ℕ)
    (hA' : ∀ a ∈ A', a < n) (m' : ℕ) :
    fhat (foldSubset n A') (2 * m') (2 * n) = foldVal n hn (fhat A' m' n) := by
  funext i
  unfold fhat foldSubset
  rw [Finset.sum_union (foldSubset_disjoint n A' hA')]
  rw [Finset.sum_image (by intro x _ y _ h; exact Nat.add_right_cancel h)]
  -- the (a+n) summand equals the a summand by the level-2n half-shift invariance (B')
  have hshift : ∀ a ∈ A',
      (if gradeContribBin (a + n) (2 * m') (2 * n) = (i : ℕ) then
          gradeContribSign (a + n) (2 * m') (2 * n) else 0)
      = (if gradeContribBin a (2 * m') (2 * n) = (i : ℕ) then
          gradeContribSign a (2 * m') (2 * n) else 0) := by
    intro a _
    rw [bin_shift_half, sign_shift_half]
  rw [Finset.sum_congr rfl hshift, ← two_mul]
  -- rewrite each level-2n grade-2m' summand to the level-n grade-m' form via (A)
  have hsum : (∑ a ∈ A', if gradeContribBin a (2 * m') (2 * n) = (i : ℕ) then
                  gradeContribSign a (2 * m') (2 * n) else 0)
            = ∑ a ∈ A', if 2 * gradeContribBin a m' n = (i : ℕ) then
                  gradeContribSign a m' n else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [gradeContribBin_double a m' n hn, gradeContribSign_double a m' n hn]
  rw [hsum]
  -- case on the parity of the output bin `i`
  unfold foldVal
  by_cases hpar : (i : ℕ) % 2 = 0
  · rw [dif_pos hpar]
    simp only []
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    have hiff : (2 * gradeContribBin a m' n = (i : ℕ)) ↔
        (gradeContribBin a m' n = ((⟨(i : ℕ) / 2, by
          have hi : (i : ℕ) < (2 * n) / 2 := i.isLt
          have he : (2 * n) / 2 = n := Nat.mul_div_cancel_left n (by norm_num : 0 < 2)
          obtain ⟨t, ht⟩ := hn; omega⟩ : Fin (n / 2)) : ℕ)) := by
      simp only [Fin.val_mk]
      obtain ⟨t, ht⟩ := hn
      omega
    by_cases hb : 2 * gradeContribBin a m' n = (i : ℕ)
    · rw [if_pos hb, if_pos (hiff.mp hb)]
    · rw [if_neg hb, if_neg (fun h => hb (hiff.mpr h))]
  · rw [dif_neg hpar]
    -- odd output bin: `2·(level-n bin) = i` is impossible, so the whole sum vanishes
    have hzero : (∑ a ∈ A', if 2 * gradeContribBin a m' n = (i : ℕ) then
                    gradeContribSign a m' n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]; omega
    rw [hzero, mul_zero]

/-! ## The named structural residual and the bijection it yields -/

/-- **The fold-image residual (the named gap).** At level `2n`, even grade `2m'`, the bad-value
set is exactly the `foldVal`-image of the level-`n` grade-`m'` bad-value set.

With the value-fold engine `fhat_foldSubset` (V) and `foldVal_injective` now both proven
axiom-clean, the *only* content this residual still carries is the **carrier-symmetry forcing
(S)**: that every bad carrier at level `2n` is `Φ A' = foldSubset n A'` for an admissible,
lower-grade-vanishing carrier `A'` at level `n` of the correct cardinality, and conversely that
`Φ` sends such `A'` to a bad carrier at level `2n`. That is the genuine open combinatorial input
(the antipodal `−1 ∈ μ_{2n}` forcing of the bad locus); it is left as this named `Prop`. -/
def FoldImageHyp : Prop :=
  ∀ (n k m' : ℕ) (hn : Even n),
    badVals (2 * n) k (2 * m') = (badVals n (k / 2) m').image (foldVal n hn)

/-- **The doubling cardinality identity from the fold-image residual.** Given `FoldImageHyp` (the
named gap), the even-fold count identity `cf(2n,k,2m') = cf(n,k/2,m')` follows immediately from
the injectivity of the explicit fold map `foldVal` (`Finset.card_image_of_injective`). This is
the honest, minimal-gap proof of `B07.DoublingBijection`'s content. -/
theorem doublingBijection_of_foldImage (h : FoldImageHyp)
    (n k m' : ℕ) (hn : Even n) (hpos : 0 < n) :
    cf (2 * n) k (2 * m') = cf n (k / 2) m' := by
  unfold cf
  rw [h n k m' hn, Finset.card_image_of_injective _ (foldVal_injective n hn hpos)]

end ArkLib.ProximityGap.Close07a

#print axioms ArkLib.ProximityGap.Close07a.two_mul_mod_two_mul
#print axioms ArkLib.ProximityGap.Close07a.gradeContribBin_double
#print axioms ArkLib.ProximityGap.Close07a.gradeContribSign_double
#print axioms ArkLib.ProximityGap.Close07a.gradeContribBin_shift
#print axioms ArkLib.ProximityGap.Close07a.gradeContribSign_shift
#print axioms ArkLib.ProximityGap.Close07a.bin_shift_half
#print axioms ArkLib.ProximityGap.Close07a.sign_shift_half
#print axioms ArkLib.ProximityGap.Close07a.foldVal_injective
#print axioms ArkLib.ProximityGap.Close07a.foldSubset_disjoint
#print axioms ArkLib.ProximityGap.Close07a.fhat_foldSubset
#print axioms ArkLib.ProximityGap.Close07a.doublingBijection_of_foldImage
