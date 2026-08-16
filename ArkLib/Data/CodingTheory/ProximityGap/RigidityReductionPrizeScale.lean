/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadPrimeNormBound

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The rigidity reduction: char-`p` far-line incidence = char-`0` incidence at prize scale (#407)

This is the conceptual **keystone** of the δ* program's char-independence claim, stated and proved
*honestly* with the one unformalized link (the Galois-divisibility input) carried as a named
hypothesis.

## The setup (governing law, in-tree)

For a monomial pencil `(a,b)` the far-line incidence is
`I(δ) = #{α : x^a + α x^b is δ-close to RS[k]}` (the bad-α count); `δ* = sup{δ : I(δ) ≤ q·ε* ≈ n}`
(`OrbitCountCrossingLaw`, `MCAThresholdLedger.mcaDeltaStar`). We compare:

* `I_0(δ)` — the count computed over a **characteristic-0** field (`ℚ(ζ_n) ⊆ ℂ`), where "`δ`-close"
  is decided by *exact* vanishing of integer/cyclotomic readouts; and
* `I_p(δ)` — the same count over the prize field `F_q`, `char F_q = p`, where vanishing is decided
  **mod `p`**.

Reduction mod `p` only ever *creates* coincidences (`x ≡ 0` in `ℤ ⟹ x ≡ 0` mod `p`), so the bad set
in char `0` always injects into the bad set in char `p`: `B_0 ⊆ B_p`, hence `I_0 ≤ I_p`. The keystone
asks for the **reverse**: at prize scale `B_p = B_0`, so `I_p = I_0` and `δ*` is char-INDEPENDENT,
collapsing the prize to the single `q`-free char-0 incidence law.

## The mechanism, and what closes the gap

An index `α ∈ B_p \ B_0` is a *char-`p`-only* bad config: a readout that vanishes mod `p` but **not**
over `ℂ`. Such a vanishing forces a nonzero rational integer `N` (the field norm of the readout, a
product of `≤ φ(n)` conjugates) to satisfy `p^r ∣ N` for the rigidity rank `r` (the number of
simultaneously-vanishing conjugate conditions), with `|N| ≤ B := (2k)^{2k}` by the archimedean
triangle/product bound (`BadPrimeNormBound`). If `B < p^r`, no such `N` exists, so `B_p \ B_0 = ∅`.

* For the **full odd system** `r = k/2`, the size bound `(2k)^{2k} < p^{k/2}` is *equivalent* to
  `(2k)^4 < p` (`charPexcessFree_iff_prizeThreshold`), which **holds at prize scale**
  (`prize_charPexcessFree`, numeric `(2^30)^4 = 2^120 < q = 2^158`). So the reduction CLOSES for the
  full system: `I_p = I_0` (`incidence_charIndependent_fullSystem`).

* For a **single low-`r` readout** (`r = 1`) the requirement degrades to `(2k)^{2k} < p`, which is
  astronomically larger than the prize field and is **NOT** met. This is not a defect of the proof:
  it is the *exact* boundary recorded in `DISPROOF_LOG.md` (2026-06-14) — at `n = 32` the single
  `deg-3` readout `h_3` has a genuine char-`p` excess prime `p = 206889121 = n^{5.525}` (prize-scale,
  `≡ 1 mod 32`), so single-condition char-faithfulness is **REFUTED** at the prize point. The
  dichotomy `r = k/2` (rigid → closes) vs `r = 1` (floppy → wall) is therefore *honestly* the scope
  of this file (`single_readout_threshold_not_prize`).

## Honest scope: PROVEN here vs. NAMED hypothesis

**Proven (axiom-clean):**
* `no_charPOnly_witness` — the arithmetic core: `B < p^r ⟹` no integer `N ≠ 0` with `p^r ∣ N`,
  `|N| ≤ B` (i.e. `CharPOnlyWitness p r B` is empty).
* `badSet_eq_of_charPexcessFree` / `incidence_eq_of_charPexcessFree` — the abstract reduction: from
  `B_0 ⊆ B_p`, the per-excess-element witness package, and `B < p^r`, conclude `B_p = B_0` and
  `#B_p = #B_0` (`I_p = I_0`).
* `charPexcessFree_iff_prizeThreshold` — the `r = k/2` size bridge `(2k)^{2k} < p^{k/2} ⟺ (2k)^4 < p`
  (k even, k > 0).
* `prize_charPexcessFree`, `incidence_charIndependent_fullSystem` — the prize-scale instantiation.
* `single_readout_threshold_not_prize` — the honest negative half: the `r = 1` threshold `(2k)^{2k}`
  exceeds the prize field, so this reduction does **not** apply to single readouts (consistent with
  the `DISPROOF_LOG` n=32 excess prime).

**Named hypothesis (NOT formalized here — the Galois-divisibility input):** that every char-`p`-only
bad index `α ∈ B_p \ B_0` actually *produces* a `CharPOnlyWitness p r B` (a nonzero integer norm `N`
with `p^r ∣ N`, `|N| ≤ B`). This is the cyclotomic-norm / `Algebra.norm` half (`RootSumNorm` carries
the `|N| ≤ card^{finrank}` archimedean side; producing `N` and `p^r ∣ N` from `r` vanishing
conjugates needs the full `NumberField` machinery). It is carried as the explicit hypothesis `hwit`,
exactly the project's modularity convention.

## References
- [ABF26] ePrint 2026/680 (the Proximity Prize; governing δ* law).
- [KKH26] ePrint 2026/782 (the bad-line ceiling; rigidity-rank dichotomy).
- in-tree: `BadPrimeNormBound.lean` (size bound), `RootSumNormBound.lean` (norm half),
  `OrbitCountCrossingLaw.lean`, `MCAThresholdLedger.lean` (governing law),
  `DISPROOF_LOG.md` 2026-06-14 (the n=32 single-readout excess prime; r=1 vs r=k/2 dichotomy).
-/

open Finset

namespace ProximityGap.RigidityReductionPrizeScale

/-! ### The char-`p`-only witness: the named Galois-divisibility package -/

/-- A **char-`p`-only witness** at rigidity rank `r` and size bound `B`: a nonzero rational integer
`N` (the field norm of the char-`p`-only-vanishing readout) divisible by `p^r` with `|N| ≤ B`.

This is precisely the divisibility input the elementary `BadPrimeNormBound` file does *not* reprove
(see that module's docstring): producing `N` from a cyclotomic norm and `p^r ∣ N` from `r` vanishing
conjugates needs `NumberField`/`Algebra.norm` machinery. Here it is the named hypothesis that a
char-`p`-only bad index supplies. The point of this file is that such a witness **cannot exist** once
`B < p^r`.  The data are `N` (the rational-integer field norm of the readout), `N ≠ 0` (it does *not*
vanish over `ℂ`), `p^r ∣ N` (from `r` vanishing conjugates mod `p`), and `|N| ≤ B` (the archimedean
triangle/product bound, `B = (2k)^{2k}`). -/
def CharPOnlyWitness (p r : ℕ) (B : ℤ) : Prop :=
  ∃ N : ℤ, N ≠ 0 ∧ (p : ℤ) ^ r ∣ N ∧ |N| ≤ B

/-- **The arithmetic core (PROVEN, axiom-clean).** Once `B < p^r`, no char-`p`-only witness exists:
a nonzero integer divisible by `p^r` has absolute value `≥ p^r > B`, contradicting `|N| ≤ B`. This is
`bad_prime_pow_le` contraposed and packaged. -/
theorem no_charPOnly_witness {p r : ℕ} {B : ℤ} (hPB : B < (p : ℤ) ^ r) :
    ¬ CharPOnlyWitness p r B := by
  rintro ⟨N, hN_ne, hN_dvd, hN_le⟩
  exact absurd
    (ArkLib.ProximityGap.BadPrimeBound.bad_prime_pow_le hN_ne hN_dvd hN_le)
    (not_le.mpr hPB)

/-! ### The abstract reduction: `B_p = B_0` -/

variable {ι : Type*} [DecidableEq ι]

/-- **The abstract rigidity reduction (PROVEN, axiom-clean).** Given:
* `hsub : B0 ⊆ Bp` — char-0 bad ⟹ char-`p` bad (reduction mod `p` only creates coincidences),
* `hwit` — the named Galois-divisibility input: every char-`p`-only index `α ∈ Bp \ B0` supplies a
  `CharPOnlyWitness p r B`, and
* `hPB : B < p^r` — the prize-scale size gap,

then the char-`p` bad set equals the char-0 bad set: `Bp = B0`. The extra (char-`p`-only) elements
would each force a witness that `hPB` forbids. -/
theorem badSet_eq_of_charPexcessFree {p r : ℕ} {B : ℤ}
    (B0 Bp : Finset ι) (hsub : B0 ⊆ Bp)
    (hwit : ∀ α ∈ Bp, α ∉ B0 → CharPOnlyWitness p r B)
    (hPB : B < (p : ℤ) ^ r) :
    Bp = B0 := by
  refine Finset.Subset.antisymm (fun α hα => ?_) hsub
  by_contra hni
  exact no_charPOnly_witness hPB (hwit α hα hni)

/-- **Char-independence of incidence (PROVEN, axiom-clean).** The cardinality form: under the same
hypotheses, `#Bp = #B0`, i.e. the char-`p` far-line incidence `I_p` equals the char-0 incidence
`I_0`. This is the keystone statement (`I_p(δ) = I_0(δ)`) in concrete `Finset.card` form. -/
theorem incidence_eq_of_charPexcessFree {p r : ℕ} {B : ℤ}
    (B0 Bp : Finset ι) (hsub : B0 ⊆ Bp)
    (hwit : ∀ α ∈ Bp, α ∉ B0 → CharPOnlyWitness p r B)
    (hPB : B < (p : ℤ) ^ r) :
    Bp.card = B0.card := by
  rw [badSet_eq_of_charPexcessFree B0 Bp hsub hwit hPB]

/-! ### The `r = k/2` full-odd-system size bridge -/

/-- **The size bridge (PROVEN).** For `k` even and positive, the char-`p`-excess-free size gap for
the full odd system `(2k)^{2k} < p^{k/2}` is *equivalent* to `(2k)^4 < p`. (Forward: raise `(2k)^4 <
p` to the power `k/2`, using `(2k)^{2k} = ((2k)^4)^{k/2}` when `k` is even. Backward: if `(2k)^4 ≥ p`
then `(2k)^{2k} = ((2k)^4)^{k/2} ≥ p^{k/2}`.) -/
theorem charPexcessFree_iff_prizeThreshold {k p : ℕ} (hk : 0 < k) (heven : 2 * (k / 2) = k) :
    ((2 * k) ^ (2 * k) : ℤ) < (p : ℤ) ^ (k / 2) ↔ (2 * k) ^ 4 < p := by
  have hpow : ((2 * k) ^ (2 * k) : ℤ) = ((2 * k) ^ 4 : ℤ) ^ (k / 2) := by
    rw [← pow_mul]; congr 1; omega
  rw [hpow]
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    exact absurd h (not_lt.mpr
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle) (k / 2)))
  · intro h
    have hbase : (0 : ℤ) < (2 * k) ^ 4 := by positivity
    have hkpos : 0 < k / 2 := by omega
    exact pow_lt_pow_left₀ (by exact_mod_cast h) (le_of_lt hbase) (by omega)

/-! ### Prize-scale instantiation -/

/-- **Prize-scale char-`p`-excess-freeness (PROVEN).** At the prize point `n = 2^30`, `k = n/2 =
2^29`, full odd system `r = k/2`, the size gap `(2k)^{2k} < p^{k/2}` holds for any prime `p` reaching
prize field scale (concretely any `p ≥ q = n·2^128 = 2^158`), because `(2k)^4 = (2^30)^4 = 2^120 < q`.
This is `BadPrimeNormBound.prize_scale_no_bad_prime` fed through the size bridge. -/
theorem prize_charPexcessFree {p : ℕ} (hp : (2 ^ 30) * 2 ^ 128 ≤ p) :
    ((2 * (2 ^ 30 / 2)) ^ (2 * (2 ^ 30 / 2)) : ℤ)
      < (p : ℤ) ^ ((2 ^ 30 / 2) / 2) := by
  have hthresh : (2 * (2 ^ 30 / 2)) ^ 4 < p :=
    lt_of_lt_of_le ArkLib.ProximityGap.BadPrimeBound.prize_scale_no_bad_prime hp
  exact (charPexcessFree_iff_prizeThreshold (by norm_num) (by norm_num)).mpr hthresh

/-- **THE KEYSTONE (PROVEN, axiom-clean modulo the named Galois-divisibility input).** At prize scale
(`p` reaching the prize field size), for the **full odd system** `r = k/2` with `k = 2^29`, the
char-`p` far-line incidence equals the char-0 incidence: `I_p = I_0`. The only non-elementary input
is `hwit` (each char-`p`-only bad index supplies a cyclotomic-norm witness), carried explicitly. The
size gap is discharged unconditionally by `prize_charPexcessFree`. This collapses the prize to the
single `q`-free char-0 incidence law. -/
theorem incidence_charIndependent_fullSystem {p : ℕ} (hp : (2 ^ 30) * 2 ^ 128 ≤ p)
    (B0 Bp : Finset ι) (hsub : B0 ⊆ Bp)
    (hwit : ∀ α ∈ Bp, α ∉ B0 →
      CharPOnlyWitness p ((2 ^ 30 / 2) / 2) ((2 * (2 ^ 30 / 2)) ^ (2 * (2 ^ 30 / 2)))) :
    Bp.card = B0.card :=
  incidence_eq_of_charPexcessFree B0 Bp hsub hwit (prize_charPexcessFree hp)

/-! ### The honest negative half: the reduction does NOT apply to single readouts -/

/-- **Honest scope boundary (PROVEN).** For a *single* low-degree readout the rigidity rank is `r =
1`, so the char-`p`-excess-free size gap degrades to `(2k)^{2k} < p`. At the prize point `k = 2^29`,
the threshold `(2k)^{2k} = (2^30)^{2^30}` is astronomically larger than the prize field `q = 2^158`,
so the gap is **NOT** met: the reduction provides *no* char-independence for single readouts. This is
not a weakness of the argument — it is the exact boundary recorded in `DISPROOF_LOG.md` (2026-06-14):
at `n = 32` the single deg-3 readout `h_3` has a genuine prize-scale char-`p` excess prime
`p = 206889121 = n^{5.525}`. The rigid (`r = k/2`) vs floppy (`r = 1`) dichotomy is real. -/
theorem single_readout_threshold_not_prize :
    ((2 ^ 30) * 2 ^ 128 : ℕ) < (2 * (2 ^ 30 / 2)) ^ (2 * (2 ^ 30 / 2)) := by
  -- q = 2^158; threshold = (2^30)^(2^30) = 2^(30·2^30) ≫ 2^158
  have hq : ((2 ^ 30) * 2 ^ 128 : ℕ) = 2 ^ 158 := by norm_num
  have hbase : (2 * (2 ^ 30 / 2)) = 2 ^ 30 := by norm_num
  rw [hq, hbase]
  calc (2 ^ 158 : ℕ)
      < 2 ^ (30 * 2 ^ 30) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        have : (2 : ℕ) ^ 30 ≥ 2 ^ 4 := by gcongr <;> norm_num
        nlinarith [this]
    _ = (2 ^ 30) ^ (2 ^ 30) := by rw [← pow_mul]

end ProximityGap.RigidityReductionPrizeScale

/-! ## Source audit -/

#print axioms ProximityGap.RigidityReductionPrizeScale.no_charPOnly_witness
#print axioms ProximityGap.RigidityReductionPrizeScale.badSet_eq_of_charPexcessFree
#print axioms ProximityGap.RigidityReductionPrizeScale.incidence_eq_of_charPexcessFree
#print axioms ProximityGap.RigidityReductionPrizeScale.charPexcessFree_iff_prizeThreshold
#print axioms ProximityGap.RigidityReductionPrizeScale.prize_charPexcessFree
#print axioms ProximityGap.RigidityReductionPrizeScale.incidence_charIndependent_fullSystem
#print axioms ProximityGap.RigidityReductionPrizeScale.single_readout_threshold_not_prize
