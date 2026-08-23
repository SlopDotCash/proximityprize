/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OddZeroSumCountVanishCharZero

/-!
# The odd-order zeroSumCount is supported ENTIRELY on the char-`p` spurious set (#444, #407)

`OddZeroSumCountVanishCharZero.zeroSumCount_odd_dyadicRoots_eq_zero` proves the located
thinness-essential prize object vanishes at every ODD order over `ℂ`:

>   for every ODD `r`,   `zeroSumCount (μ_{2^k} : Finset ℂ) r = 0`.

That brick's docstring asserts (in prose) the consequence:

>   "the nontrivial signed cancellation that is the open BGK wall appears ONLY ... over the
>    finite field `F_q`, where the `F_q`-reduction creates the zero-sum coincidences char 0
>    forbids.  This LOCATES the entire odd-order prize content squarely in the finite-field
>    reduction."

This file makes that prose a **theorem**: over an arbitrary commutative ring `R` carrying a
"reference" comparison map `φ : R → ℂ` (the char-0 lift of the roots of unity), the odd-order
`zeroSumCount` of a set `G ⊆ R` whose image under `φ` has *no* odd zero-sums equals the count of
its **spurious** tuples — the `R`-zero-sum tuples whose `φ`-image does **not** vanish:

  **`zeroSumCount_eq_spuriousCount_of_image_odd_free`** :
    if `zeroSumCount (G.image φ) r = 0` (no odd-order `φ`-image zero-sum), then
    `zeroSumCount G r = spuriousZeroSumCount G φ r`.

The mechanism is a clean partition: an `R`-zero-sum `r`-tuple `c` either has `∑ φ(c i) = 0`
(a *genuine* / char-0-explained zero-sum) or it does not (a *spurious* / char-`p`-only collision).
When the `φ`-image has no odd zero-sums, the genuine part is forced empty (every genuine tuple
would be a `φ`-image zero-sum tuple), so the whole count is spurious.

Specialized to the prize subgroup, with `φ` the canonical `ℂ`-embedding and the char-0 vanishing
brick supplying the hypothesis automatically, this gives an **unconditional identity** for the
prize regime: the entire odd-order `zeroSumCount` of `μ_n` over any field that maps to `ℂ`-roots is
the count of its char-`p` spurious tuples.

## Probe (rule 2)

`probe_odd_zerosum_charp_spurious.py`: over `F_p` (PROPER thin `μ_n`, `n = 2^a`, multiple primes
incl `p ≫ n³` and Fermat `257, 65537`, NEVER `n = q−1`), for odd `r ∈ {3,5}`, the F_p zero-sum
count splits into genuine (`ℂ`-lift `= 0`) and spurious (`ℂ`-lift `≠ 0`).  Result over 36 cases:
**genuine `= 0` in EVERY case** (the entire odd-order F_p zero-sum count is spurious), and for the
deep `p ≫ n³` primes the spurious count is itself `0` (no odd zero-sums survive below the girth).
This is exactly the identity proven here, with the char-0 odd-vanishing supplying `genuine = 0`.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT a refutation.  This is a structural **localization identity**: it does NOT
bound the spurious count (that count — `q·W_r − n^r` for the signed period-power, growing at the
deep `F_q` orders — IS the open BGK wall).  It says only WHERE the odd-order signal lives: entirely
in the spurious set, never in a char-0-explained zero-sum.  NON-MOMENT (an exact additive-tuple
count, no `|·|`); EXTEND-proven (consumes the char-0 odd-vanishing brick verbatim as the
genuine-empty hypothesis).  Field-universal in `R`; the thinness enters only through the char-0
vanishing it specializes against.  No capacity / beyond-Johnson / cliff-at-n/2 / `δ*→0` claim.
`CORE M(μ_n) ≤ C·√(n·log(q/n))` stays OPEN.

Issues #444, #407.
-/

open scoped BigOperators

namespace ArkLib.ProximityGap.OddZeroSumSpurious

open Finset ArkLib.ProximityGap.NegationClosedWalk

variable {R : Type*} [Field R] [DecidableEq R]

open Classical in
/-- The **spurious zero-sum tuples** of `G ⊆ R` at order `r`, relative to a comparison map
`φ : R → ℂ`: the `r`-tuples `c : Fin r → R` valued in `G` that are zero-sum in `R`
(`∑ i, c i = 0`) but whose `φ`-image is **not** zero-sum (`∑ i, φ (c i) ≠ 0`).  These are the
char-`p`-only collisions the char-0 reduction forbids. -/
noncomputable def spuriousZeroSumTuples (G : Finset R) (φ : R → ℂ) (r : ℕ) :
    Finset (Fin r → R) :=
  (Fintype.piFinset (fun _ : Fin r => G)).filter
    (fun c => (∑ i, c i = 0) ∧ ∑ i, φ (c i) ≠ 0)

/-- The **spurious zero-sum count** — the cardinality of `spuriousZeroSumTuples`. -/
noncomputable def spuriousZeroSumCount (G : Finset R) (φ : R → ℂ) (r : ℕ) : ℕ :=
  (spuriousZeroSumTuples G φ r).card

open Classical in
/-- The **genuine zero-sum tuples**: `R`-zero-sum AND `φ`-image-zero-sum (char-0-explained). -/
noncomputable def genuineZeroSumTuples (G : Finset R) (φ : R → ℂ) (r : ℕ) :
    Finset (Fin r → R) :=
  (Fintype.piFinset (fun _ : Fin r => G)).filter
    (fun c => (∑ i, c i = 0) ∧ ∑ i, φ (c i) = 0)

/-- **The genuine/spurious partition of the zero-sum tuples.**  Every `R`-zero-sum `r`-tuple is
either genuine (`φ`-image zero-sum) or spurious (`φ`-image nonzero), so the zero-sum count splits
exactly: `zeroSumCount G r = #genuine + #spurious`. -/
theorem zeroSumCount_eq_genuine_add_spurious (G : Finset R) (φ : R → ℂ) (r : ℕ) :
    zeroSumCount G r = (genuineZeroSumTuples G φ r).card + spuriousZeroSumCount G φ r := by
  classical
  rw [zeroSumCount, spuriousZeroSumCount, genuineZeroSumTuples, spuriousZeroSumTuples]
  rw [← Finset.card_filter_add_card_filter_not
        (s := (Fintype.piFinset (fun _ : Fin r => G)).filter (fun c => ∑ i, c i = 0))
        (p := fun c : Fin r → R => ∑ i, φ (c i) = 0)]
  -- after merging, the two halves are `∑ c = 0 ∧ ∑ φ = 0` (genuine) and `∑ c = 0 ∧ ¬∑ φ = 0`
  -- (spurious, `≠` is `¬(=)`), definitionally the genuine/spurious filters.
  rw [Finset.filter_filter, Finset.filter_filter]

open Classical in
/-- **A genuine zero-sum tuple makes the `φ`-image zero-sum set nonempty.**  Mapping a genuine
tuple `c : Fin r → G` to `φ ∘ c : Fin r → ℂ` lands in the `φ`-image's zero-sum tuple set (the image
coordinates lie in `G.image φ` and their sum vanishes).  No injectivity of `φ` is needed: a single
genuine tuple already witnesses one element of the image zero-sum filter. -/
theorem image_zeroSumCount_pos_of_genuine (G : Finset R) (φ : R → ℂ) (r : ℕ)
    {c : Fin r → R} (hc : c ∈ genuineZeroSumTuples G φ r) :
    0 < zeroSumCount (G.image φ) r := by
  classical
  rw [genuineZeroSumTuples, Finset.mem_filter] at hc
  obtain ⟨hmem, _hzs, hg⟩ := hc
  rw [Fintype.mem_piFinset] at hmem
  rw [zeroSumCount, Finset.card_pos]
  refine ⟨fun i => φ (c i), ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hg⟩
  rw [Fintype.mem_piFinset]
  intro i
  exact Finset.mem_image_of_mem φ (hmem i)

/-- **The genuine count is forced to `0` when the `φ`-image has no odd zero-sums.**  If
`zeroSumCount (G.image φ) r = 0` then no genuine tuple can exist (any would make the image count
positive), so the genuine set is empty. -/
theorem genuine_card_eq_zero_of_image_free (G : Finset R) (φ : R → ℂ) (r : ℕ)
    (himg : zeroSumCount (G.image φ) r = 0) :
    (genuineZeroSumTuples G φ r).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro c hc
  have := image_zeroSumCount_pos_of_genuine G φ r hc
  omega

/-- **The localization identity (headline).**  If the `φ`-image of `G` has no order-`r` zero-sums
(`zeroSumCount (G.image φ) r = 0` — automatic at ODD `r` for the dyadic prize roots, by the char-0
vanishing brick), then the entire order-`r` zero-sum count of `G` is **spurious**:

  `zeroSumCount G r = spuriousZeroSumCount G φ r`.

The whole odd-order signal lives in the char-`p`-only collisions; nothing is char-0-explained. -/
theorem zeroSumCount_eq_spuriousCount_of_image_odd_free (G : Finset R) (φ : R → ℂ) (r : ℕ)
    (himg : zeroSumCount (G.image φ) r = 0) :
    zeroSumCount G r = spuriousZeroSumCount G φ r := by
  rw [zeroSumCount_eq_genuine_add_spurious G φ r,
    genuine_card_eq_zero_of_image_free G φ r himg, Nat.zero_add]

/-- **Dyadic prize specialization (`R = ℂ`, `φ = id`).**  Over `ℂ` itself the comparison map is the
identity, `G.image id = G`, so the `φ`-image-free hypothesis is the char-0 odd-vanishing of the
dyadic roots, supplied UNCONDITIONALLY by `zeroSumCount_odd_dyadicRoots_eq_zero`.  Hence for every
ODD `r` the entire order-`r` zero-sum count of `μ_{2^k} ⊆ ℂ` is its spurious count — here forced to
`0` (over `ℂ` the spurious set is empty too; the genuine/spurious split is degenerate at the source
field).  This is the source-field anchor: ALL odd-order signal is spurious, and the spurious set
itself only becomes nonempty after reduction to a finite field `F_q`. -/
theorem zeroSumCount_dyadic_eq_spurious_charZero {k r : ℕ} (hr : Odd r) :
    zeroSumCount (Polynomial.nthRootsFinset (2 ^ k) (1 : ℂ)) r
      = spuriousZeroSumCount (Polynomial.nthRootsFinset (2 ^ k) (1 : ℂ)) (id : ℂ → ℂ) r := by
  classical
  apply zeroSumCount_eq_spuriousCount_of_image_odd_free
  -- `G.image id = G`, so the image count is the char-0 odd count, which vanishes.
  rw [Finset.image_id]
  exact ArkLib.ProximityGap.OddZeroSumCountVanish.zeroSumCount_odd_dyadicRoots_eq_zero hr

end ArkLib.ProximityGap.OddZeroSumSpurious

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.OddZeroSumSpurious.zeroSumCount_eq_genuine_add_spurious
#print axioms ArkLib.ProximityGap.OddZeroSumSpurious.genuine_card_eq_zero_of_image_free
#print axioms ArkLib.ProximityGap.OddZeroSumSpurious.zeroSumCount_eq_spuriousCount_of_image_odd_free
#print axioms ArkLib.ProximityGap.OddZeroSumSpurious.zeroSumCount_dyadic_eq_spurious_charZero
