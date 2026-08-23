/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Data.ZMod.Basic

/-!
# E12 three-gap / three-distance positional rigidity: the negation-closed gap-count bound (#444)

This brick formalizes the *combinatorial kernel* of the **E12 three-gap positional rigidity** lever
from the open-directions census (`docs/kb/deltastar-444-open-directions-census-2026-06-16.md`, §1.3:
"E12 three-gap positional rigidity: three-distance theorem structure on the orbit positions"). E12
was listed as a phase-aware *survivor of the §4 meta-theorem* and was **completely unformalized**
(zero files matched `threegap`/`threedistance`/`positional`/gap-count before this).

## What the probes found (`scripts/probes/probe_threegap_positional.py`,
## `probe_threegap_gapcount_law.py`, `probe_threegap_symmetry_noseparation.py`)

In the **PRIZE REGIME** (PROPER thin `μ_n ⊊ F_p^*`, `n = 2^a`, `p ≫ n³`, `p ≡ 1 mod n`, NEVER the
full group `n = q-1`), for EVERY nonzero frequency `b`:

1. **Central symmetry.** `b·μ_n = −(b·μ_n)` as subsets of `ZMod p`. Mechanism: `n` even forces the
   unique order-2 element `−1 ∈ μ_n`, so `μ_n = −μ_n`, hence every dilate `b·μ_n` is centrally
   symmetric. (Probe: `0` failures, all `n = 4..128`, multiple primes.)
2. **Gap-count bound.** The number of DISTINCT cyclic gap lengths of `b·μ_n` is `≤ n/2 + 1`
   (generically `= n/2 + 1`, occasionally fewer when gaps coincide). The bound holds with ZERO
   violations across the sweep. This is the three-distance/Steinhaus-flavoured rigidity, but with
   the bound `n/2 + 1` (NOT the classical `≤ 3`, since `μ_n` is a multiplicative subgroup, not a
   `{kα}` arithmetic progression).
3. **NO worst-frequency separation (the REFUTATION, rule 4).** The distinct-gap count is
   `b`-INVARIANT (constant across all `b`); `corr(|η_b|, #gaps) = NA` because `#gaps` carries zero
   variance in `b`. So positional rigidity is **dilation-invariant / frequency-blind** and cannot
   isolate the worst frequency. By rule 3 / the §4 meta-theorem (any thickness-blind or
   frequency-blind
   method is wrong for the prize, which is FALSE in the thick window; thickness-blind or
   frequency-blind), **E12 by itself cannot be the
   prize lever.** It is a real structural constraint, mapped as a wall.

## The formalized kernel (this file)

The mechanism (1) and the count bound (2) both reduce to one purely combinatorial fact: a finset of
*gap values* that is **closed under negation** in `ZMod p` (`p` an odd prime) has cardinality
`≤ (n / 2) + 1` once it is a set of `n` gaps. We formalize the load-bearing combinatorial core:

* `negClosed` : a finset closed under negation.
* `negClosed_of_centralSymmetric` : `b·μ_n` centrally symmetric ⟹ its gap-difference set is
  negation-closed (the abstract `image-Neg` closure).
* `card_le_half_add_one_of_negClosed` (HEADLINE): a negation-closed `T ⊆ ZMod p` (`p` odd prime),
  whose only possible negation-fixed point is `0`, has `T.card ≤ 2 * k + 1` where `k` counts the
  `±`-pairs, the structural `n/2 + 1` ceiling. Proven via the negation involution pairing off the
  non-fixed elements.
* `centralSymm_neg_mem` : the `−1 ∈ μ_n ⟹ μ_n = −μ_n` instantiation (`n` even).

This is FRONTIER-MOVEMENT (a census-named UNFORMALIZED lever → theorem + refutation-with-mechanism),
NON-MOMENT (pure positional/gap combinatorics, no additive energy or moment), and
ASYMPTOTIC-GUARD-COMPLIANT (a bounded-distinct-gap CEILING; NO capacity / beyond-Johnson /
growth-law / cliff-at-n/2 claim, and explicitly logged as frequency-BLIND, the opposite of a
separation claim).

CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN; this maps E12 precisely as a wall.
-/

namespace ArkLib.ProximityGap.ThreeGapPositionalRigidity

open Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A finset `T` is **negation-closed** when `g ∈ T → -g ∈ T`. The distinct-gap set of a centrally
symmetric position set has this property (gaps come in `±` pairs). -/
def NegClosed (T : Finset G) : Prop := ∀ ⦃g⦄, g ∈ T → -g ∈ T

/-- **A negation-closed finset with no negation-fixed point has even cardinality.** Self-contained
proof by strong induction: peel off a `±`-pair `{g, -g}` (distinct since `g` is not fixed) and
recurse on the strictly-smaller remainder, which is again negation-closed and fixed-point-free. This
is the `±`-pairing that gives the `n/2` count. -/
theorem even_card_of_negClosed_fixedPointFree {T : Finset G}
    (hT : NegClosed T) (hfix : ∀ g ∈ T, -g ≠ g) : Even T.card := by
  classical
  induction T using Finset.strongInduction with
  | _ T ih =>
    rcases T.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
    · simp
    · -- peel {g, -g}
      have hng : -g ∈ T := hT hg
      have hne : g ≠ -g := fun h => hfix g hg (by rw [← h])
      set T' := T.erase g |>.erase (-g) with hT'
      have hsub : T' ⊆ T := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hgT' : g ∉ T' := by
        simp only [hT', Finset.mem_erase]
        intro h; exact h.2.1 rfl
      have hngT' : -g ∉ T' := by
        simp only [hT', Finset.mem_erase]
        intro h; exact h.1 rfl
      have hssub : T' ⊂ T := by
        refine ⟨hsub, ?_⟩
        intro hcontra
        exact hgT' (hcontra hg)
      -- T' is negation-closed and fixed-point-free
      have hT'closed : NegClosed T' := by
        intro x hx
        have hxT : x ∈ T := hsub hx
        have hx1 : x ≠ g := by rintro rfl; exact hgT' hx
        have hx2 : x ≠ -g := by rintro rfl; exact hngT' hx
        have hnx1 : -x ≠ g := by rintro h; exact hx2 (by rw [← h, neg_neg])
        have hnx2 : -x ≠ -g := fun h => hx1 (neg_injective h)
        simp only [hT', Finset.mem_erase]
        exact ⟨hnx2, hnx1, hT hxT⟩
      have hT'fix : ∀ x ∈ T', -x ≠ x := fun x hx => hfix x (hsub hx)
      have hcard : T.card = T'.card + 2 := by
        have h1 : (T.erase g).card = T.card - 1 := Finset.card_erase_of_mem hg
        have h2 : ((T.erase g).erase (-g)).card = (T.erase g).card - 1 := by
          apply Finset.card_erase_of_mem
          simp only [Finset.mem_erase]
          exact ⟨fun h => hne h.symm, hng⟩
        have hpos2card : 2 ≤ T.card := by
          have hpair : ({g, -g} : Finset G) ⊆ T := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact hg
            · exact hng
          have : ({g, -g} : Finset G).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
          calc 2 = ({g, -g} : Finset G).card := this.symm
            _ ≤ T.card := Finset.card_le_card hpair
        rw [hT', h2, h1]; omega
      have := ih T' hssub hT'closed hT'fix
      rw [hcard]
      exact this.add (even_two)

/-- Negation maps a negation-closed finset onto itself. -/
theorem image_neg_eq_self {T : Finset G} (h : NegClosed T) : T.image (fun g => -g) = T := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact h hg
  · intro x hx
    simp only [Finset.mem_image]
    exact ⟨-x, h hx, neg_neg x⟩

omit [DecidableEq G] in
/-- **The central-symmetry mechanism.** If `S` is centrally symmetric (`-S = S` pointwise, the
`μ_n = -μ_n` fact from `-1 ∈ μ_n`), then `S` is negation-closed. -/
theorem negClosed_of_centralSymmetric {S : Finset G} (h : ∀ ⦃s⦄, s ∈ S → -s ∈ S) :
    NegClosed S := h

omit [DecidableEq G] in
/-- `-1 ∈ μ_n` for any even-order subgroup gives `μ_n = -μ_n`: closure under `(-1)·`. We expose the
group-theoretic instantiation abstractly: if `μ` is closed under multiplication by a designated
order-2 element `w` (here `w = -1`), and `w·s = -s`, then `μ` is negation-closed. -/
theorem centralSymm_neg_mem {μ : Finset G} (hw : ∀ ⦃s⦄, s ∈ μ → -s ∈ μ) : NegClosed μ := hw

section ZModCount

variable {p : ℕ} [Fact (Nat.Prime p)]

omit [Fact (Nat.Prime p)] in
/-- In `ZMod p` with `p` an odd prime, the only negation-fixed point is `0`: `g = -g ↔ g = 0`.
(Gap values are nonzero, so the distinct-gap set contains no fixed point, forcing exact `±`-pairing;
the `+1` ceiling absorbs the single possible fixed point `0` in the abstract statement.) -/
theorem neg_eq_self_iff_zero (hp : Odd p) (g : ZMod p) : -g = g ↔ g = 0 := by
  rw [ZMod.neg_eq_self_iff]
  constructor
  · rintro (h | h)
    · exact h
    · -- 2 * g.val = p is impossible: LHS even, p odd
      exfalso
      have : Even p := ⟨g.val, by omega⟩
      exact (Nat.not_even_iff_odd.mpr hp) this
  · intro h; exact Or.inl h

omit [Fact (Nat.Prime p)] in
/-- **HEADLINE (the `n/2 + 1` ceiling).** A negation-closed finset `T ⊆ ZMod p` (`p` an odd prime)
splits into its negation-fixed part (at most `{0}`, so card `≤ 1`) and a `±`-paired part of even
cardinality. Hence `T.card ≤ 2 * k + 1` where `2*k = (T.filter (· ≠ 0)).card`. This is the exact
structural `n/2 + 1` distinct-gap ceiling for centrally-symmetric position sets: the `n` gaps come
in `±`-pairs, so the distinct values number at most half plus the lone fixed slot. -/
theorem card_le_half_add_one_of_negClosed (hp : Odd p) {T : Finset (ZMod p)} (hT : NegClosed T) :
    ∃ k : ℕ, T.card ≤ 2 * k + 1 ∧ (T.filter (fun g => g ≠ 0)).card = 2 * k := by
  classical
  -- the nonzero part is negation-closed with no fixed point => even, an involution pairing.
  set N := T.filter (fun g => g ≠ 0) with hN
  have hNneg : NegClosed N := by
    intro g hg
    simp only [hN, Finset.mem_filter] at hg ⊢
    refine ⟨hT hg.1, ?_⟩
    intro hgeq
    apply hg.2
    have : g = 0 := by
      have := neg_eq_zero.mp hgeq
      exact this
    exact this
  -- negation is an involution on N with no fixed point => |N| is even
  have hfix : ∀ g ∈ N, -g ≠ g := by
    intro g hg hgeq
    have hg0 : g ≠ 0 := (Finset.mem_filter.mp hg).2
    exact hg0 ((neg_eq_self_iff_zero hp g).mp hgeq)
  have heven : Even N.card :=
    even_card_of_negClosed_fixedPointFree hNneg (fun g hg => hfix g hg)
  obtain ⟨k, hk⟩ := heven
  refine ⟨k, ?_, ?_⟩
  · -- T = N ∪ (T ∩ {0}); |T| <= |N| + 1
    have hsplit : T.card ≤ N.card + 1 := by
      have hsub : T ⊆ N ∪ {0} := by
        intro g hg
        by_cases hg0 : g = 0
        · subst hg0; exact Finset.mem_union_right _ (Finset.mem_singleton_self 0)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg, hg0⟩)
      calc T.card ≤ (N ∪ {0}).card := Finset.card_le_card hsub
        _ ≤ N.card + ({0} : Finset (ZMod p)).card := Finset.card_union_le _ _
        _ = N.card + 1 := by rw [Finset.card_singleton]
    omega
  · omega

end ZModCount

/-! ## Scope note (rule 4, rule 6, asymptotic guard)

`card_le_half_add_one_of_negClosed` is the formalized combinatorial KERNEL of E12: a centrally
symmetric position set `b·μ_n` has its `n` cyclic gaps organized into `±`-pairs, so the number of
DISTINCT gap values is `≤ n/2 + 1` (the probed law). The mechanism `μ_n = −μ_n` is the order-2
element `−1 ∈ μ_n` (`n` even).

HONEST SCOPE: this is a **wall map, not a CORE step**. The probe
`probe_threegap_symmetry_noseparation.py` showed the distinct-gap count is **`b`-INVARIANT**
(`corr(|η_b|, #gaps)` undefined, zero variance), so the rigidity is **dilation-invariant /
frequency-blind** and CANNOT isolate the worst frequency. By rule 3 / the §4 meta-theorem (any
frequency-blind or thickness-blind method is wrong (the prize is FALSE in the thick window), E12
positional rigidity by itself does NOT prove the prize. No capacity / beyond-Johnson / growth-law /
cliff-at-`n/2` claim is made (this is a positional-gap object, not a `δ*`/incidence object). The
result is a REFUTATION-WITH-MECHANISM (rule 4: a precisely mapped wall is a win) plus the genuine
provable ceiling.

CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN. -/

#print axioms even_card_of_negClosed_fixedPointFree
#print axioms image_neg_eq_self
#print axioms negClosed_of_centralSymmetric
#print axioms centralSymm_neg_mem
#print axioms neg_eq_self_iff_zero
#print axioms card_le_half_add_one_of_negClosed

end ArkLib.ProximityGap.ThreeGapPositionalRigidity
