/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib

/-!
# Li–Wan exact subset-sum equidistribution (the exact `N_fib` value)

New machinery from the 2026-06-13 proximity-prize literature sweep (see the archived
`Research/ProximityPrize/kb/archive/RESEARCH_SYNTHESIS_389.md`). Li–Wan, *Counting subset sums
of finite abelian groups* (JCTA 119(1), 2012), Cor. 1.4, concerns a finite abelian group `G`
(`|G| = s`) and the subset-sum fibre `N(k,b) = #{T ⊆ G : |T| = k, Σ T = b}`, where `T` ranges
over subsets of the **whole** group `G` and `Σ` is the group operation of `G`.

This file proves the **sufficient** direction only: if the dilation `c ↦ k·c` is surjective
(equivalently bijective, `G` being finite; the `p ∤ k` case) then all fibres have the same size
(`subsetSum_fibre_equidistributed`), so `|G| · N(k,b) = C(s,k)` (`subsetSum_fibre_card_mul`).

The converse is **not** proved here and fails without further hypotheses:
`converse_fails_ZMod_two` shows that for `G = ℤ/2` and `k = 4 > |G|` every fibre is empty (so
all fibres have equal size) while `c ↦ 4·c` is the zero map.  Any converse statement needs at
least a range restriction such as `1 ≤ k ≤ |G| − 1`, plus whatever else Li–Wan assume; it is
not formalized here.

## Scope (honest)

`G` here is an **additive** finite abelian group, and the counted subsets range over all of `G`.
This is the object governing *additive*-subgroup fixed-domain clustering ([BKR10] subspace
polynomials over `F_{2^m}^+`).

The theorem does **not** give a list size or census value for the prize's **multiplicative**
smooth domain `μ_n ⊆ F_q^×` (`n = 2^a`).  `μ_n` is not closed under the field-additive
translations `x ↦ x + c` that drive the proof, so the translation bijection is unavailable for
field-additive root sums over `μ_n`.  Instantiating `G` with `μ_n` under its own (multiplicative)
group law counts subsets with a prescribed **product**, not subsets with a prescribed
field-additive sum, so it is a different object.  No identification of `N(k,b)` with the
extremal beyond-Johnson list size, or with the `#389` Thread-A census law
`L_max(a) = max_towers N_fib(s,r)`, is proved in this file or elsewhere in-tree; the
characteristic-zero vanishing-sums lattice (Lam–Leung `W(2^a) = 2ℕ`) and its descent to `F_q`
are separate questions that remain open.

The archived `RESEARCH_SYNTHESIS_389.md` (Li–Wan sections) applies this additive translation
argument to multiplicative root sums and reads off an exact extremal list value; that
instantiation is the misidentification described above (the 2026-10-28 audit's R-119 and
PG-097), and it should not be cited as an established exact census value.

Proof: the translation bijection `T ↦ T.image (· + c)` shifts every subset sum by `k·c`; when
`c ↦ k·c` is onto, it identifies any two fibres, so all fibres have equal cardinality, hence each is
`C(s,k)/s`.
-/

namespace ArkLib.ProximityGap.LiWan

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The subset-sum fibre: the `k`-element subsets of `G` whose elements sum to `b`. Its cardinality
is `N(k, b)` in Li–Wan's notation; the campaign's `N_fib(s, k) = max_b N(k, b)`. -/
def fibre (k : ℕ) (b : G) : Finset (Finset G) :=
  (Finset.univ.powersetCard k).filter (fun T => ∑ t ∈ T, t = b)

/-- **Li–Wan equidistribution (the `p ∤ k` case).** If the dilation `c ↦ k·c` is surjective on `G`,
then every subset-sum fibre has the **same** cardinality — size-`k` subset sums are perfectly
equidistributed over `G`.

Proved by the translation bijection `T ↦ T.image (· + c)`: it is a bijection of `k`-subsets and
shifts the sum by exactly `k·c`, so choosing `c` with `k·c = b' − b` identifies `fibre k b` with
`fibre k b'`. -/
theorem subsetSum_fibre_equidistributed
    (k : ℕ) (hk : Function.Surjective (fun c : G => k • c)) (b b' : G) :
    (fibre k b).card = (fibre k b').card := by
  obtain ⟨c, hc⟩ := hk (b' - b)
  have hc' : k • c = b' - b := hc
  refine Finset.card_bij'
    (fun T _ => T.image (· + c))
    (fun T _ => T.image (· + (-c)))
    ?_ ?_ ?_ ?_
  · intro T hT
    simp only [fibre, Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
    obtain ⟨⟨_, hcard⟩, hsum⟩ := hT
    have hinj : ∀ x ∈ T, ∀ y ∈ T, x + c = y + c → x = y :=
      fun x _ y _ h => add_right_cancel h
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injOn (fun x hx y hy => hinj x hx y hy), hcard]
    · rw [Finset.sum_image (fun x hx y hy => hinj x hx y hy),
        Finset.sum_add_distrib, Finset.sum_const, hcard, hsum, hc']
      abel
  · intro T hT
    simp only [fibre, Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
    obtain ⟨⟨_, hcard⟩, hsum⟩ := hT
    have hinj : ∀ x ∈ T, ∀ y ∈ T, x + (-c) = y + (-c) → x = y :=
      fun x _ y _ h => add_right_cancel h
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injOn (fun x hx y hy => hinj x hx y hy), hcard]
    · rw [Finset.sum_image (fun x hx y hy => hinj x hx y hy),
        Finset.sum_add_distrib, Finset.sum_const, hcard, hsum]
      have hneg : k • (-c) = b - b' := by
        have h1 : k • (-c) = -(k • c) := by rw [smul_neg]
        rw [h1, hc']; abel
      rw [hneg]; abel
  · intro T _
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
    · intro ha; exact ⟨a + c, ⟨a, ha, rfl⟩, by abel⟩
  · intro T _
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
    · intro ha; exact ⟨a + (-c), ⟨a, ha, rfl⟩, by abel⟩

/-- **Exact `N_fib = C(|G|, k)/|G|` for an additive group.** Under the same surjectivity
hypothesis, `|G|·N(k,b) = C(|G|,k)`, so every fibre has exactly `C(|G|,k)/|G|` subsets.  This is
a statement about `k`-subsets of the whole additive group `G`; it is not a proved value of the
beyond-Johnson list census over a multiplicative domain `μ_n` (see the module docstring). -/
theorem subsetSum_fibre_card_mul
    (k : ℕ) (hk : Function.Surjective (fun c : G => k • c)) (b : G) :
    Fintype.card G * (fibre k b).card =
      (Finset.univ.powersetCard k : Finset (Finset G)).card := by
  have key : (Finset.univ.powersetCard k : Finset (Finset G)).card
      = ∑ _b' : G, (fibre k b).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun T => ∑ t ∈ T, t)
        (t := (Finset.univ : Finset G)) (fun T _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    exact subsetSum_fibre_equidistributed k hk b' b
  rw [key, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **The unrestricted converse fails.**  For `G = ℤ/2` and `k = 4`, every subset-sum fibre is
empty (there are no `4`-subsets of a `2`-element group), so all fibres have equal size, yet the
dilation `c ↦ 4·c` is not surjective.  Equidistribution therefore does not imply bijective
dilation without a range hypothesis on `k`. -/
theorem converse_fails_ZMod_two :
    (∀ b b' : ZMod 2, (fibre 4 b).card = (fibre 4 b').card) ∧
      ¬ Function.Surjective (fun c : ZMod 2 => (4 : ℕ) • c) := by
  refine ⟨fun b b' => ?_, fun h => ?_⟩
  · have hempty : ∀ b : ZMod 2, fibre 4 b = ∅ := by
      intro b
      rw [fibre, Finset.powersetCard_eq_empty.mpr (by simp), Finset.filter_empty]
    rw [hempty b, hempty b']
  · obtain ⟨c, hc⟩ := h 1
    revert c
    decide

end ArkLib.ProximityGap.LiWan

/-! Axiom audit. -/
#print axioms ArkLib.ProximityGap.LiWan.subsetSum_fibre_equidistributed
#print axioms ArkLib.ProximityGap.LiWan.subsetSum_fibre_card_mul
#print axioms ArkLib.ProximityGap.LiWan.converse_fails_ZMod_two
