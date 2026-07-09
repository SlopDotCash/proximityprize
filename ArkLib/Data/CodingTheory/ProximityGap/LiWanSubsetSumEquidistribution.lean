/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib

/-!
# Li–Wan exact subset-sum equidistribution (the exact `N_fib` value)

New machinery from the 2026-06-13 proximity-prize literature sweep (see
`RESEARCH_SYNTHESIS_389.md`). Li–Wan, *Counting subset sums of finite abelian groups*
(JCTA 119(1), 2012), Cor. 1.4: over a finite abelian group `G` (`|G| = s`), the subset-sum
fibre `N(k,b) = #{T ⊆ G : |T| = k, Σ T = b}` is **perfectly equidistributed** in `b` precisely
when the dilation `c ↦ k·c` is a bijection of `G` (the `p ∤ k` case), giving the exact
`N_fib(s,k) = C(s,k)/s`.

This is the exact value of the extremal beyond-Johnson list size in the `#389` Thread-A census
law `L_max(a) = max_towers N_fib(s,r)` — it upgrades the conjectured `≈ C(s,r)/s` target to a
machine-checked closed form (`subsetSum_fibre_card_mul`).

## Scope (honest)

`G` here is an **additive** finite abelian group. This is the exact additive analogue, and is the
object governing the *additive*-subgroup fixed-domain clustering ([BKR10] subspace polynomials over
`F_{2^m}^+`). For the prize's **multiplicative** smooth domain `μ_n ⊆ F_q^×` (`n = 2^a`), the
subset-sum fibre is governed by the **same** vanishing-sums-of-roots-of-unity lattice (Lam–Leung
`W(2^a) = 2ℕ`), handled in characteristic 0 by the in-tree Mann / 2-power Lam–Leung theorem; the
descent of that exact law to `F_q` past the resultant threshold is the single named residual of
Thread A. So this file pins the *value* exactly; the multiplicative transfer remains the open core.

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

/-- **Exact `N_fib = C(|G|, k)/|G|`.** Under the same bijectivity hypothesis, `|G|·N(k,b) = C(|G|,k)`,
so every fibre has exactly `C(|G|,k)/|G|` subsets. This is the exact extremal value of the
beyond-Johnson list census (Thread A target). -/
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

end ArkLib.ProximityGap.LiWan

/-! Axiom audit. -/
#print axioms ArkLib.ProximityGap.LiWan.subsetSum_fibre_equidistributed
#print axioms ArkLib.ProximityGap.LiWan.subsetSum_fibre_card_mul
