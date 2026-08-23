/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedSquarefreeExp

/-!
# Issue #232 — the FIRST windowed structure law at three primes: the fiber-count
decomposition (O112)

O111 proved the O70 coset form of the window law has no three-prime extension —
the correct surface must carry COUNTS, not cosets.  This file lands the first
positive windowed structure theorem on that surface: for distinct primes
`p, q, r` and `T ⊆ μ_{pqr}` (char 0),

    `∑_{y∈T} y^q = 0   ⟹   ∃ A B : ℕ → ℕ,  ∀ f < p·r,
        #{y ∈ T : y^q = (ζ^q)^f} = A (f % r) + B (f % p)`

— the window exponent `q` pushes `T` forward to its `q`-power FIBER-COUNT
function on `μ_{pr}`, an ℕ-weighted vanishing sum at a squarefree TWO-prime
level, where the weighted de Bruijn classification (O102) decomposes it into
nonnegative `μ_p`- and `μ_r`-packet components.  The positivity is genuine —
exactly the structure that O105 forbids for `T` itself but that its q-power
SHADOW must carry.

Mechanism: the multiplicity descent `∑_{y∈T} y^q = ∑_{f<pr} m_f·(ζ^q)^f`
(`sum_fiberwise_of_maps_to` + discrete-log reindexing), then O102 at `(p, r)`
with the primitive `pr`-th root `ζ^q`.  Composition of landed bricks; no new
analytic content — but the STATEMENT is the new, correct shape of the
three-prime window program (every window exponent with a nontrivial gcd
produces one such count law; assembling them against the `gcd = 1` reindexings
is the open reformulated window problem O111 gates).
-/

namespace ThreePrimeFiberCountLaw

open Finset

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- **The multiplicity descent**: the `q`-th-power sum of `T ⊆ μ_n` (`n = q·M`)
is the ℕ-weighted sum of its fiber counts over `μ_M`. -/
lemma sum_pow_eq_fiber_weight [DecidableEq L] {q M : ℕ} (hM : 0 < M)
    {ζq : L} (hζq : IsPrimitiveRoot ζq M)
    {T : Finset L} (hT : ∀ y ∈ T, (y ^ q) ^ M = 1) :
    ∑ y ∈ T, y ^ q
      = ∑ f ∈ Finset.range M,
          ((T.filter (fun y => y ^ q = ζq ^ f)).card : L) * ζq ^ f := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  -- partition `T` by the value of `y^q` inside `μ_M`
  have hmaps : ∀ y ∈ T, y ^ q ∈ T.image (· ^ q) :=
    fun y hy => Finset.mem_image_of_mem _ hy
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun y => y ^ q)]
  -- inner sums are constant on fibers
  have hinner : ∀ z ∈ T.image (· ^ q),
      ∑ y ∈ T.filter (fun y => y ^ q = z), y ^ q
        = ((T.filter (fun y => y ^ q = z)).card : L) * z := by
    intro z _
    rw [Finset.sum_congr rfl (fun y hy => (Finset.mem_filter.mp hy).2),
      Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner]
  -- extend the image sum to all of `μ_M` via the discrete log
  have himg : T.image (· ^ q) ⊆ (Finset.range M).image (ζq ^ ·) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨f, hf, hfe⟩ := hζq.eq_pow_of_pow_eq_one (hT y hy)
    exact Finset.mem_image.mpr ⟨f, Finset.mem_range.mpr hf, hfe⟩
  rw [Finset.sum_subset himg (fun z _ hznot => ?_), Finset.sum_image
    (fun a ha b hb hab => hζq.pow_inj (Finset.mem_range.mp ha)
      (Finset.mem_range.mp hb) hab)]
  -- off the image the fiber is empty
  have hempty : T.filter (fun y => y ^ q = z) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro y hy hyz
    exact hznot (hyz ▸ Finset.mem_image_of_mem _ hy)
  rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]

/-- **THE THREE-PRIME FIBER-COUNT LAW** (the first windowed structure theorem on
the post-O111 surface): for distinct primes `p, q, r`, `T ⊆ μ_{pqr}` (char 0)
with vanishing `q`-th-power sum, the `q`-power fiber-count function of `T`
decomposes into NONNEGATIVE `μ_p`- and `μ_r`-packet components at level `pr` —
the positivity O105 forbids for `T` itself holds for its `q`-power shadow. -/
theorem qpower_fiber_count_law [DecidableEq L] {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q * r))
    {T : Finset L} (hT : ∀ y ∈ T, y ^ (p * q * r) = 1)
    (hsumq : ∑ y ∈ T, y ^ q = 0) :
    ∃ A B : ℕ → ℕ, ∀ f < p * r,
      (T.filter (fun y => y ^ q = (ζ ^ q) ^ f)).card = A (f % r) + B (f % p) := by
  classical
  have hprpos : 0 < p * r := Nat.mul_pos hp.pos hr.pos
  have hζq : IsPrimitiveRoot (ζ ^ q) (p * r) :=
    hζ.pow (Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos) (by ring)
  have hTq : ∀ y ∈ T, (y ^ q) ^ (p * r) = 1 := by
    intro y hy
    rw [← pow_mul]
    have h : q * (p * r) = p * q * r := by ring
    rw [h]
    exact hT y hy
  -- the weighted vanishing at level `pr`
  have hw : ∑ f ∈ Finset.range (p * r),
      (((T.filter (fun y => y ^ q = (ζ ^ q) ^ f)).card : ℕ) : L)
        * (ζ ^ q) ^ f = 0 := by
    rw [← sum_pow_eq_fiber_weight hprpos hζq hTq]
    exact hsumq
  -- classify by the weighted squarefree two-prime theorem (exponent surface)
  obtain ⟨A, B, hAB⟩ :=
    (DeBruijnWeightedSquarefreeExp.debruijn_weighted_squarefree_exp
      hp hr hpr hζq
      (fun f => (T.filter (fun y => y ^ q = (ζ ^ q) ^ f)).card)).mp hw
  exact ⟨A, B, hAB⟩

end ThreePrimeFiberCountLaw

#print axioms ThreePrimeFiberCountLaw.sum_pow_eq_fiber_weight
#print axioms ThreePrimeFiberCountLaw.qpower_fiber_count_law
