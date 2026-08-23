/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnIndicatorDisjointness

/-!
# Issue #232 — the de Bruijn squarefree classification completed to an EQUIVALENCE

The O87 brick (`DeBruijnIndicatorDisjointness.debruijn_squarefree_two_prime`) proved de
Bruijn step (3) at squarefree `n = p·q` in one direction: a vanishing `0/1` subset sum
of `μ_{pq}` is closed under `e ↦ e + p` or under `e ↦ e + q`.  The packet-cover brick
(`DeBruijnTwoPrime.two_prime_packet_cover`) added the per-element necessity at general
prime powers.  What neither states is the SUFFICIENCY half: shift-closed subsets DO
vanish.  This file supplies it and closes the squarefree case as an equivalence:

* `sum_pow_val_eq_zero_of_addClosed` — **the shift engine, any modulus**: a subset of
  `ZMod n` closed under translation by `d` has vanishing sum against any `n`-th root of
  unity `ζ` with `ζ^{d.val} ≠ 1`.  (Translation is a bijection of `S` onto itself, so
  the sum absorbs a factor `ζ^{d.val}`; a nonunit factor forces `0`.)  This is the
  sufficiency mechanism at EVERY level — it consumes nothing about `n`'s factorization.
* `vanishing_of_addClosed_packet` — the prime-power instantiation: in `ZMod (p^a·q^b)`,
  closure under the packet step `+ p^a·q^{b-1}` (a union of rotated full `μ_q`-packets)
  forces vanishing, for ζ primitive.  The sufficiency converse of the landed
  packet-cover necessity, at the same generality.
* `debruijn_squarefree_two_prime_iff` — **the capstone equivalence at squarefree `n`**:
  for distinct primes `p ≠ q`, `ζ` a primitive `pq`-th root in any characteristic-zero
  field, and `S ⊆ ZMod (p·q)`:

      ∑_{e ∈ S} ζ^e = 0  ⟺  S is closed under `+p` or closed under `+q`.

  Forward is O87; backward is the shift engine at `d = p` and `d = q` (where
  `ζ^p ≠ 1 ≠ ζ^q` by primitivity and `p, q < pq`).

Witness with teeth: `ζ + ζ^4 = 0` for the primitive 6th root over `ℂ` is derived from
the equivalence by a kernel-`decide`d closure check on `{1, 4} ⊆ ZMod 6` — the
vanishing comes out of arithmetic on exponent sets, with no root-of-unity manipulation.

Falsified first (`scripts/probes/probe_debruijn_squarefree.py`, exact `ℤ[x]/Φ_n`
arithmetic, exit 0): the equivalence checked EXHAUSTIVELY over all `2^n` subsets at
`n = 6, 10, 15` (10/34/38 vanishing sets, 0 mismatches) and on 30 000 sampled +
adversarial (pure-with-one-point-toggled) subsets each at `n = 21, 35` (5 000 vanishing
each, 0 mismatches); the sufficiency direction is exactly the probe's planted pure
families (all vanish), and the one-point toggles confirm it has teeth (none vanish).

## References

- [deBruijn53] N. G. de Bruijn, *On the factorization of cyclic groups*, Indag. Math.
  15 (1953).  Tracking issue #232; DISPROOF_LOG O66/O67/O73/O79/O87.
- In-tree: `DeBruijnIndicatorDisjointness` (the forward direction),
  `DeBruijnTwoPrime` (the packet cover), `CRTExponentGridSum.pow_mod_eq`.
-/

namespace DeBruijnSquarefreeIff

open Finset

/-- **The shift engine** (sufficiency at any modulus): a subset of `ZMod n` closed
under translation by `d` has vanishing sum against any `n`-th root of unity `ζ` whose
`d.val`-th power is not `1`.  Translation by `d` is a bijection of `S` onto itself, so
the sum equals itself times `ζ^{d.val}`. -/
theorem sum_pow_val_eq_zero_of_addClosed {L : Type*} [Field L] {n : ℕ} [NeZero n]
    {ζ : L} (hζn : ζ ^ n = 1) {d : ZMod n} (hd : ζ ^ d.val ≠ 1)
    {S : Finset (ZMod n)} (hcl : ∀ e ∈ S, e + d ∈ S) :
    ∑ e ∈ S, ζ ^ e.val = 0 := by
  classical
  have hinj : Function.Injective (fun e : ZMod n => e + d) :=
    fun a b hab => by simpa using hab
  have himg : S.image (fun e => e + d) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact hcl e he
    · rw [Finset.card_image_of_injective S hinj]
  have hshift : ∑ e ∈ S, ζ ^ e.val = (∑ e ∈ S, ζ ^ e.val) * ζ ^ d.val := by
    conv_lhs => rw [← himg]
    rw [Finset.sum_image fun a _ b _ hab => hinj hab, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ZMod.val_add, CRTExponentGridSum.pow_mod_eq hζn, pow_add]
  have hfac : (∑ e ∈ S, ζ ^ e.val) * (ζ ^ d.val - 1) = 0 := by
    rw [mul_sub, mul_one, ← hshift, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hd

/-- **Packet-step sufficiency at prime powers** (the converse of the landed packet
cover, same generality): in `ZMod (p^a·q^b)` (`b ≥ 1`, `ζ` primitive), a subset closed
under the packet step `+ p^a·q^{b-1}` — i.e. a union of rotated full `μ_q`-packets —
has vanishing sum. -/
theorem vanishing_of_addClosed_packet {L : Type*} [Field L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset (ZMod (p ^ a * q ^ b))}
    (hcl : ∀ e ∈ S, e + ((p ^ a * q ^ (b - 1) : ℕ) : ZMod (p ^ a * q ^ b)) ∈ S) :
    ∑ e ∈ S, ζ ^ e.val = 0 := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hqb1 : 0 < q ^ (b - 1) := pow_pos hq.pos (b - 1)
  have hstep : p ^ a * q ^ (b - 1) < p ^ a * q ^ b := by
    have : q ^ (b - 1) < q ^ b :=
      Nat.pow_lt_pow_right hq.one_lt (by omega)
    exact (Nat.mul_lt_mul_left hpa).mpr this
  haveI : NeZero (p ^ a * q ^ b) := ⟨(Nat.mul_pos hpa (pow_pos hq.pos b)).ne'⟩
  refine sum_pow_val_eq_zero_of_addClosed hζ.pow_eq_one ?_ hcl
  rw [ZMod.val_cast_of_lt hstep]
  intro h1
  have hdvd := (hζ.pow_eq_one_iff_dvd _).mp h1
  have hle := Nat.le_of_dvd (Nat.mul_pos hpa hqb1) hdvd
  omega

/-- **The de Bruijn classification at squarefree `n = p·q`, as an equivalence**: a
`0/1` subset sum of `μ_{pq}` vanishes IFF the exponent set is closed under `+p` (a
disjoint union of rotated full `μ_q`-packets) or closed under `+q` (rotated full
`μ_p`-packets).  Forward: `DeBruijnIndicatorDisjointness.debruijn_squarefree_two_prime`
(O87).  Backward: the shift engine. -/
theorem debruijn_squarefree_two_prime_iff {L : Type*} [Field L] [CharZero L]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q)) (S : Finset (ZMod (p * q))) :
    (∑ e ∈ S, ζ ^ e.val = 0)
      ↔ ((∀ e ∈ S, e + ((p : ℕ) : ZMod (p * q)) ∈ S)
        ∨ (∀ e ∈ S, e + ((q : ℕ) : ZMod (p * q)) ∈ S)) := by
  haveI : NeZero (p * q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  constructor
  · exact fun hsum =>
      DeBruijnIndicatorDisjointness.debruijn_squarefree_two_prime hp hq hpq hζ hsum
  · rintro (hcl | hcl)
    · -- closed under `+p`: `ζ^p ≠ 1` since `p < p·q`
      refine sum_pow_val_eq_zero_of_addClosed hζ.pow_eq_one ?_ hcl
      have hlt : p < p * q := lt_mul_iff_one_lt_right hp.pos |>.mpr hq.one_lt
      rw [ZMod.val_cast_of_lt hlt]
      intro h1
      have hle := Nat.le_of_dvd hp.pos ((hζ.pow_eq_one_iff_dvd _).mp h1)
      omega
    · -- closed under `+q`: `ζ^q ≠ 1` since `q < p·q`
      refine sum_pow_val_eq_zero_of_addClosed hζ.pow_eq_one ?_ hcl
      have hlt : q < p * q := lt_mul_iff_one_lt_left hq.pos |>.mpr hp.one_lt
      rw [ZMod.val_cast_of_lt hlt]
      intro h1
      have hle := Nat.le_of_dvd hq.pos ((hζ.pow_eq_one_iff_dvd _).mp h1)
      omega

/-- Witness with teeth: `ζ + ζ^4 = 0` for the primitive 6th root of unity over `ℂ`,
derived from the equivalence by a kernel-`decide`d closure check on the exponent set
`{1, 4} ⊆ ZMod 6` (it is `+3`-closed: `1 + 3 = 4`, `4 + 3 = 1`) — no root-of-unity
manipulation. -/
example : ∑ e ∈ ({1, 4} : Finset (ZMod (2 * 3))),
    (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ e.val = 0 := by
  have h6 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 6)) 6 := by
    have h := Complex.isPrimitiveRoot_exp 6 (by norm_num)
    norm_num at h
    exact h
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 6)) (2 * 3) := by
    norm_num [h6]
  exact (debruijn_squarefree_two_prime_iff Nat.prime_two Nat.prime_three (by norm_num)
    hζ _).mpr (Or.inr (by decide))

/-- The forward direction fires on the same nonempty vanishing set, with the vanishing
hypothesis supplied by the backward direction: the closure disjunction for `{1, 4}` is
a consequence of the equivalence, end to end. -/
example :
    (∀ e ∈ ({1, 4} : Finset (ZMod (2 * 3))), e + ((2 : ℕ) : ZMod (2 * 3)) ∈
        ({1, 4} : Finset (ZMod (2 * 3))))
    ∨ (∀ e ∈ ({1, 4} : Finset (ZMod (2 * 3))), e + ((3 : ℕ) : ZMod (2 * 3)) ∈
        ({1, 4} : Finset (ZMod (2 * 3)))) := by
  have h6 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 6)) 6 := by
    have h := Complex.isPrimitiveRoot_exp 6 (by norm_num)
    norm_num at h
    exact h
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 6)) (2 * 3) := by
    norm_num [h6]
  exact (debruijn_squarefree_two_prime_iff Nat.prime_two Nat.prime_three (by norm_num)
    hζ _).mp ((debruijn_squarefree_two_prime_iff Nat.prime_two Nat.prime_three
      (by norm_num) hζ _).mpr (Or.inr (by decide)))

end DeBruijnSquarefreeIff

#print axioms DeBruijnSquarefreeIff.sum_pow_val_eq_zero_of_addClosed
#print axioms DeBruijnSquarefreeIff.vanishing_of_addClosed_packet
#print axioms DeBruijnSquarefreeIff.debruijn_squarefree_two_prime_iff
