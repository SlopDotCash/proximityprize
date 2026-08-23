/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreePrimePacketRefutation
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWindowedLaw

/-!
# Issue #232 — the O70 divisor-coset window law is FALSE at three primes (O111)

The remaining window-law residue ("the t > 1 law past two primes — no
literature") gets its statement-level redteam: the O70 FORM of the law — every
windowed-vanishing subset decomposes into full `μ_d`-cosets with `d ∣ n`,
`d > t` — is provably FALSE at the first three-prime modulus, ALREADY at the
`t = 1` stratum.

`divisor_coset_law_fails_three_primes`: the O105 witness
`S = {5, 6, 12, 18, 24, 25} ⊆ [0, 30)` vanishes, yet through the point `5` NO
full `μ_d`-coset lies inside `S` for ANY divisor `1 < d ∣ 30` — so `S` admits no
divisor-coset decomposition whatsoever (every nonempty union of cosets covers
each of its points by a full coset).

Interpretation for the ledger: the two-prime window law (O97) cannot extend to
3+ primes in its coset form — its very STATEMENT dies, not merely its proof.
Any 3+-prime window law must live on a different surface; the candidate is the
ℚ-component form (O109: vanishing ⟺ prime-fiber components), with windowed
power sums constraining the components.  That reformulation is the genuinely
open mathematics; this brick pins the obstruction that forces it.
-/

namespace ThreePrimeWindowObstruction

open Finset DeBruijnTwoPrimeAssembly DeBruijnWindowedLaw

variable {L : Type*} [Field L] [CharZero L]

omit [Field L] [CharZero L] in
/-- Rotating any element of a canonical packet by the packet step stays inside
the packet.  This is the bridge from the pointwise `5` obstruction to the
`IsWindowCosetUnion` predicate. -/
lemma packet_rotates_of_mem {n d : ℕ} (hn : 0 < n) (hd : d ∣ n)
    {P : Finset ℕ} (hP : IsPacket n d P) {e : ℕ} (he : e ∈ P) :
    ∀ t < d, (e + t * (n / d)) % n ∈ P := by
  obtain ⟨r, hr, rfl⟩ := hP
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp he
  intro t ht
  subst heq
  have hd0 : 0 < d := by omega
  have hstep0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hd) hd0
  have hn_eq : d * (n / d) = n := Nat.mul_div_cancel' hd
  have hmodlt : (s + t) % d < d := Nat.mod_lt _ hd0
  refine Finset.mem_image.mpr
    ⟨(s + t) % d, Finset.mem_range.mpr hmodlt, ?_⟩
  have hlt : r + ((s + t) % d) * (n / d) < n := by
    calc r + ((s + t) % d) * (n / d)
        < n / d + ((s + t) % d) * (n / d) := by omega
      _ = (((s + t) % d) + 1) * (n / d) := by ring
      _ ≤ d * (n / d) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hmodlt)
      _ = n := hn_eq
  have hdecomp : r + (s + t) * (n / d)
      = r + ((s + t) % d) * (n / d) + ((s + t) / d) * n := by
    calc r + (s + t) * (n / d)
        = r + (((s + t) % d + d * ((s + t) / d)) * (n / d)) := by
            rw [Nat.mod_add_div]
      _ = r + ((s + t) % d) * (n / d)
          + ((s + t) / d) * (d * (n / d)) := by ring
      _ = r + ((s + t) % d) * (n / d) + ((s + t) / d) * n := by rw [hn_eq]
  exact (calc
    (r + s * (n / d) + t * (n / d)) % n
        = (r + (s + t) * (n / d)) % n := by ring_nf
    _ = (r + ((s + t) % d) * (n / d) + ((s + t) / d) * n) % n := by rw [hdecomp]
    _ = r + ((s + t) % d) * (n / d) := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]).symm

omit [Field L] [CharZero L] in
/-- The O105 witness contains no full divisor coset through exponent `5`. -/
lemma witness_no_divisor_coset_through_five :
    ∀ d ∈ Nat.divisors 30, 1 < d →
        ¬ ∀ t < d, (5 + t * (30 / d)) % 30
            ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ) := by
  decide

omit [Field L] [CharZero L] in
/-- The O105 witness is not a window-coset union at `n = 30`, `t = 1`.
Thus the predicate used by the two-prime window law and fiber-count theorem
itself fails to describe the first three-prime vanishing witness. -/
theorem witness_not_isWindowCosetUnion :
    ¬ IsWindowCosetUnion 30 1
        ({5, 6, 12, 18, 24, 25} : Finset ℕ) := by
  rintro ⟨Ps, hPs, _hdisj, hUnion⟩
  have h5 : 5 ∈ Ps.biUnion id := by
    rw [← hUnion]
    decide
  obtain ⟨P, hP, h5P⟩ := Finset.mem_biUnion.mp h5
  obtain ⟨d, hdn, htd, hPacket⟩ := hPs P hP
  have hdmem : d ∈ Nat.divisors 30 :=
    Nat.mem_divisors.mpr ⟨hdn, by norm_num⟩
  refine (witness_no_divisor_coset_through_five d hdmem htd) ?_
  intro t ht
  rw [hUnion]
  exact Finset.mem_biUnion.mpr
    ⟨P, hP, packet_rotates_of_mem (n := 30) (d := d) (by norm_num) hdn hPacket h5P t ht⟩

omit [CharZero L] in
/-- **The divisor-coset window law fails at three primes** (`n = 30`, `t = 1`
stratum): a vanishing subset of `μ₃₀` exists through whose point `5` no full
`μ_d`-coset (`1 < d ∣ 30`) lies inside the set — the O70 coset form of the
window law has no three-prime extension. -/
theorem divisor_coset_law_fails_three_primes {ζ : L}
    (hζ : IsPrimitiveRoot ζ 30) :
    (∑ e ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ), ζ ^ e = 0)
    ∧ ∀ d ∈ Nat.divisors 30, 1 < d →
        ¬ ∀ t < d, (5 + t * (30 / d)) % 30
            ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ) := by
  refine ⟨(ThreePrimePacketRefutation.debruijn_packet_conjecture_fails_three_primes
    hζ).1, ?_⟩
  exact witness_no_divisor_coset_through_five

end ThreePrimeWindowObstruction

#print axioms ThreePrimeWindowObstruction.packet_rotates_of_mem
#print axioms ThreePrimeWindowObstruction.witness_no_divisor_coset_through_five
#print axioms ThreePrimeWindowObstruction.witness_not_isWindowCosetUnion
#print axioms ThreePrimeWindowObstruction.divisor_coset_law_fails_three_primes
