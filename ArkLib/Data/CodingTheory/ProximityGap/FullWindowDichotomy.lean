/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPrimeWindowLaw

/-!
# Issue #232 — the UNIVERSAL window endpoint: full window ⟹ ∅/full at EVERY
modulus (O113)

The three-prime window assembly (O111/O112) needs its endpoint anchored: this
file proves the `t = n−1` stratum of the window law at EVERY modulus `n` — no
prime-structure hypothesis at all:

    `∑_{y∈T} y^j = 0` for all `1 ≤ j < n`   ⟹   `T = ∅` or `T ⊇ μ_n`

(`T ⊆ μ_n`, char 0).  Mechanism: discrete Fourier orthogonality — the double sum
`D(e₀) = ∑_{j<n} ∑_{e∈S} ζ^{j(e + n − e₀)}` evaluates to `n·𝟙_S(e₀)` one way
(inner geometric sums collapse off the diagonal) and to `|S|` the other way (the
window kills every `j ≠ 0` row), so the indicator is constant.

Position in the program: with O111 (the coset strata are DEAD at three primes)
and O112 (the per-exponent fiber-count laws are the live intermediate
structure), this endpoint brackets the open assembly question from above — at
`n = pqr` the window hierarchy now has machine-checked content at `t = 1`
(O109 components), at single gcd-exponents (O112 counts), and at `t = n−1`
(this dichotomy); the open content is exactly the intermediate interpolation.
-/

namespace FullWindowDichotomy

open Finset DeBruijnTowerWiring

variable {L : Type*} [Field L] [CharZero L]

/-- **THE FULL-WINDOW DICHOTOMY** (every modulus, no prime structure): a subset
of `μ_n` whose power sums vanish on the whole window `1 ≤ j < n` is empty or
all of `μ_n` — discrete Fourier orthogonality. -/
theorem full_window_dichotomy [DecidableEq L] {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset L} (hT : ∀ y ∈ T, y ^ n = 1)
    (hwin : ∀ j, 1 ≤ j → j < n → ∑ y ∈ T, y ^ j = 0) :
    T = ∅ ∨ ∀ z : L, z ^ n = 1 → z ∈ T := by
  classical
  rcases Finset.eq_empty_or_nonempty T with hemp | ⟨y₀, hy₀⟩
  · exact Or.inl hemp
  refine Or.inr ?_
  set S : Finset ℕ := expSet n ζ T with hS
  -- the key orthogonality evaluation
  have key : ∀ e₀ < n, ((n : ℕ) : L) * (if e₀ ∈ S then 1 else 0)
      = ((S.card : ℕ) : L) := by
    intro e₀ he₀
    -- the double sum, summed over `e` first
    have hway1 : ∑ e ∈ S, ∑ j ∈ Finset.range n, (ζ ^ (e + (n - e₀))) ^ j
        = ((n : ℕ) : L) * (if e₀ ∈ S then 1 else 0) := by
      have hterm : ∀ e ∈ S, ∑ j ∈ Finset.range n, (ζ ^ (e + (n - e₀))) ^ j
          = if e = e₀ then ((n : ℕ) : L) else 0 := by
        intro e he
        have helt : e < n := (mem_expSet.mp he).1
        by_cases heq : e = e₀
        · subst heq
          have hone : ζ ^ (e + (n - e)) = 1 := by
            have harith : e + (n - e) = n := by omega
            rw [harith]
            exact hζ.pow_eq_one
          rw [if_pos rfl, hone]
          simp
        · have hne1 : ζ ^ (e + (n - e₀)) ≠ 1 := by
            intro hcon
            have hdvd : n ∣ e + (n - e₀) :=
              (IsPrimitiveRoot.pow_eq_one_iff_dvd hζ _).mp hcon
            obtain ⟨c, hc⟩ := hdvd
            have hb1 : 1 ≤ e + (n - e₀) := by omega
            have hb2 : e + (n - e₀) < 2 * n := by omega
            have hc1 : c = 1 := by
              rcases Nat.lt_or_ge c 1 with h | h
              · interval_cases c
                omega
              · rcases Nat.lt_or_ge c 2 with h2 | h2
                · omega
                · have : 2 * n ≤ n * c := by
                    calc 2 * n = n * 2 := by ring
                      _ ≤ n * c := Nat.mul_le_mul_left n h2
                  omega
            rw [hc1, Nat.mul_one] at hc
            exact heq (by omega)
          have hxn : (ζ ^ (e + (n - e₀))) ^ n = 1 := by
            rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
          rw [if_neg heq]
          have hgeom := geom_sum_eq hne1 n
          rw [hgeom, hxn, sub_self, zero_div]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S e₀ (fun _ => ((n : ℕ) : L))]
      by_cases h : e₀ ∈ S
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    -- the double sum, summed over `j` first
    have hway2 : ∑ j ∈ Finset.range n, ∑ e ∈ S, (ζ ^ (e + (n - e₀))) ^ j
        = ((S.card : ℕ) : L) := by
      have hterm : ∀ j ∈ Finset.range n, ∑ e ∈ S, (ζ ^ (e + (n - e₀))) ^ j
          = if j = 0 then ((S.card : ℕ) : L) else 0 := by
        intro j hj
        have hjn := Finset.mem_range.mp hj
        by_cases hj0 : j = 0
        · subst hj0
          simp
        · rw [if_neg hj0]
          -- split the phase and use the window through the bridge
          have hsplit : ∀ e ∈ S, (ζ ^ (e + (n - e₀))) ^ j
              = (ζ ^ (n - e₀)) ^ j * (ζ ^ j) ^ e := by
            intro e _
            rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
            congr 1
            ring
          rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
          have hbridge : ∑ e ∈ S, (ζ ^ j) ^ e = ∑ y ∈ T, y ^ j := by
            rw [hS]
            exact TwoPrimeWindowLaw.sum_pow_expSet hn hζ hT j
          rw [hbridge, hwin j (by omega) hjn, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range n) 0
        (fun _ => ((S.card : ℕ) : L)), if_pos (Finset.mem_range.mpr hn)]
    rw [← hway1, Finset.sum_comm, hway2]
  -- nonempty forces the constant to be `1` everywhere
  have he₀S : ∃ e₀, e₀ ∈ S := by
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨e, he, hee⟩ := hζ.eq_pow_of_pow_eq_one (hT y₀ hy₀)
    exact ⟨e, mem_expSet.mpr ⟨he, hee ▸ hy₀⟩⟩
  obtain ⟨estar, hestar⟩ := he₀S
  have hestarlt : estar < n := (mem_expSet.mp hestar).1
  have hcardn : ((S.card : ℕ) : L) = ((n : ℕ) : L) := by
    have h := key estar hestarlt
    rw [if_pos hestar, mul_one] at h
    exact h.symm
  have hall : ∀ e₀ < n, e₀ ∈ S := by
    intro e₀ he₀
    have h := key e₀ he₀
    rw [hcardn] at h
    have hnL : ((n : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    by_contra hnot
    rw [if_neg hnot, mul_zero] at h
    exact hnL h.symm
  -- transport back to the field surface
  intro z hz
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨e, he, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  exact (mem_expSet.mp (hall e he)).2

end FullWindowDichotomy

#print axioms FullWindowDichotomy.full_window_dichotomy
