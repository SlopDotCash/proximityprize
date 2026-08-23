/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPrimeWindowLaw
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedSquarefreeExp

/-!
# Issue #232 — the partial-DFT closure law: the dense window `{j : p ∤ j}` forces
`μ_p`-closure at EVERY modulus (O114)

The first nontrivial INTERMEDIATE stratum of the window hierarchy past two
primes.  For any prime `p ∣ n` and any `T ⊆ μ_n` (char 0):

    `∑_{y∈T} y^j = 0` for all `1 ≤ j < n` with `p ∤ j`   ⟹   `T` is `μ_p`-closed

(with the landed converse `TwoPrimeWindowLaw.pow_sum_eq_zero_of_mu_p_closed`,
an exact characterization).  Fourier mechanism: the window says the indicator's
spectrum is supported on `pℤ`, hence the indicator is invariant under the
exponent shift `+ n/p` — which is exactly multiplication by `μ_p`.

Proof: the DFT point mass `∑_{j<n} (ζ^{n−a})^j·S_j = n·𝟙_T(ζ^a)`
(`dft_point_mass`, the O113 double sum summed `e`-first) is compared at
`a = e₀` and at the shift `a = (e₀ + n/p) % n`: rows with `p ∣ j` carry EQUAL
phases (`p·(e₀ + n/p) ≡ p·e₀ [MOD n]`, no window needed), rows with `p ∤ j` die
by the window — so the two point masses agree and membership is shift-invariant;
iterating gives closure.

Position in the program: at `n = pqr` the window hierarchy is machine-checked at
FOUR strata — `t = 1` ℚ-components (O109), single gcd-exponents (O112 counts),
the dense coprime-complement windows (this: e.g. all odd `j < 30` force
antipodal closure), and the full window (O113) — with the coset strata dead
(O111).  The open interpolation is now: how SPARSE can a `μ_p`-forcing window be
at three primes (at two primes the sharp answer is O97's `{q^c}`, whose
packet mechanism O105 removed)?
-/

namespace PartialDFTClosure

open Finset DeBruijnTowerWiring

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- **The DFT point mass**: for `a < n`, the phased row sums of `T` recover the
indicator — `∑_{j<n} (ζ^{n−a})^j · (∑_{y∈T} y^j) = n·𝟙_T(ζ^a)`. -/
lemma dft_point_mass [DecidableEq L] {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset L} (hT : ∀ y ∈ T, y ^ n = 1) {a : ℕ} (ha : a < n) :
    ∑ j ∈ Finset.range n, (ζ ^ (n - a)) ^ j * (∑ y ∈ T, y ^ j)
      = (n : L) * (if ζ ^ a ∈ T then 1 else 0) := by
  classical
  have hrow : ∀ j ∈ Finset.range n,
      (ζ ^ (n - a)) ^ j * (∑ y ∈ T, y ^ j)
        = ∑ e ∈ expSet n ζ T, (ζ ^ (e + (n - a))) ^ j := by
    intro j _
    rw [← TwoPrimeWindowLaw.sum_pow_expSet hn hζ hT j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  have hterm : ∀ e ∈ expSet n ζ T,
      ∑ j ∈ Finset.range n, (ζ ^ (e + (n - a))) ^ j
        = if e = a then (n : L) else 0 := by
    intro e he
    have helt : e < n := (mem_expSet.mp he).1
    by_cases heq : e = a
    · subst heq
      have hone : ζ ^ (e + (n - e)) = 1 := by
        have harith : e + (n - e) = n := by omega
        rw [harith]
        exact hζ.pow_eq_one
      rw [if_pos rfl, hone]
      simp
    · have hne1 : ζ ^ (e + (n - a)) ≠ 1 := by
        intro hcon
        have hdvd : n ∣ e + (n - a) :=
          (IsPrimitiveRoot.pow_eq_one_iff_dvd hζ _).mp hcon
        obtain ⟨c, hc⟩ := hdvd
        have hc1 : c = 1 := by
          rcases Nat.lt_or_ge c 1 with h | h
          · interval_cases c
            omega
          · rcases Nat.lt_or_ge c 2 with h2 | h2
            · omega
            · have h3 : 2 * n ≤ n * c := by
                calc 2 * n = n * 2 := by ring
                  _ ≤ n * c := Nat.mul_le_mul_left n h2
              omega
        rw [hc1, Nat.mul_one] at hc
        exact heq (by omega)
      have hxn : (ζ ^ (e + (n - a))) ^ n = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      rw [if_neg heq, geom_sum_eq hne1 n, hxn, sub_self, zero_div]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (expSet n ζ T) a
    (fun _ => (n : L))]
  have hmem : a ∈ expSet n ζ T ↔ ζ ^ a ∈ T := by
    rw [mem_expSet]
    exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  by_cases h : ζ ^ a ∈ T
  · rw [if_pos (hmem.mpr h), if_pos h, mul_one]
  · rw [if_neg (fun hc => h (hmem.mp hc)), if_neg h, mul_zero]

/-- **THE PARTIAL-DFT CLOSURE LAW** (every modulus): power sums vanishing at
every exponent `1 ≤ j < n` not divisible by `p` force `μ_p`-closure of
`T ⊆ μ_n` — spectrum supported on `pℤ` means shift-invariance by `n/p`. -/
theorem partial_dft_mu_p_closed [DecidableEq L] {n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset L} (hT : ∀ y ∈ T, y ^ n = 1)
    (hwin : ∀ j, 1 ≤ j → j < n → ¬ p ∣ j → ∑ y ∈ T, y ^ j = 0) :
    ∀ y ∈ T, ∀ g : L, g ^ p = 1 → g * y ∈ T := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hnL : (n : L) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hζne : ζ ≠ 0 := by
    intro h0
    have h1 := hζ.pow_eq_one
    rw [h0, zero_pow hn.ne'] at h1
    exact zero_ne_one h1
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
  -- one-step shift invariance of membership
  have hshift : ∀ e₀ < n, ζ ^ e₀ ∈ T → ζ ^ ((e₀ + n / p) % n) ∈ T := by
    intro e₀ he₀ hmem₀
    set e₁ : ℕ := (e₀ + n / p) % n with he₁def
    have he₁ : e₁ < n := Nat.mod_lt _ hn
    -- congruent `p`-multiples: `p·e₁ ≡ p·e₀ [MOD n]`
    have hpe : (p * e₁) % n = (p * e₀) % n := by
      have h1 : (p * e₁) % n = (p * (e₀ + n / p)) % n := by
        rw [he₁def, Nat.mul_mod, Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.mul_mod]
      rw [h1, Nat.mul_add, hmul, Nat.add_mod_right]
    -- row-by-row agreement of the two point masses
    have hrows : ∀ j ∈ Finset.range n,
        (ζ ^ (n - e₀)) ^ j * (∑ y ∈ T, y ^ j)
          = (ζ ^ (n - e₁)) ^ j * (∑ y ∈ T, y ^ j) := by
      intro j hj
      have hjn := Finset.mem_range.mp hj
      by_cases hj0 : j = 0
      · subst hj0
        simp
      · by_cases hpj : p ∣ j
        · -- equal phases on the `pℤ` rows
          obtain ⟨u, rfl⟩ := hpj
          congr 1
          rw [← pow_mul, ← pow_mul]
          -- both phases multiply the same unit to `1`
          have hclose : ∀ a : ℕ, a < n →
              ζ ^ ((n - a) * (p * u)) * ζ ^ (p * u * a) = 1 := by
            intro a halt
            rw [← pow_add]
            have harith : (n - a) * (p * u) + p * u * a = n * (p * u) := by
              have hsum : (n - a) + a = n := by omega
              calc (n - a) * (p * u) + p * u * a
                  = ((n - a) + a) * (p * u) := by ring
                _ = n * (p * u) := by rw [hsum]
            rw [harith, pow_mul, hζ.pow_eq_one, one_pow]
          have hsame : ζ ^ (p * u * e₀) = ζ ^ (p * u * e₁) := by
            rw [← DeBruijnWeightedSquarefreeExp.pow_mod_eq hζ (p * u * e₀),
              ← DeBruijnWeightedSquarefreeExp.pow_mod_eq hζ (p * u * e₁)]
            congr 1
            calc (p * u * e₀) % n = (u * (p * e₀)) % n := by ring_nf
              _ = (u % n) * ((p * e₀) % n) % n := Nat.mul_mod u (p * e₀) n
              _ = (u % n) * ((p * e₁) % n) % n := by rw [hpe]
              _ = (u * (p * e₁)) % n := (Nat.mul_mod u (p * e₁) n).symm
              _ = (p * u * e₁) % n := by ring_nf
          have hcne : ζ ^ (p * u * e₀) ≠ 0 := pow_ne_zero _ hζne
          have h0 := hclose e₀ he₀
          have h1 := hclose e₁ he₁
          rw [← hsame] at h1
          exact mul_right_cancel₀ hcne (h0.trans h1.symm)
        · -- the window kills the `p ∤ j` rows
          rw [hwin j (by omega) hjn hpj, mul_zero, mul_zero]
    have h1 := dft_point_mass hn hζ hT he₀
    have h2 := dft_point_mass hn hζ hT he₁
    rw [Finset.sum_congr rfl hrows, h2] at h1
    have hiff := mul_left_cancel₀ hnL h1
    by_contra hnot
    rw [if_pos hmem₀, if_neg hnot] at hiff
    exact zero_ne_one hiff
  -- iterate the shift, then assemble closure
  have hiter : ∀ k : ℕ, ∀ e₀ < n, ζ ^ e₀ ∈ T →
      ζ ^ ((e₀ + k * (n / p)) % n) ∈ T := by
    intro k
    induction k with
    | zero =>
      intro e₀ he₀ h
      simpa [Nat.mod_eq_of_lt he₀] using h
    | succ k ih =>
      intro e₀ he₀ h
      have h1 := ih e₀ he₀ h
      have h2 := hshift _ (Nat.mod_lt _ hn) h1
      have harith : ((e₀ + k * (n / p)) % n + n / p) % n
          = (e₀ + (k + 1) * (n / p)) % n := by
        rw [Nat.mod_add_mod]
        congr 1
        ring
      rwa [harith] at h2
  intro y hy g hg
  obtain ⟨e, he, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hT y hy)
  have hξ : IsPrimitiveRoot (ζ ^ (n / p)) p :=
    hζ.pow hn (Nat.div_mul_cancel hpn).symm
  obtain ⟨k, _, rfl⟩ := hξ.eq_pow_of_pow_eq_one hg
  have hgy : ((ζ ^ (n / p)) ^ k) * ζ ^ e = ζ ^ ((e + k * (n / p)) % n) := by
    rw [← pow_mul, ← pow_add, DeBruijnWeightedSquarefreeExp.pow_mod_eq hζ]
    congr 1
    ring
  rw [hgy]
  exact hiter k e he hy

/-- **Exponent-set form of the partial-DFT law**: under the dense window
`p ∤ j`, the discrete logarithm support is invariant under the canonical
`μ_p` shift `e ↦ e + n/p`.  This packages the field-surface closure theorem in
the exact exponent language used by the window/interpolation files. -/
theorem partial_dft_expSet_step_closed [DecidableEq L] {n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset L} (hT : ∀ y ∈ T, y ^ n = 1)
    (hwin : ∀ j, 1 ≤ j → j < n → ¬ p ∣ j → ∑ y ∈ T, y ^ j = 0) :
    ∀ e ∈ expSet n ζ T, (e + n / p) % n ∈ expSet n ζ T := by
  intro e he
  have hcl := partial_dft_mu_p_closed hp hpn hn hζ hT hwin
  have heT : ζ ^ e ∈ T := (mem_expSet.mp he).2
  have hroot : (ζ ^ (n / p)) ^ p = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hpn, hζ.pow_eq_one]
  have hmem : ζ ^ (n / p) * ζ ^ e ∈ T := hcl (ζ ^ e) heT (ζ ^ (n / p)) hroot
  refine mem_expSet.mpr ⟨Nat.mod_lt _ hn, ?_⟩
  convert hmem using 1
  rw [DeBruijnWeightedSquarefreeExp.pow_mod_eq hζ, pow_add, mul_comm]

/-- The concrete `n = 30`, `p = 2` tooth: if all odd power sums below `30`
vanish, then the subset is antipodally closed. -/
theorem odd_window_antipodal_closed_30 {ζ : L}
    (hζ : IsPrimitiveRoot ζ 30)
    {T : Finset L} (hT : ∀ y ∈ T, y ^ 30 = 1)
    (hwin : ∀ j, 1 ≤ j → j < 30 → ¬ 2 ∣ j → ∑ y ∈ T, y ^ j = 0) :
    ∀ y ∈ T, -y ∈ T := by
  classical
  have hcl := partial_dft_mu_p_closed Nat.prime_two (by norm_num : 2 ∣ 30)
    (by norm_num : 0 < 30) hζ hT hwin
  intro y hy
  have hroot : (-1 : L) ^ 2 = 1 := by norm_num
  simpa using hcl y hy (-1 : L) hroot

/-- **The dense window EXACTLY characterizes `μ_p`-closure** at every modulus
(`0 ∉ T` for the converse): the iff packaging with O97's converse. -/
theorem partial_dft_iff [DecidableEq L] {n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {T : Finset L} (h0 : (0 : L) ∉ T) (hT : ∀ y ∈ T, y ^ n = 1) :
    (∀ j, 1 ≤ j → j < n → ¬ p ∣ j → ∑ y ∈ T, y ^ j = 0) ↔
      ∀ y ∈ T, ∀ g : L, g ^ p = 1 → g * y ∈ T := by
  constructor
  · exact partial_dft_mu_p_closed hp hpn hn hζ hT
  · intro hcl j _ _ hpj
    exact TwoPrimeWindowLaw.pow_sum_eq_zero_of_mu_p_closed hp hpn hn hζ h0
      hcl hpj

end PartialDFTClosure

#print axioms PartialDFTClosure.dft_point_mass
#print axioms PartialDFTClosure.partial_dft_mu_p_closed
#print axioms PartialDFTClosure.partial_dft_expSet_step_closed
#print axioms PartialDFTClosure.odd_window_antipodal_closed_30
#print axioms PartialDFTClosure.partial_dft_iff
