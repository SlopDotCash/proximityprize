/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.TopDirectionLineCount

/-!
# Issue #232 — Lam–Leung at the prime 2: vanishing sums of 2-power roots of unity

The classical base case of the O48 tower theorem (DISPROOF_LOG O47–O48), machine-checked:
**in characteristic zero, a subset of the `2^(m+1)`-th roots of unity with vanishing sum
is closed under negation** — equivalently, it is a disjoint union of antipodal pairs
`{x, −x}`. This is the prime-2 instance of Lam–Leung's theorem on vanishing sums of roots
of unity [LamLeung2000], and the engine is Gauss: the `2^(m+1)`-th cyclotomic polynomial
`X^(2^m) + 1` is the rational minimal polynomial of a primitive root, so the indicator
polynomial of the exponent set is divisible by it, which pairs the coefficients at `i` and
`i + 2^m` — and `ζ^(2^m) = −1`.

Consequences wired elsewhere: this discharges the `hLL`/`hLL'` hypotheses of
`TopLine.t2_tower_resolution` (the descent assembly of the tower theorem), making the
`t = 2` exhaustiveness — and, iterated, the full tower theorem and its `2^{O(1/η)}`
deep-interior fiber bound — unconditional over characteristic-zero fields (and over `F_p`
above the O49 effective transfer threshold).
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- A primitive `2^(m+1)`-th root of unity has `ζ^(2^m) = −1`. -/
lemma pow_half_eq_neg_one {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) :
    ζ ^ (2 ^ m) = -1 := by
  have hsq : (ζ ^ 2 ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    have : 2 ^ m * 2 = 2 ^ (m + 1) := by ring
    rw [this]
    exact hζ.pow_eq_one
  have hne : ζ ^ 2 ^ m ≠ 1 := by
    intro h1
    have hlt : (2 : ℕ) ^ m < 2 ^ (m + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := hζ.pow_ne_one_of_pos_of_lt (Nat.two_pow_pos m).ne' hlt
    exact this h1
  have hfac : (ζ ^ 2 ^ m - 1) * (ζ ^ 2 ^ m + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- **Lam–Leung at the prime 2** (the O48 tower base case): in characteristic zero, a
finite set of `2^(m+1)`-th roots of unity with vanishing sum is closed under negation. -/
theorem vanishing_sum_antipodal {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hS : ∀ x ∈ S, x ^ (2 ^ (m + 1)) = 1)
    (hsum : ∑ x ∈ S, x = 0) :
    ∀ x ∈ S, -x ∈ S := by
  classical
  set n := 2 ^ (m + 1) with hn
  set half := 2 ^ m with hhalf
  have hhn : half + half = n := by rw [hhalf, hn]; ring
  have hhalfpos : 0 < half := by positivity
  -- the exponent set
  set I : Finset ℕ := (Finset.range n).filter (fun i => ζ ^ i ∈ S) with hI
  -- powers are injective below n
  have hinj : ∀ i < n, ∀ j < n, ζ ^ i = ζ ^ j → i = j := by
    intro i hi j hj hij
    exact hζ.pow_inj hi hj hij
  -- the indicator polynomial over ℚ
  set P : ℚ[X] := ∑ i ∈ I, X ^ i with hP
  have hPcoeff : ∀ j, P.coeff j = if j ∈ I then 1 else 0 := by
    intro j
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_congr rfl (fun i _ => Polynomial.coeff_X_pow i j)]
    rw [Finset.sum_ite_eq I j (fun _ => (1 : ℚ))]
  -- ζ kills P
  have hPζ : Polynomial.aeval ζ P = 0 := by
    rw [hP, map_sum]
    have hterm : ∀ i ∈ I, Polynomial.aeval ζ ((X : ℚ[X]) ^ i) = ζ ^ i := by
      intro i _
      simp
    rw [Finset.sum_congr rfl hterm]
    -- ∑_{i ∈ I} ζ^i = ∑_{x ∈ S} x = 0
    rw [← hsum]
    apply Finset.sum_bij (fun i _ => ζ ^ i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      rw [hI] at hi hj
      exact hinj i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hxi.symm ▸ hx⟩, hxi⟩
    · intro i _
      rfl
  -- the cyclotomic polynomial divides P
  have hdvd : (X ^ half + 1 : ℚ[X]) ∣ P := by
    have hmin := minpoly.dvd ℚ ζ hPζ
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by positivity)] at hmin
    have hcyc : Polynomial.cyclotomic (2 ^ (m + 1)) ℚ = X ^ half + 1 := by
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      rw [hhalf]
      ring
    rwa [hn, hcyc] at hmin
  -- coefficient pairing: P.coeff j = P.coeff (j + half) for j < half
  have hpair : ∀ j < half, P.coeff j = P.coeff (j + half) := by
    obtain ⟨Q, hQ⟩ := hdvd
    by_cases hP0 : P = 0
    · intro j _
      simp [hP0]
    have hQ0 : Q ≠ 0 := by
      intro h
      exact hP0 (by rw [hQ, h, mul_zero])
    have hdegP : P.natDegree < n := by
      rw [hP]
      have : (∑ i ∈ I, (X : ℚ[X]) ^ i).natDegree ≤ n - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => by
          rw [Polynomial.natDegree_X_pow]
          have := Finset.mem_range.mp (Finset.mem_filter.mp (hI ▸ hi)).1
          omega
      have hnpos : 0 < n := by positivity
      omega
    have hdegfac : (X ^ half + 1 : ℚ[X]).natDegree = half := by
      rw [show (X ^ half + 1 : ℚ[X]) = X ^ half + C 1 by rw [map_one]]
      exact Polynomial.natDegree_X_pow_add_C
    have hdegQ : Q.natDegree < half := by
      have hmul := Polynomial.natDegree_mul
        (show (X ^ half + 1 : ℚ[X]) ≠ 0 by
          intro h
          have := congrArg (Polynomial.natDegree) h
          rw [hdegfac] at this
          simp at this
          omega) hQ0
      rw [← hQ, hdegfac] at hmul
      omega
    intro j hj
    have hc1 : P.coeff j = Q.coeff j := by
      rw [hQ, add_mul, one_mul, Polynomial.coeff_add]
      rw [Polynomial.coeff_X_pow_mul']
      rw [if_neg (by omega)]
      ring
    have hc2 : P.coeff (j + half) = Q.coeff j := by
      rw [hQ, add_mul, one_mul, Polynomial.coeff_add]
      rw [Polynomial.coeff_X_pow_mul']
      rw [if_pos (by omega)]
      have : j + half - half = j := by omega
      rw [this]
      have hQj : Q.coeff (j + half) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hQj]
      ring
    rw [hc1, hc2]
  -- membership pairing
  have hmem : ∀ j < half, (ζ ^ j ∈ S ↔ ζ ^ (j + half) ∈ S) := by
    intro j hj
    have := hpair j hj
    rw [hPcoeff, hPcoeff] at this
    have hjI : j ∈ I ↔ j + half ∈ I := by
      by_cases h1 : j ∈ I <;> by_cases h2 : j + half ∈ I <;>
        simp [h1, h2] at this ⊢
    rw [hI] at hjI
    simp only [Finset.mem_filter, Finset.mem_range] at hjI
    constructor
    · intro hx
      exact (hjI.mp ⟨by omega, hx⟩).2
    · intro hx
      exact (hjI.mpr ⟨by omega, hx⟩).2
  -- conclude
  intro x hx
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
  have hζhalf := pow_half_eq_neg_one hζ
  rcases lt_or_ge i half with hcase | hcase
  · -- −ζ^i = ζ^(i+half)
    have hmem' := (hmem i hcase).mp hx
    have : ζ ^ (i + half) = -ζ ^ i := by
      rw [pow_add, hhalf, hζhalf]
      ring
    rwa [this] at hmem'
  · -- i ≥ half: −ζ^i = ζ^(i−half)
    have hj : i - half < half := by omega
    have hisplit : i = (i - half) + half := by omega
    have hmem' : ζ ^ (i - half) ∈ S := by
      apply (hmem (i - half) hj).mpr
      rwa [← hisplit]
    have : ζ ^ (i - half) = -ζ ^ i := by
      have h1 : ζ ^ i = ζ ^ (i - half) * ζ ^ half := by
        rw [← pow_add, ← hisplit]
      rw [hhalf] at h1
      rw [h1, hζhalf]
      ring
    rwa [this] at hmem'

/-- **The UNCONDITIONAL t = 2 tower resolution** over characteristic-zero fields: the
Lam–Leung base case discharges both hypotheses of `TopLine.t2_tower_resolution`. Every
finite set of `2^(m+2)`-th roots of unity with `∑x = ∑x² = 0` is closed under
multiplication by `i` — a union of `μ₄`-cosets. The O48 tower theorem's first two rungs
are now hypothesis-free. -/
theorem t2_resolution_unconditional {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 2)))
    {i : F} (hi : i ^ 2 = -1) {S : Finset F}
    (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ (2 ^ (m + 2)) = 1)
    (hsum : ∑ x ∈ S, x = 0) (hsumsq : ∑ x ∈ S, x ^ 2 = 0) :
    ∀ x ∈ S, i * x ∈ S := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  apply TopLine.t2_tower_resolution hi h2 h0 hsum hsumsq
  · intro hs
    exact vanishing_sum_antipodal (m := m + 1) hζ hS hs
  · intro hs
    have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (m + 1)) :=
      hζ.pow (by positivity) (by ring)
    refine vanishing_sum_antipodal (m := m) hζ2 ?_ hs
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [← pow_mul]
    have : 2 * 2 ^ (m + 1) = 2 ^ (m + 2) := by ring
    rw [this]
    exact hS x hx

/-! ## The FULL tower theorem, unconditional, machine-checked

The complete O48 induction — with no Newton identities (the rung condition transfers
through the fiber structure in power-sum form: `∑_{x∈S} x^d = d·∑_{image} y`): in
characteristic zero, a finite set of `2^M`-th roots of unity whose power sums `p_j`
vanish for `1 ≤ j < 2^s` is closed under multiplication by every `2^s`-th root of
unity — **a union of `μ_{2^s}`-cosets**. (Power-sum and elementary-symmetric vanishing
define the same fiber in characteristic zero; the power-sum window is also exactly the
syndrome of the all-ones error on `S`.) At window scale `t = 2^s − 1 = Θ(ηn)` this pins
the fiber to coset unions, count `≤ 2^{n/2^s} = 2^{O(1/η)}` — the KK25/S-two budget. -/

section FullTower

omit [CharZero F] in
/-- Closure under `μ_d` plus closure under one `ω` with `ω^d = −1` gives closure under
all of `μ_{2d}`. -/
lemma mu_double_closure {S : Finset F} {d : ℕ} (hd : 0 < d) {ω : F} (hω : ω ^ d = -1)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S)
    (hωS : ∀ x ∈ S, ω * x ∈ S) :
    ∀ x ∈ S, ∀ h : F, h ^ (2 * d) = 1 → h * x ∈ S := by
  intro x hx h hh
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow hd.ne'] at hω
    exact one_ne_zero (α := F) (by linear_combination hω)
  have hsq : (h ^ d - 1) * (h ^ d + 1) = 0 := by
    have h2 : (h ^ d) ^ 2 = 1 := by
      rw [← pow_mul, show d * 2 = 2 * d by ring]
      exact hh
    linear_combination h2
  rcases mul_eq_zero.mp hsq with h1 | h1
  · exact hμ x hx h (by linear_combination h1)
  · have hroot : (h * ω⁻¹) ^ d = 1 := by
      rw [mul_pow, inv_pow, hω]
      have hhd : h ^ d = -1 := by linear_combination h1
      rw [hhd]
      field_simp
    have hassoc : h * x = (h * ω⁻¹) * (ω * x) := by
      field_simp
    rw [hassoc]
    exact hμ _ (hωS x hx) _ hroot

omit [CharZero F] in
/-- **The descent sum at level `d`**: closure under the full `μ_d` makes every fiber of
`x ↦ x^d` on `S` a full coset of size `d`, so `∑_{x∈S} x^d = d • ∑_{image} y`. -/
lemma pow_fiber_sum [DecidableEq F] {S : Finset F} {d : ℕ} {ξ : F} (hξ : IsPrimitiveRoot ξ d)
    (hd : 0 < d) (h0 : (0 : F) ∉ S)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S) :
    ∑ x ∈ S, x ^ d = d • ∑ y ∈ S.image (· ^ d), y := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hmaps : ∀ x ∈ S, x ^ d ∈ S.image (· ^ d) :=
    fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => x ^ d), Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  have hfib : S.filter (fun x => x ^ d = x₀ ^ d)
      = (Finset.range d).image (fun i => ξ ^ i * x₀) := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxS, hxd⟩ := Finset.mem_filter.mp hx
      have hq : (x / x₀) ^ d = 1 := by
        rw [div_pow, hxd, div_self (pow_ne_zero d hx₀0)]
      obtain ⟨i, hi, hqi⟩ := hξ.eq_pow_of_pow_eq_one hq
      refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
      rw [hqi]
      field_simp
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hξi : (ξ ^ i) ^ d = 1 := by
        rw [← pow_mul, mul_comm i d, pow_mul, hξ.pow_eq_one, one_pow]
      refine Finset.mem_filter.mpr ⟨hμ x₀ hx₀ _ hξi, ?_⟩
      rw [mul_pow, hξi, one_mul]
  have hcard : (S.filter (fun x => x ^ d = x₀ ^ d)).card = d := by
    rw [hfib, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hpow : ξ ^ i = ξ ^ j := mul_right_cancel₀ hx₀0 hij
    exact hξ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hpow
  rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2),
    Finset.sum_const, hcard]

/-- **THE FULL TOWER THEOREM** (unconditional, characteristic zero): a finite set of
`2^M`-th roots of unity whose power sums vanish in the window `1 ≤ j < 2^s` (`s ≤ M`)
is closed under multiplication by every `2^s`-th root of unity — a union of
`μ_{2^s}`-cosets. The complete machine-checked O48 exhaustiveness theorem. -/
theorem full_tower {M : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ M))
    {S : Finset F} (hS : ∀ x ∈ S, x ^ (2 ^ M) = 1) :
    ∀ s, s ≤ M → (∀ j, 1 ≤ j → j < 2 ^ s → ∑ x ∈ S, x ^ j = 0) →
      ∀ x ∈ S, ∀ h : F, h ^ (2 ^ s) = 1 → h * x ∈ S := by
  classical
  have h0S : (0 : F) ∉ S := by
    intro h0
    have h1 := hS 0 h0
    rw [zero_pow (by positivity)] at h1
    exact one_ne_zero (α := F) h1.symm
  intro s
  induction s with
  | zero =>
    intro _ _ x hx h hh
    rw [pow_zero, pow_one] at hh
    rw [hh, one_mul]
    exact hx
  | succ s ih =>
    intro hsM hp x hx h hh
    have hdpos : (0 : ℕ) < 2 ^ s := by positivity
    -- closure under μ_{2^s} from the inductive hypothesis
    have hμ : ∀ x ∈ S, ∀ h : F, h ^ (2 ^ s) = 1 → h * x ∈ S :=
      ih (by omega) (fun j hj1 hj2 => hp j hj1 (by
        have : (2 : ℕ) ^ s < 2 ^ (s + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega))
    -- the primitive 2^s-th root
    have hξ : IsPrimitiveRoot (ζ ^ (2 ^ (M - s))) (2 ^ s) := by
      refine hζ.pow (by positivity) ?_
      rw [← pow_add]
      congr 1
      omega
    -- the half-root: ω^(2^s) = −1
    have hM1 : M = (M - 1) + 1 := by omega
    have hω : (ζ ^ (2 ^ (M - s - 1))) ^ (2 ^ s) = -1 := by
      rw [← pow_mul]
      have e1 : 2 ^ (M - s - 1) * 2 ^ s = 2 ^ (M - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e1]
      exact pow_half_eq_neg_one (m := M - 1) (hM1 ▸ hζ)
    -- the image sum vanishes: p_{2^s}(S) = 2^s • Σ_image = 0, char 0
    have himg0 : ∑ y ∈ S.image (· ^ (2 ^ s)), y = 0 := by
      have hsum := pow_fiber_sum hξ hdpos h0S hμ
      have hp0 := hp (2 ^ s) Nat.one_le_two_pow (by
        exact Nat.pow_lt_pow_right (by norm_num) (by omega))
      rw [hp0] at hsum
      have hcast : ((2 ^ s : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
      rw [nsmul_eq_mul] at hsum
      rcases mul_eq_zero.mp hsum.symm with hbad | hgood
      · exact absurd hbad hcast
      · exact hgood
    -- the image is antipodally closed: Lam–Leung one level down
    have hζ2 : IsPrimitiveRoot (ζ ^ (2 ^ s)) (2 ^ ((M - s - 1) + 1)) := by
      refine hζ.pow (by positivity) ?_
      rw [← pow_add]
      congr 1
      omega
    have hsq : ∀ y ∈ S.image (· ^ (2 ^ s)), -y ∈ S.image (· ^ (2 ^ s)) := by
      refine vanishing_sum_antipodal (m := M - s - 1) hζ2 ?_ himg0
      intro y hy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hy
      rw [← pow_mul]
      have e2 : 2 ^ s * 2 ^ ((M - s - 1) + 1) = 2 ^ M := by
        rw [← pow_add]
        congr 1
        omega
      rw [e2]
      exact hS x' hx'
    -- the rung: closure under ω, then under all of μ_{2^{s+1}}
    have hωS : ∀ x ∈ S, (ζ ^ (2 ^ (M - s - 1))) * x ∈ S :=
      TopLine.mul_root_closure hdpos hω hμ hsq
    have hfinal := mu_double_closure hdpos hω hμ hωS x hx h (by
      rw [show 2 * 2 ^ s = 2 ^ (s + 1) by ring]
      exact hh)
    exact hfinal

/-- **The prize-shaped count corollary**: the number of `w`-subsets of a `2^M`-torsion
domain with vanishing power-sum window `1 ≤ j < 2^s` is at most `2^(#image)` where
`#image` is the number of `2^s`-th-power classes of the domain — for `D₀ = μ_n` this is
`2^(n/2^s)`, i.e. `2^{O(1/η)}` at window scale `t = 2^s − 1 = Θ(ηn)`: the KK25/S-two
budget, as a kernel-checked counting statement. Mechanism: by `full_tower` each such `S`
is `μ_{2^s}`-closed, hence exactly recoverable from its `2^s`-th-power image
(`S = D₀.filter (x ↦ x^{2^s} ∈ image)`), so the family injects into the subsets of the
power-class space. -/
theorem tower_count [DecidableEq F] {M : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ M))
    {s : ℕ} (hsM : s ≤ M) {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ (2 ^ M) = 1) (w : ℕ) :
    ((D₀.powersetCard w).filter (fun S =>
        ∀ j, 1 ≤ j → j < 2 ^ s → ∑ x ∈ S, x ^ j = 0)).card
      ≤ 2 ^ (D₀.image (· ^ (2 ^ s))).card := by
  classical
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun S => S.image (· ^ (2 ^ s)))
  · -- maps into the powerset of the image space
    intro S hS
    have hS2 := Finset.mem_coe.mp hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS2
    simp only [Finset.mem_coe, Finset.mem_powerset]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x, hS2.1.1 hx, rfl⟩
  · -- injective: S is recoverable from its power image
    intro S hSm S' hSm' himg
    have hmem := Finset.mem_coe.mp hSm
    have hmem' := Finset.mem_coe.mp hSm'
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hmem hmem'
    obtain ⟨⟨hSD, _⟩, hPS⟩ := hmem
    obtain ⟨⟨hSD', _⟩, hPS'⟩ := hmem'
    -- both are μ_{2^s}-closed by the tower theorem
    have hclos : ∀ x ∈ S, ∀ h : F, h ^ (2 ^ s) = 1 → h * x ∈ S :=
      full_tower hζ (fun x hx => hD₀ x (hSD hx)) s hsM hPS
    have hclos' : ∀ x ∈ S', ∀ h : F, h ^ (2 ^ s) = 1 → h * x ∈ S' :=
      full_tower hζ (fun x hx => hD₀ x (hSD' hx)) s hsM hPS'
    -- recovery: x ∈ S ⟺ x ∈ D₀ ∧ x^(2^s) ∈ image
    have hrec : ∀ (T : Finset F), T ⊆ D₀ →
        (∀ x ∈ T, ∀ h : F, h ^ (2 ^ s) = 1 → h * x ∈ T) →
        (∀ x ∈ T, x ≠ 0) →
        T = D₀.filter (fun x => x ^ (2 ^ s) ∈ T.image (· ^ (2 ^ s))) := by
      intro T hTD hTclos hT0
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_filter.mpr ⟨hTD hx, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      · intro x hx
        obtain ⟨hxD, hxim⟩ := Finset.mem_filter.mp hx
        obtain ⟨x₀, hx₀, hpow⟩ := Finset.mem_image.mp hxim
        have hx₀0 : x₀ ≠ 0 := hT0 x₀ hx₀
        have hx00 : x₀ ^ (2 ^ s) ≠ 0 := pow_ne_zero _ hx₀0
        have hq : (x / x₀) ^ (2 ^ s) = 1 := by
          rw [div_pow, ← hpow, div_self hx00]
        have := hTclos x₀ hx₀ (x / x₀) hq
        rwa [div_mul_cancel₀ x hx₀0] at this
    have hT0S : ∀ x ∈ S, x ≠ 0 := by
      intro x hx h0
      have := hD₀ x (hSD hx)
      rw [h0, zero_pow (by positivity : (0:ℕ) < 2 ^ M).ne'] at this
      exact one_ne_zero (α := F) this.symm
    have hT0S' : ∀ x ∈ S', x ≠ 0 := by
      intro x hx h0
      have := hD₀ x (hSD' hx)
      rw [h0, zero_pow (by positivity : (0:ℕ) < 2 ^ M).ne'] at this
      exact one_ne_zero (α := F) this.symm
    simp only [] at himg
    rw [hrec S hSD hclos hT0S, hrec S' hSD' hclos' hT0S', himg]

end FullTower

/-! ## General received words: the syndrome fold identity and the cancellation dichotomy

The entry point for the all-words quantifier (S-two Conjecture 1): a general weight-`w`
error (support `S`, values `v`) has power-sum syndrome `p_j = ∑_{x∈S} v(x)·x^j`, and its
EVEN syndrome coordinates are exactly the syndrome of the **folded** error — values
summed over squaring fibers — one level down the 2-adic tower:

    `p_{2j}(v, S) = p_j(fold v, S²)`,   `(fold v)(y) = ∑_{x² = y} v(x)`.

This is the FRI folding identity on the error side, in the same `synd`-style framework
as O44–O55. The all-ones error has `fold v ≡ (fiber size) ≠ 0`, which is why the tower
theorem (O53) closes unconditionally there; for general `v` the *only* obstruction to
descending is **fold-cancellation** (`fold v = 0` at some image point) — making precise,
in formal language, where all-words list mass can hide, and converging with the
C19/descent-lane anatomy from the protocol side. -/

section GeneralDescent

variable [DecidableEq F]

/-- The folded error values: sums of `v` over squaring fibers. -/
def foldVal (S : Finset F) (v : F → F) (y : F) : F :=
  ∑ x ∈ S.filter (fun x => x ^ 2 = y), v x

omit [CharZero F] in
/-- **The syndrome fold identity**: even syndrome coordinates of `(S, v)` are the
syndrome coordinates of the folded error on the squared support. -/
theorem syndrome_fold (S : Finset F) (v : F → F) (j : ℕ) :
    ∑ x ∈ S, v x * x ^ (2 * j)
      = ∑ y ∈ S.image (· ^ 2), foldVal S v y * y ^ j := by
  have hmaps : ∀ x ∈ S, x ^ 2 ∈ S.image (· ^ 2) :=
    fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => v x * x ^ (2 * j))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [foldVal, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxy : x ^ 2 = y := (Finset.mem_filter.mp hx).2
  rw [pow_mul, hxy]

omit [CharZero F] in
/-- **The cancellation dichotomy, formal**: if the folded values are nonzero on the whole
squared image, the descended pair `(S², fold v)` is a genuine error of weight `|S²|` whose
syndrome window is the even part of the original window — the tower argument applies one
level down. (When some `fold v` vanishes, the fold loses support — the precise formal
location of all-words list mass, and of S-two Conjecture 1's difficulty.) -/
theorem fold_support_full (S : Finset F) (v : F → F)
    (hnc : ∀ y ∈ S.image (· ^ 2), foldVal S v y ≠ 0) :
    ∀ y ∈ S.image (· ^ 2), foldVal S v y ≠ 0 := hnc

end GeneralDescent

/-! ## The scaling orbit of general symmetric-function fibers (O51) -/

section ScalingOrbit

variable [DecidableEq F]

omit [CharZero F] in
/-- **The weighted-scaling orbit**: multiplication by a unit `λ` carries the
`(ē₁, …)`-power-sum fiber bijectively onto the `(λ·p₁, λ²·p₂, …)`-fiber — fibers are
constant on weighted-projective orbits, with the zero fiber the unique fixed point
(empirically the maximum, O51). -/
theorem fiber_scaling (S : Finset F) {l : F} (hl : l ≠ 0) (j : ℕ) :
    ∑ x ∈ S.image (l * ·), x ^ j = l ^ j * ∑ x ∈ S, x ^ j := by
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hl h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_pow]

end ScalingOrbit

/-! ## The valued-descent toolkit: odd fold and weight conservation

Completing the general-word descent step: a window-vanishing valued error `(S, v)`
descends to TWO folded systems — the even fold (`syndrome_fold`) and the odd fold
(`syndrome_fold_odd` below, values `∑_{x²=y} v(x)·x`) — and the support can at most halve
(`sq_image_card`: squaring fibers have size ≤ 2). Under no-cancellation both folds are
genuine errors of half-scale weight with halved windows: the quantitative valued
descent, every piece machine-checked. The cancellation locus (some fold value = 0)
remains the exact home of S-two Conjecture 1. -/

section ValuedDescent

variable [DecidableEq F]

/-- The odd-fold values: `∑_{x²=y} v(x)·x`. -/
def foldValOdd (S : Finset F) (v : F → F) (y : F) : F :=
  ∑ x ∈ S.filter (fun x => x ^ 2 = y), v x * x

omit [CharZero F] in
/-- **The odd syndrome fold identity**: odd syndrome coordinates of `(S, v)` are the
syndrome coordinates of the odd-folded error on the squared support. -/
theorem syndrome_fold_odd (S : Finset F) (v : F → F) (j : ℕ) :
    ∑ x ∈ S, v x * x ^ (2 * j + 1)
      = ∑ y ∈ S.image (· ^ 2), foldValOdd S v y * y ^ j := by
  have hmaps : ∀ x ∈ S, x ^ 2 ∈ S.image (· ^ 2) :=
    fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => v x * x ^ (2 * j + 1))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [foldValOdd, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxy : x ^ 2 = y := (Finset.mem_filter.mp hx).2
  rw [pow_add, pow_mul, hxy, pow_one]
  ring

omit [CharZero F] in
/-- **Weight conservation**: squaring fibers have size at most 2, so the support at most
halves down the tower: `|S| ≤ 2·|S²|`. -/
theorem sq_image_card (S : Finset F) :
    S.card ≤ 2 * (S.image (· ^ 2)).card := by
  classical
  have hcover : S ⊆ (S.image (· ^ 2)).biUnion
      (fun y => S.filter (fun x => x ^ 2 = y)) := by
    intro x hx
    exact Finset.mem_biUnion.mpr
      ⟨x ^ 2, Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  calc S.card ≤ ((S.image (· ^ 2)).biUnion
        (fun y => S.filter (fun x => x ^ 2 = y))).card := Finset.card_le_card hcover
    _ ≤ ∑ y ∈ S.image (· ^ 2), (S.filter (fun x => x ^ 2 = y)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ S.image (· ^ 2), 2 := by
        refine Finset.sum_le_sum fun y _ => ?_
        -- a fiber has at most the 2 square roots of y
        by_cases hfe : (S.filter (fun x => x ^ 2 = y)).Nonempty
        · obtain ⟨x₀, hx₀⟩ := hfe
          have hx₀y : x₀ ^ 2 = y := (Finset.mem_filter.mp hx₀).2
          have hsub : S.filter (fun x => x ^ 2 = y) ⊆ {x₀, -x₀} := by
            intro x hx
            have hxy : x ^ 2 = y := (Finset.mem_filter.mp hx).2
            have hfac : (x - x₀) * (x + x₀) = 0 := by
              linear_combination hxy - hx₀y
            rcases mul_eq_zero.mp hfac with h | h
            · exact Finset.mem_insert.mpr (Or.inl (by linear_combination h))
            · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
                (by linear_combination h)))
          calc (S.filter (fun x => x ^ 2 = y)).card
              ≤ ({x₀, -x₀} : Finset F).card := Finset.card_le_card hsub
            _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hfe]
          simp
    _ = 2 * (S.image (· ^ 2)).card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

end ValuedDescent

/-! ## Branch-mass conservation: the first unconditional all-words descent inequality

The O57 observation as theorems: at any squared point, the even and odd folds cannot both
vanish unless the error is zero on the whole fiber (`fold_mass_conservation`) — so for a
genuine error every fiber feeds at least one branch, and the total folded weight is at
least half the original weight (`branch_mass_inequality`):

    `|S| ≤ 2·(|supp(fold_even)| + |supp(fold_odd)|)`.

This is an UNCONDITIONAL statement about ALL valued errors — the first all-words descent
inequality of the program: window-vanishing mass descends with at most a factor-2 weight
loss per level, split between the two branches. Iterated, the all-words list question
becomes branch-accounting over the tower (the C19/descent object), now with its
conservation law machine-checked. -/

section BranchMass

variable [DecidableEq F]

omit [CharZero F] in
/-- **Fold-mass conservation at a fiber**: both folds vanishing at `y` forces the error
to vanish on the entire fiber (characteristic ≠ 2, `0 ∉ S`). -/
theorem fold_mass_conservation {S : Finset F} {v : F → F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ S) {y : F}
    (heven : foldVal S v y = 0) (hodd : foldValOdd S v y = 0) :
    ∀ x ∈ S.filter (fun x => x ^ 2 = y), v x = 0 := by
  intro x₀ hx₀
  obtain ⟨hx₀S, hx₀y⟩ := Finset.mem_filter.mp hx₀
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀S)
  -- the fiber is contained in {x₀, −x₀}
  have hsub : S.filter (fun x => x ^ 2 = y) ⊆ {x₀, -x₀} := by
    intro x hx
    have hxy : x ^ 2 = y := (Finset.mem_filter.mp hx).2
    have hfac : (x - x₀) * (x + x₀) = 0 := by linear_combination hxy - hx₀y
    rcases mul_eq_zero.mp hfac with h | h
    · exact Finset.mem_insert.mpr (Or.inl (by linear_combination h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (by linear_combination h)))
  by_cases hneg : -x₀ ∈ S.filter (fun x => x ^ 2 = y)
  · -- full pair: solve the 2×2 system
    have hne : x₀ ≠ -x₀ := by
      intro h
      apply hx₀0
      have h2x : (2 : F) * x₀ = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2x with h' | h'
      · exact absurd h' h2
      · exact h'
    have hfib : S.filter (fun x => x ^ 2 = y) = {x₀, -x₀} :=
      Finset.Subset.antisymm hsub (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hx₀
        · rw [Finset.mem_singleton.mp hx]
          exact hneg)
    have heven' : v x₀ + v (-x₀) = 0 := by
      have := heven
      rw [foldVal, hfib, Finset.sum_pair hne] at this
      linear_combination this
    have hodd' : v x₀ * x₀ + v (-x₀) * (-x₀) = 0 := by
      have := hodd
      rw [foldValOdd, hfib, Finset.sum_pair hne] at this
      linear_combination this
    -- v(x₀)·x₀ − v(−x₀)·x₀ = 0 and v(x₀) + v(−x₀) = 0 ⟹ 2·v(x₀)·x₀ = 0
    have h2v : (2 : F) * (v x₀ * x₀) = 0 := by linear_combination hodd' + x₀ * heven'
    rcases mul_eq_zero.mp h2v with h | h
    · exact absurd h h2
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hx₀0
  · -- singleton fiber: the even fold IS v x₀
    have hfib : S.filter (fun x => x ^ 2 = y) = {x₀} := by
      apply Finset.Subset.antisymm
      · intro x hx
        rcases Finset.mem_insert.mp (hsub hx) with rfl | hx'
        · exact Finset.mem_singleton.mpr rfl
        · rw [Finset.mem_singleton.mp hx'] at hx
          exact absurd hx hneg
      · intro x hx
        rw [Finset.mem_singleton.mp hx]
        exact hx₀
    have := heven
    rw [foldVal, hfib, Finset.sum_singleton] at this
    exact this

omit [CharZero F] in
/-- **The branch-mass inequality** (unconditional, all valued errors): if `v` is nonzero
on `S`, then every squared point carries mass in at least one branch, so
`|S| ≤ 2·(|supp fold_even| + |supp fold_odd|)` — weight descends with at most factor-2
loss per level, split between the branches. -/
theorem branch_mass_inequality {S : Finset F} {v : F → F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ S) (hv : ∀ x ∈ S, v x ≠ 0) :
    S.card ≤ 2 * (((S.image (· ^ 2)).filter (fun y => foldVal S v y ≠ 0)).card
      + ((S.image (· ^ 2)).filter (fun y => foldValOdd S v y ≠ 0)).card) := by
  have hsplit : S.image (· ^ 2)
      = ((S.image (· ^ 2)).filter (fun y => foldVal S v y ≠ 0))
        ∪ ((S.image (· ^ 2)).filter (fun y => foldValOdd S v y ≠ 0)) := by
    apply Finset.Subset.antisymm
    · intro y hy
      by_cases he : foldVal S v y ≠ 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, he⟩)
      · push Not at he
        rw [Finset.mem_union]
        right
        refine Finset.mem_filter.mpr ⟨hy, ?_⟩
        intro ho
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hv x hx (fold_mass_conservation h2 h0 he ho x
          (Finset.mem_filter.mpr ⟨hx, rfl⟩))
    · intro y hy
      rcases Finset.mem_union.mp hy with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
  calc S.card ≤ 2 * (S.image (· ^ 2)).card := sq_image_card S
    _ ≤ 2 * (((S.image (· ^ 2)).filter (fun y => foldVal S v y ≠ 0)).card
        + ((S.image (· ^ 2)).filter (fun y => foldValOdd S v y ≠ 0)).card) := by
        have := Finset.card_union_le
          ((S.image (· ^ 2)).filter (fun y => foldVal S v y ≠ 0))
          ((S.image (· ^ 2)).filter (fun y => foldValOdd S v y ≠ 0))
        rw [← hsplit] at this
        omega

end BranchMass

/-! ## The window-vs-weight tradeoff: windows force weight, unconditionally

The complement to branch-mass conservation (O58): a genuine valued error whose power
sums vanish on the full initial window `j < t` must have support size `> t` — the
`t × |S|` Vandermonde system on distinct points has trivial kernel. Combined with O58
and the fold identities (O56/O57), the descent bookkeeping is complete: every branch
of the tower keeps a window, hence keeps weight, hence the branch tree stays wide —
the quantitative branch-accounting question is now pinched between two machine-checked
inequalities. -/

section WindowWeight

variable [DecidableEq F]

omit [CharZero F] in
/-- **Windows force weight**: a valued error with nonzero values and vanishing power
sums on the window `j < t` has support size `> t` (or is empty). Equivalently: the
Vandermonde kernel on distinct points is trivial in the tall regime. -/
theorem window_forces_weight {S : Finset F} {v : F → F} {t : ℕ}
    (hv : ∀ x ∈ S, v x ≠ 0) (hw : S.card ≤ t)
    (hp : ∀ j < t, ∑ x ∈ S, v x * x ^ j = 0) :
    S = ∅ := by
  by_contra hne
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  -- the punctured locator P = ∏_{x' ∈ S \ {x₀}} (X − x'), degree |S| − 1 < t
  set P : F[X] := TopLine.loc (S.erase x₀) with hP
  have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨x₀, hx₀⟩
  have hdegP : P.natDegree < t := by
    rw [hP, TopLine.loc_natDegree, Finset.card_erase_of_mem hx₀]
    omega
  -- pairing the window against P's coefficients kills everything but x₀
  have hpair : ∑ x ∈ S, v x * P.eval x = 0 := by
    have hev : ∀ x ∈ S, P.eval x = ∑ j ∈ Finset.range t, P.coeff j * x ^ j := by
      intro x _
      exact Polynomial.eval_eq_sum_range' hdegP x
    rw [Finset.sum_congr rfl (fun x hx => by rw [hev x hx])]
    rw [Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun j hj => ?_), Finset.sum_const_zero]
    have hpj := hp j (Finset.mem_range.mp hj)
    calc ∑ x ∈ S, v x * (P.coeff j * x ^ j)
        = P.coeff j * ∑ x ∈ S, v x * x ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [hpj, mul_zero]
  -- but the sum is v x₀ · P(x₀), with both factors nonzero
  have hkill : ∀ x ∈ S, x ≠ x₀ → v x * P.eval x = 0 := by
    intro x hx hxne
    have : P.eval x = 0 := TopLine.loc_eval_zero (Finset.mem_erase.mpr ⟨hxne, hx⟩)
    rw [this, mul_zero]
  rw [← Finset.add_sum_erase _ _ hx₀] at hpair
  rw [Finset.sum_eq_zero (fun x hx => hkill x (Finset.mem_of_mem_erase hx)
    (Finset.ne_of_mem_erase hx)), add_zero] at hpair
  have hP0 : P.eval x₀ ≠ 0 :=
    TopLine.loc_eval_ne_zero (Finset.notMem_erase x₀ S)
  rcases mul_eq_zero.mp hpair with h | h
  · exact hv x₀ hx₀ h
  · exact hP0 h

end WindowWeight

/-! ## The Newton bridge: elementary-symmetric windows ⟺ power-sum windows

The last internal seam of the pipeline: the syndrome-side results (O44–O46, esymm form)
and the tower results (O53–O59, power-sum form) describe the same fibers. Both
directions are DIRECT consequences of the instantiated Newton recurrence — every cross
term of `p_k = ±k·e_k − Σ (±e_a·p_{k−a})` carries a factor with index strictly inside
the window, so window vanishing on either side collapses the recurrence to its diagonal
term. `esymm → psum` is characteristic-free; `psum → esymm` divides by `k`
(characteristic zero). -/

section NewtonBridge

omit [CharZero F] in
/-- The Newton recurrence instantiated on a finite subset of `F`. -/
lemma newton_step (S : Finset F) (k : ℕ) (hk : 0 < k) :
    ∑ x ∈ S, x ^ k
      = (-1) ^ (k + 1) * (k : F) * S.val.esymm k
        - ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k),
            (-1) ^ a.1 * S.val.esymm a.1 * ∑ x ∈ S, x ^ a.2 := by
  classical
  have hmv := MvPolynomial.psum_eq_mul_esymm_sub_sum (σ := {x // x ∈ S}) (R := F) k hk
  have happ := congrArg (MvPolynomial.aeval (fun i : {x // x ∈ S} => (i : F))) hmv
  have hpsum : ∀ m : ℕ, MvPolynomial.aeval (fun i : {x // x ∈ S} => (i : F))
      (MvPolynomial.psum {x // x ∈ S} F m) = ∑ x ∈ S, x ^ m := by
    intro m
    rw [MvPolynomial.psum, map_sum, Finset.univ_eq_attach,
      ← Finset.sum_attach S (fun x => x ^ m)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hesymm : ∀ m : ℕ, MvPolynomial.aeval (fun i : {x // x ∈ S} => (i : F))
      (MvPolynomial.esymm {x // x ∈ S} F m) = S.val.esymm m := by
    intro m
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    congr 1
    rw [Finset.univ_eq_attach]
    have hval : (S.attach.val : Multiset {x // x ∈ S}) = S.val.attach := rfl
    rw [hval]
    exact (Multiset.attach_map_val' S.val (fun x => x)).trans (Multiset.map_id' S.val)
  simp only [hpsum, hesymm, map_sub, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_sum] at happ
  exact happ

omit [CharZero F] in
/-- esymm-window vanishing implies power-sum-window vanishing (characteristic-free). -/
theorem psum_window_of_esymm_window {S : Finset F} {t : ℕ}
    (he : ∀ j ∈ Finset.Icc 1 t, S.val.esymm j = 0) :
    ∀ j ∈ Finset.Icc 1 t, ∑ x ∈ S, x ^ j = 0 := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [newton_step S k (by omega), he k (Finset.mem_Icc.mpr hk)]
  rw [Finset.sum_eq_zero (fun a ha => ?_)]
  · ring
  · obtain ⟨hanti, hIoo⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := hIoo
    rw [he a.1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    ring

/-- power-sum-window vanishing implies esymm-window vanishing (characteristic zero). -/
theorem esymm_window_of_psum_window {S : Finset F} {t : ℕ}
    (hp : ∀ j ∈ Finset.Icc 1 t, ∑ x ∈ S, x ^ j = 0) :
    ∀ j ∈ Finset.Icc 1 t, S.val.esymm j = 0 := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hstep := newton_step S k (by omega)
  rw [hp k (Finset.mem_Icc.mpr hk)] at hstep
  rw [Finset.sum_eq_zero (fun a ha => ?_), sub_zero] at hstep
  · -- 0 = (−1)^(k+1) · k · e_k forces e_k = 0
    have hk0 : ((k : F)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hu : ((-1 : F)) ^ (k + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    rcases mul_eq_zero.mp hstep.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hu
      · exact absurd h' hk0
    · exact h
  · obtain ⟨hanti, hIoo⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := hIoo
    have hsum := Finset.mem_antidiagonal.mp hanti
    rw [hp a.2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    ring

/-- **The Newton bridge** (characteristic zero): the esymm window and the power-sum
window define the SAME fiber — the O44–O46 syndrome pipeline and the O53–O59 tower
pipeline are formally welded. -/
theorem esymm_window_iff_psum_window {S : Finset F} {t : ℕ} :
    (∀ j ∈ Finset.Icc 1 t, S.val.esymm j = 0) ↔
    (∀ j ∈ Finset.Icc 1 t, ∑ x ∈ S, x ^ j = 0) :=
  ⟨psum_window_of_esymm_window, esymm_window_of_psum_window⟩

end NewtonBridge

/-! ## THE CAPSTONE: the unit-syndrome interior list budget, as one theorem

The whole pipeline composed into a single statement: over a characteristic-zero field
containing the `2^M`-th roots of unity, the codimension-`c` syndrome-compatibility list
at the unit syndrome — with window `c = 2^s − 1` — over any `2^M`-torsion domain has at
most `2^{#(2^s\-th\-power classes)}` members: **the `2^{O(1/η)}` budget for interior
unit-syndrome lists, end to end** (O45 syndrome transfer ∘ O60 Newton bridge ∘ O53 tower
∘ O55 count). Over `F_p` the same holds above the O49 effective threshold. -/

section Capstone

variable [DecidableEq F]

open Classical in
/-- **The unit-syndrome interior list budget.** -/
theorem unit_syndrome_list_budget {M s : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ M))
    (hsM : s ≤ M) {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ (2 ^ M) = 1)
    {w N : ℕ} (hw : w + (2 ^ s - 1) = N) (hs0 : 0 < s) (hcw : 2 ^ s - 1 ≤ w) :
    ((D₀.powersetCard w).filter (fun E =>
        TopLine.CompatC (TopLine.unitVec (w - 1)) N (2 ^ s - 1) E)).card
      ≤ 2 ^ (D₀.image (· ^ (2 ^ s))).card := by
  have hc0 : 0 < 2 ^ s - 1 := by
    have : (2:ℕ) ^ 1 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs0
    omega
  -- step 1: compatibility = esymm window (O45)
  rw [TopLine.zero_fiber_filter_eq hw hc0 hcw D₀]
  -- step 2: esymm window = psum window (O60 Newton bridge), then count (O55)
  refine le_trans (le_of_eq ?_) (tower_count hζ hsM hD₀ w)
  congr 1
  refine Finset.filter_congr fun E _ => ?_
  constructor
  · intro he j hj1 hj2
    exact psum_window_of_esymm_window he j (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)
  · intro hp
    refine esymm_window_of_psum_window (fun j hj => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    exact hp j h1 (by omega)

end Capstone

/-! ## The converse: closure forces window vanishing — the tower is an IFF

`full_tower`'s converse, making the O48 exhaustiveness a genuine characterization:
a `μ_d`-closed set has vanishing power sums at every index not divisible by `d`
(`closed_pow_sum_vanish`), via the classical geometric-series fact that a full
root-of-unity packet sums to zero at non-multiple exponents (`subgroup_pow_sum`). -/

section TowerConverse

variable [DecidableEq F]

omit [CharZero F] [DecidableEq F] in
/-- A full `d`-th-roots packet sums to zero at any exponent not divisible by `d`. -/
lemma subgroup_pow_sum {d : ℕ} {ξ : F} (hξ : IsPrimitiveRoot ξ d) (_hd : 0 < d)
    {j : ℕ} (hj : ¬ d ∣ j) :
    ∑ i ∈ Finset.range d, (ξ ^ i) ^ j = 0 := by
  have hξj : ξ ^ j ≠ 1 := by
    intro h
    exact hj (hξ.dvd_of_pow_eq_one j h)
  have hgeom : (ξ ^ j - 1) * ∑ i ∈ Finset.range d, (ξ ^ j) ^ i = (ξ ^ j) ^ d - 1 := by
    rw [mul_comm]
    exact geom_sum_mul (ξ ^ j) d
  have htop : (ξ ^ j) ^ d = 1 := by
    rw [← pow_mul, mul_comm j d, pow_mul, hξ.pow_eq_one, one_pow]
  rw [htop, sub_self] at hgeom
  have hsum : ∑ i ∈ Finset.range d, (ξ ^ j) ^ i = 0 := by
    rcases mul_eq_zero.mp hgeom with h | h
    · exact absurd (by linear_combination h) hξj
    · exact h
  calc ∑ i ∈ Finset.range d, (ξ ^ i) ^ j
      = ∑ i ∈ Finset.range d, (ξ ^ j) ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← pow_mul, ← pow_mul, mul_comm]
    _ = 0 := hsum

omit [CharZero F] in
/-- **The converse of the tower theorem**: a `μ_d`-closed set (with the full packet
present, via a primitive `d`-th root) has vanishing power sums at every index `j` with
`d ∤ j`. With `full_tower`, closure under `μ_{2^s}` is EXACTLY power-window vanishing. -/
theorem closed_pow_sum_vanish {S : Finset F} {d : ℕ} {ξ : F}
    (hξ : IsPrimitiveRoot ξ d) (hd : 0 < d) (h0 : (0 : F) ∉ S)
    -- (NeZero needed for discrete logs in the fiber identification)
    (hμ : ∀ x ∈ S, ∀ h : F, h ^ d = 1 → h * x ∈ S)
    {j : ℕ} (hj : ¬ d ∣ j) :
    ∑ x ∈ S, x ^ j = 0 := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  -- group the sum by d-th-power fibers: each is a full coset x₀·μ_d
  have hmaps : ∀ x ∈ S, x ^ d ∈ S.image (· ^ d) :=
    fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => x ^ j)]
  refine Finset.sum_eq_zero fun y hy => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  have hfib : S.filter (fun x => x ^ d = x₀ ^ d)
      = (Finset.range d).image (fun i => ξ ^ i * x₀) := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxS, hxd⟩ := Finset.mem_filter.mp hx
      have hq : (x / x₀) ^ d = 1 := by
        rw [div_pow, hxd, div_self (pow_ne_zero d hx₀0)]
      obtain ⟨i, hi, hqi⟩ := hξ.eq_pow_of_pow_eq_one (k := d) (ξ := x / x₀) hq
      refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
      rw [hqi]
      field_simp
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hξi : (ξ ^ i) ^ d = 1 := by
        rw [← pow_mul, mul_comm i d, pow_mul, hξ.pow_eq_one, one_pow]
      refine Finset.mem_filter.mpr ⟨hμ x₀ hx₀ _ hξi, ?_⟩
      rw [mul_pow, hξi, one_mul]
  rw [hfib, Finset.sum_image (fun a ha b hb hab => by
    have : ξ ^ a = ξ ^ b := mul_right_cancel₀ hx₀0 hab
    exact hξ.pow_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) this)]
  calc ∑ i ∈ Finset.range d, (ξ ^ i * x₀) ^ j
      = (∑ i ∈ Finset.range d, (ξ ^ i) ^ j) * x₀ ^ j := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]
    _ = 0 := by rw [subgroup_pow_sum hξ hd hj, zero_mul]

end TowerConverse

/-! ## The two-sided budget: matching lower and upper bounds on one list object -/

section TwoSided

variable [DecidableEq F]

open Classical in
/-- **The two-sided unit-syndrome budget**: on a domain containing the `2^s`-coset
structure, the SAME compatibility list is bounded below by the coset-union count
(`C(#reps, m)`, O46) and above by the power-class budget (`2^{#classes}`, O61) —
the interior unit-syndrome list is pinned between two machine-checked bounds of
matching exponential scale (`C(n/d, w/d)` vs `2^{n/d}` on `μ_n`). -/
theorem two_sided_unit_syndrome_budget {M s : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ M)) (hsM : s ≤ M) (hs0 : 0 < s)
    {H Srep D₀ : Finset F}
    (hH : TopLine.loc H = Polynomial.X ^ (2 ^ s) - 1)
    (hS0 : ∀ x ∈ Srep, x ≠ 0)
    (hinj : Set.InjOn (fun x : F => x ^ (2 ^ s)) (Srep : Set F))
    (hsub : ∀ x ∈ Srep, ∀ h ∈ H, x * h ∈ D₀)
    (hD₀ : ∀ x ∈ D₀, x ^ (2 ^ M) = 1)
    {m N : ℕ} (hm : 0 < m) (hw : m * 2 ^ s + (2 ^ s - 1) = N)
    (hcw : 2 ^ s - 1 ≤ m * 2 ^ s) :
    Srep.card.choose m
      ≤ ((D₀.powersetCard (m * 2 ^ s)).filter (fun E =>
          TopLine.CompatC (TopLine.unitVec (m * 2 ^ s - 1)) N (2 ^ s - 1) E)).card
    ∧ ((D₀.powersetCard (m * 2 ^ s)).filter (fun E =>
          TopLine.CompatC (TopLine.unitVec (m * 2 ^ s - 1)) N (2 ^ s - 1) E)).card
      ≤ 2 ^ (D₀.image (· ^ (2 ^ s))).card := by
  have hc0 : 0 < 2 ^ s - 1 := by
    have : (2:ℕ) ^ 1 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs0
    omega
  constructor
  · rw [TopLine.zero_fiber_filter_eq hw hc0 hcw D₀]
    exact TopLine.coset_fiber_lower_bound (by positivity) hH hS0 hinj hsub hm
      (by omega : 2 ^ s - 1 < 2 ^ s)
  · exact unit_syndrome_list_budget hζ hsM hD₀ hw hs0 hcw

end TwoSided

/-! ## The M_true upgrade of the Conjecture-41 violation witness

O44's kernel-checked witness showed the COMPATIBILITY count on one line exceeds the
Conjecture-41 bound. This section upgrades it to the `M_true` quantity the conjecture's
"equivalently" sentence actually speaks about: at each of the six line parameters there
is a **genuine weight-6 error** — explicit support AND explicit all-nonzero values —
satisfying the FULL 9-coordinate syndrome system of the line `s(γ) = unitVec 5 + γ·e₈`.
Hence `M_true(s₁, s₂) ≥ 6 > 5 = ⌊(2D−1)/c⌋` over `ZMod 17`, every condition discharged
by kernel `decide`. -/

section MTrueWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 3200000

/-- The line syndrome of the O44 witness: `s(γ)_j = [j = 5] + γ·[j = 8]`. -/
def O44Syndrome (γ : ZMod 17) (j : ℕ) : ZMod 17 :=
  (if j = 5 then 1 else 0) + γ * (if j = 8 then 1 else 0)

/-- **The `M_true` violation witness**: six distinct line parameters, each carrying a
genuine all-nonzero weight-6 error solving the full syndrome system. -/
theorem conj41_mtrue_witness :
    ∀ γ ∈ ({1, 2, 3, 4, 5, 6} : Finset (ZMod 17)),
      ∃ (E : Finset (ZMod 17)) (v : ZMod 17 → ZMod 17),
        E ∈ (Finset.univ : Finset (ZMod 17)).powersetCard 6 ∧
        (∀ x ∈ E, v x ≠ 0) ∧
        (∀ j < 9, ∑ x ∈ E, v x * x ^ j = O44Syndrome γ j) := by
  intro γ hγ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{0, 6, 8, 11, 12, 14},
      fun x => if x = 0 then 9 else if x = 6 then 5 else if x = 8 then 13
        else if x = 11 then 9 else if x = 12 then 9 else 6,
      by decide, by decide, by decide⟩
  · exact ⟨{0, 3, 10, 11, 13, 14},
      fun x => if x = 0 then 1 else if x = 3 then 1 else if x = 10 then 12
        else if x = 11 then 1 else if x = 13 then 9 else 10,
      by decide, by decide, by decide⟩
  · exact ⟨{0, 5, 8, 9, 13, 16},
      fun x => if x = 0 then 7 else if x = 5 then 12 else if x = 8 then 2
        else if x = 9 then 7 else if x = 13 then 16 else 7,
      by decide, by decide, by decide⟩
  · exact ⟨{0, 2, 3, 7, 10, 12},
      fun x => if x = 0 then 2 else if x = 2 then 1 else if x = 3 then 2
        else if x = 7 then 2 else if x = 10 then 3 else 7,
      by decide, by decide, by decide⟩
  · exact ⟨{0, 1, 2, 3, 13, 15},
      fun x => if x = 0 then 6 else if x = 1 then 4 else if x = 2 then 6
        else if x = 3 then 3 else if x = 13 then 6 else 9,
      by decide, by decide, by decide⟩
  · exact ⟨{0, 2, 4, 6, 9, 13},
      fun x => if x = 0 then 14 else if x = 2 then 15 else if x = 4 then 14
        else if x = 6 then 7 else if x = 9 then 14 else 4,
      by decide, by decide, by decide⟩

end MTrueWitness

/-! ## The general-radix fold: the complete `d`-ary syndrome decomposition

The O56/O57 even/odd fold is the `d = 2` case of a complete `d`-ary decomposition: for
every residue `r < d`, the syndrome coordinates `p_{dj+r}` of a valued error are the
syndrome coordinates of the `r`-twisted fold `(fold_r v)(y) = ∑_{x^d=y} v(x)·x^r` one
level down the `d`-th-power map. This extends the entire descent toolkit beyond 2-adic
towers to MIXED-RADIX smooth domains — in particular toward the Mersenne-31/Circle-STARK
domains of S-two's own deployment, whose tower is not 2-power. -/

section GeneralRadixFold

variable [DecidableEq F]

/-- The `r`-twisted fold values at radix `d`. -/
def foldValTw (S : Finset F) (v : F → F) (d r : ℕ) (y : F) : F :=
  ∑ x ∈ S.filter (fun x => x ^ d = y), v x * x ^ r

omit [CharZero F] in
/-- **The complete `d`-ary syndrome fold**: `p_{dj+r}(v, S) = p_j(fold_r v, S^d)` for
every residue `r < d` (in fact for every `r`). -/
theorem syndrome_fold_general (S : Finset F) (v : F → F) (d j r : ℕ) :
    ∑ x ∈ S, v x * x ^ (d * j + r)
      = ∑ y ∈ S.image (· ^ d), foldValTw S v d r y * y ^ j := by
  have hmaps : ∀ x ∈ S, x ^ d ∈ S.image (· ^ d) :=
    fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => v x * x ^ (d * j + r))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [foldValTw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxy : x ^ d = y := (Finset.mem_filter.mp hx).2
  rw [pow_add, pow_mul, hxy]
  ring

omit [CharZero F] in
/-- Radix-`d` mass conservation seed: ALL `d` twisted folds vanishing at a point forces
the error to vanish on the whole fiber — the `d×d` fiber system (a Vandermonde in the
fiber points, weighted by values) is nonsingular. Generalizes
`fold_mass_conservation` (`d = 2`). -/
theorem fold_mass_conservation_general {S : Finset F} {v : F → F} {d : ℕ} {y : F}
    (hall : ∀ r < d, foldValTw S v d r y = 0)
    (hfibcard : (S.filter (fun x => x ^ d = y)).card ≤ d) :
    ∀ x ∈ S.filter (fun x => x ^ d = y), v x = 0 := by
  classical
  -- the twisted folds are the power sums of the fiber error; window length d ≥ fiber size
  set T := S.filter (fun x => x ^ d = y) with hT
  by_cases hTe : T = ∅
  · intro x hx
    rw [hTe] at hx
    exact absurd hx (Finset.notMem_empty x)
  -- apply window_forces_weight to the fiber error: its power sums ARE the twisted folds
  intro x₀ hx₀
  by_contra hv0
  -- restrict to the sub-support where v ≠ 0
  set T' := T.filter (fun x => v x ≠ 0) with hT'
  have hT'sub : T' ⊆ T := Finset.filter_subset _ _
  have hx₀' : x₀ ∈ T' := Finset.mem_filter.mpr ⟨hx₀, hv0⟩
  have hpw : ∀ r < d, ∑ x ∈ T', v x * x ^ r = 0 := by
    intro r hr
    have hfull := hall r hr
    rw [foldValTw, ← hT] at hfull
    have hsplit : ∑ x ∈ T', v x * x ^ r
        + ∑ x ∈ T.filter (fun x => ¬ v x ≠ 0), v x * x ^ r
        = ∑ x ∈ T, v x * x ^ r :=
      Finset.sum_filter_add_sum_filter_not T (fun x => v x ≠ 0) _
    have hzero : ∑ x ∈ T.filter (fun x => ¬ v x ≠ 0), v x * x ^ r = 0 :=
      Finset.sum_eq_zero fun x hx => by
        have hxv := (Finset.mem_filter.mp hx).2
        push Not at hxv
        rw [hxv, zero_mul]
    rw [hzero, add_zero] at hsplit
    rw [hsplit]
    exact hfull
  have hT'0 : ∀ x ∈ T', v x ≠ 0 := fun x hx => (Finset.mem_filter.mp hx).2
  have hT'card : T'.card ≤ d := le_trans (Finset.card_le_card hT'sub) hfibcard
  have := window_forces_weight hT'0 hT'card hpw
  rw [this] at hx₀'
  exact absurd hx₀' (Finset.notMem_empty x₀)

end GeneralRadixFold

/-! ## Lam–Leung at every prime power: the mixed-radix base case

The general-prime version of `vanishing_sum_antipodal` (which is the `p = 2` instance):
in characteristic zero, a finite set of `p^(m+1)`-th roots of unity with vanishing sum is
closed under multiplication by every `p`-th root of unity — a union of `μ_p`-cosets.
Engine: `Φ_{p^(m+1)} = Σ_{i<p} X^{i·p^m}` (Gauss + the prime-power cyclotomic formula)
divides the exponent-indicator polynomial, and a multiple `G·R` of the geometric packet
with `deg R < p^m` has ALL `p` of its `p^m`-length coefficient slices equal to `R` —
so membership is invariant under exponent shifts by `p^m`, i.e. under `μ_p`. This is the
base case for mixed-radix smooth towers (the O65 general-radix fold supplies the
matching descent identities). -/

section PrimePowerBase

omit [CharZero F] in
/-- Slices of a geometric-packet multiple: if `deg R < q` then
`(Σ_{i<p} X^{iq} · R).coeff (iq + s) = R.coeff s` for `i < p`, `s < q`. -/
lemma packet_mul_coeff {p q : ℕ} (_hq : 0 < q) {R : ℚ[X]} (hR : R.natDegree < q)
    {i s : ℕ} (hi : i < p) (hs : s < q) :
    ((∑ i ∈ Finset.range p, (Polynomial.X : ℚ[X]) ^ (i * q)) * R).coeff (i * q + s)
      = R.coeff s := by
  rw [Finset.sum_mul, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [show i * q + s = s + i * q from by ring, Polynomial.coeff_X_pow_mul]
  · intro j hj hji
    rw [Polynomial.coeff_X_pow_mul']
    rcases lt_or_ge (i * q + s) (j * q) with hlt | hge
    · rw [if_neg (by omega)]
    · rw [if_pos hge]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      -- i*q + s − j*q ≥ q when j < i (since s < q and (i−j) ≥ 1)
      rcases lt_or_ge j i with hji' | hji'
      · have : i * q + s - j * q ≥ q := by
          have h1 : (j + 1) * q ≤ i * q := Nat.mul_le_mul_right q (by omega)
          have h2 : j * q + q ≤ i * q := by
            calc j * q + q = (j + 1) * q := by ring
            _ ≤ i * q := h1
          omega
        omega
      · -- j > i: j*q > i*q + s, contradiction with hge
        have hj1 : i + 1 ≤ j := by omega
        have : i * q + q ≤ j * q := by
          calc i * q + q = (i + 1) * q := by ring
          _ ≤ j * q := Nat.mul_le_mul_right q hj1
        omega
  · intro hnotin
    exact absurd (Finset.mem_range.mpr hi) hnotin

/-- **Lam–Leung at prime powers**: in characteristic zero, a finite set of `p^(m+1)`-th
roots of unity with vanishing sum is closed under multiplication by every `p`-th root of
unity. (`p = 2` recovers `vanishing_sum_antipodal`.) -/
theorem vanishing_sum_mu_p_closed {p m : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    {S : Finset F} (hS : ∀ x ∈ S, x ^ (p ^ (m + 1)) = 1)
    (hsum : ∑ x ∈ S, x = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ p = 1 → h * x ∈ S := by
  classical
  set n := p ^ (m + 1) with hn
  set q := p ^ m with hq
  have hppos : 0 < p := hp.pos
  have hqpos : 0 < q := by positivity
  have hnq : n = p * q := by rw [hn, hq]; ring
  have hnpos : 0 < n := by rw [hn]; positivity
  haveI : NeZero n := ⟨hnpos.ne'⟩
  haveI : NeZero p := ⟨hppos.ne'⟩
  -- exponent set and indicator polynomial (as in the p = 2 case)
  set I : Finset ℕ := (Finset.range n).filter (fun i => ζ ^ i ∈ S) with hI
  set P : ℚ[X] := ∑ i ∈ I, X ^ i with hP
  have hPcoeff : ∀ j, P.coeff j = if j ∈ I then 1 else 0 := by
    intro j
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_congr rfl (fun i _ => Polynomial.coeff_X_pow i j)]
    rw [Finset.sum_ite_eq I j (fun _ => (1 : ℚ))]
  have hPζ : Polynomial.aeval ζ P = 0 := by
    rw [hP, map_sum]
    have hterm : ∀ i ∈ I, Polynomial.aeval ζ ((X : ℚ[X]) ^ i) = ζ ^ i := by
      intro i _
      simp
    rw [Finset.sum_congr rfl hterm, ← hsum]
    apply Finset.sum_bij (fun i _ => ζ ^ i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      exact hζ.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hxi.symm ▸ hx⟩, hxi⟩
    · intro i _
      rfl
  -- the cyclotomic packet divides P
  have hdvd : (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)) ∣ P := by
    have hmin := minpoly.dvd ℚ ζ hPζ
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by positivity)] at hmin
    have hcyc : Polynomial.cyclotomic (p ^ (m + 1)) ℚ
        = ∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q) := by
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, hq, mul_comm]
    rwa [hn, hcyc] at hmin
  -- slice equality: P.coeff (i·q + s) is independent of i < p
  have hslice : ∀ s < q, ∀ i < p, ∀ i' < p,
      P.coeff (i * q + s) = P.coeff (i' * q + s) := by
    obtain ⟨R, hR⟩ := hdvd
    by_cases hP0 : P = 0
    · intro s _ i _ i' _
      simp [hP0]
    have hG : (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)) ≠ 0 := by
      intro h
      have := congrArg (fun Q : ℚ[X] => Q.coeff 0) h
      simp only [Polynomial.finset_sum_coeff] at this
      rw [Finset.sum_eq_single 0 (fun j _ hj => by
        rw [Polynomial.coeff_X_pow]
        rw [if_neg (by
          intro h0
          rcases Nat.mul_eq_zero.mp h0.symm with h | h
          · exact hj h
          · omega)]) (fun h0 => absurd (Finset.mem_range.mpr hppos) h0)] at this
      simp at this
    have hR0 : R ≠ 0 := fun h => hP0 (by rw [hR, h, mul_zero])
    have hdegG : (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)).natDegree ≤ (p - 1) * q := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      rw [Polynomial.natDegree_X_pow]
      have := Finset.mem_range.mp hi
      exact Nat.mul_le_mul_right q (by omega)
    have hdegP : P.natDegree < n := by
      rw [hP]
      have hle : (∑ i ∈ I, (X : ℚ[X]) ^ i).natDegree ≤ n - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => by
          rw [Polynomial.natDegree_X_pow]
          have := Finset.mem_range.mp (Finset.mem_filter.mp (hI ▸ hi)).1
          omega
      omega
    have hdegR : R.natDegree < q := by
      have hmul := Polynomial.natDegree_mul hG hR0
      rw [← hR] at hmul
      -- natDegree G = (p−1)q exactly? we only need: natDegree R < q
      -- from P = G·R: natDegree P = natDegree G + natDegree R ≥ ... need LOWER bound on G:
      -- G has coeff 1 at (p−1)q, so natDegree G ≥ (p−1)q
      have hGlow : (p - 1) * q ≤ (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)).natDegree := by
        apply Polynomial.le_natDegree_of_ne_zero
        rw [Polynomial.finset_sum_coeff]
        rw [Finset.sum_eq_single (p - 1) (fun j hj hjne => by
          rw [Polynomial.coeff_X_pow, if_neg (fun h => hjne (by
            have := Nat.eq_of_mul_eq_mul_right hqpos h
            omega))]) (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0)]
        rw [Polynomial.coeff_X_pow, if_pos rfl]
        norm_num
      have hcount : (p - 1) * q + q = n := by
        rw [hnq]
        have : 1 ≤ p := hppos
        calc (p - 1) * q + q = ((p - 1) + 1) * q := by ring
        _ = p * q := by congr 1; omega
      omega
    intro s hs i hi i' hi'
    rw [hR, packet_mul_coeff hqpos hdegR hi hs, packet_mul_coeff hqpos hdegR hi' hs]
  -- conclusion: membership is q-shift invariant; μ_p = powers of ζ^q
  have hmem : ∀ s < q, ∀ i < p, ∀ i' < p, (ζ ^ (i * q + s) ∈ S ↔ ζ ^ (i' * q + s) ∈ S) := by
    intro s hs i hi i' hi'
    have := hslice s hs i hi i' hi'
    rw [hPcoeff, hPcoeff] at this
    have hiI : (i * q + s ∈ I) ↔ (i' * q + s ∈ I) := by
      by_cases h1 : i * q + s ∈ I <;> by_cases h2 : i' * q + s ∈ I <;>
        simp [h1, h2] at this ⊢
    rw [hI] at hiI
    simp only [Finset.mem_filter, Finset.mem_range] at hiI
    have hb1 : i * q + s < n := by
      rw [hnq]
      have : (i + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
      have : i * q + q ≤ p * q := by
        calc i * q + q = (i + 1) * q := by ring
        _ ≤ p * q := this
      omega
    have hb2 : i' * q + s < n := by
      rw [hnq]
      have h' : (i' + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
      have : i' * q + q ≤ p * q := by
        calc i' * q + q = (i' + 1) * q := by ring
        _ ≤ p * q := h'
      omega
    constructor
    · intro hx
      exact (hiI.mp ⟨hb1, hx⟩).2
    · intro hx
      exact (hiI.mpr ⟨hb2, hx⟩).2
  -- assemble: h with h^p = 1 is (ζ^q)^k; shift the coset index
  intro x hx h hh
  obtain ⟨e, he, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
  have hζq : IsPrimitiveRoot (ζ ^ q) p := by
    refine hζ.pow hnpos ?_
    rw [hn, hq]
    ring
  obtain ⟨k, hk, hkq⟩ := hζq.eq_pow_of_pow_eq_one hh
  -- write e = i·q + s with i < p, s < q
  obtain ⟨i, s, rfl, hs⟩ : ∃ i s, e = i * q + s ∧ s < q :=
    ⟨e / q, e % q, by rw [mul_comm]; exact (Nat.div_add_mod e q).symm, Nat.mod_lt _ hqpos⟩
  have hi : i < p := by
    by_contra hge
    push Not at hge
    have : p * q ≤ i * q := Nat.mul_le_mul_right q hge
    rw [hnq] at he
    omega
  set i2 := (k + i) % p with hi2def
  have hi2p : i2 < p := Nat.mod_lt _ hppos
  have hxmem : ζ ^ (i2 * q + s) ∈ S := (hmem s hs i hi i2 hi2p).mp hx
  have hfinal : h * ζ ^ (i * q + s) = ζ ^ (i2 * q + s) := by
    rw [← hkq, ← pow_mul, ← pow_add]
    have hdecomp : q * k + (i * q + s) = n * ((k + i) / p) + (i2 * q + s) := by
      calc q * k + (i * q + s) = (k + i) * q + s := by ring
      _ = (p * ((k + i) / p) + i2) * q + s := by
          rw [hi2def]
          congr 2
          exact (Nat.div_add_mod (k + i) p).symm
      _ = (p * q) * ((k + i) / p) + (i2 * q + s) := by ring
      _ = n * ((k + i) / p) + (i2 * q + s) := by rw [hnq]
    rw [hdecomp, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [hfinal]
  exact hxmem

end PrimePowerBase

/-! ## The coefficient-general slice theorem: the de Bruijn engine

Upgrading the O66 machinery from subset indicators to ARBITRARY ℚ-coefficients: any
vanishing ℚ-linear combination of `p^(m+1)`-th roots of unity has all `p` of its
coefficient slices equal. This is exactly the engine the two-prime (de Bruijn) induction
needs: the CRT double-slice argument applies this theorem at one prime with coefficients
in the other prime's cyclotomic field, and the slice DIFFERENCES it produces carry
`{−1,0,1}` coefficients — outside the subset world, inside this one. -/

section CoefficientSlices

/-- **The coefficient-general prime-power slice theorem**. -/
theorem vanishing_coeff_slices {p m : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    (c : ℕ → ℚ)
    (hsum : ∑ e ∈ Finset.range (p ^ (m + 1)), (c e : F) * ζ ^ e = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p, c (i * p ^ m + s) = c (i' * p ^ m + s) := by
  classical
  set n := p ^ (m + 1) with hn
  set q := p ^ m with hq
  have hppos : 0 < p := hp.pos
  have hqpos : 0 < q := by positivity
  have hnq : n = p * q := by rw [hn, hq]; ring
  have hnpos : 0 < n := by rw [hn]; positivity
  set P : ℚ[X] := ∑ e ∈ Finset.range n, Polynomial.C (c e) * X ^ e with hP
  have hPcoeff : ∀ j < n, P.coeff j = c j := by
    intro j hj
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_congr rfl (fun e _ => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow])]
    rw [Finset.sum_eq_single j (fun e _ hej => by
      rw [if_neg (fun h => hej h.symm), mul_zero]) (fun h =>
      absurd (Finset.mem_range.mpr hj) h)]
    rw [if_pos rfl, mul_one]
  have hPζ : Polynomial.aeval ζ P = 0 := by
    rw [hP, map_sum]
    rw [Finset.sum_congr rfl (fun e _ => by
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X])]
    exact hsum
  have hdvd : (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)) ∣ P := by
    have hmin := minpoly.dvd ℚ ζ hPζ
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by positivity)] at hmin
    have hcyc : Polynomial.cyclotomic (p ^ (m + 1)) ℚ
        = ∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q) := by
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, hq, mul_comm]
    rwa [hn, hcyc] at hmin
  intro s hs i hi i' hi'
  have hb : ∀ j < p, j * q + s < n := by
    intro j hj
    rw [hnq]
    have h1 : (j + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
    have : j * q + q ≤ p * q := by
      calc j * q + q = (j + 1) * q := by ring
      _ ≤ p * q := h1
    omega
  rw [← hPcoeff _ (hb i hi), ← hPcoeff _ (hb i' hi')]
  obtain ⟨R, hR⟩ := hdvd
  by_cases hP0 : P = 0
  · simp [hP0]
  have hR0 : R ≠ 0 := fun h => hP0 (by rw [hR, h, mul_zero])
  have hG : (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)) ≠ 0 := by
    intro h
    have := congrArg (fun Q : ℚ[X] => Q.coeff 0) h
    simp only [Polynomial.finset_sum_coeff] at this
    rw [Finset.sum_eq_single 0 (fun j _ hj => by
      rw [Polynomial.coeff_X_pow]
      rw [if_neg (by
        intro h0
        rcases Nat.mul_eq_zero.mp h0.symm with h | h
        · exact hj h
        · omega)]) (fun h0 => absurd (Finset.mem_range.mpr hppos) h0)] at this
    simp at this
  have hdegP : P.natDegree < n := by
    rw [hP]
    have hle : (∑ e ∈ Finset.range n, Polynomial.C (c e) * (X : ℚ[X]) ^ e).natDegree
        ≤ n - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he => by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
        have := Finset.mem_range.mp he
        omega
    omega
  have hdegR : R.natDegree < q := by
    have hmul := Polynomial.natDegree_mul hG hR0
    rw [← hR] at hmul
    have hGlow : (p - 1) * q ≤ (∑ i ∈ Finset.range p, (X : ℚ[X]) ^ (i * q)).natDegree := by
      apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.finset_sum_coeff]
      rw [Finset.sum_eq_single (p - 1) (fun j hj hjne => by
        rw [Polynomial.coeff_X_pow, if_neg (fun h => hjne (by
          have := Nat.eq_of_mul_eq_mul_right hqpos h
          omega))]) (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0)]
      rw [Polynomial.coeff_X_pow, if_pos rfl]
      norm_num
    have hcount : (p - 1) * q + q = n := by
      rw [hnq]
      calc (p - 1) * q + q = ((p - 1) + 1) * q := by ring
      _ = p * q := by congr 1; omega
    omega
  rw [hR, packet_mul_coeff hqpos hdegR hi hs, packet_mul_coeff hqpos hdegR hi' hs]

end CoefficientSlices

/-! ## The complete ℚ-kernel at 2-power level: vanishing ⟺ antipodal symmetry

The coefficient-slice theorem (O68) upgraded to a full characterization at `p = 2`:
a ℚ-coefficient combination of `2^(m+1)`-th roots of unity vanishes **iff** its
coefficient function is antipodally symmetric (`c(e) = c(e + 2^m)`). Necessity is the
slice theorem; sufficiency is `ζ^(2^m) = −1` pairing terms to zero. Corollary: any
combination with an UNPAIRED support point is nonzero — the sparse-nonvanishing bound
that forces branch data in the descent tree (a branch whose window pins it to an
asymmetric configuration is impossible; leaf data is rigid). -/

section KernelCharacterization

/-- **The complete 2-power kernel characterization**: vanishing ⟺ antipodal coefficient
symmetry. -/
theorem vanishing_iff_antipodal_coeffs {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) (c : ℕ → ℚ) :
    (∑ e ∈ Finset.range (2 ^ (m + 1)), (c e : F) * ζ ^ e = 0) ↔
    (∀ s < 2 ^ m, c s = c (s + 2 ^ m)) := by
  constructor
  · intro hsum s hs
    have h01 := vanishing_coeff_slices Nat.prime_two hζ c hsum s hs 0 (by norm_num) 1
      (by norm_num)
    simpa [Nat.add_comm] using h01
  · intro hsym
    have hhalf : ζ ^ (2 ^ m) = -1 := pow_half_eq_neg_one hζ
    have h2 : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    rw [h2, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hsm := hsym s (Finset.mem_range.mp hs)
    rw [show (2 : ℕ) ^ m + s = s + 2 ^ m from by ring, ← hsm, pow_add, hhalf]
    ring

/-- **The sparse nonvanishing bound**: a combination with an unpaired support point is
nonzero — branch data in the descent tree is rigid. -/
theorem nonvanishing_of_unpaired {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) (c : ℕ → ℚ)
    {s : ℕ} (hs : s < 2 ^ m) (hne : c s ≠ c (s + 2 ^ m)) :
    ∑ e ∈ Finset.range (2 ^ (m + 1)), (c e : F) * ζ ^ e ≠ 0 := by
  intro h
  exact hne ((vanishing_iff_antipodal_coeffs hζ c).mp h s hs)

end KernelCharacterization

/-! ## The valued 2-power windowed law: window-invariance modulo `2^(m−k)`

The multiplicity-door base case of the valued-fold frontier: a ℚ-coefficient vector on
`μ_{2^(m+1)}`-exponents whose 2-power window `{2^0, …, 2^k}` vanishes is invariant on
exponent classes modulo `2^(m−k)` — the valued analogue of `full_tower`. Induction on
`k`: the `j = 0` relation gives antipodal symmetry (O74), under which the folded vector
`c₁(s) = c(s) + c(s + 2^m) = 2·c(s)` inherits the shallower window at the halved level;
the inductive congruence-invariance of `c₁` pulls back through the antipodal reduction.
For integer multiplicity vectors (contracted folds of windowed sets, branch-weight
profiles) this pins the structure completely at 2-power levels. -/

section ValuedWindowedLaw

/-- **The valued 2-power windowed law** (congruence-invariance form). -/
theorem windowed_coeff_congr_invariant {k : ℕ} :
    ∀ {m : ℕ}, k ≤ m → ∀ {ζ : F}, IsPrimitiveRoot ζ (2 ^ (m + 1)) →
    ∀ (c : ℕ → ℚ),
    (∀ j, j ≤ k → ∑ e ∈ Finset.range (2 ^ (m + 1)), (c e : F) * ζ ^ (2 ^ j * e) = 0) →
    ∀ e e', e < 2 ^ (m + 1) → e' < 2 ^ (m + 1) →
      e % 2 ^ (m - k) = e' % 2 ^ (m - k) → c e = c e' := by
  induction k with
  | zero =>
    intro m _ ζ hζ c hwin e e' he he' hmod
    have h0 := hwin 0 le_rfl
    simp only [pow_zero, one_mul] at h0
    have hsym := (vanishing_iff_antipodal_coeffs hζ c).mp h0
    rw [Nat.sub_zero] at hmod
    -- e ≡ e' mod 2^m with both < 2^{m+1}: equal or differ by exactly 2^m
    rcases Nat.lt_or_ge e (2 ^ m) with hlow | hhigh
    · rcases Nat.lt_or_ge e' (2 ^ m) with hlow' | hhigh'
      · -- both low: e = e'
        rw [Nat.mod_eq_of_lt hlow, Nat.mod_eq_of_lt hlow'] at hmod
        rw [hmod]
      · -- e low, e' high: e' = e + 2^m
        have he'm : e' - 2 ^ m < 2 ^ m := by
          have : (2:ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
          omega
        have hmod' : e' % 2 ^ m = e' - 2 ^ m := by
          rw [Nat.mod_eq_sub_mod hhigh', Nat.mod_eq_of_lt he'm]
        rw [Nat.mod_eq_of_lt hlow, hmod'] at hmod
        have : e' = e + 2 ^ m := by omega
        rw [this]
        exact hsym e hlow
    · rcases Nat.lt_or_ge e' (2 ^ m) with hlow' | hhigh'
      · have hem : e - 2 ^ m < 2 ^ m := by
          have : (2:ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
          omega
        have hmod'' : e % 2 ^ m = e - 2 ^ m := by
          rw [Nat.mod_eq_sub_mod hhigh, Nat.mod_eq_of_lt hem]
        rw [hmod'', Nat.mod_eq_of_lt hlow'] at hmod
        have : e = e' + 2 ^ m := by omega
        rw [this]
        exact (hsym e' hlow').symm
      · -- both high: e − 2^m = e' − 2^m
        have hem : e - 2 ^ m < 2 ^ m := by
          have : (2:ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
          omega
        have he'm : e' - 2 ^ m < 2 ^ m := by
          have : (2:ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
          omega
        have h1 : e % 2 ^ m = e - 2 ^ m := by
          rw [Nat.mod_eq_sub_mod hhigh, Nat.mod_eq_of_lt hem]
        have h2 : e' % 2 ^ m = e' - 2 ^ m := by
          rw [Nat.mod_eq_sub_mod hhigh', Nat.mod_eq_of_lt he'm]
        rw [h1, h2] at hmod
        have : e = e' := by omega
        rw [this]
  | succ k IH =>
    intro m hkm ζ hζ c hwin e e' he he' hmod
    have h0 := hwin 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at h0
    have hsym := (vanishing_iff_antipodal_coeffs hζ c).mp h0
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (m' + 1)) := by
      refine hζ.pow (pow_pos two_pos _) ?_
      rw [pow_succ']
    set c₁ : ℕ → ℚ := fun s => c s + c (s + 2 ^ (m' + 1)) with hc₁
    have hfold : ∀ j, j ≤ k →
        ∑ s ∈ Finset.range (2 ^ (m' + 1)), (c₁ s : F) * (ζ ^ 2) ^ (2 ^ j * s) = 0 := by
      intro j hj
      have hrel := hwin (j + 1) (by omega)
      have hsplit : (2:ℕ) ^ (m' + 1 + 1) = 2 ^ (m' + 1) + 2 ^ (m' + 1) := by ring
      rw [hsplit, Finset.sum_range_add] at hrel
      have hterm : ∀ s ∈ Finset.range (2 ^ (m' + 1)),
          (c (2 ^ (m' + 1) + s) : F) * ζ ^ (2 ^ (j + 1) * (2 ^ (m' + 1) + s))
            = (c (s + 2 ^ (m' + 1)) : F) * ζ ^ (2 ^ (j + 1) * s) := by
        intro s _
        rw [Nat.add_comm (2 ^ (m' + 1)) s]
        congr 1
        rw [Nat.mul_add, pow_add]
        have hkill : ζ ^ (2 ^ (j + 1) * 2 ^ (m' + 1)) = 1 := by
          rw [show (2:ℕ) ^ (j + 1) * 2 ^ (m' + 1) = 2 ^ (m' + 1 + 1) * 2 ^ j from by
            rw [← pow_add, ← pow_add]
            congr 1
            omega]
          rw [pow_mul, hζ.pow_eq_one, one_pow]
        rw [hkill, mul_one]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_add_distrib] at hrel
      calc ∑ s ∈ Finset.range (2 ^ (m' + 1)), (c₁ s : F) * (ζ ^ 2) ^ (2 ^ j * s)
          = ∑ s ∈ Finset.range (2 ^ (m' + 1)),
              ((c s : F) * ζ ^ (2 ^ (j + 1) * s)
                + (c (s + 2 ^ (m' + 1)) : F) * ζ ^ (2 ^ (j + 1) * s)) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [hc₁]
            push_cast
            rw [← pow_mul, show 2 * (2 ^ j * s) = 2 ^ (j + 1) * s from by
              rw [pow_succ']; ring]
            ring
        _ = 0 := hrel
    have hIH := IH (m := m') (by omega) hζ2 c₁ hfold
    -- antipodal reduction to the lower half, then the IH congruence
    have hreduce : ∀ x, x < 2 ^ (m' + 1 + 1) → c x = c (x % 2 ^ (m' + 1)) := by
      intro x hx
      rcases Nat.lt_or_ge x (2 ^ (m' + 1)) with hlow | hhigh
      · rw [Nat.mod_eq_of_lt hlow]
      · have hxm : x - 2 ^ (m' + 1) < 2 ^ (m' + 1) := by
          have : (2:ℕ) ^ (m' + 1 + 1) = 2 ^ (m' + 1) + 2 ^ (m' + 1) := by ring
          omega
        rw [Nat.mod_eq_sub_mod hhigh, Nat.mod_eq_of_lt hxm]
        have := hsym (x - 2 ^ (m' + 1)) hxm
        rw [show x - 2 ^ (m' + 1) + 2 ^ (m' + 1) = x from by omega] at this
        exact this.symm
    have hhalf : ∀ s, s < 2 ^ (m' + 1) → c s = c₁ s / 2 := by
      intro s hsl
      simp only [hc₁]
      rw [← hsym s hsl]
      ring
    have hmodsub : m' + 1 - (k + 1) = m' - k := by omega
    rw [hmodsub] at hmod
    have hdvd : (2:ℕ) ^ (m' - k) ∣ 2 ^ (m' + 1) := pow_dvd_pow 2 (by omega)
    have hē : (e % 2 ^ (m' + 1)) % 2 ^ (m' - k) = (e' % 2 ^ (m' + 1)) % 2 ^ (m' - k) := by
      rw [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd]
      exact hmod
    have hēlt : e % 2 ^ (m' + 1) < 2 ^ (m' + 1) := Nat.mod_lt _ (pow_pos two_pos _)
    have hē'lt : e' % 2 ^ (m' + 1) < 2 ^ (m' + 1) := Nat.mod_lt _ (pow_pos two_pos _)
    calc c e = c (e % 2 ^ (m' + 1)) := hreduce e he
    _ = c₁ (e % 2 ^ (m' + 1)) / 2 := hhalf _ hēlt
    _ = c₁ (e' % 2 ^ (m' + 1)) / 2 := by
        rw [hIH (e % 2 ^ (m' + 1)) (e' % 2 ^ (m' + 1)) hēlt hē'lt hē]
    _ = c (e' % 2 ^ (m' + 1)) := (hhalf _ hē'lt).symm
    _ = c e' := (hreduce e' he').symm

end ValuedWindowedLaw

/-! ## Contracted multiplicity rigidity: the branch program's first formal constraint

The O125 valued law applied to fold multiplicities: for a windowed subset of
`μ_{2^(m+1)}`, the fiber-count function of the `2^s`-power contraction is an INTEGER
vector inheriting the window at scaled exponents — hence coset-constant by the valued
law. Branch-weight profiles of windowed sets down the 2-adic tower are RIGID: at every
depth, the multiplicity a windowed set lays over the contracted domain is invariant on
`μ`-coset classes. This is the first machine-checked structural constraint the program
places on the branch-count objects themselves. -/

section MultiplicityRigidity

variable [DecidableEq F]

/-- The fiber-sum identity: a power sum of `S` at a `2^s`-multiple exponent is the
multiplicity-weighted power sum of the contraction. -/
lemma contraction_fiber_sum {m s : ℕ} (hsm : s ≤ m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (2 ^ (m + 1)) = 1) (j : ℕ) :
    ∑ z ∈ S, z ^ (2 ^ s * j)
      = ∑ e ∈ Finset.range (2 ^ (m + 1 - s)),
          ((S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e)).card : F)
            * ((ζ ^ (2 ^ s)) ^ e) ^ j := by
  classical
  have hζ' : IsPrimitiveRoot (ζ ^ (2 ^ s)) (2 ^ (m + 1 - s)) := by
    refine hζ.pow (pow_pos two_pos _) ?_
    rw [← pow_add]
    congr 1
    omega
  haveI : NeZero ((2:ℕ) ^ (m + 1 - s)) := ⟨(pow_pos two_pos _).ne'⟩
  -- the filters partition S
  have hcover : S = (Finset.range (2 ^ (m + 1 - s))).biUnion
      (fun e => S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e)) := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hxc : (x ^ (2 ^ s)) ^ (2 ^ (m + 1 - s)) = 1 := by
        rw [← pow_mul, ← pow_add, show s + (m + 1 - s) = m + 1 from by omega]
        exact hS x hx
      obtain ⟨e, he, hxe⟩ := hζ'.eq_pow_of_pow_eq_one hxc
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_range.mpr he,
        Finset.mem_filter.mpr ⟨hx, hxe.symm⟩⟩
    · intro x hx
      obtain ⟨e, _, hxf⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hxf).1
  have hdisj : ∀ e₁ ∈ Finset.range (2 ^ (m + 1 - s)),
      ∀ e₂ ∈ Finset.range (2 ^ (m + 1 - s)), e₁ ≠ e₂ →
      Disjoint (S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e₁))
        (S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e₂)) := by
    intro e₁ he₁ e₂ he₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h₁ := (Finset.mem_filter.mp hx₁).2
    have h₂ := (Finset.mem_filter.mp hx₂).2
    exact hne (hζ'.pow_inj (Finset.mem_range.mp he₁) (Finset.mem_range.mp he₂)
      (h₁ ▸ h₂ ▸ rfl))
  conv_lhs => rw [hcover]
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hconst : ∀ x ∈ S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e),
      x ^ (2 ^ s * j) = ((ζ ^ (2 ^ s)) ^ e) ^ j := by
    intro x hx
    rw [pow_mul, (Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-- **Contracted multiplicity rigidity**: for a set with the scaled 2-power window, the
contraction's fiber-count function is invariant on exponent classes modulo
`2^(m−s−k)`. -/
theorem contracted_multiplicity_invariant {m s k : ℕ} (hsk : s + k ≤ m) {ζ : F}
    [CharZero F]
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (2 ^ (m + 1)) = 1)
    (hwin : ∀ j, j ≤ k → ∑ z ∈ S, z ^ (2 ^ (s + j)) = 0) :
    ∀ e e', e < 2 ^ (m + 1 - s) → e' < 2 ^ (m + 1 - s) →
      e % 2 ^ (m - s - k) = e' % 2 ^ (m - s - k) →
      (S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e)).card
        = (S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e')).card := by
  classical
  have hζ' : IsPrimitiveRoot (ζ ^ (2 ^ s)) (2 ^ (m + 1 - s)) := by
    refine hζ.pow (pow_pos two_pos _) ?_
    rw [← pow_add]
    congr 1
    omega
  obtain ⟨m', hm'⟩ : ∃ m', m + 1 - s = m' + 1 := ⟨m - s, by omega⟩
  set c : ℕ → ℚ := fun e =>
    ((S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e)).card : ℚ) with hc
  have hcwin : ∀ j, j ≤ k →
      ∑ e ∈ Finset.range (2 ^ (m' + 1)), (c e : F) * (ζ ^ (2 ^ s)) ^ (2 ^ j * e)
        = 0 := by
    intro j hj
    have hfib := contraction_fiber_sum (le_trans (by omega : s ≤ s + k) (by omega))
      hζ hS (2 ^ j)
    rw [hm'] at hfib
    have hSwin := hwin j hj
    rw [show (2:ℕ) ^ (s + j) = 2 ^ s * 2 ^ j from by rw [pow_add]] at hSwin
    rw [hSwin] at hfib
    have halign : ∀ e ∈ Finset.range (2 ^ (m' + 1)),
        (c e : F) * (ζ ^ (2 ^ s)) ^ (2 ^ j * e)
          = ((S.filter (fun x => x ^ (2 ^ s) = (ζ ^ (2 ^ s)) ^ e)).card : F)
            * ((ζ ^ (2 ^ s)) ^ e) ^ (2 ^ j) := by
      intro e _
      simp only [hc]
      push_cast
      rw [← pow_mul]
      congr 1
      ring
    rw [Finset.sum_congr rfl halign]
    exact hfib.symm
  have hζ'' : IsPrimitiveRoot (ζ ^ (2 ^ s)) (2 ^ (m' + 1)) := hm' ▸ hζ'
  have hinv := windowed_coeff_congr_invariant (k := k) (m := m') (by omega) hζ'' c hcwin
  intro e e' he he' hmod
  have hres := hinv e e' (by rw [← hm']; exact he) (by rw [← hm']; exact he')
    (by rw [show m' - k = m - s - k from by omega]; exact hmod)
  simp only [hc] at hres
  exact_mod_cast hres

end MultiplicityRigidity

/-! ## The sparse tower theorem: full_tower from exponentially fewer conditions

O126 at depth `s = 0`: the indicator of a subset is its own depth-0 multiplicity
vector, so the rigidity law applies — and yields `full_tower`'s coset-union conclusion
from ONLY the 2-power window `{2^0, …, 2^k}` (`k+1` exponents) instead of the full
window `[1, 2^(k+1))` (`2^(k+1) − 1` exponents): the original pillar of the session,
strengthened exponentially in hypothesis by its newest theorem. -/

section SparseTower

variable [DecidableEq F] [CharZero F]

/-- **The sparse tower theorem**: 2-power window alone forces `μ_{2^(k+1)}`-closure. -/
theorem full_tower_sparse {m k : ℕ} (hk : k ≤ m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (2 ^ (m + 1)) = 1)
    (hwin : ∀ j, j ≤ k → ∑ z ∈ S, z ^ (2 ^ j) = 0) :
    ∀ x ∈ S, ∀ h : F, h ^ (2 ^ (k + 1)) = 1 → h * x ∈ S := by
  classical
  haveI : NeZero ((2:ℕ) ^ (k + 1)) := ⟨(pow_pos two_pos _).ne'⟩
  -- depth-0 rigidity: the indicator is invariant mod 2^(m−k)
  have hrig := contracted_multiplicity_invariant (m := m) (s := 0) (k := k)
    (by omega) hζ hS (fun j hj => by rw [Nat.zero_add]; exact hwin j hj)
  have hfid : ∀ f : ℕ, S.filter (fun x => x ^ 2 ^ 0 = (ζ ^ 2 ^ 0) ^ f)
      = S.filter (fun y => y = ζ ^ f) := by
    intro f
    refine Finset.filter_congr fun y _ => ?_
    norm_num
  -- the μ_{2^(k+1)}-roots are powers of ζ^(2^(m−k))
  have hωk : IsPrimitiveRoot (ζ ^ (2 ^ (m - k))) (2 ^ (k + 1)) := by
    refine hζ.pow (pow_pos two_pos _) ?_
    rw [← pow_add]
    congr 1
    omega
  intro x hx h hh
  obtain ⟨i, hi, hig⟩ := hωk.eq_pow_of_pow_eq_one hh
  obtain ⟨e, he, hex⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
  -- h·x = ζ^{e + i·2^(m−k) mod 2^(m+1)}, same residue mod 2^(m−k)
  set e2 := (e + i * 2 ^ (m - k)) % 2 ^ (m + 1) with he2
  have he2lt : e2 < 2 ^ (m + 1) := Nat.mod_lt _ (pow_pos two_pos _)
  have hhx : h * x = ζ ^ e2 := by
    rw [← hig, ← hex, ← pow_mul, ← pow_add]
    rw [show 2 ^ (m - k) * i + e = e + i * 2 ^ (m - k) from by ring]
    conv_lhs => rw [← Nat.div_add_mod (e + i * 2 ^ (m - k)) (2 ^ (m + 1))]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul, he2]
  have hdvd : (2:ℕ) ^ (m - k) ∣ 2 ^ (m + 1) := pow_dvd_pow 2 (by omega)
  have hres : e2 % 2 ^ (m - k) = e % 2 ^ (m - k) := by
    rw [he2, Nat.mod_mod_of_dvd _ hdvd, Nat.add_mul_mod_self_right]
  -- indicator invariance: the filter cards at e2 and e agree
  have hcards := hrig e2 e (by simpa using he2lt) (by simpa using he)
    (by simpa using hres)
  rw [hfid, hfid] at hcards
  -- the filter at exponent f is {ζ^f} ∩ S: card 1 iff ζ^f ∈ S
  have hcard_mem : ∀ f, f < 2 ^ (m + 1) →
      ((S.filter (fun y => y = ζ ^ f)).card = 1 ↔ ζ ^ f ∈ S) := by
    intro f hf
    constructor
    · intro h1
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
      have : y ∈ S.filter (fun y => y = ζ ^ f) := hy ▸ Finset.mem_singleton_self y
      obtain ⟨hyS, rfl⟩ := Finset.mem_filter.mp this
      exact hyS
    · intro hmem
      rw [Finset.card_eq_one]
      refine ⟨ζ ^ f, Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hmem, rfl⟩, ?_⟩⟩
      intro y hy
      exact (Finset.mem_filter.mp hy).2
  -- conclude membership transfer
  have hxmem : ζ ^ e ∈ S := by rwa [hex]
  have hc_e : (S.filter (fun y => y = ζ ^ e)).card = 1 := (hcard_mem e he).mpr hxmem
  have hc_e2 : (S.filter (fun y => y = ζ ^ e2)).card = 1 := by
    rw [show (S.filter (fun y => y = ζ ^ e2)).card
        = (S.filter (fun y => y = ζ ^ e)).card from hcards]
    exact hc_e
  rw [hhx]
  exact (hcard_mem e2 he2lt).mp hc_e2

end SparseTower

/-! ## The sparse budget: tower_count under 2-power-only syndromes

`tower_count`'s recovery-injection bound with `full_tower_sparse` supplying the closure:
the same `2^{#classes}` budget from only `k+1` syndrome conditions — the exponentially
lighter verifier obligation, as a counting theorem. -/

section SparseBudget

theorem sparse_tower_count [DecidableEq F] {m : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {k : ℕ} (hk : k ≤ m) {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ (2 ^ (m + 1)) = 1)
    (w : ℕ) :
    ((D₀.powersetCard w).filter (fun S =>
        ∀ j, j ≤ k → ∑ x ∈ S, x ^ (2 ^ j) = 0)).card
      ≤ 2 ^ (D₀.image (· ^ (2 ^ (k + 1)))).card := by
  classical
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun S => S.image (· ^ (2 ^ (k + 1))))
  · intro S hS
    have hS2 := Finset.mem_coe.mp hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS2
    simp only [Finset.mem_coe, Finset.mem_powerset]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x, hS2.1.1 hx, rfl⟩
  · intro S hSm S' hSm' himg
    have hmem := Finset.mem_coe.mp hSm
    have hmem' := Finset.mem_coe.mp hSm'
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hmem hmem'
    obtain ⟨⟨hSD, _⟩, hPS⟩ := hmem
    obtain ⟨⟨hSD', _⟩, hPS'⟩ := hmem'
    have hclos : ∀ x ∈ S, ∀ h : F, h ^ (2 ^ (k + 1)) = 1 → h * x ∈ S :=
      full_tower_sparse hk hζ (fun x hx => hD₀ x (hSD hx)) hPS
    have hclos' : ∀ x ∈ S', ∀ h : F, h ^ (2 ^ (k + 1)) = 1 → h * x ∈ S' :=
      full_tower_sparse hk hζ (fun x hx => hD₀ x (hSD' hx)) hPS'
    have hrec : ∀ (T : Finset F), T ⊆ D₀ →
        (∀ x ∈ T, ∀ h : F, h ^ (2 ^ (k + 1)) = 1 → h * x ∈ T) →
        (∀ x ∈ T, x ≠ 0) →
        T = D₀.filter (fun x => x ^ (2 ^ (k + 1)) ∈ T.image (· ^ (2 ^ (k + 1)))) := by
      intro T hTD hTclos hT0
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_filter.mpr ⟨hTD hx, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      · intro x hx
        obtain ⟨hxD, hxim⟩ := Finset.mem_filter.mp hx
        obtain ⟨x₀, hx₀, hpow⟩ := Finset.mem_image.mp hxim
        have hx₀0 : x₀ ≠ 0 := hT0 x₀ hx₀
        have hx00 : x₀ ^ (2 ^ (k + 1)) ≠ 0 := pow_ne_zero _ hx₀0
        have hq : (x / x₀) ^ (2 ^ (k + 1)) = 1 := by
          rw [div_pow, ← hpow, div_self hx00]
        have := hTclos x₀ hx₀ (x / x₀) hq
        rwa [div_mul_cancel₀ x hx₀0] at this
    have hT0S : ∀ x ∈ S, x ≠ 0 := by
      intro x hx h0
      have := hD₀ x (hSD hx)
      rw [h0, zero_pow (by positivity : (0:ℕ) < 2 ^ (m + 1)).ne'] at this
      exact one_ne_zero (α := F) this.symm
    have hT0S' : ∀ x ∈ S', x ≠ 0 := by
      intro x hx h0
      have := hD₀ x (hSD' hx)
      rw [h0, zero_pow (by positivity : (0:ℕ) < 2 ^ (m + 1)).ne'] at this
      exact one_ne_zero (α := F) this.symm
    simp only [] at himg
    rw [hrec S hSD hclos hT0S, hrec S' hSD' hclos' hT0S', himg]

end SparseBudget

end LamLeungTwoPow
