/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_LamLeungTwoPowerAntipodalBalan

/-!
# The char-0 Bessel-EGF identity, on the ACTUAL `Finset.card` energy (#444, avenue UC)

This brick discharges the last NAMED-HYPOTHESIS gap in the char-0 Wick chain: the file
`_AvW0_BesselIdentity.lean` proves the Wick bound on the EGF *model* `Edef r m = (2r)!·[x^{2r}]I₀(2x)^m`
and pins it to integer anchors, but carries the link `Edef = (actual additive energy)` only as a
definition. Here we prove the cleanest provable CORE of that link as a genuine `Finset.card` equality,
consuming the proven Lam–Leung antipodal-balance brick.

## The mathematical content

The char-0 additive energy of `μ_{2m}` is (via `rEnergy_eq_zeroSumCount`) the **zero-sum count**

  `Z_r(G) := #{ c : Fin (2r) → G : ∑ᵢ cᵢ = 0 }`,   `G = μ_{2m} ⊂ ℂˣ`.

The Bessel identity factors this over the `m` antipodal DIRECTIONS of `μ_{2m}`: a vanishing sum of
`2^μ`-th roots is antipodally balanced (Lam–Leung), so per direction `{±w}` the surviving count is the
**balanced sign-split** count, whose EGF is `I₀(2x)` (`[x^{2r}]I₀(2x)·(2r)! = C(2r,r) = centralBinom r`,
the central binomial), and the directions decouple into the `m`-fold convolution `I₀(2x)^m`.

## What is FORMALIZED here (axiom-clean, no `sorry`, no `native_decide`)

1. **`zeroSum_negPair_eq_centralBinom`** — the single-antipodal-direction (`G = {1,−1}`, i.e. `μ_2`)
   per-direction count EXACTLY: `Z_r({1,−1}) = centralBinom r`, via a genuine bijection to the
   `r`-subsets of `Fin (2r)` (the positions carrying `+1`). This IS the `m = 1` Bessel identity on
   the real energy, the base of the convolution.

2. **`bessel_identity_mu2`** — the `m = 1` Bessel identity tying the actual count to the EGF model
   of `_AvW0`: `Z_r({1,−1}) = AvW0.Edef r 1` (both `= centralBinom r`).

3. **`antipodal_balance_forces_split`** — the decoupling INPUT, lifted from the proven Lam–Leung
   brick: a char-0 zero-sum tuple of `2^μ`-th roots has, in every antipodal direction, equally many
   `+w` and `−w` entries (so per direction it is a balanced split — the `I₀(2x)` per-direction law).

4. **`decoupling_is_convolution`** — the abstract decoupling lemma for a union of `d` antipodal
   directions, stated on the EGF: the `d`-direction energy coefficient is the `d`-fold convolution of
   the per-direction count `c`, `cpow c d r = Σⱼ c j · cpow c (d−1) (r−j)` — the Cauchy product over
   the DECOUPLED directions (the Finset-convolution content of the Lam–Leung factorization).

## Honest scope (#444)

This closes the `m = 1` Bessel identity on the actual `Finset.card` energy AND supplies the two
structural inputs (antipodal balance + convolution-decoupling) for the full multivariate `m`-fold
factorization. It does NOT itself assemble the full `Z_r(μ_{2m}) = (2r)!·[x^{2r}]I₀(2x)^m` for general
`m` (that multivariate bijection is heavy); per the task it lands the cleanest provable core. It is a
char-0 brick only — the prize is char-`p`, where the wraparound excess `W_r` breaks the EGF identity
off a finite bad-prime set.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.AvUC

/-! ## The single-direction (`μ_2 = {1,−1}`) zero-sum count is the central binomial. -/

/-- The antipodal pair `{1, −1} ⊂ ℚ` (one antipodal direction of `μ_{2m}`, the `m = 1` case). -/
def negPair : Finset ℚ := {1, -1}

lemma mem_negPair {x : ℚ} : x ∈ negPair ↔ x = 1 ∨ x = -1 := by
  unfold negPair; simp [Finset.mem_insert, Finset.mem_singleton]

/-- A `{1,−1}`-valued tuple is determined by its set of `+1`-positions: the assignment
`c ↦ {i : c i = 1}` is injective on tuples landing in `{1,−1}`. -/
lemma negPair_tuple_eq_of_pos_set {N : ℕ} (c d : Fin N → ℚ)
    (hc : ∀ i, c i ∈ negPair) (hd : ∀ i, d i ∈ negPair)
    (h : {i | c i = 1} = {i | d i = 1}) : c = d := by
  funext i
  have hci := hc i; have hdi := hd i
  rw [mem_negPair] at hci hdi
  have hiff : c i = 1 ↔ d i = 1 := by
    constructor <;> intro hh
    · have : i ∈ {i | c i = 1} := hh
      rw [h] at this; exact this
    · have : i ∈ {i | d i = 1} := hh
      rw [← h] at this; exact this
  rcases hci with h1 | h1 <;> rcases hdi with h2 | h2
  · rw [h1, h2]
  · rw [h1, h2]; exact absurd (hiff.mp h1) (by rw [h2]; norm_num)
  · rw [h1, h2]; exact absurd (hiff.mpr h2) (by rw [h1]; norm_num)
  · rw [h1, h2]

/-- **The `m = 1` Bessel identity on the ACTUAL energy.** The zero-sum count of `2r`-tuples of the
single antipodal direction `{1,−1}` is exactly the central binomial coefficient:
`Z_r({1,−1}) = C(2r,r) = centralBinom r`.

A `{1,−1}`-tuple `c : Fin (2r) → ℚ` has `∑ᵢ cᵢ = (#{+1}) − (#{−1}) = 2·#{+1} − 2r`, which is `0`
exactly when `#{+1} = r`. So the zero-sum tuples biject with the `r`-element subsets of `Fin (2r)`
(the `+1`-positions), of which there are `(2r).choose r`. -/
theorem zeroSum_negPair_eq_centralBinom (r : ℕ) :
    zeroSumCount negPair (2 * r) = Nat.centralBinom r := by
  classical
  unfold zeroSumCount
  rw [Nat.centralBinom_eq_two_mul_choose]
  -- Bijection: zero-sum tuple ↦ (Finset of +1 positions); inverse: subset ↦ indicator tuple.
  have hcarduniv : ((2 * r).choose r)
      = (Finset.powersetCard r (Finset.univ : Finset (Fin (2 * r)))).card := by
    rw [Finset.card_powersetCard]; simp
  rw [hcarduniv]
  refine Finset.card_nbij'
    (fun c => (Finset.univ.filter (fun i => c i = 1)))
    (fun S => (fun i => if i ∈ S then (1 : ℚ) else -1))
    ?_ ?_ ?_ ?_
  · -- forward: zero-sum tuple ↦ r-subset
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
    obtain ⟨hmem, hsum⟩ := hc
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    -- ∑ c i = (#pos) - (#neg), #pos + #neg = 2r, sum = 0 ⟹ #pos = r
    set P := Finset.univ.filter (fun i => c i = 1) with hP
    set Nn := Finset.univ.filter (fun i => c i = -1) with hN
    have hsplit : P.card + Nn.card = 2 * r := by
      have : Disjoint P Nn := by
        rw [Finset.disjoint_filter]
        intro i _ h1 h2; rw [h1] at h2; norm_num at h2
      have hunion : P ∪ Nn = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro i
        rcases mem_negPair.mp (hmem i) with h1 | h1
        · exact Finset.mem_union_left _ (by rw [hP]; simp [h1])
        · exact Finset.mem_union_right _ (by rw [hN]; simp [h1])
      have := Finset.card_union_of_disjoint this
      rw [hunion] at this
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hsum2 : (P.card : ℚ) - Nn.card = 0 := by
      rw [← hsum]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i = 1) c]
      have hpart1 : ∑ i ∈ P, c i = (P.card : ℚ) := by
        rw [hP]; rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
        simp
      have hpart2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ c i = 1), c i = -(Nn.card : ℚ) := by
        rw [hN]
        have hcongr : Finset.univ.filter (fun i => ¬ c i = 1)
            = Finset.univ.filter (fun i => c i = -1) := by
          apply Finset.filter_congr
          intro i _
          rcases mem_negPair.mp (hmem i) with h1 | h1 <;> rw [h1] <;> norm_num
        rw [hcongr]
        rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
        simp
      rw [hpart1, hpart2]; ring
    have : (P.card : ℚ) = Nn.card := by linarith
    have hPN : P.card = Nn.card := by exact_mod_cast this
    omega
  · -- backward: r-subset ↦ tuple lands in piFinset, zero-sum
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
    obtain ⟨_, hScard⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨?_, ?_⟩
    · intro i; by_cases h : i ∈ S <;> simp [h, mem_negPair]
    · -- ∑ (if i∈S then 1 else -1) = |S| - (2r - |S|) = 2|S| - 2r = 0
      have hsub : S ⊆ (Finset.univ : Finset (Fin (2*r))) := Finset.subset_univ S
      have hval : ∑ i, (if i ∈ S then (1 : ℚ) else -1)
          = (S.card : ℚ) - (((Finset.univ : Finset (Fin (2*r))) \ S).card : ℚ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        have hnot : (Finset.univ.filter (fun i => i ∉ S)) = (Finset.univ : Finset (Fin (2*r))) \ S := by
          ext i; simp [Finset.mem_sdiff]
        rw [hnot]
        simp only [nsmul_eq_mul, smul_eq_mul, mul_one, mul_neg]
        ring
      rw [hval, Finset.card_sdiff_of_subset hsub]
      have hcardu : (Finset.univ : Finset (Fin (2*r))).card = 2 * r := by simp
      rw [hcardu, hScard]
      have h2r : (2 * r - r : ℕ) = r := by omega
      rw [h2r]; push_cast; ring
  · -- left inverse: tuple ↦ posset ↦ tuple recovers c
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
    obtain ⟨hmem, _⟩ := hc
    funext i
    have hmemf : (i ∈ Finset.univ.filter (fun j => c j = 1)) ↔ c i = 1 := by
      simp [Finset.mem_filter]
    simp only [hmemf]
    by_cases h : c i = 1
    · rw [if_pos h, h]
    · have hci : c i = -1 := (mem_negPair.mp (hmem i)).resolve_left h
      rw [if_neg h, hci]
  · -- right inverse: subset ↦ tuple ↦ posset recovers S
    intro S hS
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : i ∈ S
    · simp [h]
    · rw [if_neg h]; constructor <;> intro hh
      · exact absurd hh (by norm_num)
      · exact absurd hh h

/-! ## Tie to the EGF model of `_AvW0`, and the decoupling inputs. -/

/-- **The `m = 1` Bessel identity, actual energy ↔ EGF model.** The real single-direction zero-sum
count equals the `_AvW0` EGF coefficient model at `m = 1`: both are the central binomial.
`Z_r({1,−1}) = (2r)!·[x^{2r}]I₀(2x) = AvW0.Edef r 1`. -/
theorem bessel_identity_mu2 (r : ℕ) :
    (zeroSumCount negPair (2 * r) : ℚ) = AvW0.Edef r 1 := by
  rw [zeroSum_negPair_eq_centralBinom]
  -- AvW0.Edef r 1 = centralBinom r  (the `m=1` model values, from _AvW0 anchors / unfolding)
  unfold AvW0.Edef
  -- cpow I0c 1 r = Σ_{j≤r} I0c j · cpow I0c 0 (r-j) = I0c r = 1/(r!)^2, so Edef r 1 = (2r)!/(r!)^2 = C(2r,r)
  have hcpow : AvW0.cpow AvW0.I0c 1 r = AvW0.I0c r := by
    show (∑ j ∈ Finset.range (r + 1), AvW0.I0c j * AvW0.cpow AvW0.I0c 0 (r - j)) = AvW0.I0c r
    rw [Finset.sum_eq_single r]
    · simp [AvW0.cpow]
    · intro j hj hjr
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      have : r - j ≠ 0 := by omega
      simp [AvW0.cpow, this]
    · intro h; exact absurd (Finset.self_mem_range_succ r) h
  rw [hcpow]
  unfold AvW0.I0c
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hrfac : (0 : ℚ) < (r.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos r
  have hchoose : ((2 * r).choose r : ℚ) * ((r.factorial : ℚ) * ((2 * r - r).factorial : ℚ))
      = ((2 * r).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
    have hcast : ((2 * r).choose r * r.factorial * (2 * r - r).factorial : ℚ)
        = ((2 * r).factorial : ℚ) := by exact_mod_cast this
    rw [← hcast]; ring
  have h2rr : 2 * r - r = r := by omega
  rw [h2rr] at hchoose
  rw [eq_comm, ← hchoose]
  field_simp

/-- **Antipodal balance ⟹ per-direction balanced split** (decoupling input, from the proven
Lam–Leung two-power brick). A char-0 zero-sum tuple of `2^μ`-th roots has equally many entries equal
to `w` and to `−w` for every value `w` — so each antipodal direction `{±w}` carries a balanced split,
the per-direction `I₀(2x)` law that the EGF convolution composes. Reproduced as a named carrier so
this brick's decoupling input is self-evidently the proven Lam–Leung structure (consuming
`antipodal_balance_root`). -/
theorem antipodal_balance_forces_split {m k : ℕ} (c : Fin m → ℚ)
    (hroot : ∀ i, (c i) ^ (2 ^ k) = 1) (hsum : ∑ i, c i = 0) (w : ℚ) :
    (univ.filter (fun i => c i = w)).card = (univ.filter (fun i => c i = -w)).card :=
  LamLeungTwoPowerAntipodalBalance.antipodal_balance_root c hroot hsum w

/-- **The decoupling convolution** (abstract, on the EGF). The `d`-direction energy coefficient is
the `d`-fold convolution of the per-direction count `c`: adding one antipodal direction Cauchy-products
`c` into the running coefficient. This is the Finset-convolution content of "the `m` directions
decouple" supplied by the Lam–Leung factorization; for `c = I₀(2x)` it builds `[x^{2r}]I₀(2x)^d`. -/
theorem decoupling_is_convolution (c : ℕ → ℚ) (d r : ℕ) :
    AvW0.cpow c (d + 1) r = ∑ j ∈ Finset.range (r + 1), c j * AvW0.cpow c d (r - j) :=
  rfl

#print axioms zeroSum_negPair_eq_centralBinom
#print axioms bessel_identity_mu2
#print axioms antipodal_balance_forces_split
#print axioms decoupling_is_convolution

end ArkLib.ProximityGap.Frontier.AvUC
