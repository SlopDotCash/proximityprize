/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Tactic.Abel

/-!
# The Gauss-phase index-parity separation (Proximity Prize #407, angle: gauss-phase-flatness-algebra)

This file isolates, **axiom-clean**, the precise *algebraic* obstruction discovered while attacking
the Gauss-phase DFT flatness directly (the `gauss-phase-flatness-algebra` angle of #407).

## Background (the object)

In the prize regime one fixes the maximal dyadic FFT subgroup `μ_n ⊆ 𝔽_p^*`, `n = 2^a` taking the
**entire** 2-part of `p − 1`, index `m = (p−1)/n`. The worst-case incomplete-subgroup-sum house
`B = max_{b≠0}‖∑_{x∈μ_n} e_p(bx)‖` equals (up to the `√p/m` scale and the `j=0` term) the **sup-norm
of the `m`-DFT of the unimodular Gauss-phase sequence** `a_j = τ(ψ^j)/√p` (`|a_j| = 1` for `m ∤ j`),
where `ψ` is a multiplicative character of order `m`. The prize floor `δ* = average` is *equivalent*
to flatness of this DFT, `max_b ‖∑_j w_b^{-j} a_j‖ ≤ C·√(m·log m)`.

The phase sequence carries a rich algebra: a Jacobi-sum **cocycle** `a_i a_j = (J(ψ^i,ψ^j)/√p)·a_{i+j}`
(unimodular structure constants), a Galois action `σ_t : a_j ↦ a_{jt}`, and — when an order-2
character is available among the `ψ`-powers — a Hasse–Davenport **duplication self-similarity**
`a_j · a_{j+m/2} = (unit) · a_{2j} · a_{m/2}` (machine-verified to `1e-13`,
`scripts/probes/_407` gauss-phase probes).

## The result (the algebraic reason the dyadic structure is invisible to the phase DFT)

The duplication self-similarity is the only lever by which the *dyadic* (2-power) structure of `μ_n`
could special-case the phase DFT toward flatness. It requires an order-2 character **inside the index
group** `ℤ/m`, i.e. requires `m` even. But in the prize regime `m` is **odd**:

* `prizeIndex_odd` : if `n = 2^a` is the full 2-part of `p−1` (`padicValNat 2 (p−1) = a`), then
  `m = (p−1)/n` is odd.

Consequently the doubling map `x ↦ 2x` on `ℤ/m` is a **bijection** (`doubling_bijective_of_odd`), so
the Hasse–Davenport order-2 fold *permutes* the phase sequence rather than folding it 2-to-1: it
provides **no** dyadic self-reduction on the index side. The 2-power structure lives entirely on the
*subgroup* side `μ_n`; the index group `ℤ/m`, where the flatness/DFT question actually lives, is of
**odd order and sees no dyadic structure at all**.

This is the *algebraic explanation* of the previously only-numerically-refuted "2-power escape"
(`RESEARCH_SYNTHESIS_407_TANGENT.md §5`): there is no extra 2-power cancellation in the phase DFT
because the 2-power and the DFT live on coprime-order (odd `m` vs `2^a`) sides of the splitting
`𝔽_p^* ≅ μ_n × (ℤ/m)`.

## Honesty contract (this does NOT close the prize)

This file proves a **structural separation**, not a flatness bound. The flatness of the `m`-DFT of
`(a_j)` over the odd group `ℤ/m` is exactly the open √-cancellation core (effective Jacobi-sum
equidistribution at constant index — the same wall as every other face, `RESEARCH_SYNTHESIS_407.md`).
What is proven here is the precise, citable reason the dyadic structure cannot help: the lever needs
`m` even, the prize forces `m` odd. No flatness, no `δ*` pin, is claimed.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Berndt–Evans–Williams, *Gauss and Jacobi Sums* (Hasse–Davenport product relation, §11.4).
-/

namespace ArkLib.ProximityGap.GaussPhaseFlatnessAlgebra

/-! ## §1  The prize-regime index parity -/

/-- **The prize index is odd.** If `n = 2^a` is the *full* 2-part of `p − 1` (the maximal dyadic FFT
domain: `padicValNat 2 (p−1) = a`), then the index `m = (p−1)/2^a` is odd.

This is the algebraic core: the 2-power `n` absorbs the entire 2-adic valuation of `p−1`, so the
quotient is coprime to 2. Equivalently, an order-2 character of `𝔽_p^*` lies in `μ_n` (the dyadic
subgroup), never in the index group `ℤ/m`. -/
theorem prizeIndex_odd {p a : ℕ} (hp : 1 < p) (hval : padicValNat 2 (p - 1) = a) :
    Odd ((p - 1) / 2 ^ a) := by
  have hp1 : 0 < p - 1 := by omega
  -- `padicValNat 2 N = a` means `2^a ∣ N` and `2^(a+1) ∤ N`.
  have hdvd : 2 ^ a ∣ (p - 1) := hval ▸ pow_padicValNat_dvd
  obtain ⟨m, hm⟩ := hdvd
  have hmne : m ≠ 0 := by rintro rfl; simp at hm; omega
  -- so `(p-1)/2^a = m`
  have hquot : (p - 1) / 2 ^ a = m := by
    rw [hm]; exact Nat.mul_div_cancel_left m (by positivity)
  rw [hquot]
  -- if `m` were even, `2^(a+1) ∣ p−1`, contradicting `padicValNat 2 (p−1) = a`.
  rw [Nat.odd_iff]
  by_contra hne
  have heven : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨k, hk⟩ := heven
  have hdvd2 : 2 ^ (a + 1) ∣ (p - 1) := by
    refine ⟨k, ?_⟩
    rw [hm, hk]; ring
  have hle : a + 1 ≤ padicValNat 2 (p - 1) :=
    (Nat.pow_dvd_iff_le_padicValNat (by norm_num) hp1.ne').mp hdvd2
  omega

/-! ## §2  The doubling map on the odd index group is a bijection -/

/-- **Doubling is bijective on a finite group of odd order.** In `ℤ/m` with `m` odd, `x ↦ 2x` is a
bijection (its inverse is multiplication by `(m+1)/2`). Hence the Hasse–Davenport order-2 duplication,
which acts on the phase index by doubling, *permutes* the phase sequence rather than folding it 2-to-1:
it offers no dyadic self-reduction on the index side. We state the abstract version: in any additive
group `G` of finite odd order, `x ↦ x + x` is bijective. -/
theorem doubling_bijective_of_odd {G : Type*} [AddCommGroup G] [Fintype G]
    (hodd : Odd (Fintype.card G)) :
    Function.Bijective (fun x : G => x + x) := by
  -- `x ↦ x + x = 2 • x`. On a finite group, multiplication by an integer coprime to the order is
  -- bijective. Here `2` is coprime to the odd order, so `2 • ·` is bijective.
  -- We prove injectivity (⟹ bijectivity on a finite type).
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  intro x y hxy
  simp only at hxy
  -- `x + x = y + y ⟹ 2 • (x - y) = 0`. Since `2` is coprime to `|G|` (= order), `x - y = 0`.
  have h2 : (2 : ℕ) • (x - y) = 0 := by
    have heq : (2 : ℕ) • (x - y) = (x + x) - (y + y) := by
      rw [two_nsmul]; abel
    rw [heq, hxy, sub_self]
  -- the order of `x - y` divides 2 and divides |G| (odd), so divides gcd(2,|G|)=1, so `x-y=0`.
  have hord : addOrderOf (x - y) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero h2
  have hordG : addOrderOf (x - y) ∣ Fintype.card G := addOrderOf_dvd_card
  have hcop : Nat.Coprime 2 (Fintype.card G) := by
    rw [Nat.coprime_two_left]; exact hodd
  have hgcd : addOrderOf (x - y) ∣ Nat.gcd 2 (Fintype.card G) := Nat.dvd_gcd hord hordG
  rw [hcop] at hgcd
  have hone : addOrderOf (x - y) = 1 := Nat.dvd_one.mp hgcd
  have hxy0 : x - y = 0 := AddMonoid.addOrderOf_eq_one_iff.mp hone
  exact sub_eq_zero.mp hxy0

/-! ## §3  The packaged separation statement -/

/-- **The dyadic-structure separation (packaged).** In the prize regime (`n = 2^a` the full 2-part of
`p − 1`), the index group `ℤ/m` (`m = (p−1)/2^a`) has *odd* order, hence (i) contains no order-2
element and (ii) the doubling map is bijective. Therefore the Hasse–Davenport order-2 duplication —
the unique algebraic lever by which the 2-power structure of `μ_n` could special-case the Gauss-phase
DFT — is unavailable on the index side. The 2-power structure and the DFT live on coprime-order sides
of `𝔽_p^* ≅ μ_n × (ℤ/m)`. -/
theorem dyadic_invisible_to_index {p a : ℕ} (hp : 1 < p) (hval : padicValNat 2 (p - 1) = a)
    {G : Type*} [AddCommGroup G] [Fintype G] (hcard : Fintype.card G = (p - 1) / 2 ^ a) :
    Odd (Fintype.card G) ∧ Function.Bijective (fun x : G => x + x) := by
  have hodd : Odd (Fintype.card G) := hcard ▸ prizeIndex_odd hp hval
  exact ⟨hodd, doubling_bijective_of_odd hodd⟩

end ArkLib.ProximityGap.GaussPhaseFlatnessAlgebra

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.GaussPhaseFlatnessAlgebra
#print axioms prizeIndex_odd
#print axioms doubling_bijective_of_odd
#print axioms dyadic_invisible_to_index
end AxiomAudit
